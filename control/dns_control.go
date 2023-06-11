/*
 * SPDX-License-Identifier: AGPL-3.0-only
 * Copyright (c) 2023, daeuniverse Organization <dae@v2raya.org>
 */

package control

import (
	"context"
	"encoding/binary"
	"fmt"
	"io"
	"math"
	"net"
	"net/netip"
	"strings"
	"sync"
	"time"

	"github.com/daeuniverse/dae/common"

	"github.com/daeuniverse/dae/common/consts"
	"github.com/daeuniverse/dae/common/netutils"
	"github.com/daeuniverse/dae/component/dns"
	"github.com/daeuniverse/dae/component/outbound"
	"github.com/daeuniverse/dae/component/outbound/dialer"
	"github.com/mohae/deepcopy"
	"github.com/mzz2017/softwind/netproxy"
	"github.com/mzz2017/softwind/pkg/fastrand"
	"github.com/mzz2017/softwind/pool"
	"github.com/sirupsen/logrus"
	"golang.org/x/net/dns/dnsmessage"
)

const (
	MaxDnsLookupDepth  = 3
	minFirefoxCacheTtl = 120
)

type IpVersionPrefer int

const (
	IpVersionPrefer_No IpVersionPrefer = 0
	IpVersionPrefer_4  IpVersionPrefer = 4
	IpVersionPrefer_6  IpVersionPrefer = 6
)

var (
	ErrSuspectedRushAnswer     = fmt.Errorf("suspected DNS rush-answer")
	ErrUnsupportedQuestionType = fmt.Errorf("unsupported question type")
)

type DnsControllerOption struct {
	Log                 *logrus.Logger
	CacheAccessCallback func(cache *DnsCache) (err error)
	CacheRemoveCallback func(cache *DnsCache) (err error)
	NewCache            func(fqdn string, answers []dnsmessage.Resource, deadline time.Time) (cache *DnsCache, err error)
	BestDialerChooser   func(req *udpRequest, upstream *dns.Upstream) (*dialArgument, error)
	IpVersionPrefer     int
	FixedDomainTtl      map[string]int
}

type DnsController struct {
	handling sync.Map

	routing     *dns.Dns
	qtypePrefer dnsmessage.Type

	log                 *logrus.Logger
	cacheAccessCallback func(cache *DnsCache) (err error)
	cacheRemoveCallback func(cache *DnsCache) (err error)
	newCache            func(fqdn string, answers []dnsmessage.Resource, deadline time.Time) (cache *DnsCache, err error)
	bestDialerChooser   func(req *udpRequest, upstream *dns.Upstream) (*dialArgument, error)

	fixedDomainTtl map[string]int
	// mutex protects the dnsCache.
	dnsCacheMu sync.Mutex
	dnsCache   map[string]*DnsCache
}

func parseIpVersionPreference(prefer int) (dnsmessage.Type, error) {
	switch prefer := IpVersionPrefer(prefer); prefer {
	case IpVersionPrefer_No:
		return 0, nil
	case IpVersionPrefer_4:
		return dnsmessage.TypeA, nil
	case IpVersionPrefer_6:
		return dnsmessage.TypeAAAA, nil
	default:
		return 0, fmt.Errorf("unknown preference: %v", prefer)
	}
}

func NewDnsController(routing *dns.Dns, option *DnsControllerOption) (c *DnsController, err error) {
	// Parse ip version preference.
	prefer, err := parseIpVersionPreference(option.IpVersionPrefer)
	if err != nil {
		return nil, err
	}

	return &DnsController{
		routing:     routing,
		qtypePrefer: prefer,

		log:                 option.Log,
		cacheAccessCallback: option.CacheAccessCallback,
		cacheRemoveCallback: option.CacheRemoveCallback,
		newCache:            option.NewCache,
		bestDialerChooser:   option.BestDialerChooser,

		fixedDomainTtl: option.FixedDomainTtl,
		dnsCacheMu:     sync.Mutex{},
		dnsCache:       make(map[string]*DnsCache),
	}, nil
}

func (c *DnsController) cacheKey(qname string, qtype dnsmessage.Type) string {
	// To fqdn.
	if !strings.HasSuffix(qname, ".") {
		qname = qname + "."
	}
	return strings.ToLower(qname) + qtype.String()
}

func (c *DnsController) RemoveDnsRespCache(qname string, qtype dnsmessage.Type) {
	c.dnsCacheMu.Lock()
	key := c.cacheKey(qname, qtype)
	_, ok := c.dnsCache[key]
	if ok {
		delete(c.dnsCache, key)
	}
	c.dnsCacheMu.Unlock()
}
func (c *DnsController) LookupDnsRespCache(qname string, qtype dnsmessage.Type) (cache *DnsCache) {
	c.dnsCacheMu.Lock()
	cache, ok := c.dnsCache[c.cacheKey(qname, qtype)]
	c.dnsCacheMu.Unlock()
	// We should make sure the cache did not expire, or
	// return nil and request a new lookup to refresh the cache.
	if ok && cache.Deadline.After(time.Now()) {
		return cache
	}
	return nil
}

// LookupDnsRespCache_ will modify the msg in place.
func (c *DnsController) LookupDnsRespCache_(msg *dnsmessage.Message) (resp []byte) {
	if len(msg.Questions) == 0 {
		return nil
	}
	q := msg.Questions[0]
	if msg.Response {
		return nil
	}
	switch q.Type {
	case dnsmessage.TypeA, dnsmessage.TypeAAAA:
	default:
		return nil
	}
	cache := c.LookupDnsRespCache(q.Name.String(), q.Type)
	if cache != nil {
		cache.FillInto(msg)
		b, err := msg.Pack()
		if err != nil {
			c.log.Warnf("failed to pack: %v", err)
			return nil
		}
		if err = c.cacheAccessCallback(cache); err != nil {
			c.log.Warnf("failed to BatchUpdateDomainRouting: %v", err)
			return nil
		}
		return b
	}
	return nil
}

func (c *DnsController) updateDnsCache(msg *dnsmessage.Message, ttl uint32, q *dnsmessage.Question) error {
	// Update DnsCache.
	if c.log.IsLevelEnabled(logrus.TraceLevel) {
		c.log.WithFields(logrus.Fields{
			"_qname":   q.Name,
			"rcode":    msg.RCode,
			"ans":      FormatDnsRsc(msg.Answers),
			"auth":     FormatDnsRsc(msg.Authorities),
			"addition": FormatDnsRsc(msg.Additionals),
		}).Tracef("Update DNS record cache")
	}

	if err := c.UpdateDnsCacheTtl(q.Name.String(), q.Type.String(), msg.Answers, int(ttl)); err != nil {
		return err
	}
	return nil
}

func (c *DnsController) __updateDnsCacheDeadline(host string, dnsTyp string, answers []dnsmessage.Resource, deadlineFunc func(now time.Time, host string) time.Time) (err error) {
	var fqdn string
	if strings.HasSuffix(host, ".") {
		fqdn = host
		host = host[:len(host)-1]
	} else {
		fqdn = host + "."
	}
	// Bypass pure IP.
	if _, err = netip.ParseAddr(host); err == nil {
		return nil
	}

	now := time.Now()
	deadline := deadlineFunc(now, host)

	cacheKey := fqdn + dnsTyp
	c.dnsCacheMu.Lock()
	cache, ok := c.dnsCache[cacheKey]
	if ok {
		cache.Answers = answers
		cache.Deadline = deadline
		c.dnsCacheMu.Unlock()
	} else {
		cache, err = c.newCache(fqdn, answers, deadline)
		if err != nil {
			c.dnsCacheMu.Unlock()
			return err
		}
		c.dnsCache[cacheKey] = cache
		c.dnsCacheMu.Unlock()
	}
	if err = c.cacheAccessCallback(cache); err != nil {
		return err
	}

	return nil
}

func (c *DnsController) UpdateDnsCacheDeadline(host string, dnsTyp string, answers []dnsmessage.Resource, deadline time.Time) (err error) {
	return c.__updateDnsCacheDeadline(host, dnsTyp, answers, func(now time.Time, host string) time.Time {
		if fixedTtl, ok := c.fixedDomainTtl[host]; ok {
			/// NOTICE: Cannot set TTL accurately.
			if now.Sub(deadline).Seconds() > float64(fixedTtl) {
				return now.Add(time.Duration(fixedTtl) * time.Second)
			}
		}
		return deadline
	})
}

func (c *DnsController) UpdateDnsCacheTtl(host string, dnsTyp string, answers []dnsmessage.Resource, ttl int) (err error) {
	return c.__updateDnsCacheDeadline(host, dnsTyp, answers, func(now time.Time, host string) time.Time {
		if fixedTtl, ok := c.fixedDomainTtl[host]; ok {
			return now.Add(time.Duration(fixedTtl) * time.Second)
		} else {
			return now.Add(time.Duration(ttl) * time.Second)
		}
	})
}

func (c *DnsController) DnsRespHandlerFactory() func(data []byte, from netip.AddrPort) (msg *dnsmessage.Message, updateCache func() error, err error) {
	return func(data []byte, from netip.AddrPort) (*dnsmessage.Message, func() error, error) {
		var msg dnsmessage.Message
		var err error
		dummyUpdateCache := func() error { return nil }
		if err = msg.Unpack(data); err != nil {
			return nil, nil, fmt.Errorf("unpack dns pkt: %w", err)
		}
		// Check healthy resp.
		if !msg.Response || len(msg.Questions) == 0 {
			return &msg, dummyUpdateCache, nil
		}

		q := msg.Questions[0]

		// Check suc resp.
		if msg.RCode != dnsmessage.RCodeSuccess {
			return &msg, dummyUpdateCache, nil
		}

		// Get TTL.
		var ttl uint32
		for i := range msg.Answers {
			if ttl == 0 {
				ttl = msg.Answers[i].Header.TTL
				break
			}
		}
		if ttl == 0 {
			// It seems no answers (NXDomain).
			ttl = minFirefoxCacheTtl
		}

		// Check req type.
		switch q.Type {
		case dnsmessage.TypeA, dnsmessage.TypeAAAA:
		default:
			return &msg, func() error {
				// Update DnsCache.
				if err = c.updateDnsCache(&msg, ttl, &q); err != nil {
					return err
				}
				return nil
			}, nil
		}

		// Set ttl.
		for i := range msg.Answers {
			// Set TTL = zero. This requests applications must resend every request.
			// However, it may be not defined in the standard.
			msg.Answers[i].Header.TTL = 0
		}

		// Check if request A/AAAA record.
		var reqIpRecord bool
	loop:
		for i := range msg.Questions {
			switch msg.Questions[i].Type {
			case dnsmessage.TypeA, dnsmessage.TypeAAAA:
				reqIpRecord = true
				break loop
			}
		}
		if !reqIpRecord {
			return &msg, func() error {
				// Update DnsCache.
				if err = c.updateDnsCache(&msg, ttl, &q); err != nil {
					return err
				}
				return nil
			}, nil
		}

		// Pack to get newData.
		return &msg, func() error {
			// Update DnsCache.
			if err = c.updateDnsCache(&msg, ttl, &q); err != nil {
				return err
			}
			return nil
		}, nil
	}
}

type udpRequest struct {
	lanWanFlag    consts.LanWanFlag
	realSrc       netip.AddrPort
	realDst       netip.AddrPort
	src           netip.AddrPort
	lConn         *net.UDPConn
	routingResult *bpfRoutingResult
}

type dialArgument struct {
	l4proto      consts.L4ProtoStr
	ipversion    consts.IpVersionStr
	bestDialer   *dialer.Dialer
	bestOutbound *outbound.DialerGroup
	bestTarget   netip.AddrPort
	mark         uint32
}

func (c *DnsController) Handle_(dnsMessage *dnsmessage.Message, req *udpRequest) (err error) {
	if c.log.IsLevelEnabled(logrus.TraceLevel) && len(dnsMessage.Questions) > 0 {
		q := dnsMessage.Questions[0]
		c.log.Tracef("Received UDP(DNS) %v <-> %v: %v %v",
			RefineSourceToShow(req.realSrc, req.realDst.Addr(), req.lanWanFlag), req.realDst.String(), strings.ToLower(q.Name.String()), q.Type,
		)
	}

	if dnsMessage.Response {
		return fmt.Errorf("DNS request expected but DNS response received")
	}

	// Prepare qname, qtype.
	var qname string
	var qtype dnsmessage.Type
	if len(dnsMessage.Questions) != 0 {
		qname = dnsMessage.Questions[0].Name.String()
		qtype = dnsMessage.Questions[0].Type
	}

	// Check ip version preference and qtype.
	switch qtype {
	case dnsmessage.TypeA, dnsmessage.TypeAAAA:
		if c.qtypePrefer == 0 {
			return c.handle_(dnsMessage, req, true)
		}
	default:
		return c.handle_(dnsMessage, req, true)
	}

	// Try to make both A and AAAA lookups.
	dnsMessage2 := deepcopy.Copy(dnsMessage).(*dnsmessage.Message)
	dnsMessage2.ID = uint16(fastrand.Intn(math.MaxUint16))
	var qtype2 dnsmessage.Type
	switch qtype {
	case dnsmessage.TypeA:
		qtype2 = dnsmessage.TypeAAAA
	case dnsmessage.TypeAAAA:
		qtype2 = dnsmessage.TypeA
	default:
		return fmt.Errorf("unexpected qtype path")
	}
	dnsMessage2.Questions[0].Type = qtype2

	done := make(chan struct{})
	go func() {
		_ = c.handle_(dnsMessage2, req, false)
		done <- struct{}{}
	}()
	err = c.handle_(dnsMessage, req, false)
	<-done
	if err != nil {
		return err
	}

	// Join results and consider whether to response.
	dnsMessage.Response = false
	resp := c.LookupDnsRespCache_(dnsMessage)
	if resp == nil {
		// resp is not valid.
		c.log.WithFields(logrus.Fields{
			"qname": qname,
		}).Tracef("Reject %v due to resp not valid", qtype.String())
		return c.sendReject_(dnsMessage, req)
	}
	// resp is valid.
	cache2 := c.LookupDnsRespCache(qname, qtype2)
	if c.qtypePrefer == qtype || cache2 == nil || !cache2.IncludeAnyIp() {
		return sendPkt(resp, req.realDst, req.realSrc, req.src, req.lConn, req.lanWanFlag)
	} else {
		return c.sendReject_(dnsMessage, req)
	}
}

func (c *DnsController) handle_(
	dnsMessage *dnsmessage.Message,
	req *udpRequest,
	needResp bool,
) (err error) {
	// Prepare qname, qtype.
	var qname string
	var qtype dnsmessage.Type
	if len(dnsMessage.Questions) != 0 {
		q := dnsMessage.Questions[0]
		qname = q.Name.String()
		qtype = q.Type
	}

	//// NOTICE: Rush-answer detector was removed because it does not always work in all districts.
	//// Make sure there is additional record OPT in the request to filter DNS rush-answer in the response process.
	//// Because rush-answer has no resp OPT. We can distinguish them from multiple responses.
	//// Note that additional record OPT may not be supported by home router either.
	//_, _ = EnsureAdditionalOpt(dnsMessage, true)

	// Route request.
	upstreamIndex, upstream, err := c.routing.RequestSelect(qname, qtype)
	if err != nil {
		return err
	}

	if upstreamIndex == consts.DnsRequestOutboundIndex_Reject {
		// Reject with empty answer.
		c.RemoveDnsRespCache(qname, qtype)
		return c.sendReject_(dnsMessage, req)
	}

	// No parallel for the same lookup.
	_mu, _ := c.handling.LoadOrStore(c.cacheKey(qname, qtype), new(sync.Mutex))
	mu := _mu.(*sync.Mutex)
	mu.Lock()
	defer mu.Unlock()

	if resp := c.LookupDnsRespCache_(dnsMessage); resp != nil {
		// Send cache to client directly.
		if needResp {
			if err = sendPkt(resp, req.realDst, req.realSrc, req.src, req.lConn, req.lanWanFlag); err != nil {
				return fmt.Errorf("failed to write cached DNS resp: %w", err)
			}
		}
		if c.log.IsLevelEnabled(logrus.DebugLevel) && len(dnsMessage.Questions) > 0 {
			q := dnsMessage.Questions[0]
			c.log.Debugf("UDP(DNS) %v <-> Cache: %v %v",
				RefineSourceToShow(req.realSrc, req.realDst.Addr(), req.lanWanFlag), strings.ToLower(q.Name.String()), q.Type,
			)
		}
		return nil
	}

	if c.log.IsLevelEnabled(logrus.TraceLevel) {
		upstreamName := upstreamIndex.String()
		if upstream != nil {
			upstreamName = upstream.String()
		}
		c.log.WithFields(logrus.Fields{
			"question": dnsMessage.Questions,
			"upstream": upstreamName,
		}).Traceln("Request to DNS upstream")
	}

	// Re-pack DNS packet.
	data, err := dnsMessage.Pack()
	if err != nil {
		return fmt.Errorf("pack DNS packet: %w", err)
	}
	return c.dialSend(0, req, data, dnsMessage.ID, upstream, needResp)
}

// sendReject_ send empty answer.
func (c *DnsController) sendReject_(dnsMessage *dnsmessage.Message, req *udpRequest) (err error) {
	dnsMessage.Answers = nil
	if len(dnsMessage.Questions) > 0 {
		dnsMessage.Answers = nil
	}
	dnsMessage.RCode = dnsmessage.RCodeSuccess
	dnsMessage.Response = true
	dnsMessage.RecursionAvailable = true
	dnsMessage.Truncated = false
	if c.log.IsLevelEnabled(logrus.TraceLevel) {
		c.log.WithFields(logrus.Fields{
			"question": dnsMessage.Questions,
		}).Traceln("Reject")
	}
	data, err := dnsMessage.Pack()
	if err != nil {
		return fmt.Errorf("pack DNS packet: %w", err)
	}
	if err = sendPkt(data, req.realDst, req.realSrc, req.src, req.lConn, req.lanWanFlag); err != nil {
		return err
	}
	return nil
}

func (c *DnsController) dialSend(invokingDepth int, req *udpRequest, data []byte, id uint16, upstream *dns.Upstream, needResp bool) (err error) {
	if invokingDepth >= MaxDnsLookupDepth {
		return fmt.Errorf("too deep DNS lookup invoking (depth: %v); there may be infinite loop in your DNS response routing", MaxDnsLookupDepth)
	}

	upstreamName := "asis"
	if upstream == nil {
		// As-is.

		// As-is should not be valid in response routing, thus using connection realDest is reasonable.
		var ip46 netutils.Ip46
		if req.realDst.Addr().Is4() {
			ip46.Ip4 = req.realDst.Addr()
		} else {
			ip46.Ip6 = req.realDst.Addr()
		}
		upstream = &dns.Upstream{
			Scheme:   "udp",
			Hostname: req.realDst.Addr().String(),
			Port:     req.realDst.Port(),
			Ip46:     &ip46,
		}
	} else {
		upstreamName = upstream.String()
	}

	// Select best dial arguments (outbound, dialer, l4proto, ipversion, etc.)
	dialArgument, err := c.bestDialerChooser(req, upstream)
	if err != nil {
		return err
	}

	networkType := &dialer.NetworkType{
		L4Proto:   dialArgument.l4proto,
		IpVersion: dialArgument.ipversion,
		IsDns:     true, // UDP relies on DNS check result.
	}

	// dnsRespHandler caches dns response and check rush answers.
	dnsRespHandler := c.DnsRespHandlerFactory()
	// Dial and send.
	var respMsg *dnsmessage.Message
	var updateCache func() error
	// defer in a recursive call will delay Close(), thus we Close() before
	// the next recursive call. However, a connection cannot be closed twice.
	// We should set a connClosed flag to avoid it.
	var connClosed bool
	var conn netproxy.Conn
	switch dialArgument.l4proto {
	case consts.L4ProtoStr_UDP:
		// Get udp endpoint.

		// TODO: connection pool.
		conn, err = dialArgument.bestDialer.Dial(
			common.MagicNetwork("udp", dialArgument.mark),
			dialArgument.bestTarget.String(),
		)
		if err != nil {
			return fmt.Errorf("failed to dial '%v': %w", dialArgument.bestTarget, err)
		}
		defer func() {
			if !connClosed {
				conn.Close()
			}
		}()

		_ = conn.SetDeadline(time.Now().Add(5 * time.Second))
		dnsReqCtx, cancelDnsReqCtx := context.WithTimeout(context.TODO(), 5*time.Second)
		defer cancelDnsReqCtx()
		go func() {
			// Send DNS request at 0, 2, 4 seconds.
			for {
				_, err = conn.Write(data)
				if err != nil {
					if c.log.IsLevelEnabled(logrus.DebugLevel) {
						c.log.WithFields(logrus.Fields{
							"to":      dialArgument.bestTarget.String(),
							"pid":     req.routingResult.Pid,
							"pname":   ProcessName2String(req.routingResult.Pname[:]),
							"mac":     Mac2String(req.routingResult.Mac[:]),
							"from":    req.realSrc.String(),
							"network": networkType.String(),
							"err":     err.Error(),
						}).Debugln("Failed to write UDP(DNS) packet request.")
					}
					return
				}
				select {
				case <-dnsReqCtx.Done():
					return
				case <-time.After(2 * time.Second):
				}
			}
		}()

		// We can block here because we are in a coroutine.
		respBuf := pool.Get(512)
		defer pool.Put(respBuf)
		for {
			// Wait for response.
			n, err := conn.Read(respBuf)
			if err != nil {
				return fmt.Errorf("failed to read from: %v (dialer: %v): %w", dialArgument.bestTarget, dialArgument.bestDialer.Property().Name, err)
			}
			respMsg, updateCache, err = dnsRespHandler(respBuf[:n], dialArgument.bestTarget)
			if err != nil {
				return err
			}
			if respMsg != nil {
				cancelDnsReqCtx()
				break
			}
		}
	case consts.L4ProtoStr_TCP:
		// We can block here because we are in a coroutine.

		conn, err = dialArgument.bestDialer.Dial(common.MagicNetwork("tcp", dialArgument.mark), dialArgument.bestTarget.String())
		if err != nil {
			return fmt.Errorf("failed to dial proxy to tcp: %w", err)
		}
		defer func() {
			if !connClosed {
				conn.Close()
			}
		}()

		_ = conn.SetDeadline(time.Now().Add(5 * time.Second))
		// We should write two byte length in the front of TCP DNS request.
		bReq := pool.Get(2 + len(data))
		defer pool.Put(bReq)
		binary.BigEndian.PutUint16(bReq, uint16(len(data)))
		copy(bReq[2:], data)
		_, err = conn.Write(bReq)
		if err != nil {
			return fmt.Errorf("failed to write DNS req: %w", err)
		}

		// Read two byte length.
		if _, err = io.ReadFull(conn, bReq[:2]); err != nil {
			return fmt.Errorf("failed to read DNS resp payload length: %w", err)
		}
		respLen := int(binary.BigEndian.Uint16(bReq))
		// Try to reuse the buf.
		var buf []byte
		if len(bReq) < respLen {
			buf = pool.Get(respLen)
			defer pool.Put(buf)
		} else {
			buf = bReq
		}
		var n int
		if n, err = io.ReadFull(conn, buf[:respLen]); err != nil {
			return fmt.Errorf("failed to read DNS resp payload: %w", err)
		}
		respMsg, updateCache, err = dnsRespHandler(buf[:n], dialArgument.bestTarget)
		if respMsg == nil && err == nil {
			err = fmt.Errorf("bad DNS response")
		}
		if err != nil {
			return fmt.Errorf("failed to write DNS resp to client: %w", err)
		}
	default:
		return fmt.Errorf("unexpected l4proto: %v", dialArgument.l4proto)
	}

	// Close conn before the recursive call.
	conn.Close()
	connClosed = true

	// Route response.
	upstreamIndex, nextUpstream, err := c.routing.ResponseSelect(respMsg, upstream)
	if err != nil {
		return err
	}

	respMsg.ID = id

	switch upstreamIndex {
	case consts.DnsResponseOutboundIndex_Accept:
		// Accept.
		if c.log.IsLevelEnabled(logrus.TraceLevel) {
			c.log.WithFields(logrus.Fields{
				"question": respMsg.Questions,
				"upstream": upstreamName,
			}).Traceln("Accept")
		}

		if c.log.IsLevelEnabled(logrus.InfoLevel) {
			var qname, qtype string
			if len(respMsg.Questions) > 0 {
				q := respMsg.Questions[0]
				qname = strings.ToLower(q.Name.String())
				qtype = q.Type.String()
			}
			fields := logrus.Fields{
				"network":  networkType.String(),
				"outbound": dialArgument.bestOutbound.Name,
				"policy":   dialArgument.bestOutbound.GetSelectionPolicy(),
				"dialer":   dialArgument.bestDialer.Property().Name,
				"_qname":   qname,
				"qtype":    qtype,
				"pid":      req.routingResult.Pid,
				"pname":    ProcessName2String(req.routingResult.Pname[:]),
				"mac":      Mac2String(req.routingResult.Mac[:]),
			}
			c.log.WithFields(fields).Infof("%v <-> %v", RefineSourceToShow(req.realSrc, req.realDst.Addr(), req.lanWanFlag), RefineAddrPortToShow(dialArgument.bestTarget))
		}
		// Keep the id the same with request.
		data, err = respMsg.Pack()
		if err != nil {
			return err
		}
		if needResp {
			if err = sendPkt(data, req.realDst, req.realSrc, req.src, req.lConn, req.lanWanFlag); err != nil {
				return err
			}
		}
		if err = updateCache(); err != nil {
			return err
		}
		return nil
	case consts.DnsResponseOutboundIndex_Reject:
		// Reject the request with empty answer.
		if c.log.IsLevelEnabled(logrus.InfoLevel) {
			c.log.WithFields(logrus.Fields{
				"question": respMsg.Questions,
				"upstream": upstreamName,
			}).Infoln("Reject with empty answer")
		}
		if needResp {
			return c.sendReject_(respMsg, req)
		} else {
			return nil
		}
	default:
		if c.log.IsLevelEnabled(logrus.TraceLevel) {
			c.log.WithFields(logrus.Fields{
				"question":      respMsg.Questions,
				"last_upstream": upstreamName,
				"next_upstream": nextUpstream.String(),
			}).Traceln("Change DNS upstream and resend")
		}
		return c.dialSend(invokingDepth+1, req, data, id, nextUpstream, needResp)
	}
}
