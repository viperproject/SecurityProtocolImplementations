package responder

//@ import arb "github.com/viperproject/ReusableProtocolVerificationLibrary/arbitrary"
//@ import att "github.com/viperproject/ReusableProtocolVerificationLibrary/attacker"
//@ import ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
import labeledlib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
//@ import u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"
//@ import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma/responder"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/responder"
//@ import pap "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/pattern"


//@ requires ResponderMem(responder)
//@ requires getPsk(responder) == tm.gamma(pskT)
//@ requires getKR(responder) == tm.gamma(ltkT)
//@ requires getPkI(responder) == tm.gamma(ltpkT)
//@ requires GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires ltkT.IsRandom()
//@ requires GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getAId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  ResponderMem(responder)
//@ ensures  ok ==> lib.ConnectionMem(conn) && lib.ConnectionNonceVal(conn) == 0
//@ ensures  ok ==> lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
//@ ensures  ok ==> lib.ConnectionSendKey(conn) == tm.gamma(kriT)
//@ ensures  ok ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
//@ ensures  ok ==> transportKeysWeakForwardSecrecy(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
//@ ensures  ok ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
func (responder *Responder) runHandshake( /*@ ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/ ) (conn *lib.Connection, ok bool /*@, ghost corrupted bool, ghost aSess uint32, ghost epkIX tm.Term, ghost ekrT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term @*/) {

	handshake := &lib.Handshake{}
	//@ ghost var sidIX, c3T, h4T tm.Term
	ok /*@, corrupted, sidIX, epkIX, c3T, h4T, aSess @*/ = responder.receiveRequest(handshake /*@, pskT, ltkT, ltpkT @*/)
	if !ok {
		return
	}

	//@ unfold ResponderMem(responder)
	//@ responder.llib.ApplyMonotonicity()
	//@ fold acc(ResponderMem(responder), 1/2)
	(responder.LibState).Println("Success Consuming Request")
	//@ fold acc(ResponderMem(responder), 1/2)
	ok /*@, ekrT, kirT, kriT @*/ = responder.sendResponse(handshake /*@, corrupted, pskT, ltkT, ltpkT, sidIX, epkIX, c3T, h4T, aSess @*/)
	if !ok {
		return
	}

	//@ s1 := responder.Snapshot()
	//@ aSessId := responder.getASessId(aSess)
	//@ bSessId := responder.getBSessId()
	//@ prefix := getSentSidRPrefix(s1, epkIX, ekrT, kirT, kriT, aSessId, bSessId)

	//@ unfold ResponderMem(responder)
	//@ responder.llib.ApplyMonotonicity()
	//@ fold ResponderMem(responder)

	//@ unfold acc(ResponderMem(responder), 1/4)
	(responder.LibState).Println("Success Sending Response")
	//@ fold acc(ResponderMem(responder), 1/4)

	//@ c7T := Term_c7(ltpkT, pskT, epkIX, c3T, ekrT)
	conn = responder.beginSymmetricSession(handshake /*@, c7T @*/)
	
	//@ unfold ResponderMem(responder)
	//@ responder.llib.ApplyMonotonicityWithSnap(prefix)
	//@ fold ResponderMem(responder)
	
	//@ corrupted = responder.establishTransportKeyLabeling(prefix, ltkT, ltpkT, pskT, epkIX, c3T, ekrT, kirT, kriT, aSess)
	//@ responder.proveSecurityProperties(epkIX, ekrT, kirT, kriT, aSess, corrupted)
	return
}

/*@
ghost
requires ResponderMem(responder)
requires sentSidR(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
requires prefix == getSentSidRPrefix(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
requires GetWgLabeling().IsLabeled(prefix, pskT, label.Public())
requires c3PropsCombined(prefix, ltkT, ltpkT, epkIX, c3T, responder.getASessId(aSess), responder.getBId())
requires GetWgLabeling().IsSecretKey(prefix, responder.getBSessId(), ekrT, labeling.KeyTypeDh(), WgEphemeralSk)
requires kirT == Term_k_IR(ltpkT, pskT, epkIX, c3T, ekrT)
requires kriT == Term_k_RI(ltpkT, pskT, epkIX, c3T, ekrT)
requires !GetWgLabeling().IsPublishable(prefix, Term_k2(ltkT, ltpkT, epkIX)) ==> sidIEventProps(prefix, epkIX, responder.getASessId(aSess), responder.getBId())
ensures  ResponderMem(responder)
ensures  responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, newCorrupted)
func (responder *Responder) establishTransportKeyLabeling(prefix tr.TraceEntry, ltkT, ltpkT, pskT, epkIX, c3T, ekrT, kirT, kriT tm.Term, aSess uint32) (newCorrupted bool) {
	aId := responder.getAId()
	aSessId := responder.getASessId(aSess)
	bId := responder.getBId()
	bSessId := responder.getBSessId()
	bothL := label.Readers(set[p.Id]{ aId, bId })

	newCorrupted = !GetWgLabeling().IsPublicKeyExistential(prefix, aSessId, epkIX, labeling.KeyTypeDh(), WgEphemeralSk)

	k2T := CreateK2(prefix, ltkT, ltpkT, epkIX, aSessId, bId)
	if GetWgLabeling().IsPublishable(prefix, k2T) {
		GetWgLabeling().CanFlowTransitive(prefix, bothL, GetWgLabeling().GetLabel(k2T), label.Public())
	}

	if GetWgLabeling().IsPublishable(prefix, c3T) {
		GetWgLabeling().CanFlowTransitive(prefix, bothL, GetWgLabeling().GetLabel(c3T), label.Public())
	}

	CreateKir(prefix, ltkT, ltpkT, pskT, epkIX, c3T, ekrT, aSessId, bSessId)
	CreateKri(prefix, ltkT, ltpkT, pskT, epkIX, c3T, ekrT, aSessId, bSessId)
	snap := responder.Snapshot()
	GetWgLabeling().IsSecretRelaxedMonotonic(prefix, snap, kirT, label.Readers(set[p.Id]{ aId, bSessId }), u.AeadKey(WgReceivingKey))
	GetWgLabeling().IsSecretRelaxedMonotonic(prefix, snap, kriT, label.Readers(set[p.Id]{ aId, bSessId }), u.AeadKey(WgSendingKey))
	GetWgLabeling().IsLabeledMonotonic(prefix, snap, GetWgUsage().getDhStaticFromKir(kirT), Label_DhStatic(aId, bId))
	GetWgLabeling().IsLabeledMonotonic(prefix, snap, GetWgUsage().getDhStaticEphemeral(kirT), Label_DhStaticEphemeral(aId, bSessId))
	
	if newCorrupted {
		GetWgLabeling().PublishableImpliesCorruption(prefix, c3T, label.Readers(set[p.Id]{ aId, bId }))
	} else {
		GetWgLabeling().IsLabeledRelaxedMonotonic(prefix, snap, kirT, label.Readers(set[p.Id]{ aSessId, bSessId }))
		GetWgLabeling().IsLabeledRelaxedMonotonic(prefix, snap, kriT, label.Readers(set[p.Id]{ aSessId, bSessId }))
		GetWgLabeling().IsLabeledPreciseMonotonic(prefix, snap, kirT, Label_k_IRPrecise(aSessId, bSessId))
		GetWgLabeling().IsLabeledPreciseMonotonic(prefix, snap, kriT, Label_k_IRPrecise(aSessId, bSessId))
	}
}
@*/

//@ requires ResponderMem(responder) && acc(hs)
//@ requires getPsk(responder) == tm.gamma(pskT)
//@ requires getKR(responder) == tm.gamma(ltkT)
//@ requires getPkI(responder) == tm.gamma(ltpkT)
//@ requires GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires ltkT.IsRandom()
//@ requires GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getAId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  ResponderMem(responder)
//@ ensures  responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()).isSuffix(responder.Snapshot())
//@ ensures  getPsk(responder) == tm.gamma(pskT)
//@ ensures  getKR(responder) == tm.gamma(ltkT)
//@ ensures  getPkI(responder) == tm.gamma(ltpkT)
//@ ensures  ok ==> HandshakeMem1(hs)
//@ ensures  ok ==> getSidI1(hs) == tm.gamma(sidIX)
//@ ensures  ok ==> getEpkI1(hs) == tm.gamma(epkIX)
//@ ensures  ok ==> getNKey1(hs) == tm.gamma(c3T)
//@ ensures  ok ==> getNHash1(hs) == tm.gamma(h4T)
//@ ensures  ok ==> GetWgLabeling().IsPublishable(responder.Snapshot(), sidIX)
//@ ensures  ok ==> c3PropsCombined(responder.Snapshot(), ltkT, ltpkT, epkIX, c3T, responder.getASessId(aSess), responder.getBId())
//@ ensures  ok ==> h4Props(responder.Snapshot(), h4T, ltkT, ltpkT, epkIX)
//@ ensures  ok ==> GetWgLabeling().IsLabeledRelaxed(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX), label.Readers(set[p.Id]{ responder.getAId(), responder.getBId() }))
//@ ensures  ok ==> (corrupted == GetWgLabeling().IsPublishable(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX)))
//@ ensures  ok && !corrupted ==> sidIEventProps(responder.Snapshot(), epkIX, responder.getASessId(aSess), responder.getBId())
func (responder *Responder) receiveRequest(hs *lib.Handshake /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/) (ok bool /*@, ghost corrupted bool, ghost sidIX tm.Term, ghost epkIX tm.Term, ghost c3T tm.Term, ghost h4T tm.Term, ghost aSess uint32 @*/) {

	//@ aId := responder.getAId()
	//@ bId := responder.getBId()
	
	//@ unfold ResponderMem(responder)
	packet, err /*@, term @*/ := responder.llib.Receive(lib.Principal(responder.a), lib.Principal(responder.b))
	ok = err == nil
	//@ responder.llib.ApplyMonotonicity()
	//@ fold ResponderMem(responder)
	if !ok {
		return
	}
	//@ b := labeledlib.Abs(packet)
	//@ unfold ResponderMem(responder)
	//@ responder.llib.MessageOccursImpliesMessageInv(lib.Principal(responder.a), lib.Principal(responder.b), term)
	//@ fold ResponderMem(responder)

	request, ok := lib.UnmarshalRequest(packet)
	if !ok {
		return
	}

	//@ BeforeConsume:
	//@ snapshot := responder.Snapshot()
	//@ ghost var ts tm.Bytes
	//@ ghost var tsX tm.Term
	//@ ghost var mac1X tm.Term
	//@ ghost var mac2X tm.Term
	ok /*@, ts, sidIX, epkIX, tsX, mac1X, mac2X @*/ = responder.consumeRequest(hs, request /*@, pskT, ltkT, ltpkT, term @*/)
	/*@
	ghost if ok {
		k2T := CreateK2(snapshot, ltkT, ltpkT, epkIX, aId, bId)
		corrupted = GetWgLabeling().IsPublishable(snapshot, k2T)
		if !corrupted {
			h3T := Term_h3(ltkT, ltpkT, epkIX)
			assert GetWgLabeling().usage.AeadPred(snapshot, WgK2, k2T, tm.zeroString(12), tsX, h3T)
			aSess = responder.applyCtsPred(ltkT, ltpkT, epkIX, tsX)
			assert GetWgLabeling().IsPublicDhKeyExistential(snapshot, responder.getASessId(aSess), epkIX, WgEphemeralSk)
		}
		aSessId := responder.getASessId(aSess)
		c3T = CreateC3(snapshot, ltkT, ltpkT, epkIX, aSessId, bId)
		h4T = CreateH4(snapshot, ltkT, ltpkT, epkIX, tsX, aSessId, bId)
	}
	@*/

	return
}

/*@
ghost
requires ResponderMem(responder)
requires GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBId(), ltkT, labeling.KeyTypeDh(), WgKey)
requires GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getAId(), ltpkT, labeling.KeyTypeDh(), WgKey)
requires GetWgLabeling().IsPublishable(responder.Snapshot(), epkIX)
requires GetWgUsage().ctsPred(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX), tsX, Term_h3(ltkT, ltpkT, epkIX))
ensures  ResponderMem(responder)
ensures  responder.ImmutableState() == old(responder.ImmutableState())
ensures  old(responder.Snapshot()) == responder.Snapshot()
ensures  old(getPsk(responder)) == getPsk(responder)
ensures  old(getKR(responder)) == getKR(responder)
ensures  old(getPkI(responder)) == getPkI(responder)
ensures  GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getASessId(aSess), epkIX, labeling.KeyTypeDh(), WgEphemeralSk)
ensures  sidIEventProps(responder.Snapshot(), epkIX, responder.getASessId(aSess), responder.getBId())
func (responder *Responder) applyCtsPred(ltkT, ltpkT, epkIX, tsX tm.Term) (ghost aSess uint32){
	usageCtx := GetWgUsage()
	snapshot := responder.Snapshot()
	aId := responder.getAId()
	bId := responder.getBId()
	k2T := CreateK2(snapshot, ltkT, ltpkT, epkIX, aId, bId)
	h3T := CreateH3(snapshot, ltkT, ltpkT, epkIX, aId, bId)
	assert usageCtx.ctsPred(snapshot, k2T, tsX, h3T)

	// from the fact that ltpkT is the DH public key of aId:
	assert exists skI tm.Term :: { tm.exp(tm.generator(), skI) } skI.IsRandom() && ltpkT == tm.exp(tm.generator(), skI) && GetWgLabeling().GetLabel(skI) == label.Readers(set[p.Id]{ aId })
	// get witness:
	skI := arb.GetArbTerm()
	assume skI.IsRandom() && ltpkT == tm.exp(tm.generator(), skI) && GetWgLabeling().GetLabel(skI) == label.Readers(set[p.Id]{ aId })

	// the following assert stmt is needed to trigger the forall quantifier in `ctsPred`
	assert usageCtx.ctsPredLhs(k2T, h3T, aId.getPrincipal(), bId.getPrincipal(), skI)
	assert exists ekI tm.Term :: { snapshot.eventOccurs(aId.getPrincipal(), ev.NewEvent(SendSidI, SendSidIParams{ aId.getPrincipal(), bId.getPrincipal(), ekI, usageCtx.getEpkIFromH3(h3T) })) } (
		GetWgUsage().getEpkIFromH3(h3T) == tm.exp(tm.generator(), ekI) &&
		snapshot.eventOccurs(aId.getPrincipal(), ev.NewEvent(SendSidI, SendSidIParams{ aId.getPrincipal(), bId.getPrincipal(), ekI, usageCtx.getEpkIFromH3(h3T) })))
	// get witness:
	ekI := arb.GetArbTerm()
	assume GetWgUsage().getEpkIFromH3(h3T) == tm.exp(tm.generator(), ekI) &&
		snapshot.eventOccurs(aId.getPrincipal(), ev.NewEvent(SendSidI, SendSidIParams{ aId.getPrincipal(), bId.getPrincipal(), ekI, usageCtx.getEpkIFromH3(h3T) }))
	// apply event inv to get the info that IsPublicDhKeyExistential
	unfold ResponderMem(responder)
	responder.llib.EventOccursImpliesEventInv(aId.getPrincipal(), ev.NewEvent(SendSidI, SendSidIParams{ aId.getPrincipal(), bId.getPrincipal(), ekI, usageCtx.getEpkIFromH3(h3T) }))
	fold ResponderMem(responder)
	
	// use event invariant to derive that epkIX is a public key:
	a := aId.getPrincipal()
	assert GetWgContext().pureEventInv(a, ev.NewEvent(SendSidI, SendSidIParams{ a, bId.getPrincipal(), ekI, epkIX }), snapshot)
	assert exists aSess uint32 :: { p.sessionId(a, aSess) } GetWgLabeling().IsPublicKey(snapshot, p.sessionId(a, aSess), epkIX, ekI, labeling.KeyTypeDh(), WgEphemeralSk)
	// get witness:
	aSess := arb.GetArbUInt32()
	assume GetWgLabeling().IsPublicKey(snapshot, p.sessionId(a, aSess), epkIX, ekI, labeling.KeyTypeDh(), WgEphemeralSk)
}
@*/

//@ requires ResponderMem(responder) && acc(hs) && lib.RequestMem(request)
//@ requires lib.RequestAbs(request) == tm.gamma(reqT)
//@ requires getPsk(responder) == tm.gamma(pskT)
//@ requires getKR(responder) == tm.gamma(ltkT)
//@ requires getPkI(responder) == tm.gamma(ltpkT)
//@ requires GetWgLabeling().IsPublishable(responder.Snapshot(), reqT)
//@ requires GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getAId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  ResponderMem(responder)
//@ ensures  responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()) == responder.Snapshot()
//@ ensures  getPsk(responder) == tm.gamma(pskT)
//@ ensures  getKR(responder) == tm.gamma(ltkT)
//@ ensures  getPkI(responder) == tm.gamma(ltpkT)
//@ ensures  ok ==> HandshakeMem1(hs)
//@ ensures  ok ==> reqT == Term_M1(sidIX, ltkT, ltpkT, epkIX, tsX, mac1X, mac2X)
//@ ensures  ok ==> getSidI1(hs) == tm.gamma(sidIX)
//@ ensures  ok ==> getEpkI1(hs) == tm.gamma(epkIX)
//@ ensures  ok ==> getNKey1(hs) == tm.gamma(Term_c3(ltkT, ltpkT, epkIX))
//@ ensures  ok ==> getNHash1(hs) == tm.gamma(Term_h4(ltkT, ltpkT, epkIX, tsX))
//@ ensures  ok ==> GetWgLabeling().IsPublishable(responder.Snapshot(), sidIX)
//@ ensures  ok ==> GetWgLabeling().IsPublishable(responder.Snapshot(), epkIX)
//@ ensures  ok ==> GetWgLabeling().IsPublishable(responder.Snapshot(), tsX)
//@ ensures  ok ==> GetWgLabeling().IsValidAead(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX), tm.zeroString(12), tsX, GetWgLabeling().GetLabel(tsX), Term_h3(ltkT, ltpkT, epkIX))
func (responder *Responder) consumeRequest(hs *lib.Handshake, request *lib.Request /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost reqT tm.Term @*/) (ok bool /*@, ghost ts tm.Bytes, ghost sidIX tm.Term, ghost epkIX tm.Term, ghost tsX tm.Term, ghost mac1X tm.Term, ghost mac2X tm.Term @*/) {
	//@ bothL := label.Readers(set[p.Id]{ responder.getAId(), responder.getBId() })

	//@ unfold acc(ResponderMem(responder), 1/2)
	args := &responder.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/4)
	//@ unfold lib.RequestMem(request)
	//@ kR := labeledlib.Abs(args.PrivateKey)
	//@ pkI := labeledlib.Abs(args.RemoteStatic)
	//@ epkI := labeledlib.Abs(request.Ephemeral)
	//@ fold acc(lib.HandshakeArgsMem(args), 1/4)

	ok = request.Type == 1
	if !ok {
		//@ fold acc(ResponderMem(responder), 1/2)
		return
	}

	//@ requires acc(request, 1/2) && acc(labeledlib.Mem(request.Ephemeral), 1/2) && labeledlib.Abs(request.Ephemeral) == epkI
	//@ requires acc(lib.HandshakeArgsMem(args), 1/8) && unfolding acc(lib.HandshakeArgsMem(args), 1/8) in labeledlib.Abs(args.PrivateKey) == kR
	//@ ensures  acc(request, 1/2) && acc(labeledlib.Mem(request.Ephemeral), 1/2)
	//@ ensures  acc(lib.HandshakeArgsMem(args), 1/8)
	//@ ensures  labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c1(epkI)
	//@ ensures  labeledlib.Mem(chainHash) && labeledlib.Size(chainHash) == 32 && labeledlib.Abs(chainHash) == Bytes_h2(kR, epkI)
	//@ outline(
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	chainKey := lib.ComputeSingleHash(lib.WireGuardBytes())
	// chainKey == c0
	chainHash := lib.NewByteString(32)
	lib.ComputeHash(chainHash, chainKey, lib.PreludeBytes())
	// chainHash == h0
	lib.ComputeHashInplace(chainHash, args.LocalStatic)
	// chainHash == h1
	lib.ComputeHashInplace(chainHash, request.Ephemeral)
	// chainHash == h2
	lib.ComputeKDF1Inplace(chainKey, request.Ephemeral)
	// chainKey == c1
	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ )

	//@ unfold acc(lib.HandshakeArgsMem(args), 1/4)

	// this would be the spec for the outline block but the performance savings are negligible
	// requires acc(request, 1/2) && acc(labeledlib.Mem(request.Ephemeral), 1/2) && labeledlib.Size(request.Ephemeral) == 32 && labeledlib.Abs(request.Ephemeral) == epkI
	// requires acc(args, 1/8) && acc(labeledlib.Mem(args.PrivateKey), 1/8) && labeledlib.Size(args.PrivateKey) == 32 && labeledlib.Abs(args.PrivateKey) == kR
	// ensures  acc(request, 1/2) && acc(labeledlib.Mem(request.Ephemeral), 1/2)
	// ensures  acc(args, 1/8) && acc(labeledlib.Mem(args.PrivateKey), 1/8)
	// ensures  acc(labeledlib.Mem(ss), 1/2) && labeledlib.Abs(ss) == tm.expB(epkI, kR)
	// outline(
	ss := lib.ComputeSharedSecret(args.PrivateKey, request.Ephemeral)
	// ss == g^(k_R * ek_I) == (g^ek_I)^k_R
	// )

	if lib.IsZero(ss) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/4)
		//@ fold acc(ResponderMem(responder), 1/2)
		ok = false
		return
	}

	// this would be the spec for the outline block but the performance savings are negligible
	// requires labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c1(epkI)
	// requires acc(labeledlib.Mem(ss), 1/2) && labeledlib.Abs(ss) == tm.expB(epkI, kR)
	// ensures  labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c2(kR, epkI)
	// ensures  labeledlib.Mem(key) && labeledlib.Size(key) == 32 && labeledlib.Abs(key) == Bytes_k1(kR, epkI)
	// outline (
	key := lib.NewByteString(32)
	lib.ComputeKDF2Inplace(key, chainKey, ss)
	// chainKey == c2
	// key == k1 == kdf2(<c1, g^(k_R * ek_I)>)
	// )

	// we can transfer knowledge about `reqT` only to its components if we
	// assume that it's a 7-tuple, i.e. has the expected shape as this is not
	// implied by the fact that `request` is a `tuple7B`.
	// therefore, we obtain here these facts only under an implication.
	// this implication is then resolved when applying the pattern property at
	// the very end of the parsing process.
	//@ predictedEpkIX := reqT.IsTuple7() ? tm.getTupleElem(reqT, 2) : tm.oneTerm(epkI) // we take this term if `reqT` is not a 7-tuple
	//@ predictedCpkI := reqT.IsTuple7() ? tm.getTupleElem(reqT, 3) : tm.oneTerm(labeledlib.Abs(request.Static)) // same here
	//@ predictedCts := reqT.IsTuple7() ? tm.getTupleElem(reqT, 4) : tm.oneTerm(labeledlib.Abs(request.Timestamp))

	//@ fold acc(lib.HandshakeArgsMem(args), 1/4)
	//@ fold acc(ResponderMem(responder), 1/2)

	//@ k1T := Term_k1(ltkT, predictedEpkIX)
	//@ h2T := Term_h2(ltkT, predictedEpkIX)

	//@ requires ResponderMem(responder)
	//@ requires acc(labeledlib.Mem(key), 1/2) && labeledlib.Size(key) == 32 && labeledlib.Abs(key) == Bytes_k1(kR, epkI)
	//@ requires tm.gamma(k1T) == Bytes_k1(kR, epkI)
	//@ requires acc(request, 1/2) && acc(labeledlib.Mem(request.Static), 1/2) && labeledlib.Abs(request.Static) == tm.gamma(predictedCpkI)
	//@ requires acc(labeledlib.Mem(chainHash), 1/2) && labeledlib.Abs(chainHash) == Bytes_h2(kR, epkI)
	//@ requires tm.gamma(h2T) == Bytes_h2(kR, epkI)
	//@ ensures  ResponderMem(responder)
	//@ ensures  responder.ImmutableState() == before(responder.ImmutableState())
	//@ ensures  before(responder.Snapshot()) == responder.Snapshot()
	//@ ensures  getPsk(responder) == before(getPsk(responder))
	//@ ensures  getKR(responder) == before(getKR(responder))
	//@ ensures  getPkI(responder) == before(getPkI(responder))
	//@ ensures  acc(labeledlib.Mem(key), 1/2)
	//@ ensures  acc(request, 1/2) && acc(labeledlib.Mem(request.Static), 1/2)
	//@ ensures  acc(labeledlib.Mem(chainHash), 1/2)
	//@ ensures  ok ==> labeledlib.Mem(peerPK) && labeledlib.Abs(request.Static) == Bytes_c_pkI(kR, labeledlib.Abs(peerPK), epkI)
	//@ outline(
	//@ unfold ResponderMem(responder)
	peerPK, err := responder.llib.AeadDec(key, lib.ZeroNonce(), request.Static, chainHash /*@, k1T, tm.zeroString(12), predictedCpkI, h2T, bothL @*/)
	//@ fold ResponderMem(responder)
	ok = err == nil
	//@ )

	if !ok {
		return
	}
	// peerPK == pk_I

	// this would be the spec for the outline block but the performance savings are negligible
	// requires labeledlib.Mem(chainHash) && labeledlib.Size(chainHash) == 32 && labeledlib.Abs(chainHash) == Bytes_h2(kR, epkI)
	// requires acc(labeledlib.Mem(peerPK), 1/8)
	// requires acc(request, 1/8) && acc(labeledlib.Mem(request.Static), 1/8) && labeledlib.Abs(request.Static) == Bytes_c_pkI(kR, labeledlib.Abs(peerPK), epkI)
	// ensures  acc(labeledlib.Mem(peerPK), 1/8)
	// ensures  labeledlib.Mem(chainHash) && labeledlib.Abs(chainHash) == Bytes_h3(kR, labeledlib.Abs(peerPK), epkI)
	// ensures  acc(request, 1/8) && acc(labeledlib.Mem(request.Static), 1/8)
	// outline(
	lib.ComputeHashInplace(chainHash, request.Static)
	// chainHash == h3
	// )

	//@ unfold acc(ResponderMem(responder), 1/2)
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/4)
	if !lib.EqualsSlice(args.RemoteStatic, peerPK) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/4)
		//@ fold acc(ResponderMem(responder), 1/2)
		ok = false
		return
	}

	// this would be the spec for the outline block but the performance savings are negligible
	// requires acc(args, 1/8) && acc(labeledlib.Mem(args.PrivateKey), 1/8) && labeledlib.Size(args.PrivateKey) == 32&& labeledlib.Abs(args.PrivateKey) == kR
	// requires acc(labeledlib.Mem(args.RemoteStatic), 1/8) && labeledlib.Size(args.RemoteStatic) == 32 && labeledlib.Abs(args.RemoteStatic) == pkI
	// ensures  acc(args, 1/8) && acc(labeledlib.Mem(args.PrivateKey), 1/8) && acc(labeledlib.Mem(args.RemoteStatic), 1/8)
	// ensures  acc(labeledlib.Mem(sharedStatic), 1/2) && labeledlib.Abs(sharedStatic) == tm.expB(pkI, kR)
	// outline(
	sharedStatic := lib.ComputeSharedSecret(args.PrivateKey, args.RemoteStatic)
	// sharedStatic == g^(k_R * k_I)
	// )

	//@ fold acc(lib.HandshakeArgsMem(args), 1/4)
	//@ fold acc(ResponderMem(responder), 1/2)

	if lib.IsZero(sharedStatic) {
		ok = false
		return
	}

	// this would be the spec for the outline block but the performance savings are negligible
	// requires labeledlib.Mem(key) && labeledlib.Size(key) == 32 && labeledlib.Abs(key) == Bytes_k1(kR, epkI)
	// requires labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c2(kR, epkI)
	// requires acc(labeledlib.Mem(sharedStatic), 1/2) && labeledlib.Abs(sharedStatic) == tm.expB(pkI, kR)
	// ensures  labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c3(kR, pkI, epkI)
	// ensures  labeledlib.Mem(key) && labeledlib.Size(key) == 32 && labeledlib.Abs(key) == Bytes_k2(kR, pkI, epkI)
	// outline (
	lib.ComputeKDF2Inplace(key, chainKey, sharedStatic)
	// chainKey == c3
	// key == k2 == kdf2(c2, g^(k_R * k_I))
	// )

	//@ k2T := Term_k2(ltkT, ltpkT, predictedEpkIX)
	//@ h3T := Term_h3(ltkT, ltpkT, predictedEpkIX)

	//@ requires ResponderMem(responder)
	//@ requires acc(labeledlib.Mem(key), 1/2) && labeledlib.Size(key) == 32 && labeledlib.Abs(key) == Bytes_k2(kR, pkI, epkI)
	//@ requires tm.gamma(k2T) == Bytes_k2(kR, pkI, epkI)
	//@ requires acc(request, 1/2) && acc(labeledlib.Mem(request.Timestamp), 1/2) && labeledlib.Abs(request.Timestamp) == tm.gamma(predictedCts)
	//@ requires acc(labeledlib.Mem(chainHash), 1/2) && labeledlib.Abs(chainHash) == Bytes_h3(kR, pkI, epkI)
	//@ requires tm.gamma(h3T) == Bytes_h3(kR, pkI, epkI)
	//@ ensures  ResponderMem(responder)
	//@ ensures  responder.ImmutableState() == before(responder.ImmutableState())
	//@ ensures  before(responder.Snapshot()) == responder.Snapshot()
	//@ ensures  getPsk(responder) == before(getPsk(responder))
	//@ ensures  getKR(responder) == before(getKR(responder))
	//@ ensures  getPkI(responder) == before(getPkI(responder))
	//@ ensures  acc(labeledlib.Mem(key), 1/2)
	//@ ensures  acc(request, 1/2) && acc(labeledlib.Mem(request.Timestamp), 1/2)
	//@ ensures  acc(labeledlib.Mem(chainHash), 1/2)
	//@ ensures  ok ==> labeledlib.Abs(request.Timestamp) == Bytes_c_ts(kR, pkI, epkI, ts)
	//@ ensures  ok ==> (forall msgT tm.Term :: { tm.aead(k2T, tm.zeroString(12), msgT, h3T) } predictedCts == tm.aead(k2T, tm.zeroString(12), msgT, h3T) ==>
	//@ 	GetWgLabeling().WasAeadDecrypted(responder.Snapshot(), k2T, tm.zeroString(12), msgT, h3T, bothL))
	//@ outline(
	//@ unfold ResponderMem(responder)
	_, err = responder.llib.AeadDec(key, lib.ZeroNonce(), request.Timestamp, chainHash /*@, k2T, tm.zeroString(12), predictedCts, h3T, bothL @*/)
	// result corresponds to decrypted timestamp from c_ts
	//@ ts = tm.aeadDecryptB(labeledlib.Abs(key), tm.zeroStringB(12), labeledlib.Abs(request.Timestamp))
	//@ fold ResponderMem(responder)
	ok = err == nil
	//@ )
	if !ok {
		return
	}

	//@ requires acc(ResponderMem(responder), 1/4) && acc(hs)
	//@ requires labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c3(kR, pkI, epkI)
	//@ requires labeledlib.Mem(chainHash) && labeledlib.Size(chainHash) == 32 && labeledlib.Abs(chainHash) == Bytes_h3(kR, pkI, epkI)
	//@ requires acc(request, 1/2)
	//@ requires labeledlib.Mem(request.Ephemeral) && labeledlib.Size(request.Ephemeral) == 32 && labeledlib.Abs(request.Ephemeral) == epkI
	//@ requires acc(labeledlib.Mem(request.Static), 1/2) && labeledlib.Abs(request.Static) == Bytes_c_pkI(kR, pkI, epkI)
	//@ requires acc(labeledlib.Mem(request.Timestamp), 1/2) && labeledlib.Abs(request.Timestamp) == Bytes_c_ts(kR, pkI, epkI, ts)
	//@ requires request.MAC1 != nil ==> acc(labeledlib.Mem(request.MAC1), 1/2)
	//@ requires request.MAC2 != nil ==> acc(labeledlib.Mem(request.MAC2), 1/2)
	//@ requires tm.gamma(reqT) == Bytes_M1(tm.integer32B(request.Sender), kR, pkI, epkI, ts, labeledlib.SafeAbs(request.MAC1, 16), labeledlib.SafeAbs(request.MAC2, 16))
	//@ requires tm.gamma(ltkT) == kR
	//@ requires tm.gamma(ltpkT) == pkI
	//@ requires GetWgLabeling().IsPublishable(responder.Snapshot(), reqT)
	//@ requires GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
	//@ requires GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBId(), ltkT, labeling.KeyTypeDh(), WgKey)
	//@ requires GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getAId(), ltpkT, labeling.KeyTypeDh(), WgKey)
	//@ requires reqT.IsTuple7() ==> predictedEpkIX == tm.getTupleElem(reqT, 2)
	//@ requires reqT.IsTuple7() ==> predictedCts == tm.getTupleElem(reqT, 4)
	//@ requires (forall msgT tm.Term :: { tm.aead(k2T, tm.zeroString(12), msgT, h3T) } predictedCts == tm.aead(k2T, tm.zeroString(12), msgT, h3T) ==>
	//@ 	GetWgLabeling().WasAeadDecrypted(responder.Snapshot(), k2T, tm.zeroString(12), msgT, h3T, label.Readers(set[p.Id]{ responder.getAId(), responder.getBId() })))
	//@ ensures  acc(ResponderMem(responder), 1/4)
	//@ ensures  HandshakeMem1(hs)
	//@ ensures  reqT == Term_M1(sidIX, ltkT, ltpkT, epkIX, tsX, mac1X, mac2X)
	//@ ensures  getSidI1(hs) == tm.gamma(sidIX)
	//@ ensures  getEpkI1(hs) == tm.gamma(epkIX)
	//@ ensures  getNKey1(hs) == tm.gamma(Term_c3(ltkT, ltpkT, epkIX))
	//@ ensures  getNHash1(hs) == tm.gamma(Term_h4(ltkT, ltpkT, epkIX, tsX))
	//@ ensures  GetWgLabeling().IsPublishable(responder.Snapshot(), sidIX)
	//@ ensures  GetWgLabeling().IsPublishable(responder.Snapshot(), epkIX)
	//@ ensures  GetWgLabeling().IsPublishable(responder.Snapshot(), tsX)
	//@ ensures  GetWgLabeling().IsValidAead(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX), tm.zeroString(12), tsX, GetWgLabeling().GetLabel(tsX), Term_h3(ltkT, ltpkT, epkIX))
	//@ outline (
	/*@
	snapshot := responder.Snapshot()
	aId := responder.getAId()
	sidI := tm.integer32B(request.Sender)
	mac1 := labeledlib.SafeAbs(request.MAC1, 16)
	mac2 := labeledlib.SafeAbs(request.MAC2, 16)
	unfold acc(ResponderMem(responder), 1/4)
	fold pap.pattern3Constraints(responder.llib, aId, ltkT, ltpkT)
	sidIX, epkIX, tsX, mac1X, mac2X = pap.patternProperty3(responder.llib, aId, ltkT, ltpkT, tm.oneTerm(sidI), tm.oneTerm(epkI), tm.oneTerm(ts), tm.oneTerm(mac1), tm.oneTerm(mac2), reqT)
	unfold pap.pattern3Constraints(responder.llib, aId, ltkT, ltpkT)
	fold acc(ResponderMem(responder), 1/4)
	GetWgLabeling().IsMsgTupleResolve(snapshot, reqT, label.Public())

	// we simply call `CreateK2` to learn k2T's labeling:
	k2T = CreateK2(snapshot, ltkT, ltpkT, epkIX, aId, responder.getBId())
	h3T = Term_h3(ltkT, ltpkT, predictedEpkIX)
	assert GetWgLabeling().IsValidAead(snapshot, k2T, tm.zeroString(12), tsX, GetWgLabeling().GetLabel(tsX), h3T)
	@*/
	lib.ComputeHashInplace(chainHash, request.Timestamp)
	// ChainHash == h4
	//@ assert labeledlib.Abs(chainHash) == Bytes_h4(kR, pkI, epkI, ts)

	hs.ChainHash = chainHash
	hs.ChainKey = chainKey
	hs.RemoteIndex = request.Sender
	hs.RemoteEphemeral = request.Ephemeral
	//@ fold HandshakeMem1(hs)
	//@ )
	return
}

//@ requires ResponderMem(responder) && HandshakeMem1(hs)
//@ requires getPsk(responder) == tm.gamma(pskT)
//@ requires getKR(responder) == tm.gamma(ltkT)
//@ requires getPkI(responder) == tm.gamma(ltpkT)
//@ requires getSidI1(hs) == tm.gamma(sidIX)
//@ requires getEpkI1(hs) == tm.gamma(epkIX)
//@ requires getNKey1(hs) == tm.gamma(c3T)
//@ requires getNHash1(hs) == tm.gamma(h4T)
//@ requires GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsPublishable(responder.Snapshot(), sidIX)
//@ requires c3PropsCombined(responder.Snapshot(), ltkT, ltpkT, epkIX, c3T, responder.getASessId(aSess), responder.getBId())
//@ requires h4Props(responder.Snapshot(), h4T, ltkT, ltpkT, epkIX)
//@ requires GetWgLabeling().IsLabeledRelaxed(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX), label.Readers(set[p.Id]{ responder.getAId(), responder.getBId() }))
//@ requires (corrupted == GetWgLabeling().IsPublishable(responder.Snapshot(), Term_k2(ltkT, ltpkT, epkIX)))
//@ requires !corrupted ==> sidIEventProps(responder.Snapshot(), epkIX, responder.getASessId(aSess), responder.getBId())
//@ ensures  ResponderMem(responder)
//@ ensures  responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()).isSuffix(responder.Snapshot())
//@ ensures  ok ==> HandshakeMem2(hs)
//@ ensures  ok ==> kirT == Term_k_IR(ltpkT, pskT, epkIX, c3T, ekrT)
//@ ensures  ok ==> kriT == Term_k_RI(ltpkT, pskT, epkIX, c3T, ekrT)
//@ ensures  ok ==> sentSidR(responder.Snapshot(), epkIX, ekrT, Term_k_IR(ltpkT, pskT, epkIX, c3T, ekrT), Term_k_RI(ltpkT, pskT, epkIX, c3T, ekrT), responder.getASessId(aSess), responder.getBSessId())
//@ ensures  ok ==> old(responder.Snapshot()).isSuffix(getSentSidRPrefix(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()))
//@ ensures  ok ==> c3PropsCombined(getSentSidRPrefix(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()), ltkT, ltpkT, epkIX, c3T, responder.getASessId(aSess), responder.getBId())
//@ ensures  ok ==> GetWgLabeling().IsSecretKey(getSentSidRPrefix(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()), responder.getBSessId(), ekrT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ ensures  ok ==> GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBSessId(), ekrT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ ensures  ok ==> getNKey2(hs) == tm.gamma(Term_c7(ltpkT, pskT, epkIX, c3T, ekrT))
//@ ensures  ok ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
func (responder *Responder) sendResponse(hs *lib.Handshake /*@, ghost corrupted bool, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost sidIX tm.Term, ghost epkIX tm.Term, ghost c3T tm.Term, ghost h4T tm.Term, ghost aSess uint32 @*/) (ok bool /*@, ghost ekrT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term @*/) {

	//@ s0 := responder.Snapshot()
	//@ aId := responder.getAId()
	//@ aSessId := responder.getASessId(aSess)
	//@ bId := responder.getBId()
	//@ bSessId := responder.getBSessId()
	//@ bothL := label.Readers(set[p.Id]{ aId, bId })
	//@ justALabel := label.Readers(set[p.Id]{ aId })
	//@ justBLabel := label.Readers(set[p.Id]{ bId })
	//@ ghost rid := responder.getRid()
	//@ unfold ResponderMem(responder)
	var newPk labeledlib.ByteString
	var err error
	newPk, err /*@, ekrT @*/ = responder.llib.GenerateDHKey(/*@ WgEphemeralSk, set[ev.EventType]{ SendSidR, ReceivedFirstResp } @*/)
	if err != nil {
		ok = false
		//@ fold ResponderMem(responder)
		return
	}

	//@ s1 := responder.llib.Snapshot()
	//@ responder.llib.ApplyMonotonicity()
	//@ ekR := labeledlib.Abs(newPk)
	//@ sidI := old(getSidI1(hs))
	//@ sidR, sidRT := old(getSidR(responder)), rid
	//@ pkI := old(getPkI(responder))
	//@ psk := old(getPsk(responder))
	//@ epkI := old(getEpkI1(hs))
	//@ c3 := old(getNKey1(hs))
	//@ h4 := old(getNHash1(hs))

	/*@
	// the following assert stmts are necessary:
	assert GetWgLabeling() == responder.llib.LabelCtx()
	assert GetWgLabeling().IsValid(responder.llib.Snapshot(), tm.generator())
	kirT = Term_k_IR(ltpkT, pskT, epkIX, c3T, ekrT)
	kriT = Term_k_RI(ltpkT, pskT, epkIX, c3T, ekrT)
	sendSidREvent := sendSidREv(epkIX, ekrT, kirT, kriT, aSessId, bSessId)
	ghost if corrupted {
		GetWgLabeling().PublishableImpliesCorruption(s1, Term_k2(ltkT, ltpkT, epkIX), label.Readers(set[p.Id]{ aId, bId }))
	}
	fold GetWgContext().eventInv(bId.getPrincipal(), sendSidREvent, responder.llib.Snapshot())
	responder.llib.TriggerEvent(sendSidREvent)
	@*/

	//@ s2 := responder.llib.Snapshot()
	//@ s0.isSuffixTransitive(s1, s2)
	//@ responder.llib.ApplyMonotonicity()
	//@ fold ResponderMem(responder)

	//@ c3PropsCombinedMonotonic(s0, s2, ltkT, ltpkT, epkIX, c3T, aSessId, bId)
	response, ok := responder.createResponse(hs, newPk /*@, pskT, ltkT, ltpkT, epkIX, c3T, h4T, ekrT, aSess @*/)
	if !ok {
		return
	}

	packet := lib.MarshalResponse(response)
	//@ unfold acc(ResponderMem(responder), 1/4)

	/*@ mac1, mac1T := @*/ (responder.LibState).AddMac1(packet /*@, Bytes_M2(sidI,sidR,pkI,psk,epkI,c3,h4,ekR,tm.zeroStringB(16),tm.zeroStringB(16)) @*/)

	/*@ mac2, mac2T := @*/ (responder.LibState).AddMac2(packet /*@, Bytes_M2(sidI,sidR,pkI,psk,epkI,c3,h4,ekR,mac1,tm.zeroStringB(16)) @*/)

	//@ assert labeledlib.Abs(packet) == Bytes_M2(sidI,sidR,pkI,psk,epkI,c3,h4,ekR,mac1,mac2)
	//@ assert getNKey2(hs) == Bytes_c7(pkI,psk,epkI,c3,ekR)
	
	//@ packetT := Term_M2(sidIX, sidRT, ltpkT, pskT, epkIX, c3T, h4T, ekrT, mac1T, mac2T)
	//@ CreateM2(s2, ltkT, ltpkT, pskT, epkIX, c3T, h4T, ekrT, sidIX, mac1T, mac2T, aSessId, bSessId)
	//@ assert labeledlib.Abs(packet) == tm.gamma(packetT)
	//@ assert getNKey2(hs) == tm.gamma(Term_c7(ltpkT, pskT, epkIX, c3T, ekrT))

	//@ unfold acc(ResponderMem(responder), 3/4)
	err = responder.llib.Send(lib.Principal(responder.b), lib.Principal(responder.a), packet /*@, packetT @*/)
	ok = err == nil
	//@ s3 := responder.llib.Snapshot()
	//@ s0.isSuffixTransitive(s2, s3)
	//@ responder.llib.ApplyMonotonicity()

	// apply monotonicity to the trace prefix up until the SendSidR event as well:
	//@ assert s2 == getSentSidRPrefix(s2, epkIX, ekrT, kirT, kriT, aSessId, bSessId)
	//@ prefix := getSentSidRPrefix(s3, epkIX, ekrT, kirT, kriT, aSessId, bSessId)
	// `prefix` might be different from `s2` except if we would take the event's uniqueness into account
	//@ s0.isSuffixTransitive(s2, prefix)
	//@ responder.llib.ApplyMonotonicityWithSnap(prefix)
	//@ fold ResponderMem(responder)
	//@ c3PropsCombinedMonotonic(s0, prefix, ltkT, ltpkT, epkIX, c3T, aSessId, bId)
	return
}

//@ requires ResponderMem(responder) && HandshakeMem1(hs)
//@ requires labeledlib.Mem(newPk) && labeledlib.Size(newPk) == 32
//@ requires getPsk(responder) == tm.gamma(pskT)
//@ requires getKR(responder) == tm.gamma(ltkT)
//@ requires getPkI(responder) == tm.gamma(ltpkT)
//@ requires getEpkI1(hs) == tm.gamma(epkIX)
//@ requires getNKey1(hs) == tm.gamma(c3T)
//@ requires getNHash1(hs) == tm.gamma(h4T)
//@ requires labeledlib.Abs(newPk) == tm.gamma(ekrT)
//@ requires GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
//@ requires c3PropsCombined(responder.Snapshot(), ltkT, ltpkT, epkIX, c3T, responder.getASessId(aSess), responder.getBId())
//@ requires h4Props(responder.Snapshot(), h4T, ltkT, ltpkT, epkIX)
//@ requires GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBSessId(), ekrT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ requires sidREventProps(responder.Snapshot(), epkIX, ekrT, Term_k_IR(ltpkT, pskT, epkIX, c3T, ekrT), Term_k_RI(ltpkT, pskT, epkIX, c3T, ekrT), responder.getASessId(aSess), responder.getBSessId())
//@ ensures  ResponderMem(responder)
//@ ensures  responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()) == responder.Snapshot()
//@ ensures  old(getSidR(responder)) == getSidR(responder)
//@ ensures  getPsk(responder) == tm.gamma(pskT)
//@ ensures  getPkI(responder) == tm.gamma(ltpkT)
//@ ensures  ok ==> lib.ResponseMem(response) && HandshakeMem2(hs)
//@ ensures  ok ==> lib.ResponseAbs(response) == Bytes_M2(old(getSidI1(hs)),getSidR(responder),getPkI(responder),getPsk(responder),old(getEpkI1(hs)),old(getNKey1(hs)),old(getNHash1(hs)),old(labeledlib.Abs(newPk)),tm.zeroStringB(16),tm.zeroStringB(16))
//@ ensures  ok ==> getSidI2(hs) == old(getSidI1(hs)) && getEpkI2(hs) == old(getEpkI1(hs))
//@ ensures  ok ==> getNKey2(hs) == Bytes_c7(getPkI(responder),getPsk(responder),old(getEpkI1(hs)),old(getNKey1(hs)),old(labeledlib.Abs(newPk)))
func (responder *Responder) createResponse(hs *lib.Handshake, newPk lib.ByteString /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost epkIX tm.Term, ghost c3T tm.Term, ghost h4T tm.Term, ghost ekrT tm.Term, ghost aSess uint32 @*/) (response *lib.Response, ok bool) {

	//@ unfold acc(ResponderMem(responder), 1/8)
	args := &responder.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ unfold HandshakeMem1(hs)

	//@ kR := labeledlib.Abs(args.PrivateKey)
	//@ pkI := labeledlib.Abs(args.RemoteStatic)
	//@ psk := labeledlib.Abs(args.PresharedKey)
	//@ epkI := labeledlib.Abs(hs.RemoteEphemeral)
	//@ c3 := labeledlib.Abs(hs.ChainKey)
	//@ h4 := labeledlib.Abs(hs.ChainHash)
	//@ ekR := labeledlib.Abs(newPk)

	hs.LocalEphemeral = newPk
	// handshake.localEphemeral == ek_R

	ephemeral := lib.PublicKey(hs.LocalEphemeral)
	// ephemeral == epk_R

	lib.ComputeHashInplace(hs.ChainHash, ephemeral)
	// ChainHash == h5 == hash(<h4, epk_R>)
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h5(h4, ekR)
	lib.ComputeKDF1Inplace(hs.ChainKey, ephemeral)
	// ChainKey == c4
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c4(c3, ekR)

	{
		ss := lib.ComputeSharedSecret(hs.LocalEphemeral, hs.RemoteEphemeral)
		// ss == (g^ek_I)^ek_R
		lib.ComputeKDF1Inplace(hs.ChainKey, ss)
		// ChainKey == c5
		ss = lib.ComputeSharedSecret(hs.LocalEphemeral, args.RemoteStatic)
		// ss == (g^k_I)^ek_R
		lib.ComputeKDF1Inplace(hs.ChainKey, ss)
		// ChainKey == c6
	}
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c6(pkI, epkI,c3, ekR)

	tau := lib.NewByteString(32)
	key := lib.NewByteString(32)
	lib.ComputeKDF3Inplace(tau, key, hs.ChainKey, args.PresharedKey)
	// ChainKey == c7
	// tau == pi
	// key == k3
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c7(pkI, psk, epkI, c3, ekR)
	//@ assert labeledlib.Abs(tau) == Bytes_pi(pkI, psk, epkI, c3, ekR)
	//@ assert labeledlib.Abs(key) == Bytes_k3(pkI, psk, epkI, c3, ekR)

	lib.ComputeHashInplace(hs.ChainHash, tau)
	// ChainHash == h6
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h6(pkI, psk, epkI, c3, h4, ekR)

	//@ snapshot := responder.Snapshot()
	//@ aId := responder.getAId()
	//@ aSessId := responder.getASessId(aSess)
	//@ bId := responder.getBId()
	//@ bSessId := responder.getBSessId()
	//@ aBSessL := label.Readers(set[p.Id]{ aId, bSessId })
	//@ k3T := CreateK3(snapshot, ltkT, ltpkT, pskT, epkIX, c3T, ekrT, aSessId, bSessId)
	//@ h6T := CreateH6(snapshot, ltkT, ltpkT, pskT, epkIX, c3T, h4T, ekrT, aSessId, bSessId)
	//@ unfold acc(ResponderMem(responder), 7/8)
	// we use `CreateCEmptyNew` to derive that `AeadPred` holds:
	//@ CreateCEmpty(snapshot, ltkT, ltpkT, pskT, epkIX, c3T, h4T, ekrT, aSessId, bSessId)
	// the following assert stmts are necessary:
	//@ assert GetWgLabeling().IsAeadKey(snapshot, k3T, aBSessL, WgK3)
	//@ assert GetWgLabeling().IsPublishable(snapshot, tm.zeroString(12))
	//@ assert GetWgLabeling().IsPublishable(snapshot, tm.zeroString(0))
	empty, err := responder.llib.AeadEnc(key, lib.ZeroNonce(), nil, hs.ChainHash /*@, k3T, tm.zeroString(12), tm.zeroString(0), h6T, aBSessL @*/)
	//@ fold acc(ResponderMem(responder), 7/8)
	ok = err == nil
	// empty == c_empty
	if !ok { // ADAPT
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(ResponderMem(responder), 1/8)
		return
	}
	//@ assert labeledlib.Abs(empty) == Bytes_c_empty(pkI, psk, epkI, c3, h4, ekR)

	lib.ComputeHashInplace(hs.ChainHash, empty)
	// chainHash == hash(<h6, c_empty>)

	response = &lib.Response{
		Type:      2,
		Sender:    args.LocalIndex,
		Receiver:  hs.RemoteIndex,
		Ephemeral: ephemeral,
		Empty:     empty,
	}

	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(ResponderMem(responder), 1/8)
	//@ fold lib.ResponseMem(response)
	//@ fold HandshakeMem2(hs)

	return
}

//@ requires acc(ResponderMem(responder), 1/4) && HandshakeMem2(hs)
//@ requires getNKey2(hs) == tm.gamma(c7T)
//@ ensures  acc(ResponderMem(responder), 1/4) && lib.ConnectionMem(conn)
//@ ensures  lib.ConnectionRecvKey(conn) == tm.gamma(tm.kdf1(c7T))
//@ ensures  lib.ConnectionSendKey(conn) == tm.gamma(tm.kdf2(c7T))
//@ ensures  lib.ConnectionNonceVal(conn) == 0
//@ ensures  lib.ConnectionSidI(conn) == old(getSidI2(hs))
func (responder *Responder) beginSymmetricSession(hs *lib.Handshake /*@, ghost c7T tm.Term @*/) (conn *lib.Connection) {

	sendKey := lib.NewByteString(32)
	recvKey := lib.NewByteString(32)
	//@ unfold HandshakeMem2(hs)
	lib.ComputeKDF2(recvKey, sendKey, hs.ChainKey, nil)
	// recvKey == kdf1(c7) == k_IR
	// sendKey == kdf2(c7) == k_RI

	// zero handshake
	hs.ChainKey = nil
	hs.ChainHash = nil
	hs.LocalEphemeral = nil

	conn = &lib.Connection{
		Nonce:       0,
		SendKey:     sendKey,
		RecvKey:     recvKey,
		RemoteIndex: hs.RemoteIndex,
	}

	//@ fold lib.ConnectionMem(conn)

	return
}
