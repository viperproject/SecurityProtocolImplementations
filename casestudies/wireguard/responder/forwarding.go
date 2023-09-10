package responder

//@ import arb "github.com/viperproject/ReusableProtocolVerificationLibrary/arbitrary"
//@ import ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
//@ import labeledlib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
//@ import u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma/responder"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/responder"
//@ import pap "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/pattern"


// trusted wrapper around the library's `GetPacket` function
// to express that the returned payload can only be sent to
// this actor's session or its peer but no one else. In particular, this
// stops an implementation of sending out the payload (i.e. a VPN packet)
// in plaintext to the network.
//@ trusted
//@ requires acc(ResponderMem(responder), 1/2)
//@ ensures  acc(ResponderMem(responder), 1/2)
//@ ensures  ok ==> labeledlib.Mem(res) && tm.gamma(term) == labeledlib.Abs(res)
//@ ensures  ok ==> GetWgLabeling().IsMsg(responder.Snapshot(), term, label.Readers(set[p.Id]{ responder.getAId(), responder.getBSessId() }))
func (responder *Responder) GetPacket() (res lib.ByteString, ok bool /*@, ghost term tm.Term @*/) {
	//@ unfold acc(ResponderMem(responder), 1/2)
	res, ok /*@, term @*/ = responder.LibState.GetPacket()
	//@ fold acc(ResponderMem(responder), 1/2)
	return
}

//@ requires ResponderMem(responder) && lib.ConnectionMem(conn)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kriT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionNonceVal(conn) == 0
//@ requires responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
//@ requires GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
func (responder *Responder) forwardPackets(conn *lib.Connection /*@, ghost epkIX tm.Term, ghost ekrT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost corrupted bool, ghost aSess uint32 @*/) {

	//@ ghost firstReceive := true
	//@ ghost var ekiT tm.Term
	//@ responder.proveSecurityProperties(epkIX, ekrT, kirT, kriT, aSess, corrupted)

	//@ invariant ResponderMem(responder) && lib.ConnectionMem(conn)
	//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kriT)
	//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
	//@ invariant lib.ConnectionNonceVal(conn) >= 0
	//@ invariant firstReceive ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
	//@ invariant firstReceive ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
	//@ invariant firstReceive ==> transportKeysWeakForwardSecrecy(responder.Snapshot(), epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
	//@ invariant !firstReceive ==> responder.transportKeysLabelingAfterRecvFirstMsg(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
	//@ invariant !firstReceive ==> transportKeysStrongForwardSecrecy(responder.Snapshot(), ekiT, epkIX, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId())
	//@ invariant !firstReceive ==> responder.InjectiveAgreementWithKCIResistance(responder.getASessId(aSess), responder.getBSessId(), receivedFirstRespEv(ekiT, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()), sendFirstInitEv(ekiT, ekrT, kirT, kriT, responder.getASessId(aSess), responder.getBSessId()))
	for {

		var response lib.ByteString
		var done bool = false // ADAPT

		//@ invariant ResponderMem(responder) && acc(lib.ConnectionMem(conn), 1/2)
		//@ invariant lib.ConnectionSendKey(conn) == tm.gamma(kriT)
		//@ invariant lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
		//@ invariant (!done && firstReceive) ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
		//@ invariant (!done && firstReceive) ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
		//@ invariant (done || !firstReceive) ==> responder.transportKeysLabelingAfterRecvFirstMsg(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
		//@ invariant  done ==> labeledlib.Mem(response)
		for !done {
			response, done /*@, ekiT, aSess, corrupted @*/ = responder.receiveMessage(conn /*@, ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted, firstReceive @*/)
		}
		//@ firstReceive = false


		//@ ghost rid := responder.getRid()
		//@ unfold ResponderMem(responder)
		(responder.LibState).ConsumePacket(response)
		//@ fold ResponderMem(responder)
		request, ok /*@, msgT @*/ := responder.GetPacket()
		if ok {
			//@ s1 := responder.Snapshot()
			responder.sendMessage(request, conn /*@, ekiT, epkIX, ekrT, kirT, kriT, msgT, corrupted, aSess @*/)
			//@ unfold ResponderMem(responder)
			//@ responder.llib.ApplyMonotonicity()
			//@ fold ResponderMem(responder)
			//@ responder.transportKeysLabelingAfterRecvFirstMsgMonotonic(s1, ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
		}

		// with the following statement, we show that we can prove the specified
		// security properties after each iteration of the transport phase:
		//@ responder.proveSecurityPropertiesAfter(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
	}
}

//@ requires ResponderMem(responder) && lib.ConnectionMem(conn) && labeledlib.Mem(msg)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kriT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionNonceVal(conn) >= 0
//@ requires tm.gamma(msgT) == labeledlib.Abs(msg)
//@ requires GetWgLabeling().IsMsg(responder.Snapshot(), msgT, label.Readers(set[p.Id]{ responder.getAId(), responder.getBSessId() }))
//@ requires responder.transportKeysLabelingAfterRecvFirstMsg(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
//@ ensures  ResponderMem(responder) && lib.ConnectionMem(conn)
//@ ensures  responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()).isSuffix(responder.Snapshot())
//@ ensures  lib.ConnectionSidI(conn) == old(lib.ConnectionSidI(conn)) && lib.ConnectionSendKey(conn) == old(lib.ConnectionSendKey(conn)) && lib.ConnectionRecvKey(conn) == old(lib.ConnectionRecvKey(conn))
//@ ensures  lib.ConnectionNonceVal(conn) >= 0
func (responder *Responder) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost ekiT tm.Term, ghost epkIX tm.Term, ghost ekrT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost msgT tm.Term, ghost corrupted bool, ghost aSess uint32 @*/) (ok bool) {

	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	//@ unfold lib.ConnectionMem(conn)

	nonce := lib.GetCounter(conn.Nonce)

	if conn.Nonce >= 18446744073709543423 {
		//@ fold lib.ConnectionMem(conn)
		ok = false
		return
	}
	nonceBytes := lib.NonceToBytes(nonce)

	//@ unfold acc(ResponderMem(responder), 1/8)
	plaintext := (responder.LibState).PadMsg(msg)
	//@ fold acc(ResponderMem(responder), 1/8)

	//@ snapshot := responder.Snapshot()
	//@ aId := responder.getAId()
	//@ aSessId := responder.getASessId(aSess)
	//@ bSessId := responder.getBSessId()
	//@ aBSessL := label.Readers(set[p.Id]{ aId, bSessId })
	// the following assert stmts are necessary:
	//@ assert GetWgLabeling().IsAeadKey(snapshot, kriT, aBSessL, WgSendingKey)
	//@ assert GetWgUsage().AeadPred(snapshot, WgSendingKey, kriT, tm.integer64(nonce), msgT, tm.zeroString(0))
	//@ unfold ResponderMem(responder)
	encryptedMsg, err := responder.llib.AeadEnc(conn.SendKey, nonceBytes, plaintext, nil /*@, kriT, tm.integer64(nonce), msgT, tm.zeroString(0), aBSessL @*/)
	ok = err == nil
	//@ fold ResponderMem(responder)
	if !ok {
		//@ fold lib.ConnectionMem(conn)
		return
	}

	message := &lib.Message{
		Type:     4,
		Receiver: conn.RemoteIndex,
		Nonce:    nonce,
		Payload:  encryptedMsg,
	}

	packet := lib.MarshalMessage(message)

	//@ sidiT := tm.integer32(conn.RemoteIndex)
	//@ packetT := tm.tuple4(tm.integer32(4), sidiT, tm.integer64(nonce), tm.aead(kriT, tm.integer64(nonce), msgT, tm.zeroString(0)))
	// the following assert stmts are necessary:
	//@ assert GetWgLabeling().IsValid(responder.Snapshot(), tm.integer64(nonce))
	//@ assert GetWgLabeling().IsValid(responder.Snapshot(), msgT)
	//@ assert GetWgLabeling().IsValid(responder.Snapshot(), tm.zeroString(0))
	//@ assert GetWgLabeling().IsValidAead(responder.Snapshot(), kriT, tm.integer64(nonce), msgT, GetWgLabeling().GetLabel(msgT), tm.zeroString(0))
	//@ GetWgLabeling().IsMsgTupleCreate(responder.Snapshot(), packetT, label.Public())

	//@ unfold ResponderMem(responder)
	err = responder.llib.Send(lib.Principal(responder.b), lib.Principal(responder.a), packet /*@, packetT @*/)
	ok = err == nil
	//@ fold ResponderMem(responder)

	if ok {
		conn.Nonce += 1
	}

	//@ fold lib.ConnectionMem(conn)

	return
}

//@ requires ResponderMem(responder) && acc(lib.ConnectionMem(conn), 1/8)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kriT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kirT)
//@ requires firstReceive ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
//@ requires firstReceive ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
//@ requires !firstReceive ==> responder.transportKeysLabelingAfterRecvFirstMsg(ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
//@ ensures  ResponderMem(responder) && acc(lib.ConnectionMem(conn), 1/8)
//@ ensures  responder.ImmutableState() == old(responder.ImmutableState())
//@ ensures  old(responder.Snapshot()).isSuffix(responder.Snapshot())
//@ ensures  ok ==> labeledlib.Mem(msg)
//@ ensures  ok ==> responder.transportKeysLabelingAfterRecvFirstMsg(newEkiT, epkIX, ekrT, kirT, kriT, newASess, newCorrupted)
//@ ensures !ok && firstReceive ==> responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, newASess, newCorrupted)
//@ ensures !ok && firstReceive ==> GetWgLabeling().NonceForEventIsUnique(ekrT, ReceivedFirstResp)
//@ ensures !ok && !firstReceive ==> responder.transportKeysLabelingAfterRecvFirstMsg(newEkiT, epkIX, ekrT, kirT, kriT, newASess, newCorrupted)
func (responder *Responder) receiveMessage(conn *lib.Connection /*@, ghost ekiT tm.Term, ghost epkIX tm.Term, ghost ekrT tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost aSess uint32, ghost corrupted bool, ghost firstReceive bool @*/) (msg lib.ByteString, ok bool /*@, ghost newEkiT tm.Term, ghost newASess uint32, ghost newCorrupted bool @*/) {

	// assign out params in case of early returns:
	//@ newEkiT = ekiT
	//@ newASess = aSess
	//@ newCorrupted = corrupted
	//@ s0 := responder.Snapshot()
	//@ ghost rid := responder.getRid()
	//@ ghost pp := responder.getPP()
	//@ unfold ResponderMem(responder)
	packet, err /*@, term @*/ := responder.llib.Receive(lib.Principal(responder.a), lib.Principal(responder.b))
	ok = err == nil
	//@ fold ResponderMem(responder)
	/*@
	ghost if firstReceive {
		responder.transportKeysLabelingBeforeRecvFirstMsgMonotonic(s0, epkIX, ekrT, kirT, kriT, newASess, newCorrupted)
	} else {
		responder.transportKeysLabelingAfterRecvFirstMsgMonotonic(s0, ekiT, epkIX, ekrT, kirT, kriT, aSess, newCorrupted)
	}
	@*/
	if !ok {
		return
	}

	message, ok := lib.UnmarshalMessage(packet)
	if !ok {
		return
	}

	ok = message.Type == 4
	if !ok {
		return
	}

	//@ unfold acc(ResponderMem(responder), 1/8)
	//@ unfold acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), 1/8)
	ok = (responder.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), 1/8)
	//@ fold acc(ResponderMem(responder), 1/8)
	if !ok {
		return
	}

	nonceBytes := lib.NonceToBytes(message.Nonce)

	//@ s1 := responder.Snapshot()
	//@ aId := responder.getAId()
	//@ bId := responder.getBId()
	//@ bSessId := responder.getBSessId()
	//@ bothL := label.Readers(set[p.Id]{ aId, bId })
	//@ aBSessL := label.Readers(set[p.Id]{ aId, bSessId })
	/*@
	unfold ResponderMem(responder)
	responder.llib.MessageOccursImpliesMessageInv(aId.getPrincipal(), bId.getPrincipal(), term)
	fold ResponderMem(responder)
	predictedPayloadT := tm.oneTerm(labeledlib.Abs(message.Payload))
	ghost if term.IsTuple4() {
		predictedPayloadT = tm.getTupleElem(term, 3)
		// we can transfer knowledge about `term` only to its components if we
		// assume that it's a 4-tuple, i.e. has the expected shape as this is not
		// implied by the fact that `message.Payload` is a `tuple4B`.
		// therefore, we obtain here these facts only under an implication.
		// this implication is then resolved when applying the pattern property at
		// the very end of the parsing process.
		GetWgLabeling().IsMsgTupleResolve(s1, term, label.Public())
	}
	@*/
	//@ unfold acc(lib.ConnectionMem(conn), 1/8)
	//@ unfold ResponderMem(responder)
	plaintext, err := responder.llib.AeadDec(conn.RecvKey, nonceBytes, message.Payload, nil /*@, kirT, tm.integer64(message.Nonce), predictedPayloadT, tm.zeroString(0), bothL @*/)
	//@ fold ResponderMem(responder)
	ok = err == nil
	//@ fold acc(lib.ConnectionMem(conn), 1/8)
	if !ok { // ADAPT
		return
	}
	//@ m := labeledlib.Abs(plaintext)
	//@ n := tm.integer64B(message.Nonce)
	//@ unfold acc(ResponderMem(responder), 1/4)
	// the following assert stmt is needed to overcome an incompleteness in the set axiomatization:
	//@ assert set[p.Id]{ aId, bSessId } == set[p.Id]{ bSessId, aId }
	//@ fold pap.pattern4Constraints(responder.llib, aId, WgReceivingKey, rid, kirT)
	//@ nX, mX := pap.patternProperty4(responder.llib, aId, WgReceivingKey, rid, kirT, tm.oneTerm(n), tm.oneTerm(m), term)
	//@ unfold pap.pattern4Constraints(responder.llib, aId, WgReceivingKey, rid, kirT)
	//@ fold acc(ResponderMem(responder), 1/4)
	//@ assert GetWgLabeling().IsValidAead(s1, kirT, nX, mX, GetWgLabeling().GetLabel(mX), tm.zeroString(0))
	//@ aSessId := responder.getASessId(aSess)
	//@ bSessId := responder.getBSessId()

	/*@
	ghost if firstReceive {
		newASess, newEkiT = responder.processPayloadToResponderPred(ekiT, epkIX, ekrT, kirT, kriT, mX, aSess, corrupted)
		newASessId := responder.getASessId(newASess)
		receivedFirstRespEvent := receivedFirstRespEv(newEkiT, ekrT, kirT, kriT, newASessId, bSessId)
		
		if GetWgLabeling().IsPublishable(s1, kirT) {
			GetWgLabeling().PublishableImpliesCorruption(s1, kirT, aBSessL)
		}
		fold GetWgContext().eventInv(bSessId.getPrincipal(), receivedFirstRespEvent, s1)
		unfold ResponderMem(responder)
		responder.llib.TriggerEvent(receivedFirstRespEvent)
		s2 := responder.llib.Snapshot()
		s0.isSuffixTransitive(s1, s2)
		responder.llib.ApplyMonotonicity()
		fold ResponderMem(responder)

		assert recvFirstTransportMsg(s2, newEkiT, epkIX, ekrT, kirT, kriT, newASessId, bSessId)
		newCorrupted = GetWgLabeling().IsPublishable(s2, kirT)
		if newCorrupted {
			GetWgLabeling().PublishableImpliesCorruption(s2, kirT, aBSessL)
			assert tr.containsCorruptId(s2.getCorruptIds(), set[p.Id]{ aId, bSessId })
		} else {
			assert GetWgLabeling().IsPublicKeyExistential(s2, newASessId, epkIX, labeling.KeyTypeDh(), WgEphemeralSk)
			assert GetWgLabeling().IsLabeledPrecise(s2, kirT, Label_k_IRPrecise(newASessId, bSessId))
			GetWgLabeling().SimplifyJoinToReaders(s2, kirT, newASessId, bSessId)
			GetWgLabeling().SimplifyJoinToReaders(s2, kriT, newASessId, bSessId)
		}
	} else {
		responder.transportKeysLabelingAfterRecvFirstMsgMonotonic(s0, ekiT, epkIX, ekrT, kirT, kriT, aSess, corrupted)
	}
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}

/*@
ghost
requires ResponderMem(responder)
requires GetWgLabeling().IsPublishable(responder.Snapshot(), kirT) ||
	GetWgUsage().payloadToResponderPred(responder.Snapshot(), kirT, mX)
requires responder.transportKeysLabelingBeforeRecvFirstMsg(epkIX, ekrT, kirT, kriT, aSess, corrupted)
ensures  ResponderMem(responder)
ensures  responder.ImmutableState() == old(responder.ImmutableState())
ensures  old(responder.Snapshot()) == responder.Snapshot()
ensures  GetWgLabeling().IsPublishable(responder.Snapshot(), kirT) || (
	isFirstMsgSent(responder.Snapshot(), newEkiT, epkIX, ekrT, kirT, kriT, responder.getASessId(newASess), responder.getBSessId()) &&
	GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getASessId(newASess), epkIX, labeling.KeyTypeDh(), WgEphemeralSk)) &&
	GetWgLabeling().IsLabeledPrecise(responder.Snapshot(), kirT, Label_k_IRPrecise(responder.getASessId(newASess), responder.getBSessId()))
func (responder *Responder) processPayloadToResponderPred(ekiT, epkIX, ekrT, kirT, kriT, mX tm.Term, aSess uint32, corrupted bool) (newASess uint32, newEkiT tm.Term) {
	snapshot := responder.Snapshot()
	aId := responder.getAId()
	aSessId := responder.getASessId(aSess)
	bId := responder.getBId()
	bSessId := responder.getBSessId()
	bSess := tm.getInt32(responder.getRid())
	aBSessL := label.Readers(set[p.Id]{ aId, bSessId })
	prefix := getSentSidRPrefix(snapshot, epkIX, ekrT, kirT, kriT, aSessId, bSessId)

	if GetWgLabeling().IsPublishable(snapshot, kirT) {
		// GetWgLabeling().PublishableImpliesCorruption(snapshot, kirT, aBSessL)
		return
	}

	assert GetWgUsage().payloadToResponderPred(snapshot, kirT, mX)
	ghost if GetWgLabeling().CanFlow(snapshot, GetWgLabeling().GetLabel(kirT), label.Public()) {
		assert GetWgLabeling().IsPublishable(snapshot, kirT)
		assert false // we can prove false because this case is already handled in a different branch
	}

	assert GetWgUsage().payloadToResponderPredContent(snapshot, kirT)
	assert GetWgUsage().payloadToResponderPredContentLhs(kirT, aId.getPrincipal(), bId.getPrincipal(), bSess, epkIX, ekrT)
	assert GetWgUsage().payloadToResponderPredContentRhs(snapshot, kirT, aId.getPrincipal(), bId.getPrincipal(), bSess, epkIX, ekrT)
	assert exists aSess uint32, ekI tm.Term :: { SendFirstInitParams{ aId.getPrincipal(), bId.getPrincipal(), aSess, bSess, ekI, tm.exp(tm.generator(), ekI), ekrT, kirT, tm.kdf2(tm.getInput(kirT)) } } (
		epkIX == tm.exp(tm.generator(), ekI) &&
		GetWgLabeling().GetLabel(ekI) == label.Readers(set[p.Id]{ p.sessionId(aId.getPrincipal(), aSess) }) &&
		GetWgLabeling().GetLabel(kirT) == Label_k_IR(p.sessionId(aId.getPrincipal(), aSess), p.sessionId(bId.getPrincipal(), bSess)) &&
		snapshot.eventOccurs(aId.getPrincipal(), ev.NewEvent(SendFirstInit, SendFirstInitParams{ aId.getPrincipal(), bId.getPrincipal(), aSess, bSess, ekI, tm.exp(tm.generator(), ekI), ekrT, kirT, tm.kdf2(tm.getInput(kirT)) })))
	// existential elimination:
	arbASess := arb.GetArbUInt32()
	arbEkI := arb.GetArbTerm()
	assume epkIX == tm.exp(tm.generator(), arbEkI) &&
		GetWgLabeling().GetLabel(arbEkI) == label.Readers(set[p.Id]{ p.sessionId(aId.getPrincipal(), arbASess) }) &&
		GetWgLabeling().GetLabel(kirT) == Label_k_IR(p.sessionId(aId.getPrincipal(), arbASess), p.sessionId(bId.getPrincipal(), bSess)) &&
		snapshot.eventOccurs(aId.getPrincipal(), ev.NewEvent(SendFirstInit, SendFirstInitParams{ aId.getPrincipal(), bId.getPrincipal(), arbASess, bSess, arbEkI, tm.exp(tm.generator(), arbEkI), ekrT, kirT, tm.kdf2(tm.getInput(kirT)) }))
	
	sendFirstInitEvent := sendFirstInitEv(arbEkI, ekrT, kirT, kriT, p.sessionId(aId.getPrincipal(), arbASess), bSessId)
	newASess = arbASess
	newEkiT = arbEkI
	assert snapshot.eventOccurs(aId.getPrincipal(), sendFirstInitEvent)
	unfold ResponderMem(responder)
	prev := responder.llib.EventOccursImpliesEventInvWithSnap(snapshot, aId.getPrincipal(), sendFirstInitEvent)
	fold ResponderMem(responder)
	assert GetWgLabeling().IsPublicKeyExistential(tr.getPrev(prev), p.sessionId(aId.getPrincipal(), arbASess), epkIX, labeling.KeyTypeDh(), WgEphemeralSk)
	if !corrupted {
		// apply IsPublicDhPkExistential:
		assert exists sk1 tm.Term :: GetWgLabeling().IsPublicDhKey(snapshot, aSessId, epkIX, sk1, WgEphemeralSk)
		assert exists sk2 tm.Term :: GetWgLabeling().IsPublicDhKey(snapshot, p.sessionId(aId.getPrincipal(), arbASess), epkIX, sk2, WgEphemeralSk)
		// existential elimination:
		sk1 := arb.GetArbTerm()
		sk2 := arb.GetArbTerm()
		assume GetWgLabeling().IsPublicDhKey(snapshot, aSessId, epkIX, sk1, WgEphemeralSk)
		assume GetWgLabeling().IsPublicDhKey(snapshot, p.sessionId(aId.getPrincipal(), arbASess), epkIX, sk2, WgEphemeralSk)
		assert epkIX == tm.exp(tm.generator(), sk1)
		assert epkIX == tm.exp(tm.generator(), sk2)
		assert aSessId == p.sessionId(aId.getPrincipal(), arbASess)
		return
	}
}
@*/
