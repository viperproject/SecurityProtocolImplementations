package initiator

//@ import arb "github.com/viperproject/ReusableProtocolVerificationLibrary/arbitrary"
//@ import ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
//@ import labeledlib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
//@ import u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"
//@ import .   "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/initiator"
//@ import pap "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/pattern"


// trusted wrapper around the library's `GetPacket` function
// to express that the returned payload can only be sent to
// this actor's session or its peer but no one else. In particular, this
// stops an implementation of sending out the payload (i.e. a VPN packet)
// in plaintext to the network.
//@ trusted
//@ requires acc(InitiatorMemFwd(initiator, 0), 1/8)
//@ ensures  acc(InitiatorMemFwd(initiator, 0), 1/8)
//@ ensures  ok ==> labeledlib.Mem(res) && tm.gamma(term) == labeledlib.Abs(res)
//@ ensures  ok ==> GetWgLabeling().IsMsg(initiator.SnapshotFwd(0), term, label.Readers(set[p.Id]{ initiator.getASessIdFwd(0), initiator.getBIdFwd(0) }))
func (initiator *Initiator) GetPacket() (res lib.ByteString, ok bool /*@, ghost term tm.Term @*/) {
	//@ unfold acc(InitiatorMemFwd(initiator, 0), 1/8)
	res, ok /*@, term @*/ = initiator.LibState.GetPacket()
	//@ fold acc(InitiatorMemFwd(initiator, 0), 1/8)
	return
}

/*@
pred InitiatorMemFwd(initiator *Initiator, threadId int) {
	acc(lib.LibMem(&initiator.LibState), 1/2) &&
	acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/2) &&
	acc(&initiator.a, 1/2) && acc(&initiator.b, 1/2) &&
	acc(&initiator.llib, 1/2) &&
	acc(&initiator.llib2, 1/2) &&
	(threadId == 0 ==>
		initiator.llib.Mem() &&
		initiator.llib.Ctx() == GetWgContext() &&
		initiator.llib.LabelCtx() == GetWgLabeling() &&
		unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/2) in
			initiator.llib.Owner() == p.sessionThreadId(lib.Principal(initiator.a), initiator.HandshakeInfo.LocalIndex, 0)) &&
	(threadId != 0 ==>
		initiator.llib2.Mem() &&
		initiator.llib2.Ctx() == GetWgContext() &&
		initiator.llib2.LabelCtx() == GetWgLabeling() &&
		unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/2) in
			initiator.llib2.Owner() == p.sessionThreadId(lib.Principal(initiator.a), initiator.HandshakeInfo.LocalIndex, 1))
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) getRidFwd(threadId int) (rid tm.Term) {
	return unfolding acc(InitiatorMemFwd(initiator, threadId), _) in unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in (
		tm.integer32((initiator.HandshakeInfo).LocalIndex))
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) getPPFwd(threadId int) (pp tm.Term) {
	return unfolding acc(InitiatorMemFwd(initiator, threadId), _) in tm.tuple4(tm.integer32(initiator.a), tm.integer32(initiator.b), tm.prologueTerm(), tm.infoTerm())
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) getAIdFwd(threadId int) p.Id {
	return unfolding acc(InitiatorMemFwd(initiator, threadId), _) in lib.principalId(initiator.a)
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) getASessIdFwd(threadId int) p.Id {
	return p.sessionId(initiator.getAIdFwd(threadId).getPrincipal(), tm.getInt32(initiator.getRidFwd(threadId)))
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) getBIdFwd(threadId int) p.Id {
	return unfolding acc(InitiatorMemFwd(initiator, threadId), _) in lib.principalId(initiator.b)
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) getBSessIdFwd(bSess uint32, threadId int) p.Id {
	return p.sessionId(initiator.getBIdFwd(threadId).getPrincipal(), bSess)
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) SnapshotFwd(threadId int) tr.TraceEntry {
	return unfolding acc(InitiatorMemFwd(initiator, threadId), _) in threadId == 0 ? initiator.llib.Snapshot() : initiator.llib2.Snapshot()
}

ghost
requires acc(InitiatorMemFwd(initiator, threadId), _)
pure func (initiator *Initiator) ImmutableStateFwd(threadId int) ImmutableState {
	return unfolding acc(InitiatorMemFwd(initiator, threadId), _) in
		unfolding acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), _) in
			ImmutableState{ initiator.a, initiator.b, initiator.HandshakeInfo.LocalIndex, threadId == 0 ? initiator.llib.ImmutableState() : initiator.llib2.ImmutableState() }
}

pred ConnectionMemFwd(conn *lib.Connection) {
	acc(conn) && labeledlib.Mem(conn.SendKey) && acc(labeledlib.Mem(conn.RecvKey), 1/2) &&
	labeledlib.Size(conn.SendKey) == 32 && labeledlib.Size(conn.RecvKey) == 32
}

ghost
requires acc(ConnectionMemFwd(conn), _)
pure func ConnectionSendKeyFwd(conn *lib.Connection) tm.Bytes {
	return unfolding acc(ConnectionMemFwd(conn), _) in labeledlib.Abs(conn.SendKey)
}

ghost
requires acc(ConnectionMemFwd(conn), _)
pure func ConnectionRecvKeyFwd(conn *lib.Connection) tm.Bytes {
	return unfolding acc(ConnectionMemFwd(conn), _) in labeledlib.Abs(conn.RecvKey)
}

ghost
requires acc(ConnectionMemFwd(conn), _)
pure func ConnectionNonceValFwd(conn *lib.Connection) uint64 {
	return unfolding acc(ConnectionMemFwd(conn), _) in conn.Nonce
}
@*/

//@ requires InitiatorMem(initiator) && lib.ConnectionMem(conn)
//@ requires lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ requires lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ requires initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
//@ requires lib.ConnectionNonceVal(conn) == 0
func (initiator *Initiator) forwardPackets(conn *lib.Connection /*@, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost bSess uint32, ghost corrupted bool @*/) {
	//@ aSessId := initiator.getASessId()
	//@ unfold InitiatorMem(initiator)
	//@ unfold acc(initiator.llib.Mem(), 1/2)
	//@ unfold initiator.llib2.Mem()
	//@ initiator.llib2.manager.SetSnapshot(initiator.llib.manager, initiator.llib.ctx, initiator.llib2.owner, initiator.llib.owner)
	//@ fold initiator.llib2.Mem()
	//@ fold acc(initiator.llib.Mem(), 1/2)
	//@ fold InitiatorMemFwd(initiator, 0)
	//@ fold InitiatorMemFwd(initiator, 1)
	//@ unfold lib.ConnectionMem(conn)
	recvKey := conn.RecvKey
	//@ fold ConnectionMemFwd(conn)
	go initiator.sendPackets(conn /*@ , ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted @*/)
	initiator.recvPackets(recvKey /*conn*/ /*@ , ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted @*/)
}

//@ requires InitiatorMemFwd(initiator, 0) && ConnectionMemFwd(conn)
//@ requires ConnectionSendKeyFwd(conn) == tm.gamma(kirT)
//@ requires ConnectionRecvKeyFwd(conn) == tm.gamma(kriT)
//@ requires initiator.transportKeysLabelingFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 0)
//@ requires ConnectionNonceValFwd(conn) == 0
func (initiator *Initiator) sendPackets(conn *lib.Connection /*@, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost bSess uint32, ghost corrupted bool @*/) {
	//@ ghost isFirstMessage := true
	//@ initiator.proveSecurityPropertiesFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 0)

	//@ invariant InitiatorMemFwd(initiator, 0) && ConnectionMemFwd(conn)
	//@ invariant ConnectionSendKeyFwd(conn) == tm.gamma(kirT)
	//@ invariant ConnectionRecvKeyFwd(conn) == tm.gamma(kriT)
	//@ invariant initiator.transportKeysLabelingFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 0)
	//@ invariant  isFirstMessage ==> ConnectionNonceValFwd(conn) == 0
	//@ invariant !isFirstMessage ==> ConnectionNonceValFwd(conn) > 0
	//@ invariant transportKeysStrongForwardSecrecy(initiator.SnapshotFwd(0), ekiT, epkRX, ekRX, kirT, kriT, initiator.getASessIdFwd(0), initiator.getBSessIdFwd(bSess, 0))
	//@ invariant initiator.InjectiveAgreementWithKCIResistanceFwd(initiator.getASessIdFwd(0), initiator.getBSessIdFwd(bSess, 0), sendFirstInitEv(ekiT, ekRX, kirT, kriT, initiator.getASessIdFwd(0), initiator.getBSessIdFwd(bSess, 0)), sendSidREv(tm.exp(tm.generator(), ekiT), ekRX, kirT, kriT, initiator.getASessIdFwd(0), initiator.getBSessIdFwd(bSess, 0)), 0)
	for {
		//@ ghost s0 := initiator.SnapshotFwd(0)
		var request lib.ByteString
		var ok bool
		//@ ghost var term tm.Term
		request, ok /*@, term @*/ = initiator.GetPacket()
		if ok {
			//@ ghost var isInState3 bool
			ok /*@, isInState3 @*/ = initiator.sendMessage(request, conn /*@, isFirstMessage, ekiT, epkRX, ekRX, kirT, kriT, term, bSess, corrupted @*/)
			//@ isFirstMessage = !isInState3;
			//@ initiator.transportKeysLabelingFwdMonotonic(s0, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 0)
		}
		//@ initiator.proveSecurityPropertiesFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 0)
	}
}

//@ requires InitiatorMemFwd(initiator, 1)
//@ requires acc(labeledlib.Mem(recvKey), 1/4) && labeledlib.Abs(recvKey) == tm.gamma(kriT) && labeledlib.Size(recvKey) == 32
//@ requires initiator.transportKeysLabelingFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 1)
func (initiator *Initiator) recvPackets(recvKey lib.ByteString /*@, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost bSess uint32, ghost corrupted bool @*/) {
	//@ initiator.proveSecurityPropertiesFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 1)
	
	//@ invariant InitiatorMemFwd(initiator, 1)
	//@ invariant acc(labeledlib.Mem(recvKey), 1/4) && labeledlib.Abs(recvKey) == tm.gamma(kriT) && labeledlib.Size(recvKey) == 32
	//@ invariant initiator.transportKeysLabelingFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 1)
	//@ invariant transportKeysStrongForwardSecrecy(initiator.SnapshotFwd(1), ekiT, epkRX, ekRX, kirT, kriT, initiator.getASessIdFwd(1), initiator.getBSessIdFwd(bSess, 1))
	//@ invariant initiator.InjectiveAgreementWithKCIResistanceFwd(initiator.getASessIdFwd(1), initiator.getBSessIdFwd(bSess, 1), sendFirstInitEv(ekiT, ekRX, kirT, kriT, initiator.getASessIdFwd(1), initiator.getBSessIdFwd(bSess, 1)), sendSidREv(tm.exp(tm.generator(), ekiT), ekRX, kirT, kriT, initiator.getASessIdFwd(1), initiator.getBSessIdFwd(bSess, 1)), 1)
	for {
		//@ ghost s0 := initiator.SnapshotFwd(1)
		response, done := initiator.receiveMessage(recvKey /*@, kirT, kriT @*/)
		//@ initiator.transportKeysLabelingFwdMonotonic(s0, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 1)
		if done {
			//@ unfold acc(InitiatorMemFwd(initiator, 1), 1/2)
			initiator.LibState.ConsumePacket(response)
			//@ fold acc(InitiatorMemFwd(initiator, 1), 1/2)
		}
		//@ initiator.proveSecurityPropertiesFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 1)
	}
}

//@ requires InitiatorMemFwd(initiator, 0) && ConnectionMemFwd(conn) && labeledlib.Mem(msg)
//@ requires labeledlib.Abs(msg) == tm.gamma(msgTerm)
//@ requires GetWgLabeling().IsMsg(initiator.SnapshotFwd(0), msgTerm, label.Readers(set[p.Id]{ initiator.getASessIdFwd(0), initiator.getBIdFwd(0) }))
//@ requires ConnectionSendKeyFwd(conn) == tm.gamma(kirT)
//@ requires ConnectionRecvKeyFwd(conn) == tm.gamma(kriT)
//@ requires initiator.transportKeysLabelingFwd(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted, 0)
//@ requires  isFirstMessage ==> ConnectionNonceValFwd(conn) == 0
//@ requires !isFirstMessage ==> ConnectionNonceValFwd(conn) > 0
//@ ensures  InitiatorMemFwd(initiator, 0) && ConnectionMemFwd(conn)
//@ ensures  initiator.ImmutableStateFwd(0) == old(initiator.ImmutableStateFwd(0))
//@ ensures  old(initiator.SnapshotFwd(0)).isSuffix(initiator.SnapshotFwd(0))
//@ ensures  ConnectionSendKeyFwd(conn) == tm.gamma(kirT)
//@ ensures  ConnectionRecvKeyFwd(conn) == tm.gamma(kriT)
//@ ensures  !isFirstMessage ==> isInState3
//@ ensures  ok ==> isInState3
//@ ensures  !isInState3 ==> ConnectionNonceValFwd(conn) == 0
//@ ensures  isInState3  ==> ConnectionNonceValFwd(conn) > 0
func (initiator *Initiator) sendMessage(msg lib.ByteString, conn *lib.Connection /*@, ghost isFirstMessage bool, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term, ghost msgTerm tm.Term, ghost bSess uint32, ghost corrupted bool @*/) (ok bool /*@, ghost isInState3 bool @*/) {

	//@ ghost rid := initiator.getRidFwd(0)
	//@ ghost pp := initiator.getPPFwd(0)
	//@ isInState3 = !isFirstMessage
	//@ unfold ConnectionMemFwd(conn)

	if conn.Nonce >= 18446744073709543423 {
		//@ fold ConnectionMemFwd(conn)
		ok = false
		return
	}

	var nonce uint64
	if conn.Nonce == 0 {
		nonce = 0
	} else {
		nonce = lib.GetCounter(conn.Nonce)
	}
	nonceBytes := lib.NonceToBytes(nonce)

	//@ unfold acc(InitiatorMemFwd(initiator, 0), 1/8)
	plaintext := (initiator.LibState).PadMsg(msg)
	//@ fold acc(InitiatorMemFwd(initiator, 0), 1/8)

	//@ snapshot := initiator.SnapshotFwd(0)
	//@ aId := initiator.getAIdFwd(0)
	//@ aSessId := initiator.getASessIdFwd(0)
	//@ bId := initiator.getBIdFwd(0)
	//@ bSessId := initiator.getBSessIdFwd(bSess, 0)
	//@ a := aSessId.getPrincipal()
	//@ b := bSessId.getPrincipal()
	//@ aSessBId := label.Readers(set[p.Id]{ aSessId, bId })
	// the following assert stmt is necessary:
	//@ assert GetWgLabeling().IsAeadKey(snapshot, kirT, aSessBId, WgSendingKey)
	//@ dhStatic := GetWgUsage().getDhStaticFromKir(kirT)
	// note that the next assert stmt is needed because `payloadToResponderPred` is triggered on `p.principalId(a)` and `p.principalId(b)`:
	//@ assert GetWgLabeling().GetLabel(dhStatic) == label.Join(label.Readers(set[p.Id]{ p.principalId(a) }), label.Readers(set[p.Id]{ p.principalId(b) }))
	//@ prefix := getHandshakeDonePrefix(snapshot, ekiT, epkRX, ekRX, kirT, kriT, aSessId, bSessId)
	/*@
	ghost if corrupted {
		GetWgLabeling().IsPublishableMonotonic(prefix, snapshot, kirT)
	}
	@*/
	//@ assert GetWgUsage().AeadPred(snapshot, WgSendingKey, kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0))
	//@ unfold InitiatorMemFwd(initiator, 0)
	encryptedMsg, err := initiator.llib.AeadEnc(conn.SendKey, nonceBytes, plaintext, nil /*@, kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0), aSessBId @*/)
	ok = err == nil
	//@ fold InitiatorMemFwd(initiator, 0)
	if !ok {
		//@ fold ConnectionMemFwd(conn)
		return
	}

	message := &lib.Message{
		Type:     4,
		Receiver: conn.RemoteIndex,
		Nonce:    nonce,
		Payload:  encryptedMsg,
	}
	//@ sidR := tm.integer32B(conn.RemoteIndex)
	//@ sidrT := tm.integer32(conn.RemoteIndex)

	//@ fold ConnectionMemFwd(conn)

	packet := lib.MarshalMessage(message)

	//@ packetT := tm.tuple4(tm.integer32(4), sidrT, tm.integer64(nonce), tm.aead(kirT, tm.integer64(nonce), msgTerm, tm.zeroString(0)))
	//@ assert labeledlib.Abs(packet) == tm.gamma(packetT)

	//@ isInState3 = true

	//@ unfold ConnectionMemFwd(conn)
	conn.Nonce += 1
	//@ fold ConnectionMemFwd(conn)

	// the following assert stmts are necessary:
	//@ assert GetWgLabeling().IsValid(snapshot, tm.integer64(nonce))
	//@ assert GetWgLabeling().IsValid(snapshot, msgTerm)
	//@ assert GetWgLabeling().IsValid(snapshot, tm.zeroString(0))
	//@ assert GetWgLabeling().IsValidAead(snapshot, kirT, tm.integer64(nonce), msgTerm, GetWgLabeling().GetLabel(msgTerm), tm.zeroString(0))
	//@ GetWgLabeling().IsMsgTupleCreate(snapshot, packetT, label.Public())

	//@ unfold InitiatorMemFwd(initiator, 0)
	err = initiator.llib.Send(lib.Principal(initiator.a), lib.Principal(initiator.b), packet /*@, packetT @*/)
	ok = err == nil
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMemFwd(initiator, 0)

	return
}

//@ requires InitiatorMemFwd(initiator, 1)
//@ requires acc(labeledlib.Mem(recvKey), 1/8) && labeledlib.Abs(recvKey) == tm.gamma(kriT) && labeledlib.Size(recvKey) == 32
//@ requires GetWgLabeling().IsSecretRelaxed(initiator.SnapshotFwd(1), kirT, label.Readers(set[p.Id]{ initiator.getASessIdFwd(1), initiator.getBIdFwd(1) }), u.AeadKey(WgSendingKey))
//@ requires GetWgLabeling().IsSecretRelaxed(initiator.SnapshotFwd(1), kriT, label.Readers(set[p.Id]{ initiator.getASessIdFwd(1), initiator.getBIdFwd(1) }), u.AeadKey(WgReceivingKey))
//@ ensures  InitiatorMemFwd(initiator, 1)
//@ ensures  acc(labeledlib.Mem(recvKey), 1/8)
//@ ensures  initiator.ImmutableStateFwd(1) == old(initiator.ImmutableStateFwd(1))
//@ ensures  old(initiator.SnapshotFwd(1)).isSuffix(initiator.SnapshotFwd(1))
//@ ensures  ok ==> labeledlib.Mem(msg)
func (initiator *Initiator) receiveMessage(recvKey lib.ByteString /*conn *lib.Connection*/ /*@, ghost kirT tm.Term, ghost kriT tm.Term @*/) (msg lib.ByteString, ok bool) {

	//@ snapshot := initiator.SnapshotFwd(1)
	//@ ghost rid := initiator.getRidFwd(1)
	//@ unfold InitiatorMemFwd(initiator, 1)
	packet, err /*@, term @*/ := initiator.llib2.Receive(lib.Principal(initiator.b), lib.Principal(initiator.a))
	ok = err == nil
	//@ fold InitiatorMemFwd(initiator, 1)
	if !ok {
		return
	}
	//@ recvB := labeledlib.Abs(packet)

	message, ok := lib.UnmarshalMessage(packet)
	if !ok {
		return
	}

	ok = message.Type == 4
	if !ok {
		return
	}

	//@ unfold acc(InitiatorMemFwd(initiator, 1), 1/2)
	//@ unfold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	ok = (initiator.HandshakeInfo).LocalIndex == message.Receiver
	//@ fold acc(lib.HandshakeArgsMem(&initiator.HandshakeInfo), 1/8)
	//@ fold acc(InitiatorMemFwd(initiator, 1), 1/2)
	if !ok {
		return
	}

	nonceBytes := lib.NonceToBytes(message.Nonce)

	//@ aSessId := initiator.getASessIdFwd(1)
	//@ bId := initiator.getBIdFwd(1)
	//@ bothL := label.Readers(set[p.Id]{ aSessId, bId })
	/*@
	predictedPayloadT := tm.oneTerm(labeledlib.Abs(message.Payload))
	ghost if term.IsTuple4() {
		predictedPayloadT = tm.getTupleElem(term, 3)
	}
	@*/
	//@ unfold InitiatorMemFwd(initiator, 1)
	plaintext, err := initiator.llib2.AeadDec(recvKey, nonceBytes, message.Payload, nil /*@, kriT, tm.integer64(message.Nonce), predictedPayloadT, tm.zeroString(0), bothL @*/)
	//@ fold InitiatorMemFwd(initiator, 1)
	ok = err == nil
	if !ok { // ADAPT
		return
	}

	/*@
	pp := initiator.getPPFwd(1)
	recvB := labeledlib.Abs(packet)
	sidI := tm.integer32B(message.Receiver)
	nonceB := tm.integer64B(message.Nonce)
	assert recvB == tm.gamma(tm.tuple4(tm.oneTerm(tm.integer32B(4)), rid, tm.oneTerm(nonceB), tm.aead(kriT, tm.oneTerm(nonceB), tm.oneTerm(labeledlib.Abs(plaintext)), tm.zeroString(0))))
	GetWgLabeling().IsSecretRelaxedMonotonic(snapshot, initiator.SnapshotFwd(1), kriT, label.Readers(set[p.Id]{ initiator.getASessIdFwd(1), initiator.getBIdFwd(1) }), u.AeadKey(WgReceivingKey))

	unfold acc(InitiatorMemFwd(initiator, 1), 1/4)
	fold pap.pattern4Constraints(initiator.llib2, bId, WgReceivingKey, rid, kriT)
	nRI, p := pap.patternProperty4(initiator.llib2, bId, WgReceivingKey, rid, kriT, tm.oneTerm(nonceB), tm.oneTerm(labeledlib.Abs(plaintext)), term)
	unfold pap.pattern4Constraints(initiator.llib2, bId, WgReceivingKey, rid, kriT)
	fold acc(InitiatorMemFwd(initiator, 1), 1/4)
	assert term == tm.tuple4(tm.integer32(4), rid, nRI, tm.aead(kriT, nRI, p, tm.zeroString(0)))
	@*/

	msg = lib.CombineMsg(message.Type, message.Receiver, message.Nonce, plaintext)

	return
}
