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

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/labellemma/initiator"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/common"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/messages/initiator"
//@ import pap "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/pattern"


//@ requires InitiatorMem(initiator)
//@ requires getPsk(initiator) == tm.gamma(pskT)
//@ requires getKI(initiator) == tm.gamma(ltkT)
//@ requires getPkR(initiator) == tm.gamma(ltpkT)
//@ requires GetWgLabeling().IsLabeled(initiator.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  InitiatorMem(initiator)
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
//@ ensures  ok ==> lib.ConnectionMem(conn) && lib.ConnectionNonceVal(conn) == 0
//@ ensures  ok ==> lib.ConnectionSendKey(conn) == tm.gamma(kirT)
//@ ensures  ok ==> lib.ConnectionRecvKey(conn) == tm.gamma(kriT)
//@ ensures  ok ==> initiator.transportKeysLabeling(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
//@ ensures  ok ==> transportKeysStrongForwardSecrecy(initiator.Snapshot(), ekiT, epkRX, ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess))
//@ ensures  ok ==> initiator.InjectiveAgreementWithKCIResistance(initiator.getASessId(), initiator.getBSessId(bSess), sendFirstInitEv(ekiT, ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess)), sendSidREv(tm.exp(tm.generator(), ekiT), ekRX, kirT, kriT, initiator.getASessId(), initiator.getBSessId(bSess)))
func (initiator *Initiator) runHandshake( /*@ ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/ ) (conn *lib.Connection, ok bool /*@, ghost corrupted bool, ghost bSess uint32, ghost ekiT tm.Term, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost kirT tm.Term, ghost kriT tm.Term @*/) {

	//@ s0 := initiator.Snapshot()
	//@ aSessId := initiator.getASessId()
	//@ bId := initiator.getBId()
	handshake := &lib.Handshake{}
	//@ ghost var c3T, h4T tm.Term
	ok /*@, ekiT, c3T, h4T @*/ = initiator.sendRequest(handshake /*@, pskT, ltkT, ltpkT @*/)
	if !ok {
		return
	}

	//@ assert getEkI(handshake) == tm.gamma(ekiT)

	//@ unfold InitiatorMem(initiator)
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold acc(InitiatorMem(initiator), 1/2)
	(initiator.LibState).Println("Success Sending Request")
	//@ fold acc(InitiatorMem(initiator), 1/2)

	//@ ghost var c7T tm.Term
	//@ s1 := initiator.Snapshot()
	//@ BeforeRecvResp:
	ok /*@, corrupted, bSess, epkRX, ekRX, c7T @*/ = initiator.receiveResponse(handshake /*@, pskT, ltkT, ltpkT, ekiT, c3T, h4T @*/)
	//@ s2 := initiator.Snapshot()
	//@ s0.isSuffixTransitive(s1, s2)
	if !ok {
		return
	}

	//@ unfold acc(InitiatorMem(initiator), 1/2)
	(initiator.LibState).Println("Success Consuming Response")
	//@ unfold acc(InitiatorMem(initiator), 1/2)
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)

	//@ BeforeSymSess:
	conn = initiator.beginSymmetricSession(handshake /*@, c7T @*/)

	//@ aId := initiator.getAId()
	//@ bSessId := initiator.getBSessId(bSess)
	// GetWgLabeling().IsSecretKeyMonotonic(s0, s2, )
	//@ kirT = CreateKir(s2, ltkT, pskT, ekiT, c3T, epkRX, aSessId, bSessId)
	//@ kriT = CreateKri(s2, ltkT, pskT, ekiT, c3T, epkRX, aSessId, bSessId)

	/*@
	ghost if !corrupted {
		// the following proof steps are needed to derive the event's invariant
		aBSessL := label.Join(label.Readers(set[p.Id]{ aId }), label.Readers(set[p.Id]{ bSessId }))
		aSessBSessL := label.Join(label.Readers(set[p.Id]{ aSessId }), label.Readers(set[p.Id]{ bSessId }))
		GetWgLabeling().PrincipalsJoinFlowsToBSessions(s2, bSessId, aSessId)
		GetWgLabeling().CanFlowTransitive(s2, aBSessL, aSessBSessL, GetWgLabeling().GetLabel(kirT))
	}
	sendFirstInitEv := sendFirstInitEv(ekiT, ekRX, kirT, kriT, aSessId, bSessId)
	ghost if corrupted {
		GetWgLabeling().PublishableImpliesCorruption(s2, c7T, label.Readers(set[p.Id]{ aSessId, bId }))
	}
	// corruption of {aId, bId} covers corruption of { aSessId, bId }
	ghost if tr.containsCorruptId(s2.getCorruptIds(), set[p.Id]{ aSessId, bId }) {
		GetWgLabeling().PrincipalsIncludeSessions(aSessId, bId)
		GetWgLabeling().containsCorruptIdMonotonic(s2.getCorruptIds(), set[p.Id]{ aSessId, bId }, set[p.Id]{ aId, bId })
	}
	fold GetWgContext().eventInv(aSessId.getPrincipal(), sendFirstInitEv, s2)
	unfold InitiatorMem(initiator)
	initiator.llib.TriggerEvent(sendFirstInitEv)
	s3 := initiator.llib.Snapshot()
	s0.isSuffixTransitive(s2, s3)
	initiator.llib.ApplyMonotonicity()
	fold InitiatorMem(initiator)

	// we could prove an even stronger version of forward secrecy but by using `SentFirstInit` as
	// a marker we have to allow corruption of B's long term key up until now:
	corrupted = GetWgLabeling().IsPublishable(s3, kirT)
	initiator.proveSecurityProperties(ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted)
	@*/
	return
}

//@ requires InitiatorMem(initiator) && acc(hs)
//@ requires getPsk(initiator) == tm.gamma(pskT)
//@ requires getKI(initiator) == tm.gamma(ltkT)
//@ requires getPkR(initiator) == tm.gamma(ltpkT)
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  InitiatorMem(initiator)
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
//@ ensures  getPsk(initiator) == tm.gamma(pskT)
//@ ensures  getKI(initiator) == tm.gamma(ltkT)
//@ ensures  getPkR(initiator) == tm.gamma(ltpkT)
//@ ensures  ok ==> HandshakeMem(hs)
//@ ensures  ok ==> getEkI(hs) == tm.gamma(ekiT)
//@ ensures  ok ==> ekiT.IsRandom()
//@ ensures  ok ==> GetWgLabeling().NonceForEventIsUnique(ekiT, SendFirstInit)
//@ ensures  ok ==> getNKey(hs) == tm.gamma(c3T)
//@ ensures  ok ==> getNHash(hs) == tm.gamma(h4T)
//@ ensures  ok ==> GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getASessId(), ekiT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ ensures  ok ==> c3Props(initiator.Snapshot(), ekiT, c3T, initiator.getASessId(), initiator.getBId())
//@ ensures  ok ==> h4Props(initiator.Snapshot(), h4T, ltkT, ltpkT, ekiT)
//@ ensures  ok ==> sidIEventProps(initiator.Snapshot(), ekiT, initiator.getASessId(), initiator.getBId())
func (initiator *Initiator) sendRequest(hs *lib.Handshake /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/) (ok bool /*@, ghost ekiT tm.Term, ghost c3T tm.Term, ghost h4T tm.Term @*/) {

	//@ ghost rid := initiator.getRid()
	//@ aSessId := initiator.getASessId()
	//@ bId := initiator.getBId()
	//@ s0 := initiator.Snapshot()
	//@ unfold InitiatorMem(initiator)
	var newPk lib.ByteString
	var err error
	newPk, err /*@, ekiT @*/ = initiator.llib.GenerateDHKey(/*@ WgEphemeralSk, set[ev.EventType]{ SendSidI, SendFirstInit } @*/)
	//@ ekiL := label.Readers(set[p.Id]{ aSessId })
	if err != nil {
		ok = false
		//@ fold InitiatorMem(initiator)
		return
	}
	//@ s1 := initiator.llib.Snapshot()
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)
	// the following assert stmt is needed to derive the corresponding postcondition
	//@ assert GetWgLabeling().IsLabeled(s1, ekiT, ekiL)

	var newTs lib.ByteString
	_ = newTs // stops go's syntactic check from complaining
	//@ ghost var tsT tm.Term
	newTs /*@, tsT @*/ = lib.Timestamp()

	//@ epkiT := tm.exp(tm.generator(), ekiT)
	//@ sendSidIEv := sendSidIEv(ekiT, epkiT, aSessId, bId)
	// the following assert stmt is necessary to fold `eventInv`:
	//@ assert GetWgLabeling().IsPublicKey(s1, p.sessionId(aSessId.getPrincipal(), p.getIdSession(aSessId)), epkiT, ekiT, labeling.KeyTypeDh(), WgEphemeralSk)
	//@ fold GetWgContext().eventInv(aSessId.getPrincipal(), sendSidIEv, s1)
	//@ unfold InitiatorMem(initiator)
	//@ initiator.llib.TriggerEvent(sendSidIEv)
	//@ s2 := initiator.llib.Snapshot()
	//@ s0.isSuffixTransitive(s1, s2)
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)

	//@ sidI, kI, pkR, psk, ekI, ts := getSidI(initiator), getKI(initiator), getPkR(initiator), getPsk(initiator), labeledlib.Abs(newPk), labeledlib.Abs(newTs)

	request, ok := initiator.createRequest(hs, newPk, newTs /*@, ltkT, ltpkT, ekiT, tsT @*/)
	if !ok {
		return
	}

	packet := lib.MarshalRequest(request)
	//@ pp := initiator.getPP()
	//@ unfold InitiatorMem(initiator)
	
	/*@ mac1, mac1T := @*/ (initiator.LibState).AddMac1(packet /*@, Bytes_M1(sidI, kI, pkR, ekI, ts, tm.zeroStringB(16), tm.zeroStringB(16)) @*/)

	/*@ mac2, mac2T := @*/ (initiator.LibState).AddMac2(packet /*@, Bytes_M1(sidI, kI, pkR, ekI, ts, mac1, tm.zeroStringB(16)) @*/)

	/*@ 
	packetTerm := CreateM1(s2, ltkT, ltpkT, ekiT, tsT, mac1T, mac2T, aSessId, bId)
	assert labeledlib.Abs(packet) == tm.gamma(packetTerm)
	@*/

	err = initiator.llib.Send(lib.Principal(initiator.a), lib.Principal(initiator.b), packet /*@, packetTerm @*/)
	ok = err == nil
	//@ old(initiator.Snapshot()).isSuffixTransitive(s2, initiator.llib.Snapshot())
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)

	//@ c3T = CreateC3(initiator.Snapshot(), ltkT, ltpkT, ekiT, aSessId, bId)
	//@ h4T = CreateH4(initiator.Snapshot(), ltkT, ltpkT, ekiT, tsT, aSessId, bId)

	return
}

//@ requires InitiatorMem(initiator) && acc(hs)
//@ requires labeledlib.Mem(newPk) && labeledlib.Size(newPk) == 32 && labeledlib.Mem(newTs) && labeledlib.Size(newTs) == 12
//@ requires getKI(initiator) == tm.gamma(ltkT)
//@ requires getPkR(initiator) == tm.gamma(ltpkT)
//@ requires labeledlib.Abs(newPk) == tm.gamma(ekiT)
//@ requires labeledlib.Abs(newTs) == tm.gamma(tsT)
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getASessId(), ekiT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ requires GetWgLabeling().IsLabeled(initiator.Snapshot(), tsT, label.Public()) // can this be relaxed?
//@ requires sidIEventProps(initiator.Snapshot(), ekiT, initiator.getASessId(), initiator.getBId())
//@ ensures  InitiatorMem(initiator)
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()) == initiator.Snapshot()
//@ ensures  old(initiator.getRid()) == initiator.getRid()
//@ ensures  old(getPsk(initiator)) == getPsk(initiator)
//@ ensures  getKI(initiator) == tm.gamma(ltkT)
//@ ensures  getPkR(initiator) == tm.gamma(ltpkT)
//@ ensures  ok ==> HandshakeMem(hs) && lib.RequestMem(request)
//@ ensures  ok ==> lib.RequestAbs(request) == Bytes_M1(getSidI(initiator), getKI(initiator), getPkR(initiator), old(labeledlib.Abs(newPk)), old(labeledlib.Abs(newTs)), tm.zeroStringB(16),tm.zeroStringB(16))
//@ ensures  ok ==> getNHash(hs) == Bytes_h4(getKI(initiator), getPkR(initiator), old(labeledlib.Abs(newPk)), old(labeledlib.Abs(newTs)))
//@ ensures  ok ==> getNKey(hs) == Bytes_c3(getKI(initiator), getPkR(initiator), old(labeledlib.Abs(newPk)))
//@ ensures  ok ==> getEkI(hs) == old(labeledlib.Abs(newPk))
func (initiator *Initiator) createRequest(hs *lib.Handshake, newPk, newTs lib.ByteString /*@, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost ekiT tm.Term, ghost tsT tm.Term @*/) (request *lib.Request, ok bool) {

	//@ unfold acc(InitiatorMem(initiator), 1/8)
	args := &initiator.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)

	//@ kI  := labeledlib.Abs(args.PrivateKey)
	//@ pkR := labeledlib.Abs(args.RemoteStatic)
	//@ ekI := labeledlib.Abs(newPk)
	//@ ts  := labeledlib.Abs(newTs)

	hs.ChainKey = lib.ComputeSingleHash(lib.WireGuardBytes())
	// ChainKey == c0
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c0()
	hs.ChainHash = lib.NewByteString(32)
	lib.ComputeHash(hs.ChainHash, hs.ChainKey, lib.PreludeBytes())
	// ChainHash == h0
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h0()

	hs.LocalEphemeral = newPk
	// localEphemeral == ekI

	publicEphemeral := lib.PublicKey(hs.LocalEphemeral)
	// publicEphemeral == epk_I

	lib.ComputeHashInplace(hs.ChainHash, args.RemoteStatic)
	// ChainHash == h1
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h1(pkR)

	lib.ComputeKDF1Inplace(hs.ChainKey, publicEphemeral)
	// hs.ChainKey == c1
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c1(ekI)
	lib.ComputeHashInplace(hs.ChainHash, publicEphemeral)
	// hs.ChainHash == h2
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h2(pkR, ekI)

	ss := lib.ComputeSharedSecret(hs.LocalEphemeral, args.RemoteStatic)
	// ss == g^(k_R * ek_I) == (g^k_R)^ek_I

	if lib.IsZero(ss) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return nil, false
	}

	key := lib.NewByteString(32)
	lib.ComputeKDF2Inplace(key, hs.ChainKey, ss)
	// ChainKey == c2
	// key == k1 == kdf2(<c1, g^(k_R * ek_I)>)
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c2(pkR, ekI)
	//@ assert labeledlib.Abs(key) == Bytes_k1(pkR, ekI)

	//@ snapshot := initiator.Snapshot()
	//@ aId := initiator.getAId()
	//@ aSessId := initiator.getASessId()
	//@ bId := initiator.getBId()
	//@ bothSessL := label.Readers(set[p.Id]{ aSessId, bId })
	//@ pkiT := CreatePki(snapshot, ltkT, aId)
	//@ k1T := CreateK1(snapshot, ltpkT, ekiT, aSessId, bId)
	//@ h2T := CreateH2(snapshot, ltpkT, ekiT, aSessId, bId)
	//@ assert GetWgUsage().AeadPred(snapshot, WgK1, k1T, tm.zeroString(12), pkiT, h2T)
	// the following assert stmts are necessary:
	//@ assert GetWgLabeling().IsAeadKey(snapshot, k1T, bothSessL, WgK1)
	//@ assert GetWgLabeling().IsPublishable(snapshot, tm.zeroString(12))
	//@ assert GetWgLabeling().IsPublishable(snapshot, pkiT)
	//@ unfold acc(InitiatorMem(initiator), 7/8)
	encryptedStaticPk, err := initiator.llib.AeadEnc(key, lib.ZeroNonce(), args.LocalStatic, hs.ChainHash /*@, k1T, tm.zeroString(12), pkiT, h2T, bothSessL @*/)
	ok = err == nil
	//@ fold acc(InitiatorMem(initiator), 7/8)
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}
	// encryptedStaticPk == c_pk_I
	//@ assert labeledlib.Abs(encryptedStaticPk) == Bytes_c_pkI(kI, pkR, ekI)

	lib.ComputeHashInplace(hs.ChainHash, encryptedStaticPk)
	// ChainHash == h3
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h3(kI, pkR, ekI)

	sharedStatic := lib.ComputeSharedSecret(args.PrivateKey, args.RemoteStatic)
	// sharedStatic == g^(k_R * k_I)

	if lib.IsZero(sharedStatic) {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return nil, false
	}

	lib.ComputeKDF2Inplace(key, hs.ChainKey, sharedStatic)
	// key == k2 == kdf2(c2, g^(k_R * k_I))
	// ChainKey == c3
	//@ assert labeledlib.Abs(key) == Bytes_k2(kI, pkR, ekI)
	//@ assert labeledlib.Abs(hs.ChainKey) == Bytes_c3(kI, pkR, ekI)

	//@ k2T := CreateK2(snapshot, ltkT, ltpkT, ekiT, aSessId, bId)
	//@ h3T := CreateH3(snapshot, ltkT, ltpkT, ekiT, aSessId, bId)
	// we use `CreateCts` to derive that `AeadPred` holds:
	//@ CreateCts(snapshot, ltkT, ltpkT, ekiT, tsT, aSessId, bId)
	// the following assert stmt is necessary:
	//@ assert GetWgLabeling().IsAeadKey(snapshot, k2T, bothSessL, WgK2)
	//@ unfold acc(InitiatorMem(initiator), 7/8)
	timestamp, err := initiator.llib.AeadEnc(key, lib.ZeroNonce(), newTs, hs.ChainHash /*@, k2T, tm.zeroString(12), tsT, h3T, bothSessL @*/)
	ok = err == nil
	//@ fold acc(InitiatorMem(initiator), 7/8)
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}
	// timestamp == c_t2
	//@ assert labeledlib.Abs(timestamp) == Bytes_c_ts(kI, pkR, ekI, ts)

	request = &lib.Request{
		Type:      1,
		Sender:    args.LocalIndex,
		Ephemeral: publicEphemeral,
		Static:    encryptedStaticPk,
		Timestamp: timestamp,
	}

	lib.ComputeHashInplace(hs.ChainHash, timestamp)
	// ChainHash == h4
	//@ assert labeledlib.Abs(hs.ChainHash) == Bytes_h4(kI, pkR, ekI, ts)

	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(InitiatorMem(initiator), 1/8)
	//@ fold lib.RequestMem(request)
	//@ fold HandshakeMem(hs)

	return
}

//@ requires InitiatorMem(initiator) && HandshakeMem(hs)
//@ requires getPsk(initiator) == tm.gamma(pskT)
//@ requires getKI(initiator) == tm.gamma(ltkT)
//@ requires getPkR(initiator) == tm.gamma(ltpkT)
//@ requires getEkI(hs) == tm.gamma(ekiT)
//@ requires getNKey(hs) == tm.gamma(c3T)
//@ requires getNHash(hs) == tm.gamma(h4T)
//@ requires GetWgLabeling().IsLabeled(initiator.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getASessId(), ekiT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ requires c3Props(initiator.Snapshot(), ekiT, c3T, initiator.getASessId(), initiator.getBId())
//@ requires h4Props(initiator.Snapshot(), h4T, ltkT, ltpkT, ekiT)
//@ ensures  InitiatorMem(initiator) && HandshakeMem(hs)
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()).isSuffix(initiator.Snapshot())
//@ ensures  getEkI(hs) == old(getEkI(hs))
//@ ensures  ok ==> epkRXProps(initiator.Snapshot(), epkRX, initiator.getBSessId(bSess), corrupted)
//@ ensures  ok ==> getNKey(hs) == tm.gamma(c7T)
//@ ensures  ok ==> c7T == Term_c7(ltkT, pskT, ekiT, c3T, epkRX)
//@ ensures  ok ==> GetWgLabeling().IsSecretRelaxed(initiator.Snapshot(), c7T, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), u.KdfKey(WgChaininigKey))
//@ ensures  ok ==> (corrupted == GetWgLabeling().IsPublishable(initiator.Snapshot(), c7T))
//@ ensures  ok && !corrupted ==> GetWgLabeling().IsPublicKey(initiator.Snapshot(), initiator.getBSessId(bSess), epkRX, ekRX, labeling.KeyTypeDh(), WgEphemeralSk)
//@ ensures  ok && !corrupted ==> (GetWgLabeling().GetLabel(c7T) == Label_c7(initiator.getASessId(), initiator.getBSessId(bSess)) &&
//@		GetWgLabeling().IsSecretPrecise(initiator.Snapshot(), c7T, label.Join(label.Readers(set[p.Id]{ initiator.getBSessId(bSess) }), label.Readers(set[p.Id]{ initiator.getASessId() })), u.KdfKey(WgChaininigKey)) &&
//@		sidREventProps(initiator.Snapshot(), pskT, ltkT, ekiT, c3T, ekRX, initiator.getASessId(), initiator.getBSessId(bSess)))
func (initiator *Initiator) receiveResponse(hs *lib.Handshake /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost ekiT tm.Term, ghost c3T tm.Term, ghost h4T tm.Term @*/) (ok bool /*@, ghost corrupted bool, ghost bSess uint32, ghost epkRX tm.Term, ghost ekRX tm.Term, ghost c7T tm.Term @*/) {

	//@ s0 := initiator.Snapshot()
	//@ aId := initiator.getAId()
	//@ aSessId := initiator.getASessId()
	//@ unfold InitiatorMem(initiator)
	packet, err /*@, term @*/ := initiator.llib.Receive(lib.Principal(initiator.b), lib.Principal(initiator.a))
	ok = err == nil
	//@ fold InitiatorMem(initiator)
	if !ok {
		return
	}
	//@ s1 := initiator.Snapshot()
	//@ 
	//@ unfold InitiatorMem(initiator)
	//@ recvB := labeledlib.Abs(packet)
	//@ assert recvB == tm.gamma(term)
	//@ initiator.llib.MessageOccursImpliesMessageInv(lib.Principal(initiator.b), lib.Principal(initiator.a), term)
	//@ assert GetWgLabeling().IsPublishable(s1, term)
	//@ initiator.llib.ApplyMonotonicity()
	//@ fold InitiatorMem(initiator)

	response, ok := lib.UnmarshalResponse(packet)
	if !ok {
		return
	}

	//@ BeforeConsume:
	//@ ghost var sidRX tm.Term
	//@ ghost var mac1X tm.Term
	//@ ghost var mac2X tm.Term
	ok /*@, sidRX, epkRX, mac1X, mac2X @*/ = initiator.consumeResponse(hs, response /*@, pskT, ltkT, ltpkT, ekiT, c3T, h4T, term @*/)
	
	/*@
	ghost if ok {
		k3T := Term_k3(ltkT, pskT, ekiT, c3T, epkRX)
		bId := initiator.getBId()
		corrupted = GetWgLabeling().IsPublishable(s1, k3T)
		if !corrupted {
			h6T := Term_h6(ltkT, pskT, ekiT, c3T, h4T, epkRX)
			assert GetWgLabeling().usage.AeadPred(s1, WgK3, k3T, tm.zeroString(12), tm.zeroString(0), h6T)
			bSess, ekRX = initiator.applyCemptyPred(pskT, ltkT, ltpkT, ekiT, c3T, h4T, epkRX)
			bSessId := initiator.getBSessId(bSess)
			CreateK3(s1, ltkT, pskT, ekiT, c3T, epkRX, aSessId, bSessId)
			bothSessL := label.Readers(set[p.Id]{ aSessId, bSessId })
			assert GetWgLabeling().IsPublicDhKeyExistential(s1, bSessId, epkRX, WgEphemeralSk)
		} else {
			// we are in a state where b's session does not matter anyway
			// thus, we simply use bId instead of bSessId here
			CreateK3(s1, ltkT, pskT, ekiT, c3T, epkRX, aSessId, bId)
		}
		bSessId := initiator.getBSessId(bSess)
		c7T = CreateC7(s1, ltkT, pskT, ekiT, c3T, epkRX, aSessId, bSessId)
	}
	@*/
	return
}

/*@
ghost
requires InitiatorMem(initiator)
requires GetWgLabeling().IsLabeled(initiator.Snapshot(), pskT, label.Public())
requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
requires GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getASessId(), ekiT, labeling.KeyTypeDh(), WgEphemeralSk)
requires c3Props(initiator.Snapshot(), ekiT, c3T, initiator.getASessId(), initiator.getBId())
requires h4Props(initiator.Snapshot(), h4T, ltkT, ltpkT, ekiT)
requires GetWgLabeling().IsPublishable(initiator.Snapshot(), epkRX)
requires GetWgUsage().cemptyPred(initiator.Snapshot(), Term_k3(ltkT, pskT, ekiT, c3T, epkRX), Term_h6(ltkT, pskT, ekiT, c3T, h4T, epkRX))
ensures  InitiatorMem(initiator)
ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
ensures  old(initiator.Snapshot()) == initiator.Snapshot()
ensures  GetWgLabeling().IsPublicKey(initiator.Snapshot(), initiator.getBSessId(bSess), epkRX, ekR, labeling.KeyTypeDh(), WgEphemeralSk)
ensures  sidREventProps(initiator.Snapshot(), pskT, ltkT, ekiT, c3T, ekR, initiator.getASessId(), initiator.getBSessId(bSess))
func (initiator *Initiator) applyCemptyPred(pskT, ltkT, ltpkT, ekiT, c3T, h4T, epkRX tm.Term) (ghost bSess uint32, ekR tm.Term) {
	usageCtx := GetWgUsage()
	snapshot := initiator.Snapshot()
	aId := initiator.getAId()
	aSessId := initiator.getASessId()
	bId := initiator.getBId()
	k3T := CreateK3(snapshot, ltkT, pskT, ekiT, c3T, epkRX, aSessId, bId)
	h6T := CreateH6(snapshot, ltkT, ltpkT, pskT, ekiT, c3T, h4T, epkRX, aSessId, bId)
	epkiT := tm.exp(tm.generator(), ekiT)
	assert usageCtx.cemptyPred(snapshot, k3T, h6T)
	assert epkiT == usageCtx.getEpkIFromH6(h6T)
	kirT := usageCtx.getKirFromK3(k3T)
	kriT := usageCtx.getKriFromK3(k3T)

	// after knowing that `cemptyPred` holds, we instanciate `a` and `b` with the principal
	// component in `aId` and `bId` to learn that the SendSidR event has occurred, which in
	// turn provides us with the knowledge that the received epkRX is indeed a DH public key.
	
	// from the fact that ltpkT is the DH public key of bId:
	assert exists skR tm.Term :: skR.IsRandom() && ltpkT == tm.exp(tm.generator(), skR) && GetWgLabeling().GetLabel(skR) == label.Readers(set[p.Id]{ bId })
	// get witness:
	skR := arb.GetArbTerm()
	assume skR.IsRandom() && ltpkT == tm.exp(tm.generator(), skR) && GetWgLabeling().GetLabel(skR) == label.Readers(set[p.Id]{ bId })

	// trigger forall quantifier in `cemptyPred`:
	assert usageCtx.cemptyPredLhs(h6T, aId.getPrincipal(), bId.getPrincipal(), ltkT, skR)
	assert exists bSess uint32, ekR tm.Term :: (
		ekR.IsRandom() && GetWgLabeling().GetLabel(ekR) == label.Readers(set[p.Id]{ p.sessionId(bId.getPrincipal(), bSess) }) &&
		usageCtx.getEpkRFromH6(h6T) == tm.exp(tm.generator(), ekR) &&
		snapshot.eventOccurs(bId.getPrincipal(), ev.NewEvent(SendSidR, SendSidRParams{ aId.getPrincipal(), bId.getPrincipal(), bSess, epkiT, ekR, kirT, kriT })))
	// get witness:
	bSess = arb.GetArbUInt32()
	ekR = arb.GetArbTerm()
	assume ekR.IsRandom() && GetWgLabeling().GetLabel(ekR) == label.Readers(set[p.Id]{ p.sessionId(bId.getPrincipal(), bSess) }) &&
		usageCtx.getEpkRFromH6(h6T) == tm.exp(tm.generator(), ekR) &&
		snapshot.eventOccurs(bId.getPrincipal(), ev.NewEvent(SendSidR, SendSidRParams{ aId.getPrincipal(), bId.getPrincipal(), bSess, epkiT, ekR, kirT, kriT }))
	bSessId := initiator.getBSessId(bSess)
	sendSidREvent := ev.NewEvent(SendSidR, SendSidRParams{ aId.getPrincipal(), bId.getPrincipal(), bSess, epkiT, ekR, kirT, kriT })
	// apply event inv to get the info that IsPublicDhKeyExistential
	unfold InitiatorMem(initiator)
	initiator.llib.EventOccursImpliesEventInv(bId.getPrincipal(), sendSidREvent)
	fold InitiatorMem(initiator)
}

ghost
pure func sidREventProps(snapshot tr.TraceEntry, pskT, ltkT, ekI, c3T, ekR tm.Term, aSessId, bSessId p.Id) bool {
	return aSessId.getSession() != none[uint32] &&
		bSessId.IsSession() &&
		(tr.containsCorruptId(snapshot.getCorruptIds(), set[p.Id]{ aSessId, bSessId.getPrincipalId() }) ||
        	snapshot.eventOccurs(bSessId.getPrincipal(), sendSidREv(tm.exp(tm.generator(), ekI), ekR, Term_k_IR(ltkT, pskT, ekI, c3T, tm.exp(tm.generator(), ekR)), Term_k_RI(ltkT, pskT, ekI, c3T, tm.exp(tm.generator(), ekR)), aSessId, bSessId)))
}
@*/

//@ requires InitiatorMem(initiator) && HandshakeMem(hs) && lib.ResponseMem(response)
//@ requires lib.ResponseAbs(response) == tm.gamma(respT)
//@ requires getPsk(initiator) == tm.gamma(pskT)
//@ requires getKI(initiator) == tm.gamma(ltkT)
//@ requires getPkR(initiator) == tm.gamma(ltpkT)
//@ requires getEkI(hs) == tm.gamma(ekiT)
//@ requires getNKey(hs) == tm.gamma(c3T)
//@ requires getNHash(hs) == tm.gamma(h4T)
//@ requires GetWgLabeling().IsPublishable(initiator.Snapshot(), respT)
//@ requires GetWgLabeling().IsLabeled(initiator.Snapshot(), pskT, label.Public())
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ requires GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getASessId(), ekiT, labeling.KeyTypeDh(), WgEphemeralSk)
//@ requires c3Props(initiator.Snapshot(), ekiT, c3T, initiator.getASessId(), initiator.getBId())
//@ requires h4Props(initiator.Snapshot(), h4T, ltkT, ltpkT, ekiT)
//@ ensures  InitiatorMem(initiator) && HandshakeMem(hs)
//@ ensures  getEkI(hs) == old(getEkI(hs))
//@ ensures  initiator.ImmutableState() == old(initiator.ImmutableState())
//@ ensures  old(initiator.Snapshot()) == initiator.Snapshot()
//@ ensures  ok ==> old(lib.ResponseAbs(response)) == Bytes_M2(getSidI(initiator), getSidR(hs), getKI(initiator), getPsk(initiator), old(getEkI(hs)), old(getNKey(hs)), old(getNHash(hs)), old(lib.ResponseEpkR(response)), old(lib.ResponseMac1(response)), old(lib.ResponseMac2(response)))
//@ ensures  ok ==> GetWgLabeling().IsPublishable(initiator.Snapshot(), epkRX)
// we directly apply the pattern property in this method and thus have the following postconditions:
//@ ensures  ok ==> respT == Term_M2(initiator.getRid(), sidRX, ltkT, pskT, ekiT, c3T, h4T, epkRX, mac1X, mac2X)
//@ ensures  ok ==> getNKey(hs) == tm.gamma(Term_c7(ltkT, pskT, ekiT, c3T, epkRX))
//@ ensures  ok ==> GetWgLabeling().IsValidAead(initiator.Snapshot(), Term_k3(ltkT, pskT, ekiT, c3T, epkRX), tm.zeroString(12), tm.zeroString(0), label.Public(), Term_h6(ltkT, pskT, ekiT, c3T, h4T, epkRX))
func (initiator *Initiator) consumeResponse(hs *lib.Handshake, response *lib.Response /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term, ghost ekiT tm.Term, ghost c3T tm.Term, ghost h4T tm.Term, ghost respT tm.Term @*/) (ok bool /*@, ghost sidRX tm.Term, ghost epkRX tm.Term, ghost mac1X tm.Term, ghost mac2X tm.Term @*/) {

	//@ rid := initiator.getRid()
	//@ aId := initiator.getAId()
	//@ aSessId := initiator.getASessId()
	//@ bId := initiator.getBId()
	//@ bothL := label.Readers(set[p.Id]{ aId, bId })
	//@ bothSessL := label.Readers(set[p.Id]{ aSessId, bId })
	//@ snapshot := initiator.Snapshot()
	//@ unfold acc(InitiatorMem(initiator), 1/8)
	args := &initiator.HandshakeInfo
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ unfold lib.ResponseMem(response)
	//@ kI := labeledlib.Abs(args.PrivateKey)
	//@ psk := labeledlib.Abs(args.PresharedKey)
	//@ epkR := labeledlib.Abs(response.Ephemeral)

	ok = response.Type == 2
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}

	ok = response.Receiver == args.LocalIndex
	if !ok {
		//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
		//@ fold acc(InitiatorMem(initiator), 1/8)
		return
	}

	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(lib.ResponseMem(response), 1/2)

	//@ requires acc(HandshakeMem(hs), 1/2) && acc(lib.ResponseMem(response), 1/2) && acc(lib.HandshakeArgsMem(args), 1/8)
	//@ requires epkR == lib.ResponseEpkR(response)
	//@ requires unfolding acc(lib.HandshakeArgsMem(args), 1/8) in kI == labeledlib.Abs(args.PrivateKey) && psk == labeledlib.Abs(args.PresharedKey)
	//@ ensures  acc(HandshakeMem(hs), 1/2) && acc(lib.ResponseMem(response), 1/2) && acc(lib.HandshakeArgsMem(args), 1/8)
	//@ ensures  labeledlib.Mem(key) && labeledlib.Size(key) == 32 && labeledlib.Abs(key) == Bytes_k3(kI, psk, getEkI(hs), getNKey(hs), epkR)
	//@ ensures  labeledlib.Mem(chainHash) && labeledlib.Size(chainHash) == 32 && labeledlib.Abs(chainHash) == Bytes_h6(kI, psk, getEkI(hs), getNKey(hs), getNHash(hs), epkR)
	//@ ensures  labeledlib.Mem(chainKey) && labeledlib.Size(chainKey) == 32 && labeledlib.Abs(chainKey) == Bytes_c7(kI, psk, getEkI(hs), getNKey(hs), epkR)
	//@ outline(
	//@ unfold acc(HandshakeMem(hs), 1/2)
	//@ unfold acc(lib.ResponseMem(response), 1/2)
	//@ unfold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ ekI := labeledlib.Abs(hs.LocalEphemeral)
	//@ c3 := labeledlib.Abs(hs.ChainKey)
	//@ h4 := labeledlib.Abs(hs.ChainHash)
	chainHash := lib.NewByteString(32)
	chainKey := lib.NewByteString(32)

	lib.ComputeHash(chainHash, hs.ChainHash, response.Ephemeral)
	// chainHash == h5 == hash(<h4, epk_R>)
	//@ assert labeledlib.Abs(chainHash) == Bytes_h5(h4, epkR)
	lib.ComputeKDF1(chainKey, hs.ChainKey, response.Ephemeral)
	// chainKey == c4
	//@ assert labeledlib.Abs(chainKey) == Bytes_c4(c3, epkR)

	{
		ss := lib.ComputeSharedSecret(hs.LocalEphemeral, response.Ephemeral)
		// ss == epk_R^k_I == (g^ek_R)^ek_I
		lib.ComputeKDF1Inplace(chainKey, ss)
		// chainKey == c5
		lib.SetZero(ss)
	}
	//@ assert labeledlib.Abs(chainKey) == Bytes_c5(ekI, c3, epkR)

	{
		ss := lib.ComputeSharedSecret(args.PrivateKey, response.Ephemeral)
		// ss == (g^ek_R)^k_I
		lib.ComputeKDF1Inplace(chainKey, ss)
		// chainKey == c6
		lib.SetZero(ss)
	}
	//@ assert labeledlib.Abs(chainKey) == Bytes_c6(kI, ekI, c3, epkR)

	tau := lib.NewByteString(32)
	key := lib.NewByteString(32)
	lib.ComputeKDF3Inplace(tau, key, chainKey, args.PresharedKey)
	// chainKey == c7
	// tau == pi
	// key == k3
	//@ assert labeledlib.Abs(chainKey) == Bytes_c7(kI, psk, ekI, c3, epkR)
	//@ assert labeledlib.Abs(tau) == Bytes_pi(kI, psk, ekI, c3, epkR)
	//@ assert labeledlib.Abs(key) == Bytes_k3(kI, psk, ekI, c3, epkR)

	lib.ComputeHashInplace(chainHash, tau)
	// chainHash == h6
	//@ assert labeledlib.Abs(chainHash) == Bytes_h6(kI, psk, ekI, c3, h4, epkR)
	//@ fold acc(lib.HandshakeArgsMem(args), 1/8)
	//@ fold acc(HandshakeMem(hs), 1/2)
	//@ fold acc(lib.ResponseMem(response), 1/2)
	//@ )

	/*@
	predictedEpkRX := tm.oneTerm(labeledlib.Abs(response.Ephemeral)) // we take this term if `respT` is not a 7-tuple
	ciphertextT := tm.oneTerm(labeledlib.Abs(response.Empty)) // same here
	ghost if respT.IsTuple7() {
		predictedEpkRX = tm.getTupleElem(respT, 3)
		ciphertextT = tm.getTupleElem(respT, 4)
		// we can transfer knowledge about `respT` only to its components if we
		// assume that it's a 7-tuple, i.e. has the expected shape as this is not
		// implied by the fact that `response` is a `tuple7B`.
		// therefore, we obtain here these facts only under an implication.
		// this implication is then resolved when applying the pattern property at
		// the very end of the parsing process.
		GetWgLabeling().IsMsgTupleResolve(snapshot, respT, label.Public())
	}
	@*/

	// authenticate transcript

	//@ unfold acc(InitiatorMem(initiator), 7/8) // the remaining perm to have 1/1 unfolded afterwards
	//@ keyT := Term_k3(ltkT, pskT, ekiT, c3T, predictedEpkRX)
	//@ nonceT := tm.zeroString(12)
	//@ adT := Term_h6(ltkT, pskT, ekiT, c3T, h4T, predictedEpkRX)
	
	// only check whether c_empty can be decrypted
	_, err := initiator.llib.AeadDec(key, lib.ZeroNonce(), response.Empty, chainHash /*@, keyT, nonceT, ciphertextT, adT, bothL @*/)
	ok = err == nil
	if !ok {
		//@ fold InitiatorMem(initiator)
		return
	}

	/*@
	sidR := tm.integer32B(response.Sender)
	mac1 := labeledlib.SafeAbs(response.MAC1, 16)
	mac2 := labeledlib.SafeAbs(response.MAC2, 16)
	fold pap.pattern1Constraints(initiator.llib, bId, rid, ltkT, ltpkT, pskT, ekiT, c3T, h4T)
	sidRX, epkRX, mac1X, mac2X = pap.patternProperty1(initiator.llib, bId, rid, ltkT, ltpkT, pskT, ekiT, c3T, h4T, tm.oneTerm(sidR), tm.oneTerm(epkR), tm.oneTerm(mac1), tm.oneTerm(mac2), respT)
	unfold pap.pattern1Constraints(initiator.llib, bId, rid, ltkT, ltpkT, pskT, ekiT, c3T, h4T)
	fold InitiatorMem(initiator)
	@*/

	lib.ComputeHashInplace(chainHash, response.Empty)
	// chainHash == hash(<h6, c_empty>)

	//@ unfold HandshakeMem(hs)
	hs.ChainHash = chainHash
	hs.ChainKey = chainKey
	hs.RemoteIndex = response.Sender
	//@ fold HandshakeMem(hs)

	return
}

//@ requires acc(InitiatorMem(initiator), 1/4) && HandshakeMem(hs)
//@ requires getNKey(hs) == tm.gamma(c7T)
//@ requires GetWgLabeling().IsSecretRelaxed(initiator.Snapshot(), c7T, label.Readers(set[p.Id]{ initiator.getASessId(), initiator.getBId() }), u.KdfKey(WgChaininigKey))
//@ ensures  acc(InitiatorMem(initiator), 1/4) && lib.ConnectionMem(conn)
//@ ensures  lib.ConnectionSendKey(conn) == tm.gamma(tm.kdf1(c7T))
//@ ensures  lib.ConnectionRecvKey(conn) == tm.gamma(tm.kdf2(c7T))
//@ ensures  lib.ConnectionNonceVal(conn) == 0
//@ ensures  lib.ConnectionSidI(conn) == old(getSidR(hs))
func (initiator *Initiator) beginSymmetricSession(hs *lib.Handshake /*@, ghost c7T tm.Term @*/) (conn *lib.Connection) {

	sendKey := lib.NewByteString(32)
	recvKey := lib.NewByteString(32)
	//@ unfold HandshakeMem(hs)
	lib.ComputeKDF2(sendKey, recvKey, hs.ChainKey, nil)
	// sendKey == kdf1(c7) == k_IR
	// recvKey == kdf2(c7) == k_RI

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
