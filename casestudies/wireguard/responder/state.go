package responder

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"

import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
//@ import labeledlib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"


type Responder struct {
	LibState      lib.LibraryState
	HandshakeInfo lib.HandshakeArguments
	a, b          uint32
	llib 		  *ll.LabeledLibrary // added
}

/*@
const WgReceivingKey = "WG kir Key"
const WgSendingKey = "WG kri Key"

pred HandshakeMem1(hs *lib.Handshake) {
	acc(hs) && labeledlib.Mem(hs.ChainHash) && labeledlib.Mem(hs.ChainKey) && labeledlib.Mem(hs.RemoteEphemeral) &&
	labeledlib.Size(hs.ChainHash) == 32 && labeledlib.Size(hs.ChainKey) == 32 && labeledlib.Size(hs.RemoteEphemeral) == 32
}

pred HandshakeMem2(hs *lib.Handshake) {
	acc(hs) && labeledlib.Mem(hs.ChainHash) && labeledlib.Mem(hs.ChainKey) && labeledlib.Mem(hs.LocalEphemeral) && labeledlib.Mem(hs.RemoteEphemeral) &&
	labeledlib.Size(hs.ChainHash) == 32 && labeledlib.Size(hs.ChainKey) == 32 && labeledlib.Size(hs.LocalEphemeral) == 32 && labeledlib.Size(hs.RemoteEphemeral) == 32
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getNHash1(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in labeledlib.Abs(hs.ChainHash)
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getNKey1(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in labeledlib.Abs(hs.ChainKey)
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getEpkI1(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in labeledlib.Abs(hs.RemoteEphemeral)
}

ghost
requires acc(HandshakeMem1(hs), _)
pure func getSidI1(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem1(hs), _) in tm.integer32B(hs.RemoteIndex)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getNHash2(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in labeledlib.Abs(hs.ChainHash)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getNKey2(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in labeledlib.Abs(hs.ChainKey)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getEpkI2(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in labeledlib.Abs(hs.RemoteEphemeral)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getEkR2(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in labeledlib.Abs(hs.LocalEphemeral)
}

ghost
requires acc(HandshakeMem2(hs), _)
pure func getSidI2(hs *lib.Handshake) tm.Bytes {
	return unfolding acc(HandshakeMem2(hs), _) in tm.integer32B(hs.RemoteIndex)
}


pred ResponderMem(responder * Responder) {
	lib.LibMem(&responder.LibState) &&
	lib.HandshakeArgsMem(&responder.HandshakeInfo) &&
	acc(&responder.a) && acc(&responder.b) &&
	acc(&responder.llib) &&
	responder.llib.Mem() &&
	responder.llib.Ctx() == GetWgContext() &&
	responder.llib.LabelCtx() == GetWgLabeling() &&
	unfolding lib.HandshakeArgsMem(&responder.HandshakeInfo) in
		responder.llib.Owner() == p.sessionId(lib.Principal(responder.b), responder.HandshakeInfo.LocalIndex)
}


ghost
requires acc(ResponderMem(responder), _)
pure func getSidR(responder *Responder) tm.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in tm.integer32B((responder.HandshakeInfo).LocalIndex)
}

ghost
requires acc(ResponderMem(responder), _)
pure func getKR(responder *Responder) tm.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in labeledlib.Abs((responder.HandshakeInfo).PrivateKey)
}

ghost
requires acc(ResponderMem(responder), _)
pure func getPkI(responder *Responder) tm.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in labeledlib.Abs((responder.HandshakeInfo).RemoteStatic)
}

ghost
requires acc(ResponderMem(responder), _)
pure func getPsk(responder *Responder) tm.Bytes {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in labeledlib.Abs((responder.HandshakeInfo).PresharedKey)
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getRid() (rid tm.Term) {
	return unfolding acc(ResponderMem(responder), _) in unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in (
		tm.integer32((responder.HandshakeInfo).LocalIndex))
}



ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getPP() (pp tm.Term) {
	return unfolding acc(ResponderMem(responder), _) in tm.tuple4(tm.integer32(responder.a), tm.integer32(responder.b), tm.prologueTerm(), tm.infoTerm())
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) Snapshot() tr.TraceEntry {
	return unfolding acc(ResponderMem(responder), _) in responder.llib.Snapshot()
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getAId() p.Id {
	return unfolding acc(ResponderMem(responder), _) in lib.principalId(responder.a)
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getASessId(aSess uint32) p.Id {
	return p.sessionId(responder.getAId().getPrincipal(), aSess)
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getBId() p.Id {
	return unfolding acc(ResponderMem(responder), _) in lib.principalId(responder.b)
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) getBSessId() p.Id {
	return p.sessionId(responder.getBId().getPrincipal(), tm.getInt32(responder.getRid()))
}

type ImmutableState struct {
	a, b, rid uint32
	llib ll.ImmutableState
}

ghost
requires acc(ResponderMem(responder), _)
pure func (responder *Responder) ImmutableState() ImmutableState {
	return unfolding acc(ResponderMem(responder), _) in
		unfolding acc(lib.HandshakeArgsMem(&responder.HandshakeInfo), _) in
			ImmutableState{ responder.a, responder.b, responder.HandshakeInfo.LocalIndex, responder.llib.ImmutableState() }
}
@*/
