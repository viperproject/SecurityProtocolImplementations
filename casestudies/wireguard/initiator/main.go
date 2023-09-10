package initiator

//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
//@ import labeledlib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"


// to retain a similar code structure, the parameters passed to the implementation (such as its secret key or the peer's public key)
// are not directly parameters to this function but are returned by `getInitialState`
//@ requires lib.LibMem(&initiator.LibState) && acc(initiator)
//@ requires llib.Mem() && llib.Ctx() == GetWgContext() && llib.LabelCtx() == GetWgLabeling() && llib.Owner() == p.sessionThreadId(lib.Principal(a), sid, 0)
//@ requires llib2.Mem() && llib2.Ctx() == GetWgContext() && llib2.LabelCtx() == GetWgLabeling() && llib2.Owner() == p.sessionThreadId(lib.Principal(a), sid, 1)
//@ requires unfolding llib.Mem() in unfolding llib2.Mem() in llib.manager.ImmutableState(llib.ctx, llib.owner) == llib2.manager.ImmutableState(llib2.ctx, llib2.owner)
func (initiator *Initiator) RunInitiator(sid, a, b uint32, llib *ll.LabeledLibrary, llib2 *ll.LabeledLibrary) {
	ok /*@, pskT, ltkT, ltpkT @*/ := initiator.getInitialState(sid, a, b, llib, llib2)
	if !ok {
		return
	}
	
	//@ ghost var corrupted bool
	//@ ghost var bSess uint32
	//@ ghost var ekiT, epkRX, ekRX, kirT, kriT tm.Term
	keypair, ok /*@, corrupted, bSess, ekiT, epkRX, ekRX, kirT, kriT @*/ := initiator.runHandshake( /*@ pskT, ltkT, ltpkT @*/ )
	if !ok {
		return
	}

	go initiator.forwardPackets(keypair /*@, ekiT, epkRX, ekRX, kirT, kriT, bSess, corrupted @*/)
}

//@ requires lib.LibMem(&initiator.LibState) && acc(initiator)
//@ requires llib.Mem() && llib.Ctx() == GetWgContext() && llib.LabelCtx() == GetWgLabeling() && llib.Owner() == p.sessionThreadId(lib.Principal(a), sid, 0)
//@ requires llib2.Mem() && llib2.Ctx() == GetWgContext() && llib2.LabelCtx() == GetWgLabeling() && llib2.Owner() == p.sessionThreadId(lib.Principal(a), sid, 1)
//@ requires unfolding llib.Mem() in unfolding llib2.Mem() in llib.manager.ImmutableState(llib.ctx, llib.owner) == llib2.manager.ImmutableState(llib2.ctx, llib2.owner)
//@ ensures  ok ==> InitiatorMem(initiator)
//@ ensures  ok ==> getPsk(initiator) == tm.gamma(pskT)
//@ ensures  ok ==> getKI(initiator) == tm.gamma(ltkT)
//@ ensures  ok ==> getPkR(initiator) == tm.gamma(ltpkT)
//@ ensures  ok ==> GetWgLabeling().IsLabeled(initiator.Snapshot(), pskT, label.Public())
//@ ensures  ok ==> GetWgLabeling().IsSecretKey(initiator.Snapshot(), initiator.getAId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  ok ==> ltkT.IsRandom()
//@ ensures  ok ==> GetWgLabeling().IsPublicKeyExistential(initiator.Snapshot(), initiator.getBId(), ltpkT, labeling.KeyTypeDh(), WgKey)
func (initiator *Initiator) getInitialState(sid, a, b uint32, llib *ll.LabeledLibrary, llib2 *ll.LabeledLibrary) (ok bool /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/) {

	var psk lib.ByteString
	ok, psk /*@, pskT @*/ = initiator.LibState.GetPsKBio(a, b /*@, llib @*/)
	if !ok || len(psk) != 32 {
		ok = false
		return
	}

	var ltk lib.ByteString
	ok, ltk /*@, ltkT @*/ = initiator.LibState.GetLtKBio(a /*@, llib @*/)
	if !ok || len(ltk) != 32 {
		ok = false
		return
	}

	var ltpk lib.ByteString
	ok, ltpk /*@, ltpkT @*/ = initiator.LibState.GetLtpKBio(b /*@, llib @*/)
	if !ok || len(ltpk) != 32 {
		ok = false
		return
	}

	initiator.HandshakeInfo.PresharedKey = psk
	initiator.HandshakeInfo.PrivateKey = ltk
	initiator.HandshakeInfo.LocalIndex = sid
	initiator.HandshakeInfo.LocalStatic = lib.PublicKey(ltk)
	initiator.HandshakeInfo.RemoteStatic = ltpk
	initiator.a = a
	initiator.b = b
	initiator.llib = llib
	initiator.llib2 = llib2

	//@ fold lib.HandshakeArgsMem(&initiator.HandshakeInfo)
	//@ fold InitiatorMem(initiator)
	return
}
