package responder

import lib "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/library"

//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
//@ import labeledlib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"


// to retain a similar code structure, the parameters passed to the implementation (such as its secret key or the peer's public key)
// are not directly parameters to this function but are returned by `getInitialState`
//@ requires lib.LibMem(&responder.LibState) && acc(&responder.HandshakeInfo) && acc(&responder.a) && acc(&responder.b) && acc(&responder.llib)
//@ requires llib.Mem() && llib.Ctx() == GetWgContext() && llib.LabelCtx() == GetWgLabeling() && llib.Owner() == p.sessionId(lib.Principal(b), sid)
func (responder *Responder) RunResponder(sid, a, b uint32, llib *ll.LabeledLibrary) {
	ok /*@, pskT, ltkT, ltpkT @*/ := responder.getInitialState(sid, a, b, llib)
	if !ok {
		return
	}

	//@ ghost var corrupted bool
	//@ ghost var aSess uint32
	//@ ghost var epkIX, ekrT, kirT, kriT tm.Term
	keypair, ok /*@, corrupted, aSess, epkIX, ekrT, kirT, kriT @*/ := responder.runHandshake( /*@ pskT, ltkT, ltpkT @*/ )
	if !ok {
		return
	}

	go responder.forwardPackets(keypair /*@, epkIX, ekrT, kirT, kriT, corrupted, aSess @*/)
}

//@ requires lib.LibMem(&responder.LibState) && acc(&responder.HandshakeInfo) && acc(&responder.a) && acc(&responder.b) && acc(&responder.llib)
//@ requires llib.Mem() && llib.Ctx() == GetWgContext() && llib.LabelCtx() == GetWgLabeling() && llib.Owner() == p.sessionId(lib.Principal(b), sid)
//@ ensures  ok ==> ResponderMem(responder)
//@ ensures  ok ==> getPsk(responder) == tm.gamma(pskT)
//@ ensures  ok ==> getKR(responder) == tm.gamma(ltkT)
//@ ensures  ok ==> getPkI(responder) == tm.gamma(ltpkT)
//@ ensures  ok ==> GetWgLabeling().IsLabeled(responder.Snapshot(), pskT, label.Public())
//@ ensures  ok ==> GetWgLabeling().IsSecretKey(responder.Snapshot(), responder.getBId(), ltkT, labeling.KeyTypeDh(), WgKey)
//@ ensures  ok ==> ltkT.IsRandom()
//@ ensures  ok ==> GetWgLabeling().IsPublicKeyExistential(responder.Snapshot(), responder.getAId(), ltpkT, labeling.KeyTypeDh(), WgKey)
func (responder *Responder) getInitialState(sid, a, b uint32, llib *ll.LabeledLibrary) (ok bool /*@, ghost pskT tm.Term, ghost ltkT tm.Term, ghost ltpkT tm.Term @*/) {

	var psk lib.ByteString
	ok, psk /*@, pskT @*/ = responder.LibState.GetPsKBio(a, b /*@, llib @*/)
	if !ok || len(psk) != 32 {
		ok = false
		return
	}

	var ltk lib.ByteString
	ok, ltk /*@, ltkT @*/ = responder.LibState.GetLtKBio(b /*@, llib @*/)
	if !ok || len(ltk) != 32 {
		ok = false
		return
	}

	var ltpk lib.ByteString
	ok, ltpk /*@, ltpkT @*/ = responder.LibState.GetLtpKBio(a /*@, llib @*/)
	if !ok || len(ltpk) != 32 {
		ok = false
		return
	}

	responder.HandshakeInfo.PresharedKey = psk
	responder.HandshakeInfo.PrivateKey = ltk
	responder.HandshakeInfo.LocalIndex = sid
	responder.HandshakeInfo.LocalStatic = lib.PublicKey(ltk)
	responder.HandshakeInfo.RemoteStatic = ltpk
	responder.a = a
	responder.b = b
	responder.llib = llib

	//@ fold lib.HandshakeArgsMem(&responder.HandshakeInfo)
	//@ fold ResponderMem(responder)
	return
}
