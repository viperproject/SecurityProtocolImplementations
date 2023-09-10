package responder

//@ import arb "github.com/viperproject/ReusableProtocolVerificationLibrary/arbitrary"
//@ import ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
import lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/dh/common"
import . "github.com/viperproject/ProtocolVerificationCaseStudies/dh/common/library"
import p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
//@ import tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
//@ import tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
//@ import tman "github.com/viperproject/ReusableProtocolVerificationLibrary/tracemanager"
//@ import u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"

type B struct {
	// identifier of B
	IdB p.Principal
	// B's public key
	PkB []byte
	// B's secret key
	SkB []byte
	// identifier of A
	IdA p.Principal
	Version uint
	// A's public key
	PkA []byte
	llib *ll.LabeledLibrary
	// TODO make these proper ghost field
	//@ SkAT tm.Term
	//@ SkBT tm.Term
}

/*@
pred (b *B) Mem(xT, yT, sharedSecretT tm.Term) {
	acc(b) &&
	0 <= b.Version && b.Version <= 3 &&
	// full permission if not yet initialized, otherwise only 1/2:
	acc(lib.Mem(b.PkB), 1/2) && (b.Version == 0 ==> acc(lib.Mem(b.PkB), 1/2)) &&
	lib.Mem(b.SkB) &&
	lib.Abs(b.SkB) == tm.gamma(b.SkBT) &&
	lib.Abs(b.PkB) == tm.gamma(tm.createPk(b.SkBT)) &&
	b.llib.Mem() &&
	b.llib.Ctx() == GetDhContext() &&
	b.llib.LabelCtx() == GetDhLabeling() &&
	b.llib.Owner() == p.principalId(b.IdB) &&
	GetDhLabeling().IsSecretKey(b.llib.Snapshot(), p.principalId(b.IdB), b.SkBT, labeling.KeyTypeSigning(), DhKey) &&
	(b.Version >= 1 ==>
		acc(lib.Mem(b.PkA), 1/2) &&
		lib.Abs(b.PkA) == tm.gamma(tm.createPk(b.SkAT)) &&
		GetDhLabeling().IsPublicKey(b.llib.Snapshot(), p.principalId(b.IdA), tm.createPk(b.SkAT), b.SkAT, labeling.KeyTypeSigning(), DhKey)) &&
	(b.Version >= 2 ==>
		GetDhLabeling().IsLabeled(b.llib.Snapshot(), yT, label.Readers(set[p.Id]{ p.principalId(b.IdB) })) &&
		GetDhLabeling().IsLabeledRelaxed(b.llib.Snapshot(), sharedSecretT, label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })) &&
		b.llib.Snapshot().eventOccurs(b.IdB, ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, xT, yT, sharedSecretT })) &&
		(	// either a has been corrupted ...
			tr.containsCorruptId(b.llib.Snapshot().getCorruptIds(), set[p.Id]{ p.principalId(b.IdA) }) ||
			// ... or xT is labeled to only be readable by a and the shared secret is (g^x)^y:
            // this is stronger than `isMsg` as it excludes the possibility of restricting a
            // less secret value. This is necessary to invoke the secrecy lemma
			(GetDhLabeling().IsLabeled(b.llib.Snapshot(), xT, label.Readers(set[p.Id]{ p.principalId(b.IdA) })) &&
				sharedSecretT == tm.exp(tm.exp(tm.generator(), xT), yT)))) &&
	(b.Version >= 3 ==>
		b.llib.Secrecy(sharedSecretT, set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) &&
		b.llib.InjectiveAgreement(b.IdB, b.IdA, ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, xT, yT, sharedSecretT }), ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, xT, yT, sharedSecretT }), set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }))
}

ghost
requires acc(b.Mem(xT, yT, sharedSecret), _)
pure func (b *B) Vers(xT, yT, sharedSecret tm.Term) uint {
	return unfolding acc(b.Mem(xT, yT, sharedSecret), _) in b.Version
}
@*/

//@ requires acc(l.Mem(), 1/8)
//@ requires acc(com.LibMem(), 1/8) && com != nil && isComparable(com)
//@ requires manager.Mem(GetDhContext(), p.principalId(responder))
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures  err == nil ==> b.Mem(defaultTerm, defaultTerm, defaultTerm) && unfolding b.Mem(defaultTerm, defaultTerm, defaultTerm) in b.Version == 0 &&
//@				b.IdA == initiator &&
//@				b.IdB == responder &&
//@				manager == b.llib.Manager() &&
//@				// the following conjuncts are necessary such that monotonicity can be applied by the scheduler 
//@				// to the generated secret & public keys:
//@				old(manager.Snapshot(GetDhContext(), p.principalId(responder))).isSuffix(b.llib.Snapshot()) &&
//@				(old(manager.ImmutableState(GetDhContext(), p.principalId(responder))) == unfolding b.llib.Mem() in b.llib.manager.ImmutableState(GetDhContext(), p.principalId(responder)))
// TODO make manager ghost
// TODO remove `defaultTerm` as parameter and simply create it in the body
func InitB(l *lib.LibraryState, com ll.Communication, initiator, responder p.Principal /*@, manager *tman.TraceManager, defaultTerm tm.Term @*/) (b *B, err error) {
	//@ ctx := GetDhContext()
	llib := ll.NewLabeledLibrary(l, com /*@, manager, ctx, p.NewPrincipalId(responder) @*/)
	pk, sk, err /*@, skT @*/ := llib.GenerateSigningKey(/*@ DhKey @*/)
	if err != nil {
		return nil, err
	}
	b = &B{responder, pk, sk, initiator, 0, nil, llib /*@, defaultTerm, skT @*/}
	//@ fold b.Mem(defaultTerm, defaultTerm, defaultTerm)
	return b, nil
}

//@ requires b.Mem(defaultTerm, defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm, defaultTerm) == 1
//@ ensures  err == nil ==> b.Mem(xT, yT, sharedSecretT) && b.Vers(xT, yT, sharedSecretT) == 3
func RunB(b *B /*@, defaultTerm tm.Term @*/) (err error /*@, ghost xT tm.Term, ghost yT tm.Term, ghost sharedSecretT tm.Term @*/) {
	//@ unfold b.Mem(defaultTerm, defaultTerm, defaultTerm)
	//@ s0 := b.llib.Snapshot()
	//@ ctx := GetDhContext()
	//@ labelCtx := GetDhLabeling()
	//@ usageCtx := DhUsageContext{}

	// receive msg1
	msg1Data, err /*@, msg1DataT @*/ := b.llib.Receive(b.IdA, b.IdB)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ s1 := b.llib.Snapshot()
	//@ b.llib.ApplyMonotonicity()
	// decompose msg1Data
	msg1, err := UnmarshalMsg1(msg1Data)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ unfold msg1.Mem()
	X := msg1.X
	//@ XT := msg1DataT

	// create y
	//@ justAL := label.Readers(set[p.Id]{ p.principalId(b.IdA) })
	//@ justBL := label.Readers(set[p.Id]{ p.principalId(b.IdB) })
	//@ labelCtx.CanFlowReflexive(s1, justBL)
	y, err := b.llib.CreateNonce(/*@ justBL, DhNonce, set[ev.EventType]{ Respond, FinishR } @*/)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ s2 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s1, s2)
	//@ yT = tm.random(lib.Abs(y), justBL, u.Nonce(DhNonce))

	Y, err := b.llib.DhExp(y /*@, yT @*/)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ YT := tm.exp(tm.generator(), yT)

	sharedSecret, err := b.llib.DhSharedSecret(y, X)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ sharedSecretT = tm.exp(XT, yT)

	/*@
	respEv := ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, XT, yT, sharedSecretT })
	fold ctx.eventInv(b.IdB, respEv, s2)
	b.llib.TriggerEvent(respEv)
	s3 := b.llib.Snapshot()
	s0.isSuffixTransitive(s2, s3)
	s1.isSuffixTransitive(s2, s3)
	b.llib.ApplyMonotonicity()
	@*/

	// build & sign msg2
	msg2/*@ @ @*/ := &Msg2{b.IdA, b.IdB, X, Y}
	//@ fold msg2.Mem()
	msg2Data, err := MarshalMsg2(msg2)
	//@ unfold msg2.Mem()
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ msg2T := tm.tuple5(tm.integer32(Msg2Tag), tm.stringTerm(b.IdB), tm.stringTerm(b.IdA), XT, YT)
	//@ assert lib.Abs(msg2Data) == tm.gamma(msg2T)
	//@ b.llib.ApplyMonotonicity()
	//@ s1.isSuffixTransitive(s2, s3)
	//@ labelCtx.IsPublishableMonotonic(s1, s3, XT)
	//@ labelCtx.IsPublishableMonotonic(s2, s3, YT)
	//@ labelCtx.IsMsgTupleCreate(s3, msg2T, label.Public())
	//@ assert labelCtx.IsSignKey(s3, b.SkBT, p.principalId(b.IdB), DhKey)
	// the following assertion is necessary:
	//@ assert usageCtx.SignPredMsg2(s3, msg2T, yT)
	signedMsg2, err := b.llib.Sign(msg2Data, b.SkB /*@, msg2T, b.SkBT, p.principalId(b.IdB) @*/)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	// send msg2
	//@ ghost signedMsg2T := tm.sign(msg2T, b.SkBT)
	err = b.llib.Send(b.IdB, b.IdA, signedMsg2 /*@, signedMsg2T @*/)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ s4 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s3, s4)
	// receive msg3
	signedMsg3, err /*@, signedMsg3T @*/ := b.llib.Receive(b.IdA, b.IdB)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ s5 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s4, s5)
	//@ b.llib.ApplyMonotonicity()
	// open msg3
	msg3Data, err := b.llib.Open(signedMsg3, b.PkA /*@, signedMsg3T, b.SkAT, p.principalId(b.IdA) @*/)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	// decompose msg3Data
	msg3, err := UnmarshalMsg3(msg3Data)
	if err != nil {
		return err /*@, xT, yT, sharedSecretT @*/
	}
	//@ unfold msg3.Mem()
	// check validity of msg3:
	if !lib.Compare(X, msg3.X) {
		return lib.NewError("X does not match") /*@, xT, yT, sharedSecretT @*/
	}
	if !lib.Compare(Y, msg3.Y) {
		return lib.NewError("Y does not match") /*@, xT, yT, sharedSecretT @*/
	}
	if b.IdA != msg3.IdA {
		return lib.NewError("idA does not match") /*@, xT, yT, sharedSecretT @*/
	}
	if b.IdB != msg3.IdB {
		return lib.NewError("idB does not match") /*@, xT, yT, sharedSecretT @*/
	}
	/*@
	patternRequirement3(tm.stringTerm(b.IdA), tm.stringTerm(b.IdB), b.SkAT, yT, XT, signedMsg3T)
	msg3T := tm.tuple5(tm.integer32(Msg3Tag), tm.stringTerm(b.IdA), tm.stringTerm(b.IdB), YT, XT)
	// patternRequirement3 gives us uniqueness for signedMsg3T:
	assert signedMsg3T == tm.sign(msg3T, b.SkAT)

	s3.isSuffixTransitive(s4, s5)
	// the following 2 lemma applications help in deriving `IsSignKey`:
	labelCtx.CanFlowReflexive(s0, justAL)
	labelCtx.IsSecretRelaxedMonotonic(s0, s5, b.SkAT, justAL, u.SigningKey(DhKey))
	xT = processMsg3(b.llib, msg3T, b.SkAT, XT, yT, b.IdA, b.IdB)

	finishREv := ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, xT, yT, sharedSecretT })
	fold ctx.eventInv(b.IdB, finishREv, s5)
	b.llib.TriggerEvent(finishREv)
	s6 := b.llib.Snapshot()
	s0.isSuffixTransitive(s5, s6)
	b.llib.ApplyMonotonicity()
	@*/

	if err == nil {
		PrintResponderSuccess(sharedSecret)
	}
	b.Version = 2
	//@ fold b.Mem(xT, yT, sharedSecretT)

	//@ b.proveSecurityProperties(xT, yT, sharedSecretT)

	return err /*@, xT, yT, sharedSecretT @*/
}

/*@
ghost
decreases
requires llib.Mem() && llib.Ctx() == GetDhContext() && llib.LabelCtx() == GetDhLabeling() && llib.Owner() == p.principalId(idB)
requires msg3T == tm.tuple5(tm.integer32(Msg3Tag), tm.stringTerm(idA), tm.stringTerm(idB), tm.exp(tm.generator(), yT), XT)
requires GetDhLabeling().IsSignKey(llib.Snapshot(), skAT, p.principalId(idA), DhKey)
requires llib.Snapshot().nonceOccurs(yT, label.Readers(set[p.Id]{ p.principalId(idB) }), u.Nonce(DhNonce))
requires GetDhLabeling().IsPublishable(llib.Snapshot(), tm.sign(msg3T, skAT))
requires GetDhLabeling().WasOpened(llib.Snapshot(), msg3T, skAT, p.principalId(idA))
ensures  llib.Mem() && llib.Ctx() == GetDhContext() && llib.LabelCtx() == GetDhLabeling() && llib.Owner() == p.principalId(idB)
ensures  old(llib.Snapshot()) == llib.Snapshot()
ensures  GetDhLabeling().IsLabeledRelaxed(llib.Snapshot(), tm.exp(XT, yT), label.Readers(set[p.Id]{ p.principalId(idA), p.principalId(idB) }))
ensures  tr.containsCorruptId(llib.Snapshot().getCorruptIds(), set[p.Id]{ p.principalId(idA), p.principalId(idB) }) ||
	llib.Snapshot().eventOccurs(idA, ev.NewEvent(FinishI, FinishIParams{ idA, idB, xT, yT, tm.exp(XT, yT) }))
ensures  tr.containsCorruptId(llib.Snapshot().getCorruptIds(), set[p.Id]{ p.principalId(idA) }) ||
	(XT == tm.exp(tm.generator(), xT) &&
		GetDhLabeling().IsLabeled(llib.Snapshot(), xT, label.Readers(set[p.Id]{ p.principalId(idA) })))
func processMsg3(llib *ll.LabeledLibrary, msg3T, skAT, XT, yT tm.Term, idA, idB string) (xT tm.Term) {
	labelCtx := GetDhLabeling()
	usageCtx := DhUsageContext{}
	snap := llib.Snapshot()
	aCorrupted := tr.containsCorruptId(snap.getCorruptIds(), set[p.Id]{ p.principalId(idA) })
	eitherCorrupted := tr.containsCorruptId(snap.getCorruptIds(), set[p.Id]{ p.principalId(idA), p.principalId(idB) })
	if labelCtx.IsPublishable(snap, skAT) && labelCtx.IsPublishable(snap, msg3T) {
		labelCtx.IsMsgTupleResolve(snap, msg3T, label.Public())
		if aCorrupted && eitherCorrupted {} else {
			labelCtx.PublishableImpliesCorruption(snap, skAT, label.Readers(set[p.Id]{ p.principalId(idA) }))
			labelCtx.containsCorruptIdMonotonic(snap.getCorruptIds(), set[p.Id]{ p.principalId(idA) }, set[p.Id]{ p.principalId(idA), p.principalId(idB) })
			assert false // contradiction -- as expected
		}
	} else {
		// `SignPred` holds
		assert exists x, y tm.Term :: { usageCtx.SignPredMsg3(snap, msg3T, x, y) } usageCtx.SignPredMsg3(snap, msg3T, x, y)
		// get witnesses
		xT = arb.GetArbTerm()
		yWit := arb.GetArbTerm()
		assume usageCtx.SignPredMsg3(snap, msg3T, xT, yWit)
		assert yT == yWit || tr.containsCorruptId(snap.getCorruptIds(), set[p.Id]{ p.principalId(idB) })
		llib.NonceOccursImpliesRandInv(xT)
	}

	bothLabel := label.Readers(set[p.Id]{ p.principalId(idA), p.principalId(idB) })
	// the following assert stmt is needed:
	assert labelCtx.IsValidSignature(snap, msg3T, skAT)
	labelCtx.IsMsgTupleResolve(snap, msg3T, label.Public())
	llib.NonceOccursImpliesRandInv(yT)

	ghost if eitherCorrupted {
		labelCtx.FlowsToPublicCanFlow(snap, bothLabel, labelCtx.GetLabel(tm.exp(XT, yT)))
	} else {
		// this branch also implies that idA and idB cannot have been corrupted:
		if tr.containsCorruptId(snap.getCorruptIds(), set[p.Id]{ p.principalId(idA) }) {
			labelCtx.containsCorruptIdMonotonic(snap.getCorruptIds(), set[p.Id]{ p.principalId(idA) }, set[p.Id]{ p.principalId(idA), p.principalId(idB) })
			assert false // contradiction -- as expected
		}
		if tr.containsCorruptId(snap.getCorruptIds(), set[p.Id]{ p.principalId(idB) }) {
			labelCtx.containsCorruptIdMonotonic(snap.getCorruptIds(), set[p.Id]{ p.principalId(idB) }, set[p.Id]{ p.principalId(idA), p.principalId(idB) })
			assert false // contradiction -- as expected
		}

		labelCtx.CanFlowToSubsetReaders(snap, bothLabel, label.Readers(set[p.Id]{ p.principalId(idA) }))
		labelCtx.CanFlowToSubsetReaders(snap, bothLabel, label.Readers(set[p.Id]{ p.principalId(idB) }))
	}
}
@*/
