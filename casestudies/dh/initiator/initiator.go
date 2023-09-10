package initiator

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

type A struct {
	// identifier of A
	IdA p.Principal
	// A's public key
	PkA lib.ByteString
	// A's secret key
	SkA lib.ByteString
	// identifier of B
	IdB p.Principal
	Version uint
	// B's public key
	PkB lib.ByteString
	llib *ll.LabeledLibrary
	// TODO make these proper ghost field
	//@ SkAT tm.Term
	//@ SkBT tm.Term
}

/*@
pred (a *A) Mem(xT, yT tm.Term) {
	acc(a) &&
	0 <= a.Version && a.Version <= 3 &&
	// full permission if not yet initialized, otherwise only 1/2:
	acc(lib.Mem(a.PkA), 1/2) && (a.Version == 0 ==> acc(lib.Mem(a.PkA), 1/2)) &&
	lib.Mem(a.SkA) &&
	lib.Abs(a.SkA) == tm.gamma(a.SkAT) &&
	lib.Abs(a.PkA) == tm.gamma(tm.createPk(a.SkAT)) &&
	a.llib.Mem() &&
	a.llib.Ctx() == GetDhContext() &&
	a.llib.LabelCtx() == GetDhLabeling() &&
	a.llib.Owner() == p.principalId(a.IdA) &&
	GetDhLabeling().IsSecretKey(a.llib.Snapshot(), p.principalId(a.IdA), a.SkAT, labeling.KeyTypeSigning(), DhKey) &&
	(a.Version >= 1 ==>
		acc(lib.Mem(a.PkB), 1/2) &&
		lib.Abs(a.PkB) == tm.gamma(tm.createPk(a.SkBT)) &&
		GetDhLabeling().IsPublicKey(a.llib.Snapshot(), p.principalId(a.IdB), tm.createPk(a.SkBT), a.SkBT, labeling.KeyTypeSigning(), DhKey)) &&
	(a.Version >= 2 ==>
		let sharedSecretT := tm.exp(tm.exp(tm.generator(), xT), yT) in
		GetDhLabeling().IsLabeled(a.llib.Snapshot(), xT, label.Readers(set[p.Id]{ p.principalId(a.IdA) })) &&
		GetDhLabeling().IsLabeledRelaxed(a.llib.Snapshot(), sharedSecretT, label.Readers(set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) })) &&
		a.llib.Snapshot().eventOccurs(a.IdA, ev.NewEvent(FinishI, FinishIParams{ a.IdA, a.IdB, xT, yT, sharedSecretT })) &&
		( 	// either b has been corrupted ...
			tr.containsCorruptId(a.llib.Snapshot().getCorruptIds(), set[p.Id]{ p.principalId(a.IdB) }) ||
			// ... or y is labeled to only be readable by b
            // this is stronger than `isMsg` as it excludes the possibility of restricting a
            // less secret value. This is necessary to invoke the secrecy lemma
			GetDhLabeling().IsLabeled(a.llib.Snapshot(), yT, label.Readers(set[p.Id]{ p.principalId(a.IdB) })))) &&
	(a.Version >= 3 ==>
		let sharedSecretT := tm.exp(tm.exp(tm.generator(), yT), xT) in
		a.llib.Secrecy(sharedSecretT, set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) }) &&
		a.llib.InjectiveAgreement(a.IdA, a.IdB, ev.NewEvent(FinishI, FinishIParams{ a.IdA, a.IdB, xT, yT, sharedSecretT }), ev.NewEvent(Respond, RespondParams{ a.IdA, a.IdB, tm.exp(tm.generator(), xT), yT, sharedSecretT }), set[p.Id]{ p.principalId(a.IdB) }))
}

ghost
requires acc(a.Mem(x, y), _)
pure func (a *A) Vers(x, y tm.Term) uint {
	return unfolding acc(a.Mem(x, y), _) in a.Version
}
@*/

//@ requires acc(l.Mem(), 1/8)
//@ requires acc(com.LibMem(), 1/8) && com != nil && isComparable(com)
//@ requires manager.Mem(GetDhContext(), p.principalId(initiator))
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures  err == nil ==> a.Mem(defaultTerm, defaultTerm) && unfolding a.Mem(defaultTerm, defaultTerm) in a.Version == 0 &&
//@ 			a.IdA == initiator &&
//@				a.IdB == responder &&
//@				manager == a.llib.Manager() &&
//@				// the following conjuncts are necessary such that monotonicity can be applied by the scheduler 
//@				// to the generated secret & public keys:
//@				old(manager.Snapshot(GetDhContext(), p.principalId(initiator))).isSuffix(a.llib.Snapshot()) &&
//@				(old(manager.ImmutableState(GetDhContext(), p.principalId(initiator))) == unfolding a.llib.Mem() in a.llib.manager.ImmutableState(GetDhContext(), p.principalId(initiator)))
// TODO make manager ghost
// TODO remove `defaultTerm` as parameter and simply create it in the body
func InitA(l *lib.LibraryState, com ll.Communication, initiator, responder p.Principal /*@, manager *tman.TraceManager, defaultTerm tm.Term @*/) (a *A, err error) {
	//@ ctx := GetDhContext()
	llib := ll.NewLabeledLibrary(l, com /*@, manager, ctx, p.NewPrincipalId(initiator) @*/)
	pk, sk, err /*@, skT @*/ := llib.GenerateSigningKey(/*@ DhKey @*/)
	if err != nil {
		return nil, err
	}
	a = &A{initiator, pk, sk, responder, 0, nil, llib /*@, skT, defaultTerm @*/}
	//@ fold a.Mem(defaultTerm, defaultTerm)
	return a, nil
}

//@ requires a.Mem(defaultTerm, defaultTerm) && a.Vers(defaultTerm, defaultTerm) == 1
//@ ensures  err == nil ==> a.Mem(xT, yT) && a.Vers(xT, yT) == 3
func RunA(a *A /*@, defaultTerm tm.Term @*/) (err error /*@, ghost xT tm.Term, ghost yT tm.Term @*/) {
	//@ unfold a.Mem(defaultTerm, defaultTerm)

	//@ s0 := a.llib.Snapshot()
	//@ ctx := GetDhContext()
	//@ labelCtx := GetDhLabeling()
	//@ usageCtx := DhUsageContext{}

	// create x
	//@ justAL := label.Readers(set[p.Id]{ p.principalId(a.IdA) })
	//@ justBL := label.Readers(set[p.Id]{ p.principalId(a.IdB) })
	//@ labelCtx.CanFlowReflexive(s0, justAL)
	x, err := a.llib.CreateNonce(/*@ justAL, DhNonce, set[ev.EventType]{ Initiate, FinishI } @*/)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ s1 := a.llib.Snapshot()
	//@ xT = tm.random(lib.Abs(x), justAL, u.Nonce(DhNonce))
	// the following assert stmt is needed such that monotonicity will trigger for xT:
	//@ assert s1.nonceOccurs(xT, justAL, u.Nonce(DhNonce))

	X, err := a.llib.DhExp(x /*@, xT @*/)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ XT := tm.exp(tm.generator(), xT)

	/*@
	initEv := ev.NewEvent(Initiate, InitiateParams{ a.IdA, a.IdB, xT, tm.exp(tm.generator(), xT) })
	fold ctx.eventInv(a.IdA, initEv, s1)
	a.llib.TriggerEvent(initEv)
	s2 := a.llib.Snapshot()
	s0.isSuffixTransitive(s1, s2)
	a.llib.ApplyMonotonicity()
	@*/

	// build & encrypt msg1
	msg1/*@ @ @*/ := &Msg1{X}
	//@ fold msg1.Mem()
	msg1Data, err := MarshalMsg1(msg1)
	//@ unfold msg1.Mem()
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ labelCtx.IsPublishableMonotonic(s1, s2, XT)
	err = a.llib.Send(a.IdA, a.IdB, msg1Data /*@, XT @*/)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ s3 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s2, s3)
	// receive msg2
	signedMsg2, err /*@, signedMsg2T @*/ := a.llib.Receive(a.IdB, a.IdA)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ s4 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s3, s4)
	//@ a.llib.ApplyMonotonicity()
	// open msg2
	msg2Data, err := a.llib.Open(signedMsg2, a.PkB /*@, signedMsg2T, a.SkBT, p.principalId(a.IdB) @*/)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	// decompose msg2Data
	msg2, err := UnmarshalMsg2(msg2Data)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ unfold msg2.Mem()
	// check validity of msg2:
	if !lib.Compare(X, msg2.X) {
		return lib.NewError("X does not match") /*@, xT, yT @*/
	}
	if a.IdA != msg2.IdA {
		return lib.NewError("idA does not match") /*@, xT, yT @*/
	}
	if a.IdB != msg2.IdB {
		return lib.NewError("idB does not match") /*@, xT, yT @*/
	}
	Y := msg2.Y
	//@ YT := patternRequirement2(tm.stringTerm(a.IdA), tm.stringTerm(a.IdB), a.SkBT, xT, tm.oneTerm(lib.Abs(msg2.Y)), signedMsg2T)
	// the following assert stmt is necessary to derive the assertion right after it:
	//@ assert tm.verifyB(tm.signB(tm.tuple5B(tm.integer32B(Msg2Tag), tm.gamma(tm.stringTerm(a.IdB)), tm.gamma(tm.stringTerm(a.IdA)), lib.Abs(X), lib.Abs(msg2.Y)), tm.gamma(a.SkBT)), tm.createPkB(tm.gamma(a.SkBT)))
	//@ assert lib.Abs(msg2.Y) == tm.gamma(YT)

	//@ msg2T := tm.tuple5(tm.integer32(Msg2Tag), tm.stringTerm(a.IdB), tm.stringTerm(a.IdA), XT, YT)
	//@ assert lib.Abs(msg2Data) == tm.gamma(msg2T)
	//@ assert signedMsg2T == tm.sign(msg2T, a.SkBT)

	// the following lemma application is necessary to derive that `IsSignKey` holds:
	//@ labelCtx.CanFlowReflexive(s4, justBL)
	// the following assert stmt is necessary to trigger the quantifier we obtain in `Open`'s postcondition:
	//@ assert labelCtx.IsSignKey(s4, a.SkBT, p.principalId(a.IdB), DhKey)

	/*@
	ghost if labelCtx.IsPublishable(s4, a.SkBT) && labelCtx.IsPublishable(s4, msg2T) {
		labelCtx.IsMsgTupleResolve(s4, msg2T, label.Public())
		assert labelCtx.IsPublishable(s4, YT)
	} else {
		// `SignPred` holds
		assert exists yT tm.Term :: { usageCtx.SignPredMsg2(s4, msg2T, yT) } usageCtx.SignPredMsg2(s4, msg2T, yT)
		// get witness
		yT = arb.GetArbTerm()
		assume usageCtx.SignPredMsg2(s4, msg2T, yT)
		a.llib.NonceOccursImpliesRandInv(yT)
	}
	@*/

	/*@
	// facts after receiving msg2:
	corruptionOccurred := tr.containsCorruptId(s4.getCorruptIds(), set[p.Id]{ p.principalId(a.IdB) })
	assert labelCtx.IsPublishable(s4, YT)
	ghost if !corruptionOccurred {
		assert s4.nonceOccurs(yT, justBL, u.Nonce(DhNonce))
		assert s4.eventOccurs(a.IdB, ev.NewEvent(Respond, RespondParams{ a.IdA, a.IdB, XT, yT, tm.exp(XT, yT) }))
	}
	@*/

	sharedSecret, err := a.llib.DhSharedSecret(x, Y)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ sharedSecretT := tm.exp(tm.exp(tm.generator(), yT), xT)
	//@ aJoinBL := label.Join(justAL, justBL)
	//@ assert corruptionOccurred || labelCtx.IsLabeled(s4, sharedSecretT, aJoinBL)

	// we prove next that `bothLabel` flows to shared secret's label (by contradiction)
	/*@
	bothLabel := label.Readers(set[p.Id]{ p.principalId(a.IdA), p.principalId(a.IdB) })
	ghost if labelCtx.IsLabeledRelaxed(s4, sharedSecretT, bothLabel) {} else {
		labelCtx.CanFlowToSubsetReaders(s4, bothLabel, justBL)
		if corruptionOccurred {
			labelCtx.CanFlowTransitive(s4, bothLabel, justBL, label.Public())
			labelCtx.FlowsToPublicCanFlow(s4, bothLabel, labelCtx.GetLabel(sharedSecretT))
		} else {
			labelCtx.CanFlowToSubsetReaders(s4, bothLabel, justAL)
		}
		assert false // contradiction -- as expected
	}
	@*/

	/*@
	finishIEv := ev.NewEvent(FinishI, FinishIParams{ a.IdA, a.IdB, xT, yT, sharedSecretT })
	s1.isSuffixTransitive(s2, s3)
	s1.isSuffixTransitive(s3, s4)
	fold ctx.eventInv(a.IdA, finishIEv, s4)
	a.llib.TriggerEvent(finishIEv)
	s5 := a.llib.Snapshot()
	s0.isSuffixTransitive(s4, s5)
	a.llib.ApplyMonotonicity()
	@*/

	// build & sign msg3
	msg3/*@ @ @*/ := &Msg3{ a.IdA, a.IdB, X, Y }
	//@ fold msg3.Mem()
	msg3Data, err := MarshalMsg3(msg3)
	if err != nil {
		return err /*@, xT, yT @*/
	}
	//@ msg3T := tm.tuple5(tm.integer32(Msg3Tag), tm.stringTerm(a.IdA), tm.stringTerm(a.IdB), YT, XT)
	//@ assert lib.Abs(msg3Data) == tm.gamma(msg3T)
	
	//@ labelCtx.IsPublishableMonotonic(s4, s5, YT)
	//@ labelCtx.IsPublishableMonotonic(s4, s5, XT)
	//@ labelCtx.IsMsgTupleCreate(s5, msg3T, label.Public())
	// the following assert stmt is necessary:
	//@ assert labelCtx.IsSignKey(s5, a.SkAT, p.principalId(a.IdA), DhKey)
	// the following assertion is necessary:
	//@ assert usageCtx.SignPredMsg3(s5, msg3T, xT, yT)
	signedMsg3, err := a.llib.Sign(msg3Data, a.SkA /*@, msg3T, a.SkAT, p.principalId(a.IdA) @*/)
	if err != nil {
		return err /*@, xT, yT @*/
	}

	// send msg3
	//@ ghost signedMsg3T := tm.sign(msg3T, a.SkAT)
	err = a.llib.Send(a.IdA, a.IdB, signedMsg3 /*@, signedMsg3T @*/)
	if err == nil {
		PrintInitiatorSuccess(sharedSecret)
	}

	//@ s6 := a.llib.Snapshot()
	//@ s0.isSuffixTransitive(s5, s6)
	//@ a.llib.ApplyMonotonicity()
	a.Version = 2
	//@ s5.eventOccursMonotonic(s6, a.IdA, finishIEv)
	//@ fold a.Mem(xT, yT)

	//@ a.proveSecurityProperties(xT, yT)
	
	return err /*@, xT, yT @*/
}
