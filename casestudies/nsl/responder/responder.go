package responder

//@ import arb "github.com/viperproject/ReusableProtocolVerificationLibrary/arbitrary"
//@ import ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
import ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
import lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
//@ import "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
//@ import . "github.com/viperproject/ProtocolVerificationCaseStudies/nsl/common"
import . "github.com/viperproject/ProtocolVerificationCaseStudies/nsl/common/library"
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
pred (b *B) Mem(naT, nbT tm.Term) {
	acc(b) &&
	0 <= b.Version && b.Version <= 3 &&
	// full permission if not yet initialized, otherwise only 1/2:
	acc(lib.Mem(b.PkB), 1/2) && (b.Version == 0 ==> acc(lib.Mem(b.PkB), 1/2)) &&
	lib.Mem(b.SkB) &&
	lib.Abs(b.SkB) == tm.gamma(b.SkBT) &&
	lib.Abs(b.PkB) == tm.gamma(tm.createPk(b.SkBT)) &&
	b.llib.Mem() &&
	b.llib.Ctx() == GetNslContext() &&
	b.llib.LabelCtx() == GetNslLabeling() &&
	b.llib.Owner() == p.principalId(b.IdB) &&
	GetNslLabeling().IsSecretKey(b.llib.Snapshot(), p.principalId(b.IdB), b.SkBT, labeling.KeyTypePke(), NslKey) &&
	(b.Version >= 1 ==>
		acc(lib.Mem(b.PkA), 1/2) &&
		lib.Abs(b.PkA) == tm.gamma(tm.createPk(b.SkAT)) &&
		GetNslLabeling().IsPublicKey(b.llib.Snapshot(), p.principalId(b.IdA), tm.createPk(b.SkAT), b.SkAT, labeling.KeyTypePke(), NslKey)) &&
	(b.Version >= 2 ==>
		GetNslLabeling().IsLabeled(b.llib.Snapshot(), nbT, label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })) &&
		b.llib.Snapshot().eventOccurs(b.IdB, ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, naT, nbT })) &&
		(	// either a or b have been corrupted ...
			tr.containsCorruptId(b.llib.Snapshot().getCorruptIds(), set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) ||
			// ... or naT is labeled to only be readable by a and b
            // this is stronger than `isMsg` as it excludes the possibility of restricting a
            // less secret value. This is necessary to invoke the secrecy lemma
			GetNslLabeling().IsLabeled(b.llib.Snapshot(), naT, label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })))) &&
	(b.Version >= 3 ==>
		b.llib.Secrecy(naT, set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) &&
		b.llib.Secrecy(nbT, set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }) &&
		b.llib.InjectiveAgreement(b.IdB, b.IdA, ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, naT, nbT }), ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, naT, nbT }), set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) }))
}

ghost
requires acc(b.Mem(naT, nbT), _)
pure func (b *B) Vers(naT, nbT tm.Term) uint {
	return unfolding acc(b.Mem(naT, nbT), _) in b.Version
}
@*/

//@ requires acc(l.Mem(), 1/8)
//@ requires acc(com.LibMem(), 1/8) && com != nil && isComparable(com)
//@ requires manager.Mem(GetNslContext(), p.principalId(responder))
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures  err == nil ==> b.Mem(defaultTerm, defaultTerm) && unfolding b.Mem(defaultTerm, defaultTerm) in b.Version == 0 &&
//@				b.IdA == initiator &&
//@				b.IdB == responder &&
//@				manager == b.llib.Manager() &&
//@				// the following conjuncts are necessary such that monotonicity can be applied by the scheduler 
//@				// to the generated secret & public keys:
//@				old(manager.Snapshot(GetNslContext(), p.principalId(responder))).isSuffix(b.llib.Snapshot()) &&
//@				(old(manager.ImmutableState(GetNslContext(), p.principalId(responder))) == unfolding b.llib.Mem() in b.llib.manager.ImmutableState(GetNslContext(), p.principalId(responder)))
// TODO make manager ghost
// TODO remove `defaultTerm` as parameter and simply create it in the body
func InitB(l *lib.LibraryState, com ll.Communication, initiator, responder p.Principal /*@, manager *tman.TraceManager, defaultTerm tm.Term @*/) (b *B, err error) {
	//@ ctx := GetNslContext()
	llib := ll.NewLabeledLibrary(l, com /*@, manager, ctx, p.NewPrincipalId(responder) @*/)
	pk, sk, err /*@, skT @*/ := llib.GeneratePkeKey(/*@ NslKey @*/)
	if err != nil {
		return nil, err
	}
	b = &B{responder, pk, sk, initiator, 0, nil, llib /*@, defaultTerm, skT @*/}
	//@ fold b.Mem(defaultTerm, defaultTerm)
	return b, nil
}

//@ requires b.Mem(defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm) == 1
//@ ensures  err == nil ==> b.Mem(naT, nbT) && b.Vers(naT, nbT) == 3
func RunB(b *B /*@, defaultTerm tm.Term @*/) (err error /*@, ghost naT tm.Term, ghost nbT tm.Term @*/) {
	//@ unfold b.Mem(defaultTerm, defaultTerm)
	//@ s0 := b.llib.Snapshot()
	//@ ctx := GetNslContext()
	//@ labelCtx := GetNslLabeling()
	//@ usageCtx := NslUsageContext{}

	// receive msg1
	ciphertext1, err /*@, ciphertext1T @*/ := b.llib.Receive(b.IdA, b.IdB)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s1 := b.llib.Snapshot()
	//@ b.llib.ApplyMonotonicity()
	// decrypt msg1
	msg1Data, err := b.llib.Dec(ciphertext1, b.SkB /*@, ciphertext1T, b.SkBT, p.principalId(b.IdB) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decompose msg1Data
	msg1, err := UnmarshalMsg1(msg1Data)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// check validity of msg1:
	if b.IdA != msg1.IdA {
		return lib.NewError("idA does not match") /*@, naT, nbT @*/
	}
	
	/*@
	naT = PatternPropertyMsg1(tm.oneTerm(lib.Abs(msg1.Na)), tm.stringTerm(b.IdA), b.SkBT, ciphertext1T)
	// the following assert stmt is necessary to derive the assertion right after it:
	assert tm.decryptB(tm.encryptB(tm.tuple3B(tm.integer32B(1), lib.Abs(msg1.Na), tm.gamma(tm.stringTerm(b.IdA))), tm.createPkB(lib.Abs(b.SkB))), lib.Abs(b.SkB)) == tm.tuple3B(tm.integer32B(1), lib.Abs(msg1.Na), tm.gamma(tm.stringTerm(b.IdA)))
	assert lib.Abs(msg1.Na) == tm.gamma(naT)
	msg1T := tm.tuple3(tm.integer32(1), naT, tm.stringTerm(b.IdA))
	
	bothLabel := label.Readers(set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })
	ghost var msg1Label label.SecrecyLabel
	ghost if labelCtx.IsPublishable(s1, msg1T) {
		msg1Label = label.Public()
	} else {
		msg1Label = label.Readers(set[p.Id]{ p.principalId(b.IdB) })
	}

	labelCtx.IsMsgTupleResolve(s1, msg1T, msg1Label)

	ghost if !msg1Label.IsPublic() {
		assert s1.nonceOccurs(naT, bothLabel, u.Nonce(NslNonce))
		// since msg1 is not publishable, we know now that `PkePred` must hold
		nonceAtSnapshot := b.llib.NonceOccursImpliesRandInv(naT)
	} else {
		labelCtx.IsMsgTransitive(s1, naT, label.Public(), bothLabel)
	}
	@*/

	/*@
	labelCtx.CanFlowReflexive(s1, bothLabel)
	// facts after receiving msg1:
	assert labelCtx.IsMsg(s1, naT, bothLabel)
	assert labelCtx.IsPublishable(s1, naT) || s1.nonceOccurs(naT, bothLabel, u.Nonce(NslNonce))
	@*/

	// create nb
	nb, err := b.llib.CreateNonce(/*@ bothLabel, NslNonce, set[ev.EventType]{ Respond, FinishR } @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s2 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s1, s2)
	//@ nbT = tm.random(lib.Abs(nb), bothLabel, u.Nonce(NslNonce))
	// the following assert stmt is needed such that monotonicity will trigger for nbT:
	//@ assert s2.OnlyNonceOccurs(nbT)

	/*@
	respEv := ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, naT, nbT })
	fold ctx.eventInv(b.IdB, respEv, s2)
	b.llib.TriggerEvent(respEv)
	s3 := b.llib.Snapshot()
	s0.isSuffixTransitive(s2, s3)
	s1.isSuffixTransitive(s2, s3)
	b.llib.ApplyMonotonicity()
	@*/

	// build & encrypt msg2
	msg2 := &Msg2{msg1.Na, nb, b.IdB}
	msg2Data := MarshalMsg2(msg2)
	//@ msg2T := tm.tuple4(tm.integer32(2), naT, nbT, tm.stringTerm(b.IdB))
	//@ assert lib.Abs(msg2Data) == tm.gamma(msg2T)
	//@ b.llib.ApplyMonotonicity()
	//@ justALabel := label.Readers(set[p.Id]{ p.principalId(b.IdA) })
	//@ labelCtx.CanFlowReflexive(s3, bothLabel)
	//@ assert labelCtx == b.llib.LabelCtx()
	//@ labelCtx.Restrict(s3, naT, bothLabel, justALabel)
	//@ labelCtx.IsMsgTupleCreate(s3, msg2T, justALabel)
	ciphertext2, err := b.llib.Enc(msg2Data, b.PkA /*@, msg2T, tm.createPk(b.SkAT) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// send msg2
	//@ ciphertext2T := tm.encrypt(msg2T, tm.createPk(b.SkAT))
	err = b.llib.Send(b.IdB, b.IdA, ciphertext2 /*@, ciphertext2T @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s4 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s3, s4)
	// receive msg3
	ciphertext3, err /*@, ciphertext3T @*/ := b.llib.Receive(b.IdA, b.IdB)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	//@ s5 := b.llib.Snapshot()
	//@ s0.isSuffixTransitive(s4, s5)
	//@ b.llib.ApplyMonotonicity()
	// decrypt msg3
	// the following assert stmt is necessary to derive Dec's precondition:
	//@ assert labelCtx.IsPrivateDecKey(s5, p.principalId(b.IdB), b.SkBT, NslKey)
	msg3Data, err := b.llib.Dec(ciphertext3, b.SkB /*@, ciphertext3T, b.SkBT, p.principalId(b.IdB) @*/)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// decompose msg3Data
	msg3, err := UnmarshalMsg3(msg3Data)
	if err != nil {
		return err /*@, naT, nbT @*/
	}
	// check validity of msg3 (assuming no corruption, the equality of receivedNa and receivedIdA can be deduced (see below)):
	if !lib.Compare(nb, msg3.Nb) {
		return lib.NewError("nb does not match") /*@, naT, nbT @*/
	}

	/*@
	PatternPropertyMsg3(nbT, b.SkBT, ciphertext3T)
	msg3T := tm.tuple2(tm.integer32(3), nbT)
	// PatternPropertyMsg3 gives us uniqueness for ciphertext3T:
	assert ciphertext3T == tm.encrypt(msg3T, tm.createPk(b.SkBT))

	ghost var msg3Label label.SecrecyLabel
	ghost if labelCtx.IsPublishable(s5, msg3T) {
		msg3Label = label.Public()
	} else {
		msg3Label = label.Readers(set[p.Id]{ p.principalId(b.IdB) })
	}

	s3.isSuffixTransitive(s4, s5)
	s3.eventOccursMonotonic(s5, b.IdB, ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, naT, nbT }))
	ghost if (msg3Label.IsPublic()) {
		// corruption must have occurred because plaintext is publishable and contains nbT
		labelCtx.IsMsgTupleResolve(s5, msg3T, label.Public())
	} else {
		// ppred holds because message is not known to the attacker
		// assert usageCtx.ppred(s5, NslKey, msg3T, tm.createPk(b.SkBT), b.IdB)

		assert exists idA p.Principal, na tm.Term :: { s5.eventOccurs(idA, ev.NewEvent(FinishI, FinishIParams{ idA, b.IdB, na, nbT })) } s5.eventOccurs(idA, ev.NewEvent(FinishI, FinishIParams{ idA, b.IdB, na, nbT }))
		// get witness
		idAWitness := arb.GetArbPrincipal()
		naWitness := arb.GetArbTerm()
		assume s5.eventOccurs(idAWitness, ev.NewEvent(FinishI, FinishIParams{ idAWitness, b.IdB, naWitness, nbT }))
	
		// FinishI event must have occurred based on ppred, which in turn implies that the 
        // respond event has occurred.
        // By uniqueness of the respond event, we know that the respond events
        // from programStateB and ppred must be the same one:

		// get respond event via FinishI event:
		b.llib.EventOccursImpliesEventInv(idAWitness, ev.NewEvent(FinishI, FinishIParams{ idAWitness, b.IdB, naWitness, nbT }))
		respond1 := ev.NewEvent(Respond, RespondParams{ idAWitness, b.IdB, naWitness, nbT })
		if labelCtx.IsPublishable(s5, nbT) {
			// nbT being publishable means that either b.IdA or b.IdB have been corrupted because
			// nbT is only readable by them
			labelCtx.PublishableImpliesCorruption(s5, nbT, bothLabel)
		} else {
			// from the FinishI event, we learn that either idAWitness or b.IdB must have been corrupted or the
			// Respond event has occurred.
			// However, b.IdB cannot have been corrupted because nbT would otherwise be publishable and we would
			// not reach this branch.
			// Therefore, we distinguish two cases here:
			// (1) idAWitness has not been corrupted. Thus, Respond event has occurred and due to uniqueness of
			//		the Respond event, we know that idAWitness == b.IdA
			// (2) idAWitness has been corrupted. In this case, we can use the fact that we know the labeling of
			// 		nbT (because we have created the nonce) and nbT's labeling given by `pureEventInv`: Because
			//		the labeling is unique, idAWitness must be equal to b.IdA

			if tr.containsCorruptId(s5.getCorruptIds(), set[p.Id]{ p.principalId(idAWitness) }) {
				// assert idAWitness == b.IdA
				// this is a contradiction because we know that b.IdA has not been corrupted, otherwise nbT would be publishable:
				labelCtx.containsCorruptIdMonotonic(s5.getCorruptIds(), set[p.Id]{ p.principalId(b.IdA) }, set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })
				// assert false
			} else {
				// lift respond event from this program state to s5:
				respond2 := ev.NewEvent(Respond, RespondParams{ b.IdA, b.IdB, naT, nbT })
				b.llib.UniqueEventsAreUnique(b.IdB, b.IdB, respond1, respond2)
			}

			// assert idAWitness == b.IdA
			// assert naWitness == naT
			
			// we therefore know that the FinishI event with naT and nbT must have occurred:
			// assert s5.eventOccurs(b.IdA, ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, naT, nbT }))
		}
	}
	@*/

	/*@
	// facts after receiving msg3:
	corruptionOccurred := tr.containsCorruptId(s5.getCorruptIds(), set[p.Id]{ p.principalId(b.IdA), p.principalId(b.IdB) })
	ghost if !corruptionOccurred {
		assert s5.eventOccurs(b.IdA, ev.NewEvent(FinishI, FinishIParams{ b.IdA, b.IdB, naT, nbT }))
	}
	@*/

	/*@
	finishREv := ev.NewEvent(FinishR, FinishRParams{ b.IdA, b.IdB, naT, nbT })
	fold ctx.eventInv(b.IdB, finishREv, s5)
	b.llib.TriggerEvent(finishREv)
	s6 := b.llib.Snapshot()
	s0.isSuffixTransitive(s5, s6)
	b.llib.ApplyMonotonicity()
	@*/

	if err == nil {
		PrintResponderSuccess(msg1.Na, nb)
	}
	b.Version = 2
	//@ fold b.Mem(naT, nbT)

	//@ b.proveSecurityProperties(naT, nbT)

	return err /*@, naT, nbT @*/
}
