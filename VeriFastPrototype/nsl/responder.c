#include "responder.h"
#include <stdlib.h>
#include <string.h>
//@ #include "bytes.gh"
//@ #include "labeling.gh"
#include "messages.h"
//@ #include "nsl_pke_pred.gh"
//@ #include "pattern.gh"
//@ #include "security_properties.gh"
//@ #include "subset_helpers.gh"
//@ #include "term.gh"


/*@
predicate NaNonce(Trace snap, int idA, int idB, char *na, Term naT) =
    chars(na, NonceLength, ?abs_na) &*& malloc_block(na, NonceLength) &*&
        gamma(naT) == abs_na &*&
        (containsCorruptId(getCorruptIds(snap), cons(idA, cons(idB, nil))) || isLabeled(naT, snap, Readers(cons(idA, cons(idB, nil))), pkePred));

predicate NbNonce(Trace snap, int idA, int idB, char *nb, Term nbT) =
    chars(nb, NonceLength, ?abs_nb) &*& malloc_block(nb, NonceLength) &*&
        gamma(nbT) == abs_nb &*&
        isLabeled(nbT, snap, Readers(cons(idA, cons(idB, nil))), pkePred) == true;

predicate Mem(struct B* b, int version) =
    malloc_block_B(b) &*&
    b->labeledLib |-> ?labeledLib &*& LabeledLibMem(labeledLib, ?snap, ?idB, pkePred) &*&
    b->version |-> version &*& 0 <= version &*&
    b->idB |-> idB &*&
    b->pkB |-> ?pkB &*& 
    b->pkB_len |-> ?pkB_len &*& chars(pkB, pkB_len, ?abs_pkB) &*& malloc_block(pkB, pkB_len) &*&
    b->skB |-> ?skB &*&
    b->skB_len |-> ?skB_len &*&
    chars(skB, skB_len, ?abs_skB) &*& malloc_block(skB, skB_len) &*&
    b->idA |-> ?idA &*&
    b->pkA |-> ?pkA &*&
    b->pkA_len |-> ?pkA_len &*&
    b->skBT |-> ?skBT &*&
    b->skAT |-> ?skAT &*&
    abs_skB == gamma(skBT) &*&
    isSecretKey(snap, idB, skBT, 1, pkePred) == true &*&
    (1 <= version ?
        chars(pkA, pkA_len, ?abs_pkA) &*& malloc_block(pkA, pkA_len) &*&
        abs_pkA == gamma(publicKey(skAT)) &*&
        isPublicKey(snap, idA, publicKey(skAT), skAT, 1, pkePred) == true : true) &*&
    (2 <= version ?
        NaNonce(snap, idA, idB, ?na, ?naT) &*&
        NbNonce(snap, idA, idB, ?nb, ?nbT) &*&
        eventOccurs(snap, idB, newEvent(FINISHR, FinishRParams(idA, idB, naT, nbT))) == true &*&
        (3 <= version ?
            Secrecy(naT, snap, cons(idA, cons(idB, nil)), pkePred) == true &*& 
            Secrecy(nbT, snap, cons(idA, cons(idB, nil)), pkePred) == true &*&
            InjectiveAgreement(snap, idB, idA, FINISHR, FinishRParams(idA, idB, naT, nbT), FINISHI, FinishIParams(idA, idB, naT, nbT), cons(idA, cons(idB, nil))) : true)
        : true);
@*/

struct B *initB(struct IoLib *io_lib, struct TraceManager *tm, int initiator, int responder)
//@ requires IoLibMem(io_lib) &*& TraceManagerMem(tm, responder, ?snap0, pkePred);
//@ ensures  result != 0 ? Mem(result, 0) : emp;
{
    struct B* b = malloc(sizeof(struct B));
    if(b == 0) {
        abort();
    }
    //@ getPkeCtxt();
    b->labeledLib = createLabeledLib(io_lib, tm, responder);
    if(b->labeledLib == 0) {
        abort();
    }
    b->version = 0;
    b->idB = responder;
    b->idA = initiator;

    // generate keypair
    //@ close exists(Readers(cons(responder, nil)));
    struct keypair *keys = labeledGeneratePkeKey(b->labeledLib);
    if (keys == 0) {
        abort();
    }
    char *skB = keys->sk;
    b->skB = skB;
    b->skB_len = keys->sk_len;
    b->pkB = keys->pk;
    b->pkB_len = keys->pk_len;
    free(keys);
    //@ assert chars(skB, _, ?abs_sk);
    //@ b->skBT = nonce(abs_sk, Readers(cons(responder, nil)));

    //@ close Mem(b, 0);
    return b;
}

void responderNonInjectiveAgreement(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, pkePred) &*&
        NaNonce(snap, ?idA, ?idB, ?na, ?naT) &*&
        NbNonce(snap, idA, idB, ?nb, ?nbT) &*&
        eventOccurs(snap, idB, newEvent(FINISHR, FinishRParams(idA, idB, naT, nbT))) == true; @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        NaNonce(snap, idA, idB, na, naT) &*&
        NbNonce(snap, idA, idB, nb, nbT) &*&
        NonInjectiveAgreement(snap, idB, idA, FINISHR, FinishRParams(idA, idB, naT, nbT), FINISHI, FinishIParams(idA, idB, naT, nbT), cons(idA, cons(idB, nil))) == true; @*/
{
    //@ ParameterizedEvent ev = newEvent(FINISHR, FinishRParams(idA, idB, naT, nbT));
    //@ close exists(idB);
    //@ close exists(ev);
    //@ getPkeCtxt();
    labeledEventOccursImpliesEventInv(lib);
    //@ assert exists<Trace>(?finishRWitness);
    /*@
    if (!eventOccurs(finishRWitness, idA, newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT)))) {
        getCorruptIdsMonotonic(finishRWitness, snap);
        subset_intersection_helper(getCorruptIds(finishRWitness), getCorruptIds(snap), cons(idA, cons(idB, nil)));
    }     
    @*/
    //@ leakPkeCtxt();
}

void responderInjectiveAgreement(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, pkePred) &*&
        NaNonce(snap, ?idA, ?idB, ?na, ?naT) &*&
        NbNonce(snap, idA, idB, ?nb, ?nbT) &*&
        eventOccurs(snap, idB, newEvent(FINISHR, FinishRParams(idA, idB, naT, nbT))) == true; @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        NaNonce(snap, idA, idB, na, naT) &*&
        NbNonce(snap, idA, idB, nb, nbT) &*&
        InjectiveAgreement(snap, idB, idA, FINISHR, FinishRParams(idA, idB, naT, nbT), FINISHI, FinishIParams(idA, idB, naT, nbT), cons(idA, cons(idB, nil))); @*/
{
    responderNonInjectiveAgreement(lib);
    //@ close exists(idB);
    //@ list<int> bothIds = cons(idA, cons(idB, nil));
    //@ ParameterizedEvent finishREv = newEvent(FINISHR, FinishRParams(idA, idB, naT, nbT));
    //@ close exists(finishREv);
    //@ getPkeCtxt();
    labeledUniqueEventIsUnique(lib);
    //@ assert EventIsUnique(snap, idB, finishREv);
    //@ close InjectiveAgreement(snap, idB, idA, FINISHR, FinishRParams(idA, idB, naT, nbT), FINISHI, FinishIParams(idA, idB, naT, nbT), bothIds);
    //@ Trace finishRWitness = getEventTrace(snap, idB, finishREv);
    /*@
    if (containsCorruptId(getCorruptIds(finishRWitness), bothIds)) {
        leak EventIsUnique(snap, idB, finishREv);
    }
    @*/
    //@ leakPkeCtxt();
}

void responderProveSecurityProperties(struct B* b)
//@ requires Mem(b, 2);
//@ ensures  Mem(b, 3);
{
    //@ open Mem(b, 2);
    struct LabeledLib *lib = b->labeledLib;

    responderInjectiveAgreement(lib);

    //@ open NaNonce(?snap, ?idA, ?idB, ?na, ?naT);
    //@ list<int> bothIds = cons(idA, cons(idB, nil));
    //@ Label both_label = Readers(bothIds);
    //@ close exists(naT);
    //@ close exists(bothIds);
    //@ getPkeCtxt();
    labeledSecrecyLemma(lib);
    //@ close NaNonce(snap, idA, idB, na, naT);

    //@ open NbNonce(snap, idA, idB, ?nb, ?nbT);
    //@ close exists(nbT);
    //@ close exists(bothIds);
    labeledSecrecyLemma(lib);
    //@ close NbNonce(snap, idA, idB, nb, nbT);

    b->version = 3;
    //@ close Mem(b, 3);
    //@ leakPkeCtxt();
}

/*@
lemma triple<int, int, Term> getEventOccursFinishIWitness(Trace snap, int idB, Term nbT)
    requires eventOccursFinishI(snap, idB, nbT) == true;
    ensures  eventOccurs(snap, triple_fst(result), newEvent(FINISHI, FinishIParams(triple_snd(result), idB, triple_thrd(result), nbT))) == true;
{
    switch(snap) {
        case root(root_terms):
        case makeEvent(t0, p, e):
            switch(e) {
                case newEvent(type, params):
                    bool found = false;
                    triple<int, int, Term> res;
                    switch (params) {
                        case InitiateParams(a, b, na):
                        case RespondParams(a, b, na, nb):
                        case FinishIParams(a, b, na, nb):
                            if (type == FINISHI && b == idB && nb == nbT) {
                                found = true;
                                res = triple(p, a, na);
                                assert eventOccurs(snap, p, newEvent(FINISHI, params)) == true;
                                assert eventOccurs(snap, p, newEvent(FINISHI, FinishIParams(a, idB, na, nbT))) == true;
                            }
                        case FinishRParams(a, b, na, nb):
                    }
                    if (!found) {
                        res = getEventOccursFinishIWitness(t0, idB, nbT);
                    }
                    return res;
            }
        case makeCorrupt(t0, id):
            return getEventOccursFinishIWitness(t0, idB, nbT);
        case makeMessage(t0, to, from, term):
            return getEventOccursFinishIWitness(t0, idB, nbT);
        case makeDropMessage(t0, to, from, term):
            return getEventOccursFinishIWitness(t0, idB, nbT);
        case makeNonce(t0, term):
            return getEventOccursFinishIWitness(t0, idB, nbT);
        case makePublic(t0, term):
            return getEventOccursFinishIWitness(t0, idB, nbT);
    }
}
@*/

bool runB(struct B* b)
//@ requires Mem(b, 1);
//@ ensures  result ? Mem(b, 3) : emp;
{
    unsigned int msg1Data_len = 0;
    unsigned int ciphertext1_len = 0;
    unsigned int msg2Data_len = 0;
    unsigned int ciphertext2_len = 0;
    unsigned int msg3Data_len = 0;
    unsigned int ciphertext3_len = 0;

    //@ open Mem(b, 1);
    struct LabeledLib *lib = b->labeledLib;
    //@ assert LabeledLibMem(lib, ?snap0, ?idB, pkePred) &*& b->skBT |-> ?skBT &*& b->skAT |-> ?skAT;
    //@ int idA = b->idA;

    char *ciphertext1 = labeledReceive(lib, b->idA, b->idB, &ciphertext1_len);
    //@ assert LabeledLibMem(lib, ?snap1, idB, pkePred);
    if (ciphertext1 == 0){
		abort();
	}

    // apply monotonicity snap0 -> snap1:
    //@ getPkeCtxt();
    //@ isSecretKeyMonotonic(snap0, snap1, idB, skBT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap0, snap1, idA, skAT, 1, pkePred);

    /*@ assert exists(?ciphertext1T) &*&
        chars(ciphertext1, ?ciphertext1Size, ?abs_ciphertext1) &*&
        gamma(ciphertext1T) == abs_ciphertext1; @*/
    //@ leak exists(ciphertext1T);
    //@ close exists(skBT);
    //@ close exists(ciphertext1T);
    
    char *skB = b->skB;
    //@ assert chars(skB, _, ?abs_sk);
    //@ close exists(idB);
    char *msg1Data = labeledDec(lib, ciphertext1, ciphertext1_len, skB, b->skB_len, &msg1Data_len);
    free(ciphertext1);
    if (msg1Data == 0){
		abort();
	}
    //@ assert chars(msg1Data, _, ?abs_msg1);
    struct Msg1 *msg1 = unmarshalMsg1(msg1Data, msg1Data_len);
    free(msg1Data);
    if (msg1 == 0){
		abort();
	}

    // check idA:
    if (msg1->idA != b->idA){
        abort();
    }

    char *na = msg1->Na;
    //@ assert chars(na, NonceLength, ?abs_na);
    //@ Term naT = PatternPropertyMsg1(oneTerm(abs_na), integer(idA), skBT, ciphertext1T);
    free(msg1);

    //@ Term msg1T = tuple3(integer(1), naT, integer(idA));

    /*@ assert [_]is_forall_t<Term>(?quantifiedExp1) &*&
            quantifiedExp1((msgIsDecrypted)(snap1, ciphertext1T, skBT, idB, pkePred)) == true; @*/
    //@ forall_t_elim(quantifiedExp1, (msgIsDecrypted)(snap1, ciphertext1T, skBT, idB, pkePred), msg1T);
    //@ assert wasDecrypted(snap1, msg1T, skBT, idB, pkePred) == true;
    // we no longer need the quantifier and thus leak the corresponding resource:
    //@ leak [_]is_forall_t(quantifiedExp1);

    //@ assert chars(skB, _, ?abs_skB);
    // the following assertion is needed:
    //@ assert decryptB(abs_skB, encryptB(publicKeyB(abs_skB), abs_msg1)) == abs_msg1; 

    // the following 2 assertions seems to be needed:
    //@ assert abs_msg1 == tuple3B(integerB(1), abs_na, integerB(idA));
    //@ assert getSecondB(abs_msg1) == abs_na;

    //@ Label msg1Label = isPublishable(snap1, msg1T, pkePred) ? Public : Readers(cons(idB, nil));
    //@ isMsgTupleThreeResolve(snap1, integer(1), naT, integer(idA), msg1Label, pkePred);
    //@ close exists(naT);
    //@ close exists(msg1Label != Public);
    labeledNonceOccursImpliesRandInvConditional(lib);
    //@ Label both_label = Readers(cons(idA, cons(idB, nil)));
    /*@
    if (msg1Label == Public) {
        isMsgTransitive(snap1, naT, Public, both_label, pkePred);
    }
    @*/

    // facts after receiving msg1:
    //@ assert isMsg(snap1, naT, both_label, pkePred) == true;
    //@ assert isPublishable(snap1, naT, pkePred) || nonceOccurs(snap1, naT, both_label);

    // create nonce nb
    //@ list<int> eventTypes = cons(RESPOND, cons(FINISHR, nil));
    //@ close exists(eventTypes);
    //@ close exists(both_label);
    char *nb = labeledCreateNonce(lib);
    //@ assert LabeledLibMem(lib, ?snap2, idB, pkePred);
    if(nb == 0) {
        abort();
    }
    //@ assert chars(nb, NonceLength, ?abs_nb);
    //@ Term nbT = nonce(abs_nb, both_label);

    // apply monotonicity snap1 -> snap2:
    //@ isSecretKeyMonotonic(snap1, snap2, idB, skBT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap1, snap2, idA, skAT, 1, pkePred);
    /*@
    if (msg1Label == Public) {
        isPublishableMonotonic(snap1, snap2, naT, pkePred);
    } else {
        nonceOccursMonotonic(snap1, snap2, naT, both_label);
    }
    @*/

    //@ ParameterizedEvent respond = newEvent(RESPOND, RespondParams(idA, idB, naT, nbT)); 
    //@ close exists(respond);
    //@ open eventUniquePointer(eventTypes, nbT);
    //@ close event_pred(idB, respond, snap2);
    labeledTriggerEvent(lib);
    //@ assert LabeledLibMem(lib, ?snap3, idB, pkePred);

    // apply monotonicity snap2 -> snap3:
    //@ isSecretKeyMonotonic(snap2, snap3, idB, skBT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap2, snap3, idA, skAT, 1, pkePred);
    //@ nonceOccursMonotonic(snap2, snap3, nbT, both_label);
    /*@
    if (msg1Label == Public) {
        isPublishableMonotonic(snap2, snap3, naT, pkePred);
        isMsgTransitive(snap3, naT, Public, Readers(cons(idA, nil)), pkePred);
    } else {
        nonceOccursMonotonic(snap2, snap3, naT, both_label);
    }
    @*/

    struct Msg2 *msg2 = malloc(sizeof(struct Msg2));
	if (msg2 == 0) {
        abort();
    }
	msg2->Na = na;
    msg2->Nb = nb;
	msg2->idB = b->idB;
	char *msg2Data = marshalMsg2(msg2, &msg2Data_len);
    free(msg2);
    if (msg2Data == 0) {
        abort();
    }
    //@ assert chars(msg2Data, ?msg2Size, ?abs_msg2);

    //@ Term msg2T = tuple4(integer(2), naT, nbT, integer(idB));
    //@ Term pkAT = publicKey(b->skAT);
    //@ close exists(pkAT);
    //@ close exists(msg2T);
    //@ char *pkA = b->pkA;
    //@ unsigned int pkA_len = b->pkA_len;
    //@ open chars(pkA, pkA_len, ?abs_pkA);
    //@ close chars(pkA, pkA_len, abs_pkA);
    //@ Label justALabel = Readers(cons(idA, nil));
    //@ isMsgTupleFourCreate(snap3, integer(2), naT, nbT, integer(idB), justALabel, pkePred);
    //@ assert canEncrypt(snap3, msg2T, pkAT, pkePred) == true;
    char *ciphertext2 = labeledEnc(lib, msg2Data, msg2Data_len, b->pkA, b->pkA_len, &ciphertext2_len);
    //@ leak exists(msg2T);
    //@ leak exists(pkAT);
    free(msg2Data);
    if (ciphertext2 == 0) {
        abort();
    }

    //@ Term ciphertext2T = encrypt(pkAT, msg2T);
    //@ close exists(ciphertext2T);
    bool success = labeledSend(lib, b->idB, b->idA, ciphertext2, ciphertext2_len);
    //@ assert LabeledLibMem(lib, ?snap4, idB, pkePred);
    //@ leak exists(ciphertext2T);
    free(ciphertext2);
    if (!success){
		abort();
	}

    // apply monotonicity snap3 -> snap4:
    //@ isSecretKeyMonotonic(snap3, snap4, idB, skBT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap3, snap4, idA, skAT, 1, pkePred);
    //@ nonceOccursMonotonic(snap3, snap4, nbT, both_label);
    //@ eventOccursMonotonic(snap3, snap4, idB, respond);
    /*@
    if (msg1Label == Public) {
        isPublishableMonotonic(snap3, snap4, naT, pkePred);
    } else {
        nonceOccursMonotonic(snap3, snap4, naT, both_label);
    }
    @*/

    char *ciphertext3 = labeledReceive(lib, b->idA, b->idB, &ciphertext3_len);
    //@ assert LabeledLibMem(lib, ?snap5, idB, pkePred);
    if (ciphertext3 == 0){
		abort();
	}

    // apply monotonicity snap4 -> snap5:
    //@ isSecretKeyMonotonic(snap4, snap5, idB, skBT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap4, snap5, idA, skAT, 1, pkePred);
    //@ nonceOccursMonotonic(snap4, snap5, nbT, both_label);
    //@ eventOccursMonotonic(snap4, snap5, idB, respond);
    /*@
    if (msg1Label == Public) {
        isPublishableMonotonic(snap4, snap5, naT, pkePred);
    } else {
        nonceOccursMonotonic(snap4, snap5, naT, both_label);
    }
    @*/

    /*@ assert exists(?ciphertext3T) &*&
        chars(ciphertext3, ?ciphertext3Size, ?abs_ciphertext3) &*&
        gamma(ciphertext3T) == abs_ciphertext3; @*/
    //@ close exists(skBT);
    //@ open chars(ciphertext3, ciphertext3Size, abs_ciphertext3);
    //@ close chars(ciphertext3, ciphertext3Size, abs_ciphertext3);
    //@ close exists(idB);
    char *msg3Data = labeledDec(lib, ciphertext3, ciphertext3_len, skB, b->skB_len, &msg3Data_len);
    free(ciphertext3);
    if (msg3Data == 0){
		abort();
	}
    //@ assert chars(msg3Data, _, ?abs_msg3);
    struct Msg3 *msg3 = unmarshalMsg3(msg3Data, msg3Data_len);
    free(msg3Data);
    if (msg3 == 0){
		abort();
	}

    // check nb:
    if(memcmp(msg3->Nb, nb, NonceLength) != 0){
        abort();
    }

    //@ PatternPropertyMsg3(nbT, skBT, ciphertext3T);
    free(msg3->Nb);
    free(msg3);

    //@ Term msg3T = tuple2(integer(3), nbT);
    
    /*@ assert [_]is_forall_t<Term>(?quantifiedExp3) &*&
            quantifiedExp3((msgIsDecrypted)(snap5, ciphertext3T, skBT, idB, pkePred)) == true; @*/
    //@ forall_t_elim(quantifiedExp3, (msgIsDecrypted)(snap5, ciphertext3T, skBT, idB, pkePred), msg3T);
    //@ assert wasDecrypted(snap5, msg3T, skBT, idB, pkePred) == true;
    // we no longer need the quantifier and thus leak the corresponding resource:
    //@ leak [_]is_forall_t(quantifiedExp3);

    //@ Label msg3Label;
    //@ bool nbTIsPublishable = false;
    //@ int principalW;
    //@ int idAW;
    //@ Term naTW;
    /*@
    if (isPublishable(snap5, msg3T, pkePred)) {
        msg3Label = Public;
        isMsgTupleTwoResolve(snap5, integer(3), nbT, Public, pkePred);
    } else {
        msg3Label = Readers(cons(idB, nil));
        // assert eventOccursFinishI(snap5, idB, nbT) == true;

        // FinishI event must have occurred based on pke_pred, which in turn implies that the 
        // respond event has occurred.
        // By uniqueness of the respond event, we know that the respond events
        // from the current program state and pke_pred must be the same one:

        triple<int, int, Term> witnesses = getEventOccursFinishIWitness(snap5, idB, nbT);
        principalW = triple_fst(witnesses);
        idAW = triple_snd(witnesses);
        naTW = triple_thrd(witnesses);

        if (isPublishable(snap5, nbT, pkePred)) {
            publishableImpliesCorruption(snap5, nbT, both_label, cons(idA, cons(idB, nil)), pkePred);
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
            
            nbTIsPublishable = true;
            // we continue below...
        }
    }
    @*/

    //@ close exists(principalW);
    //@ ParameterizedEvent ev = newEvent(FINISHI, FinishIParams(idAW, idB, naTW, nbT));
    //@ close exists(ev);
    //@ close exists(nbTIsPublishable);
    labeledEventOccursImpliesEventInvConditional(lib);
    /*@
    if (nbTIsPublishable) {
        // we've now learnt the event invariant for FinishI and can thus deduce that:
        // assert principalW == idAW;
        if (containsCorruptId(getCorruptIds(snap5), cons(idAW, nil))) {
            // this is a contradiction because we know that b.IdA has not been corrupted, otherwise nbT would be publishable:
            assert false;
        }
        // use uniqueness below to learn that naT == naTW;
    }
    @*/
    //@ close exists(nbTIsPublishable);
    //@ close Event1(idB, respond);
    //@ close Event2(idB, newEvent(RESPOND, RespondParams(idAW, idB, naTW, nbT)));
    labeledUniqueEventsAreUniqueGhostArgsConditional(lib);

	// facts after receiving msg3:
	//@ bool corruptionOccurred = containsCorruptId(getCorruptIds(snap5), cons(idA, cons(idB, nil)));
	/*@
    if (!corruptionOccurred) {
		assert eventOccurs(snap5, idA, newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT))) == true;
	}
	@*/

    //@ ParameterizedEvent finishR = newEvent(FINISHR, FinishRParams(idA, idB, naT, nbT)); 
    //@ close exists(finishR);
    //@ open eventUniquePointer(cons(FINISHR, nil), nbT);
    //@ close event_pred(idB, finishR, snap5);
    labeledTriggerEvent(lib);
    //@ open eventUniquePointer(nil, nbT);
    //@ assert LabeledLibMem(lib, ?snap6, idB, pkePred);

    // apply monotonicity snap5 -> snap6:
    //@ isSecretKeyMonotonic(snap5, snap6, idB, skBT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap5, snap6, idA, skAT, 1, pkePred);
    //@ nonceOccursMonotonic(snap5, snap6, nbT, both_label);

    /*@
    if (corruptionOccurred) {
        getCorruptIdsMonotonic(snap5, snap6);
        containsCorruptIdMonotonic2(getCorruptIds(snap5), getCorruptIds(snap6), cons(idA, cons(idB, nil)));
    } else {
        nonceOccursMonotonic(snap5, snap6, naT, both_label);
    }
    @*/

    b->version = 2;

    print_hex("B has successfully finished the protocol run\nB.na", na, NonceLength);
    print_hex("B.nb", nb, NonceLength);

    //@ close NaNonce(snap6, idA, idB, na, naT);
    //@ close NbNonce(snap6, idA, idB, nb, nbT);
    //@ leakPkeCtxt();
    //@ close Mem(b, 2);

    responderProveSecurityProperties(b);

    return true;
}
