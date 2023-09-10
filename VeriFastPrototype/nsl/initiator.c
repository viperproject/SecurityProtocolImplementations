#include "initiator.h"
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
        isLabeled(naT, snap, Readers(cons(idA, cons(idB, nil))), pkePred) == true;

predicate NbNonce(Trace snap, int idA, int idB, char *nb, Term nbT) =
    chars(nb, NonceLength, ?abs_nb) &*& malloc_block(nb, NonceLength) &*&
        gamma(nbT) == abs_nb &*&
        (containsCorruptId(getCorruptIds(snap), cons(idA, cons(idB, nil))) || isLabeled(nbT, snap, Readers(cons(idA, cons(idB, nil))), pkePred));

predicate Mem(struct A* a, int version) =
    malloc_block_A(a) &*&
    a->labeledLib |-> ?labeledLib &*& LabeledLibMem(labeledLib, ?snap, ?idA, pkePred) &*&
    a->version |-> version &*& 0 <= version &*&
    a->idA |-> idA &*&
    a->pkA |-> ?pkA &*&
    a->pkA_len |-> ?pkA_len &*& chars(pkA, pkA_len, ?abs_pkA) &*& malloc_block(pkA, pkA_len) &*&
    a->skA |-> ?skA &*&
    a->skA_len |-> ?skA_len &*& chars(skA, skA_len, ?abs_skA) &*& malloc_block(skA, skA_len) &*&
    a->idB |-> ?idB &*&
    a->pkB |-> ?pkB &*&
    a->pkB_len |-> ?pkB_len &*&
    a->skAT |-> ?skAT &*&
    a->skBT |-> ?skBT &*&
    abs_skA == gamma(skAT) &*&
    isSecretKey(snap, idA, skAT, 1, pkePred) == true &*&
    (1 <= version ?
        chars(pkB, pkB_len, ?abs_pkB) &*& malloc_block(pkB, pkB_len) &*&
        abs_pkB == gamma(publicKey(skBT)) &*&
        isPublicKey(snap, idB, publicKey(skBT), skBT, 1, pkePred) == true : true) &*&
    (2 <= version ?
        NaNonce(snap, idA, idB, ?na, ?naT) &*&
        NbNonce(snap, idA, idB, ?nb, ?nbT) &*&
        eventOccurs(snap, idA, newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT))) == true &*&
        (3 <= version ?
            Secrecy(naT, snap, cons(idA, cons(idB, nil)), pkePred) == true &*& 
            Secrecy(nbT, snap, cons(idA, cons(idB, nil)), pkePred) == true &*&
            InjectiveAgreement(snap, idA, idB, FINISHI, FinishIParams(idA, idB, naT, nbT), RESPOND, RespondParams(idA, idB, naT, nbT), cons(idA, cons(idB, nil))) : true)
        : true);
@*/

struct A *initA(struct IoLib *io_lib, struct TraceManager *tm, int initiator, int responder)
//@ requires IoLibMem(io_lib) &*& TraceManagerMem(tm, initiator, ?snap0, pkePred);
//@ ensures  result != 0 ? Mem(result, 0) : emp;
{
    struct A* a = malloc(sizeof(struct A));
    if(a == 0) {
        abort();
    }
    //@ getPkeCtxt();
    a->labeledLib = createLabeledLib(io_lib, tm, initiator);
    if(a->labeledLib == 0) {
        abort();
    }
    a->version = 0;
    a->idA = initiator;
    a->idB = responder;

    // generate keypair
    //@ close exists(Readers(cons(initiator, nil)));
    struct keypair *keys = labeledGeneratePkeKey(a->labeledLib);
    if (keys == 0) {
        abort();
    }
    char *skA = keys->sk;
    a->skA = skA; 
    a->skA_len = keys->sk_len;
    a->pkA = keys->pk;
    a->pkA_len = keys->pk_len;
    free(keys);
    //@ assert chars(skA, _, ?abs_sk);
    //@ a->skAT = nonce(abs_sk, Readers(cons(initiator, nil)));

    //@ close Mem(a, 0);
    return a;
}

void initiatorNonInjectiveAgreement(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, pkePred) &*&
        NaNonce(snap, ?idA, ?idB, ?na, ?naT) &*&
        NbNonce(snap, idA, idB, ?nb, ?nbT) &*&
        eventOccurs(snap, idA, newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT))) == true; @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        NaNonce(snap, idA, idB, na, naT) &*&
        NbNonce(snap, idA, idB, nb, nbT) &*&
        NonInjectiveAgreement(snap, idA, idB, FINISHI, FinishIParams(idA, idB, naT, nbT), RESPOND, RespondParams(idA, idB, naT, nbT), cons(idA, cons(idB, nil))) == true; @*/
{
    //@ ParameterizedEvent ev = newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT));
    //@ close exists(idA);
    //@ close exists(ev);
    //@ getPkeCtxt();
    labeledEventOccursImpliesEventInv(lib);
    //@ assert exists<Trace>(?finishIWitness);
    /*@
    if (!eventOccurs(finishIWitness, idB, newEvent(RESPOND, RespondParams(idA, idB, naT, nbT)))) {
        getCorruptIdsMonotonic(finishIWitness, snap);
        subset_intersection_helper(getCorruptIds(finishIWitness), getCorruptIds(snap), cons(idA, cons(idB, nil)));
    }     
    @*/
    //@ leakPkeCtxt();
}

void initiatorInjectiveAgreement(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, pkePred) &*&
        NaNonce(snap, ?idA, ?idB, ?na, ?naT) &*&
        NbNonce(snap, idA, idB, ?nb, ?nbT) &*&
        eventOccurs(snap, idA, newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT))) == true; @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        NaNonce(snap, idA, idB, na, naT) &*&
        NbNonce(snap, idA, idB, nb, nbT) &*&
        InjectiveAgreement(snap, idA, idB, FINISHI, FinishIParams(idA, idB, naT, nbT), RESPOND, RespondParams(idA, idB, naT, nbT), cons(idA, cons(idB, nil))); @*/
{
    initiatorNonInjectiveAgreement(lib);
    //@ close exists(idA);
    //@ list<int> bothIds = cons(idA, cons(idB, nil));
    //@ ParameterizedEvent finishIEv = newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT));
    //@ close exists(finishIEv);
    //@ getPkeCtxt();
    labeledUniqueEventIsUnique(lib);
    //@ assert EventIsUnique(snap, idA, finishIEv);
    //@ close InjectiveAgreement(snap, idA, idB, FINISHI, FinishIParams(idA, idB, naT, nbT), RESPOND, RespondParams(idA, idB, naT, nbT), bothIds);
    //@ Trace finishIWitness = getEventTrace(snap, idA, finishIEv);
    /*@
    if (containsCorruptId(getCorruptIds(finishIWitness), bothIds)) {
        leak EventIsUnique(snap, idA, finishIEv);
    }
    @*/
    //@ leakPkeCtxt();
}

void initiatorProveSecurityProperties(struct A* a)
//@ requires Mem(a, 2);
//@ ensures  Mem(a, 3);
{
    //@ open Mem(a, 2);
    struct LabeledLib *lib = a->labeledLib;

    initiatorInjectiveAgreement(lib);

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

    a->version = 3;
    //@ close Mem(a, 3);
    //@ leakPkeCtxt();
}

bool runA(struct A* a)
//@ requires Mem(a, 1);
//@ ensures  result ? Mem(a, 3) : emp;
{
    unsigned int msg1Data_len = 0;
    unsigned int ciphertext1_len = 0;
    unsigned int msg2Data_len = 0;
    unsigned int ciphertext2_len = 0;
    unsigned int msg3Data_len = 0;
    unsigned int ciphertext3_len = 0;

    //@ open Mem(a, 1);
    struct LabeledLib *lib = a->labeledLib;
    //@ assert LabeledLibMem(lib, ?snap0, ?idA, pkePred);
    //@ int idB = a->idB;

    // create nonce na
    //@ Label both_label = Readers(cons(idA, cons(idB, nil)));
    //@ list<int> eventTypes = cons(INITIATE, cons(FINISHI, nil));
    //@ close exists(eventTypes);
    //@ close exists(both_label);
    char *na = labeledCreateNonce(lib);
    if(na == 0) {
        abort();
    }
    //@ assert chars(na, NonceLength, ?abs_na);
    //@ Term naT = nonce(abs_na, both_label);
    //@ assert LabeledLibMem(lib, ?snap1, idA, pkePred) &*& a->skAT |-> ?skAT &*& a->skBT |-> ?skBT;

    // apply monotonicity snap0 -> snap1:
    //@ getPkeCtxt();
    //@ isSecretKeyMonotonic(snap0, snap1, idA, skAT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap0, snap1, idB, skBT, 1, pkePred);
    
    //@ ParameterizedEvent initEv = newEvent(INITIATE, InitiateParams(idA, idB, naT));
    //@ close exists(initEv);
    //@ open eventUniquePointer(eventTypes, naT);
    //@ close event_pred(idA, initEv, snap1);
    labeledTriggerEvent(lib);
    //@ assert LabeledLibMem(lib, ?snap2, idA, pkePred);

    // apply monotonicity snap1 -> snap2:
    //@ isSecretKeyMonotonic(snap1, snap2, idA, skAT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap1, snap2, idB, skBT, 1, pkePred);
    //@ nonceOccursMonotonic(snap1, snap2, naT, both_label);

    struct Msg1 *msg1 = malloc(sizeof(struct Msg1));
	if (msg1 == 0) {
        abort();
    }
	msg1->Na = na;
	msg1->idA = a->idA;
	char *msg1Data = marshalMsg1(msg1, &msg1Data_len);
    free(msg1);
    if (msg1Data == 0) {
        abort();
    }
    //@ assert chars(msg1Data, _, ?abs_msg1);

    //@ Term msg1T = tuple3(integer(1), naT, integer(idA));
    //@ Term pkBT = publicKey(a->skBT);
    //@ close exists(pkBT);
    //@ close exists(msg1T);
    //@ assert abs_msg1 == gamma(msg1T);
    //@ char *pkB = a->pkB;
    //@ assert chars(pkB, _, ?abs_pk);
    //@ assert abs_pk == gamma(pkBT);
    //@ Label justBLabel = Readers(cons(idB, nil));
    //@ isMsgTupleThreeCreate(snap2, integer(1), naT, integer(idA), justBLabel, pkePred);
    //@ assert canEncrypt(snap2, msg1T, pkBT, pkePred) == true;
    char *ciphertext1 = labeledEnc(lib, msg1Data, msg1Data_len, a->pkB, a->pkB_len, &ciphertext1_len);
    //@ leak exists(msg1T);
    //@ leak exists(pkBT);
    free(msg1Data);
    if (ciphertext1 == 0) {
        abort();
    }

    //@ Term ciphertext1T = encrypt(pkBT, msg1T);
    //@ close exists(ciphertext1T);
    bool success = labeledSend(lib, a->idA, a->idB, ciphertext1, ciphertext1_len);
    //@ assert LabeledLibMem(lib, ?snap3, idA, pkePred);
    //@ leak exists(ciphertext1T);
    free(ciphertext1);
    if (!success){
		abort();
	}

    // apply monotonicity snap2 -> snap3:
    //@ isSecretKeyMonotonic(snap2, snap3, idA, skAT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap2, snap3, idB, skBT, 1, pkePred);
    //@ nonceOccursMonotonic(snap2, snap3, naT, both_label);

    char *ciphertext2 = labeledReceive(lib, a->idB, a->idA, &ciphertext2_len);
    //@ assert LabeledLibMem(lib, ?snap4, idA, pkePred);
    if (ciphertext2 == 0){
		abort();
	}

    // apply monotonicity snap3 -> snap4:
    //@ isSecretKeyMonotonic(snap3, snap4, idA, skAT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap3, snap4, idB, skBT, 1, pkePred);
    //@ nonceOccursMonotonic(snap3, snap4, naT, both_label);

    /*@ assert exists(?ciphertext2T) &*&
        chars(ciphertext2, ?ciphertext2Size, ?abs_ciphertext2) &*&
        gamma(ciphertext2T) == abs_ciphertext2; @*/
    //@ leak exists(ciphertext2T);
    //@ close exists(ciphertext2T);
    //@ close exists(skAT);
    
    char *skA = a->skA;
    //@ assert chars(skA, _, ?abs_sk);
    //@ close exists(idA);
    char *msg2Data = labeledDec(lib, ciphertext2, ciphertext2_len, skA, a->skA_len, &msg2Data_len);
    free(ciphertext2);
    if (msg2Data == 0){
		abort();
	}
    //@ assert chars(msg2Data, _, ?abs_msg2);
    struct Msg2 *msg2 = unmarshalMsg2(msg2Data, msg2Data_len);
    free(msg2Data);
    if (msg2 == 0){
		abort();
	}

    // check na and idB:
    if(memcmp(msg2->Na, na, NonceLength) != 0) {
        abort();
    }
    if (msg2->idB != a->idB) {
        abort();
    }

    char *nb = msg2->Nb;
    //@ assert chars(nb, NonceLength, ?abs_nb);
    //@ Term nbT = PatternPropertyMsg2(naT, oneTerm(abs_nb), integer(idB), skAT, ciphertext2T);
    free(msg2->Na);
    free(msg2);

    //@ Term msg2T = tuple4(integer(2), naT, nbT, integer(idB));

    /*@ assert [_]is_forall_t<Term>(?quantifiedExp) &*&
            quantifiedExp((msgIsDecrypted)(snap4, ciphertext2T, skAT, idA, pkePred)) == true; @*/
    //@ forall_t_elim(quantifiedExp, (msgIsDecrypted)(snap4, ciphertext2T, skAT, idA, pkePred), msg2T);
    //@ assert wasDecrypted(snap4, msg2T, skAT, idA, pkePred) == true;
    // we no longer need the quantifier and thus leak the corresponding resource:
    //@ leak [_]is_forall_t(quantifiedExp);

    //@ assert chars(skA, _, ?abs_skA);
    // the following assertion is needed:
    //@ assert decryptB(abs_skA, encryptB(publicKeyB(abs_skA), abs_msg2)) == abs_msg2; 

    // the following 2 assertions seems to be needed:
    //@ assert abs_msg2 == tuple4B(integerB(2), gamma(naT), abs_nb, integerB(idB));
    //@ assert getThirdB(abs_msg2) == abs_nb;

    //@ Label msg2Label = isPublishable(snap4, msg2T, pkePred) ? Public : Readers(cons(idA, nil));
    //@ isMsgTupleFourResolve(snap4, integer(2), naT, nbT, integer(idB), msg2Label, pkePred);
    //@ close exists(nbT);
    //@ close exists(msg2Label != Public);
    labeledNonceOccursImpliesRandInvConditional(lib);
    /*@
    if (msg2Label == Public) {
        isMsgTransitive(snap4, nbT, Public, both_label, pkePred);
        publishableImpliesCorruption(snap4, naT, both_label, cons(a->idA, cons(a->idB, nil)), pkePred);
        assert isPublishable(snap4, nbT, pkePred) == true; 
    }
    @*/

    // facts after receiving msg2:
    //@ bool corruptionOccured = containsCorruptId(getCorruptIds(snap4), cons(idA, cons(idB, nil)));
    /*@
    if (corruptionOccured) {
        assert isPublishable(snap4, nbT, pkePred) == true;
    } else {
       	assert nonceOccurs(snap4, nbT, both_label) == true;
        assert eventOccurs(snap4, idB, newEvent(RESPOND, RespondParams(idA, idB, naT, nbT))) == true;
    }
    @*/

    //@ ParameterizedEvent finishI = newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT)); 
    //@ close exists(finishI);
    //@ open eventUniquePointer(cons(FINISHI, nil), naT);
    //@ close event_pred(idA, finishI, snap4);
    labeledTriggerEvent(lib);
    //@ open eventUniquePointer(nil, naT);
    //@ assert LabeledLibMem(lib, ?snap5, idA, pkePred);

    // apply monotonicity snap4 -> snap5:
    //@ isSecretKeyMonotonic(snap4, snap5, idA, skAT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap4, snap5, idB, skBT, 1, pkePred);
    //@ nonceOccursMonotonic(snap4, snap5, naT, both_label);
    /*@
    if (corruptionOccured) {
        isPublishableMonotonic(snap4, snap5, nbT, pkePred);
    } else {
        nonceOccursMonotonic(snap4, snap5, nbT, both_label);
    }
    @*/

    /*@
    if (corruptionOccured) {
        isMsgTransitive(snap5, nbT, Public, justBLabel, pkePred);
    } else {
        isMsgTransitive(snap5, nbT, both_label, justBLabel, pkePred);
    }
    @*/

    struct Msg3 *msg3 = malloc(sizeof(struct Msg3));
    if (msg3 == 0) {
        abort();
    }
    msg3->Nb = nb;
    char *msg3Data = marshalMsg3(msg3, &msg3Data_len);
    free(msg3);
    if (msg3Data == 0) {
        abort();
    }
    //@ assert chars(msg3Data, _, ?abs_msg3);

    //@ Term msg3T = tuple2(integer(3), nbT);
    //@ close exists(pkBT);
    //@ close exists(msg3T);
    //@ isMsgTupleTwoCreate(snap5, integer(3), nbT, justBLabel, pkePred);
    //@ eventOccursImpliesEventOccursFinishI(snap5, idA, idB, naT, nbT);
    //@ assert canEncrypt(snap5, msg3T, pkBT, pkePred) == true;
    char *ciphertext3 = labeledEnc(lib, msg3Data, msg3Data_len, a->pkB, a->pkB_len, &ciphertext3_len);
    //@ leak exists(msg3T);
    //@ leak exists(pkBT);
    free(msg3Data);
    if (ciphertext3 == 0) {
        abort();
    }

    //@ Term ciphertext3T = encrypt(pkBT, msg3T);
    //@ close exists(ciphertext3T);
    success = labeledSend(lib, a->idA, a->idB, ciphertext3, ciphertext3_len);
    //@ assert LabeledLibMem(lib, ?snap6, idA, pkePred);
    //@ leak exists(ciphertext3T);
    free(ciphertext3);
    if (!success){
		abort();
	}

    // apply monotonicity snap5 -> snap6:
    //@ isSecretKeyMonotonic(snap5, snap6, idA, skAT, 1, pkePred);
    //@ isPublicKeyMonotonic(snap5, snap6, idB, skBT, 1, pkePred);
    //@ nonceOccursMonotonic(snap5, snap6, naT, both_label);
    //@ eventOccursMonotonic(snap5, snap6, idA, finishI);
    /*@
    if (corruptionOccured) {
        isPublishableMonotonic(snap5, snap6, nbT, pkePred);
    } else {
        nonceOccursMonotonic(snap5, snap6, nbT, both_label);
    }
    @*/

    a->version = 2;

    print_hex("A has successfully finished the protocol run\nA.na", na, NonceLength);
    print_hex("A.nb", nb, NonceLength);

    //@ close NaNonce(snap6, idA, idB, na, naT);
    /*@
    if (corruptionOccured) {
        isSuffixTransitive(snap4, snap5, snap6);
        getCorruptIdsMonotonic(snap4, snap6);
        subset_intersection_helper(getCorruptIds(snap4), getCorruptIds(snap6), cons(idA, cons(idB, nil)));
        assert containsCorruptId(getCorruptIds(snap6), cons(idA, cons(idB, nil))) == true;
    }
    @*/
    //@ close NbNonce(snap6, idA, idB, nb, nbT);
    //@ leakPkeCtxt();
    //@ close Mem(a, 2);

    initiatorProveSecurityProperties(a);

    return true;
}
