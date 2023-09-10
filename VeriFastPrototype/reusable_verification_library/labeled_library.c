#include "labeled_library.h"
#include <stdlib.h>


struct LabeledLib {
    struct IoLib *io_lib;
    struct TraceManager *tm;
    int owner;
};

/*@
predicate LabeledLibMem(struct LabeledLib *lib, Trace snap, int owner, PkePred pkePred) =
    malloc_block_LabeledLib(lib) &*&
    lib->io_lib |-> ?io_lib &*&
    IoLibMem(io_lib) &*&
    lib->tm |-> ?tm &*&
    lib->owner |-> owner &*&
    TraceManagerMem(tm, owner, snap, pkePred) &*&
    PkeCtxt(pkePred);
@*/

struct LabeledLib *createLabeledLib(struct IoLib *io_lib, struct TraceManager *tm, int owner)
/*@ requires IoLibMem(io_lib) &*& TraceManagerMem(tm, owner, ?snap, ?pkePred) &*&
        PkeCtxt(pkePred); @*/
//@ ensures  result != 0 ? LabeledLibMem(result, snap, owner, pkePred) : emp;
{
    struct LabeledLib* a = malloc(sizeof(struct LabeledLib));
    if(a == 0) {
        abort();
    } else {
        a->io_lib = io_lib;
        a->tm = tm;
        a->owner = owner;
        //@ close LabeledLibMem(a, snap, owner, pkePred);
    }
    return a;
}

void labeledTriggerEvent(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        exists<ParameterizedEvent>(?event) &*& event_pred(owner, event, snap0) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        eventOccurs(snap1, owner, event) == true &*&
        PkeCtxt(pkePred); @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    logEvent(tm);
    //@ assert TraceManagerMem(tm, owner, ?snap1, pkePred);
    //@ close LabeledLibMem(lib, snap1, owner, pkePred);
}


// ----- I/O -----
bool labeledSend(struct LabeledLib *lib, int idSender, int idReceiver, char *msg, unsigned int msg_len)
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        owner == idSender &*&
        exists<Term>(?msgT) &*& [?f]chars(msg, msg_len, ?msgBytes) &*& gamma(msgT) == msgBytes &*&
        messageInv(idReceiver, idSender, msgT, snap0, pkePred) == true; @*/
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        [f]chars(msg, msg_len, msgBytes) &*&
        (result ? snap1 == makeMessage(_, idReceiver, idSender, msgT): emp); @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    //@ assert exists<Term>(msgT); 
    logSend(tm, idReceiver);
    //@ assert TraceManagerMem(tm, owner, ?snap1, pkePred);
    //@ close exists<Trace>(snap1);
    bool result = io_send(lib->io_lib, idSender, idReceiver, msg, msg_len);
    //@ close LabeledLibMem(lib, snap1, owner, pkePred);
    return result;
}

char *labeledReceive(struct LabeledLib *lib, int idSender, int idReceiver, unsigned int *msg_len)
//@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*& *msg_len |-> _;
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*& *msg_len |-> ?res_len &*&
        isSuffix(snap0, snap1) == true &*&
        result != 0 ?
            (exists<Term>(?msgT) &*& chars(result, res_len, ?msgBytes) &*&
                malloc_block_chars(result, res_len) &*&
                gamma(msgT) == msgBytes &*&
                messageInv(idReceiver, idSender, msgT, snap1, pkePred) == true &*&
                msgOccurs(msgT, idReceiver, idSender, snap1) == true) :
            emp; @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    tmSync(tm);
    //@ assert TraceManagerMem(tm, owner, ?snap1, pkePred);
    //@ close exists<Trace>(snap1);
    char *msg = io_receive(lib->io_lib, idSender, idReceiver, msg_len);
    if (msg != 0) {
        //@ assert exists<Term>(?msgT);
        msgOccursImpliesMsgInv(tm, idSender, idReceiver);
        //@ close exists(msgT);
    }
    //@ close LabeledLibMem(lib, snap1, owner, pkePred);
    return msg;
}


// ----- crypto -----
char *labeledCreateNonce(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        exists<EventTypes>(?eventTypes) &*& exists<Label>(?l) &*& distinct(eventTypes) == true &*&
        canFlow(snap0, l, Readers(cons(owner, nil))) == true; @*/
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        result != 0 ?
            (chars(result, NonceLength, ?bytes_list) &*& malloc_block(result, NonceLength) &*& 
                eventUniquePointer(eventTypes, nonce(bytes_list, l)) &*&
                bytes_list == gamma(nonce(bytes_list, l)) &*&
                snap1 == makeNonce(_, nonce(bytes_list, l))) :
            emp; @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    char *nonce = createNonce();
    if (nonce != 0) {
        logNonce(tm);
    } else {
        //@ isSuffixReflexive(snap0);
    }
    //@ close LabeledLibMem(lib, ?snap1, owner, pkePred);
    return nonce;
}

struct keypair *labeledGeneratePkeKey(struct LabeledLib *lib)
//@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred);
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        result != 0 ?
            (result->pk |-> ?pk &*& pk != 0 &*&
                result->pk_len |-> ?pk_len &*&
                result->sk |-> ?sk &*& sk != 0 &*&
                result->sk_len |-> ?sk_len &*&
                chars(pk, pk_len, ?abs_pk) &*& malloc_block_chars(pk, pk_len) &*&
                chars(sk, sk_len, ?abs_sk) &*& malloc_block_chars(sk, sk_len) &*&
                abs_pk == publicKeyB(abs_sk) &*&
                abs_sk == gamma(nonce(abs_sk, Readers(cons(owner, nil)))) &*&
                snap1 == makeNonce(_, nonce(abs_sk, Readers(cons(owner, nil)))) &*&
                malloc_block_keypair(result)) :
            emp; @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    //@ close exists<Label>(Readers(cons(owner, nil)));
    struct keypair *res = generatePkeKey();
    if (res != 0) {
        logNonce(tm);
    } else {
        //@ isSuffixReflexive(snap0);
    }
    //@ close LabeledLibMem(lib, ?snap1, owner, pkePred);
    return res;
}

char *labeledEnc(struct LabeledLib *lib, char *msg, unsigned int msg_len, const char *pk, unsigned int pk_len, unsigned int *ciphertext_len)
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        [?f]chars(msg, msg_len, ?abs_msg) &*& [?g]chars(pk, pk_len, ?abs_pk) &*& *ciphertext_len |-> _ &*&
        exists<Term>(?msgT) &*& exists<Term>(?pkT) &*&
        abs_msg == gamma(msgT) &*& abs_pk == gamma(pkT) &*&
        (canEncrypt(snap0, msgT, pkT, pkePred) || isPublishable(snap0, msgT, pkePred) && isPublishable(snap0, pkT, pkePred)); @*/
/*@ ensures  LabeledLibMem(lib, snap0, owner, pkePred) &*&
        [f]chars(msg, msg_len, abs_msg) &*& [g]chars(pk, pk_len, abs_pk) &*& *ciphertext_len |-> ?ciphertextSize &*&
        exists<Term>(msgT) &*& exists<Term>(pkT) &*&
        result != 0 ?
            (chars(result, ciphertextSize, ?abs_ciphertext) &*&
                malloc_block_chars(result, ciphertextSize) &*&
                abs_ciphertext == encryptB(abs_pk, abs_msg) &*&
                isPublishable(snap0, encrypt(pkT, msgT), pkePred) == true) :
            emp; @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    char *ciphertext = enc(msg, msg_len, pk, pk_len, ciphertext_len);
    //@ ciphertextIsPublishable(snap0, msgT, pkT, pkePred);
    //@ close LabeledLibMem(lib, snap0, owner, pkePred);
    return ciphertext;
}

char *labeledDec(struct LabeledLib *lib, char *ciphertext, unsigned int ciphertext_len, const char *sk, unsigned int sk_len, unsigned int *plaintext_len)
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        [?f]chars(ciphertext, ciphertext_len, ?abs_ciphertext) &*& [?g]chars(sk, sk_len, ?abs_sk) &*& *plaintext_len |-> _ &*&
        exists<Term>(?ciphertextT) &*& exists<Term>(?skT) &*&
        abs_ciphertext == gamma(ciphertextT) &*& abs_sk == gamma(skT) &*&
        exists<int>(?skOwner) &*&
        canDecrypt(snap0, ciphertextT, skT, skOwner, pkePred) == true; @*/
/*@ ensures  LabeledLibMem(lib, snap0, owner, pkePred) &*&
        [f]chars(ciphertext, ciphertext_len, abs_ciphertext) &*& [g]chars(sk, sk_len, abs_sk) &*& *plaintext_len |-> ?msgSize &*&
        result != 0 ?
            (chars(result, msgSize, ?abs_msg) &*&
                malloc_block_chars(result, msgSize) &*&
                abs_ciphertext == encryptB(publicKeyB(abs_sk), abs_msg) &*&
                [_]is_forall_t<Term>(?quantifiedExp) &*&
                quantifiedExp((msgIsDecrypted)(snap0, ciphertextT, skT, skOwner, pkePred)) == true) :
            emp; @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    char *plaintext = dec(ciphertext, ciphertext_len, sk, sk_len, plaintext_len);
    if (plaintext != 0) {
        //@ Term pkT = publicKey(skT);

        // follows the proof of `cg_level_ccs_max` in the VeriFast example `crytogram_levels.c`.
        //@ get_forall_t<Term>();
        //@ assert [_]is_forall_t<Term>(?quantifiedExp);
        //@ fixpoint(Term, bool) p = (msgIsDecrypted)(snap0, ciphertextT, skT, skOwner, pkePred);
        /*@
        if (!quantifiedExp(p)) {
            Term msgT = not_forall_t(quantifiedExp, p);
            decryptSatisfiesInvariant(snap0, msgT, skT, skOwner, pkePred);
            assert false; // we have reached a contradiction -- as expected
        }
        @*/
    }
    //@ close LabeledLibMem(lib, snap0, owner, pkePred);
    return plaintext;
}

void labeledSecrecyLemma(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        exists<Term>(?term) &*& exists<list<int> >(?readers) &*&
        (isLabeled(term, snap0, Readers(readers), pkePred) || containsCorruptId(getCorruptIds(snap0), readers)) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap0, owner, pkePred) &*&
        Secrecy(term, snap0, readers, pkePred) == true &*&
        exists<optiontype>(?result) &*&
        switch (result) {
            case some(y): return mem(y, getCorruptIds(snap0)) && mem(y, readers);
            case none: return !attackerKnows(snap0, term);
        } &*& PkeCtxt(pkePred); @*/
{
    //@ open LabeledLibMem(lib, snap0, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    secrecyLemma(tm);
    //@ close LabeledLibMem(lib, snap0, owner, pkePred);
}

void labeledNonceOccursImpliesRandInvConditional(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<Term>(?nonce) &*& exists<bool>(?cond) &*&
        cond ? onlyNonceOccurs(snap, nonce) == true : true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        cond ? isNonce(nonce) == true : true &*&
        PkeCtxt(pkePred); @*/
{
    //@ open LabeledLibMem(lib, snap, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    nonceOccursImpliesRandInvConditional(tm);
    //@ close LabeledLibMem(lib, snap, owner, pkePred);
}

void labeledNonceOccursImpliesRandInv(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<Term>(?nonce) &*&
        onlyNonceOccurs(snap, nonce) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        isNonce(nonce) == true &*&
        PkeCtxt(pkePred); @*/
{
    //@ close exists(true);
    labeledNonceOccursImpliesRandInvConditional(lib);
}

void labeledEventOccursImpliesEventInvConditional(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<int>(?principal) &*&
        exists<ParameterizedEvent >(?e) &*&
        exists<bool>(?cond) &*&
        (cond ? eventOccurs(snap, principal, e) == true : true) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*&
        (cond ?
                event_pure_pred_consistent(e, principal, snap) == true &*&
                event_pure_pred_consistent(e, principal, result) == true &*&
                result == getEventTrace(snap, principal, e) : true) &*&
        PkeCtxt(pkePred); @*/
{
    //@ open LabeledLibMem(lib, snap, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    eventOccursImpliesEventInvConditional(tm);
    //@ close LabeledLibMem(lib, snap, owner, pkePred);
}

void labeledEventOccursImpliesEventInv(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<int>(?principal) &*&
        exists<ParameterizedEvent >(?e) &*&
        eventOccurs(snap, principal, e) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*&
        event_pure_pred_consistent(e, principal, snap) == true &*&
        event_pure_pred_consistent(e, principal, result) == true &*&
        result == getEventTrace(snap, principal, e) &*&
        PkeCtxt(pkePred); @*/
{
    //@ close exists(true);
    labeledEventOccursImpliesEventInvConditional(lib);
}

void labeledUniqueEventIsUnique(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<int>(?principal) &*&
        exists<ParameterizedEvent >(?e) &*&
        eventOccurs(snap, principal, e) == true &*&
        isUnique(getEventType(e)) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        EventIsUnique(snap, principal, e) &*&
        PkeCtxt(pkePred); @*/
{
    // follows the proof of `cg_level_ccs_max` in the VeriFast example `crytogram_levels.c`.
    //@ get_forall_t<QuantifiedTriple>();
    //@ assert [_]is_forall_t<QuantifiedTriple>(?quantifiedExp);
    //@ int event_type = getEventType(e);
    //@ EventParams params = getEventParams(e);
    //@ fixpoint(QuantifiedTriple, bool) p = (matchingEventDoesNotOccur)(snap, principal, e);
    
    // Since `uniqueEventsAreUniqueGhostArgsConditional` and `uniqueEventsAreUniqueAtConditional`
    // are a non-ghost function, we assign "meaningful" values to the following variables in the 
    // then branch and do not care about their values when we take the else branch.
    // As illustrated by the second if statement, this preparation is enough to derive a
    // contradiction in the then branch.
    //@ int principal2;
    //@ ParameterizedEvent event2;
    //@ int idx2;
    /*@
    if (!quantifiedExp(p)) {
        QuantifiedTriple quantifier = not_forall_t(quantifiedExp, p);
        assert !p(quantifier);
        switch (quantifier) {
            case triple(p2, e2, i):
                principal2 = p2;
                event2 = e2;
                idx2 = i;
        }
        eventOccursAtLemma(snap, principal2, event2, idx2);
    }
    @*/
    //@ open LabeledLibMem(lib, snap, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    //@ close Event1(principal, e);
    //@ close Event2(principal2, event2);
    //@ close exists(!quantifiedExp(p));
    uniqueEventsAreUniqueConditional(tm);
    //@ int idx1 = eventOccursAtTimeLemma(snap, principal, e);
    //@ close Event1At(principal, e, idx1);
    //@ close Event2At(principal2, event2, idx2);
    //@ close exists(!quantifiedExp(p));
    uniqueEventsAreUniqueAtConditional(tm);
    /*@
    if (!quantifiedExp(p)) {
        assert false; // we have reached a contradiction -- as expected
    }
    @*/
    //@ close LabeledLibMem(lib, snap, owner, pkePred);
    labeledEventOccursImpliesEventInv(lib);
    //@ close EventIsUnique(snap, principal, e);
}

void labeledUniqueEventsAreUniqueGhostArgsConditional(struct LabeledLib *lib)
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        Event1(?principal1, ?e1) &*& Event2(?principal2, ?e2) &*&
        eventOccurs(snap, principal1, e1) == true &*&
        isUnique(getEventType(e1)) == true &*&
        exists(?cond) &*&
        (cond ?
            eventOccurs(snap, principal2, e2) == true &*&
            eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
            getEventType(e1) == getEventType(e2) : true); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        (cond ? principal1 == principal2 &*& e1 == e2 : true); @*/
{
    //@ open LabeledLibMem(lib, snap, owner, pkePred);
    struct TraceManager *tm = lib->tm;
    uniqueEventsAreUniqueConditional(tm);
    //@ close LabeledLibMem(lib, snap, owner, pkePred);
}

/*@
lemma void applyMonotonicity<t>(trace<EventParams> t1, trace<EventParams> t2, Term t, Label l1, Label l2, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& PkeCtxt(pkePred);
    ensures (isValid(t1, t, pkePred) ? isValid(t2, t, pkePred) == true : emp) &*& 
        (isPublishable(t1, t, pkePred) ? isPublishable(t2, t, pkePred) == true : emp) &*&
        (canFlow(t1, l1, l2) ? canFlow(t2, l1, l2) == true : emp) &*&
        PkeCtxt(pkePred);
{
    if (isValid(t1, t, pkePred)) {
        isValidMonotonic(t1, t2, t, pkePred);
    }
    if (isPublishable(t1, t, pkePred)) {
        isPublishableMonotonic(t1, t2, t, pkePred);
    }
    if (canFlow(t1, l1, l2)) {
        canFlowMonotonic(t1, t2, l1, l2);
    }
}
@*/
