#ifndef LABELED_LIBRARY
#define LABELED_LIBRARY

#include <stdbool.h>
//@ #include "quantifiers.gh"
//@ #include "bytes.gh"
#include "crypto.h"
#include "io.h"
//@ #include "labeling.gh"
//@ #include "trace_entry.gh"
//@ #include "trace_entry_helpers.gh"
#include "trace_manager.h"

struct LabeledLib;


//@ predicate LabeledLibMem(struct LabeledLib *lib, Trace snap, int owner, PkePred pkePred);

struct LabeledLib *createLabeledLib(struct IoLib *io_lib, struct TraceManager *tm, int owner);
/*@ requires IoLibMem(io_lib) &*& TraceManagerMem(tm, owner, ?snap, ?pkePred) &*&
        PkeCtxt(pkePred); @*/
//@ ensures  result != 0 ? LabeledLibMem(result, snap, owner, pkePred) : emp;

void labeledTriggerEvent(struct LabeledLib *lib);
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        exists<ParameterizedEvent>(?event) &*& event_pred(owner, event, snap0) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        eventOccurs(snap1, owner, event) == true &*&
        PkeCtxt(pkePred); @*/


// ----- I/O -----
bool labeledSend(struct LabeledLib *lib, int idSender, int idReceiver, char *msg, unsigned int msg_len);
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        owner == idSender &*&
        exists<Term>(?msgT) &*& [?f]chars(msg, msg_len, ?msgBytes) &*& gamma(msgT) == msgBytes &*&
        messageInv(idReceiver, idSender, msgT, snap0, pkePred) == true; @*/
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        [f]chars(msg, msg_len, msgBytes) &*&
        (result ? snap1 == makeMessage(_, idReceiver, idSender, msgT): emp); @*/

char *labeledReceive(struct LabeledLib *lib, int idSender, int idReceiver, unsigned int *msg_len);
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


// ----- crypto -----
char *labeledCreateNonce(struct LabeledLib *lib);
/*@ requires LabeledLibMem(lib, ?snap0, ?owner, ?pkePred) &*&
        exists<EventTypes>(?eventTypes) &*& exists<Label>(?l) &*& distinct(eventTypes) == true &*&
        canFlow(snap0, l, Readers(cons(owner, nil))) == true; @*/
/*@ ensures  LabeledLibMem(lib, ?snap1, owner, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        result != 0 ?
            (chars(result, NonceLength, ?bytes_list) &*& malloc_block_chars(result, NonceLength) &*& 
                eventUniquePointer(eventTypes, nonce(bytes_list, l)) &*&
                bytes_list == gamma(nonce(bytes_list, l)) &*&
                snap1 == makeNonce(_, nonce(bytes_list, l))) :
            emp; @*/

struct keypair *labeledGeneratePkeKey(struct LabeledLib *lib);
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

char *labeledEnc(struct LabeledLib *lib, char *msg, unsigned int msg_len, const char *pk, unsigned int pk_len, unsigned int *ciphertext_len);
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

// encoding of the quantifier in `labeledDec`'s postcondition. I.e., we partially
// apply the following fixpoint:
/*@
fixpoint bool msgIsDecrypted(Trace snap, Term ciphertextT, Term skT, int skOwner, PkePred pkePred, Term msgT) {
    return ciphertextT == encrypt(publicKey(skT), msgT) ?
        wasDecrypted(snap, msgT, skT, skOwner, pkePred) : true;
}
@*/

char *labeledDec(struct LabeledLib *lib, char *ciphertext, unsigned int ciphertext_len, const char *sk, unsigned int sk_len, unsigned int *plaintext_len);
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

void labeledSecrecyLemma(struct LabeledLib *lib);
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

void labeledNonceOccursImpliesRandInvConditional(struct LabeledLib *lib);
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<Term>(?nonce) &*& exists<bool>(?cond) &*&
        cond ? onlyNonceOccurs(snap, nonce) == true : true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        cond ? isNonce(nonce) == true : true &*&
        PkeCtxt(pkePred); @*/

void labeledNonceOccursImpliesRandInv(struct LabeledLib *lib);
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<Term>(?nonce) &*&
        onlyNonceOccurs(snap, nonce) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        isNonce(nonce) == true &*&
        PkeCtxt(pkePred); @*/

void labeledEventOccursImpliesEventInvConditional(struct LabeledLib *lib);
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

void labeledEventOccursImpliesEventInv(struct LabeledLib *lib);
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

void labeledUniqueEventIsUnique(struct LabeledLib *lib);
/*@ requires LabeledLibMem(lib, ?snap, ?owner, ?pkePred) &*&
        exists<int>(?principal) &*&
        exists<ParameterizedEvent >(?e) &*&
        eventOccurs(snap, principal, e) == true &*&
        isUnique(getEventType(e)) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  LabeledLibMem(lib, snap, owner, pkePred) &*&
        EventIsUnique(snap, principal, e) &*&
        PkeCtxt(pkePred); @*/

void labeledUniqueEventsAreUniqueGhostArgsConditional(struct LabeledLib *lib);
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

/*@
lemma void applyMonotonicity<t>(trace<EventParams> t1, trace<EventParams> t2, Term t, Label l1, Label l2, PkePred pkePred);
    requires isSuffix(t1, t2) == true &*& PkeCtxt(pkePred);
    ensures (isValid(t1, t, pkePred) ? isValid(t2, t, pkePred) == true : emp) &*& 
        (isPublishable(t1, t, pkePred) ? isPublishable(t2, t, pkePred) == true : emp) &*&
        (canFlow(t1, l1, l2) ? canFlow(t2, l1, l2) == true : emp) &*&
        PkeCtxt(pkePred);
@*/

#endif
