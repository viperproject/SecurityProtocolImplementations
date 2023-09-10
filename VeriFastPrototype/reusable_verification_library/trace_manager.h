#ifndef TRACE_MANAGER
#define TRACE_MANAGER

//@ #include "attacker.gh"
#include "concurrent_datastructure.h"
//@ #include "labeling.gh"
//@ #include "security_properties.gh"


#define optiontype option<int>

// Trace Manager struct that contains the concurrent datastructure
struct TraceManager {
    int noOfClients;
    struct ConcurrentDataStructure *cds;
};

// Allocates `noOfClients` many trace manager instances that are handed to each 
// session to manipulate the global trace via the concurrent data structure.
struct TraceManager *create_trace_managers(int noOfClients);
/*@ requires exists<TermList>(?root_terms) &*&
        exists<PkePred>(?pkePred) &*&
        0 < noOfClients &*& noOfClients * sizeof(struct TraceManager) < UINTPTR_MAX &*&
        publicInv(root_terms, root(root_terms), pkePred) == true;  @*/ 
/*@ ensures  exists<SnapIdList>(?owners) &*&
        exists<SnapList>(?snapshots) &*&
        length(owners) == noOfClients &*&
        length(snapshots) == noOfClients &*&
        TraceManagerMemAll(result, owners, snapshots, pkePred) &*&
        malloc_block_chars((void *)result, noOfClients * sizeof(struct TraceManager)); @*/

/*@ 
// Wraps the memory related predicates for TraceManagers
predicate TraceManagerMem(struct TraceManager *tm, SnapId owner, Trace snapshot, PkePred pkePred) =
    tm->noOfClients |-> ?noOfClients &*&
    tm->cds |-> ?cds &*&
    ConcurrentDataStructurePerClientMem(cds, owner, snapshot, pkePred) &*&
    struct_TraceManager_padding(tm);

predicate TraceManagerMemAll(struct TraceManager *tms, SnapIdList owners, SnapList snapshots, PkePred pkePred) =
    switch (owners) {
        case nil: return true;
        case cons(owner, remOwners):
            return switch (snapshots) {
                case nil: return false;
                case cons(snapshot, remSnapshots):
                    return TraceManagerMem(tms, owner, snapshot, pkePred) &*&
                        TraceManagerMemAll(tms + 1, remOwners, remSnapshots, pkePred);
            };
    };
@*/

void *tmSync(struct TraceManager *tm);
//@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred);
/*@ ensures  TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        isSuffix(snap0, snap1) == true; @*/
  
// Adds an event to the trace
void *logEvent(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred) &*& 
        exists<ParameterizedEvent>(?e) &*& event_pred(owner, e, snap0) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        snap1 == makeEvent(_, owner, e) &*&
        PkeCtxt(pkePred); @*/

void *logSend(struct TraceManager *tm, int to);
/*@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred) &*& 
        exists<Term>(?msg) &*&
        messageInv(to, owner, msg, snap0, pkePred) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        exists<Term>(msg) &*&
        isSuffix(snap0, snap1) == true &*&
        snap1 == makeMessage(_, to, owner, msg) &*&
        PkeCtxt(pkePred); @*/

void *logNonce(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred) &*&
        NonceUniqueResource(?nonce) &*& isNonce(nonce) == true &*&
        canFlow(snap0, getNonceLabel(nonce), Readers(cons(owner, nil))) == true; @*/
/*@ ensures TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        snap1 == makeNonce(_, nonce); @*/

void msgOccursImpliesMsgInv(struct TraceManager *tm, int idSender, int idReceiver);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<Term>(?msg) &*&
        msgOccurs(msg, idReceiver, idSender, snap) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, snap, pkePred) &*&
        messageInv(idReceiver, idSender, msg, snap, pkePred) == true &*&
        PkeCtxt(pkePred); @*/

// The lemmas in this module prove the secrecy lemma. This is an important 
// security property that states that either the attacker does not know a
// non-public and valid term or one of the readers of this term must have been corrupted.
void attackerOnlyKnowsPublishableValuesWithSnap(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Trace>(?snap) &*& exists<Term>(?term) &*&
        attackerKnows(snap, term) == true &*& isSuffix(snap, snapshot) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*& isPublishable(snap, term, pkePred) == true &*&
        PkeCtxt(pkePred); @*/

void secrecyLemma(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<Term>(?term) &*& exists<list<int> >(?readers) &*&
        (isLabeled(term, snap, Readers(readers), pkePred) || containsCorruptId(getCorruptIds(snap), readers)) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        Secrecy(term, snap, readers, pkePred) == true &*&
        exists<optiontype>(?result) &*&
        switch (result) {
            case some(y): return mem(y, getCorruptIds(snap)) && mem(y, readers);
            case none: return !attackerKnows(snap, term);
        } &*& PkeCtxt(pkePred); @*/

void nonceOccursImpliesRandInvConditional(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<Term>(?nonce) &*& exists<bool>(?cond) &*&
        cond ? onlyNonceOccurs(snap, nonce) == true : true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        cond ? isNonce(nonce) == true : true &*&
        PkeCtxt(pkePred); @*/

void eventOccursImpliesEventInvConditional(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<int>(?principal) &*&
        exists<ParameterizedEvent >(?e) &*&
        exists<bool>(?cond) &*&
        (cond ? eventOccurs(snap, principal, e) == true : true) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*&
        (cond ?
                event_pure_pred_consistent(e, principal, snap) == true &*&
                event_pure_pred_consistent(e, principal, result) == true &*&
                result == getEventTrace(snap, principal, e) : true) &*&
        PkeCtxt(pkePred); @*/

/*@
// we introduce the following 4 indirections such that VeriFast does not
// pick the wrong resources when trying to instantiate existentials:
predicate Event1(int principal1, ParameterizedEvent e1) =
    exists(pair(principal1, e1));

predicate Event2(int principal2, ParameterizedEvent e2) =
    exists(pair(principal2, e2));

predicate Event1At(int principal1, ParameterizedEvent e1, int idx1) =
    exists(triple(principal1, e1, idx1));

predicate Event2At(int principal2, ParameterizedEvent e2, int idx2) =
    exists(triple(principal2, e2, idx2));
@*/

void uniqueEventsAreUniqueAtConditional(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        Event1At(?principal1, ?e1, ?idx1) &*& Event2At(?principal2, ?e2, ?idx2) &*&
        eventOccursAt(snap, principal1, e1, idx1) == true &*&
        isUnique(getEventType(e1)) == true &*&
        exists(?cond) &*&
        (cond ?
            eventOccursAt(snap, principal2, e2, idx2) == true &*&
            eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
            getEventType(e1) == getEventType(e2) : true); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        (cond ? principal1 == principal2 &*& e1 == e2 &*& idx1 == idx2 : true); @*/

void uniqueEventsAreUniqueConditional(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        Event1(?principal1, ?e1) &*& Event2(?principal2, ?e2) &*&
        eventOccurs(snap, principal1, e1) == true &*&
        isUnique(getEventType(e1)) == true &*&
        exists(?cond) &*&
        (cond ?
            eventOccurs(snap, principal2, e2) == true &*&
            eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
            getEventType(e1) == getEventType(e2) : true); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        (cond ? principal1 == principal2 &*& e1 == e2 : true); @*/

void uniqueEventsAreUnique(struct TraceManager *tm);
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        Event1(?principal1, ?e1) &*& Event2(?principal2, ?e2) &*&
        eventOccurs(snap, principal1, e1) == true &*&
        eventOccurs(snap, principal2, e2) == true &*&
        eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
        isUnique(getEventType(e1)) == true &*&
        getEventType(e1) == getEventType(e2); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        principal1 == principal2 &*& e1 == e2; @*/

#endif
