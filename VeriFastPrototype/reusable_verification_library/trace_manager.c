#include "trace_manager.h"
#include <stdlib.h>
//@ #include "event_lemmas.gh"
//@ #include "protocol_specific_event_lemma.gh"
//@ #include "trace_entry.gh"

#define IntList list<int>


void init_trace_managers(struct TraceManager *managers, struct ConcurrentDataStructure *cds, int noOfClients, int i)
/*@ requires exists<SnapIdList>(?snapshotIds) &*&
        exists<SnapList>(?snapshots) &*&
        0 <= i && i < noOfClients &*&
        noOfClients - i == length(snapshots) &*&
        noOfClients - i == length(snapshotIds) &*&
        chars((void *)(managers + i), (noOfClients - i) * sizeof(struct TraceManager), _) &*&
        ConcurrentDataStructureAllClientMem(cds, snapshotIds, snapshots, ?pkePred) &*&
        (uintptr_t)(managers + noOfClients) <= UINTPTR_MAX; @*/
/*@ ensures  exists(snapshotIds) &*&
        exists(snapshots) &*&
        TraceManagerMemAll(managers + i, snapshotIds, snapshots, pkePred); @*/
{
    //@ mul_mono_l(1, (noOfClients - i), sizeof(struct TraceManager));
    //@ chars_split((void *)(managers + i), sizeof(struct TraceManager));
    //@ close_struct(managers + i);
    //@ assert snapshotIds == cons(?snapshotId, ?remSnapshotIds);
    //@ assert snapshots == cons(?snapshot, ?remSnapshots);
    //@ mul_mono_l(0, i, sizeof(struct TraceManager));
    (managers + i)->noOfClients = noOfClients;
    (managers + i)->cds = cds;
    //@ open ConcurrentDataStructureAllClientMem(cds, snapshotIds, snapshots, pkePred);
    //@ close TraceManagerMem(managers + i, snapshotId, snapshot, pkePred);
    if (i < noOfClients - 1) {
        //@ open exists(snapshotIds);
        //@ open exists(snapshots);
        //@ close exists(remSnapshotIds);
        //@ close exists(remSnapshots);
        init_trace_managers(managers, cds, noOfClients, i + 1);
    } else {
        /*@
        switch (remSnapshots) {
            case nil:
            case cons(x, y):
                assert false; // this case cannot occur
        }
        @*/
        //@ open ConcurrentDataStructureAllClientMem(cds, remSnapshotIds, nil, pkePred);
        //@ close TraceManagerMemAll(managers + i + 1, nil, nil, pkePred);
    }
    //@ close TraceManagerMemAll(managers + i, snapshotIds, snapshots, pkePred);
}

struct TraceManager *create_trace_managers(int noOfClients)
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
{     
    //@ mul_mono_l(0, noOfClients, sizeof(struct TraceManager));      
    struct TraceManager *managers = malloc(noOfClients * sizeof(struct TraceManager));
    if (managers == 0) {
        abort();
    }
    struct ConcurrentDataStructure *cds = createConcurrentDataStructure(noOfClients);
    init_trace_managers(managers, cds, noOfClients, 0);
    return managers;
}

/*@
lemma Trace sync_helper(SnapIdList snapshotIds)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true;
    ensures  ghost_cell(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, globalTrace) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        result == globalTrace;
{
    switch(snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
  	        if (snapshotId == curSnapId) {
 			    merge_fractions ghost_cell(snapshotId,_);
  		        ghost_cell_mutate<Trace>(snapshotId, globalTrace);
  		        split_fraction ghost_cell(snapshotId, globalTrace) by 1/2;
                isSuffixReflexive(globalTrace);
            } else {
                sync_helper(remSnapshotIds);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            return globalTrace;
    }
}
@*/

void *tmSync(struct TraceManager *tm)
//@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred);
/*@ ensures  TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        isSuffix(snap0, snap1) == true; @*/
{
    //@ open TraceManagerMem(tm, owner, snap0, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap0, ?snapshotIds, ?globalTrace, pkePred);
    //@ sync_helper(snapshotIds);
    //@ isSuffixReflexive(globalTrace);
    //@ close locked_properties(cds, owner, globalTrace, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, globalTrace, pkePred);
    return tm;
}

/*@
lemma Trace write_event_helper(SnapIdList snapshotIds, ParameterizedEvent e)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*&
        event_pred(snapshotId, e, snapshot) &*&
        valid_trace(globalTrace, ?pkePred) &*&
        PkeCtxt(pkePred);
    ensures  ghost_cell<Trace>(globalTraceId, result) &*&
        [1/2]ghost_cell<Trace>(snapshotId, result) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, result) &*&
        result == makeEvent(globalTrace, snapshotId, e) &*&
        traceLength(result) <= 1 + traceLength(globalTrace) &*&
        valid_trace(result, pkePred) &*&
        PkeCtxt(pkePred);
{  
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            Trace newGlobalTrace;
  	        if (snapshotId == curSnapId) {
 			    merge_fractions ghost_cell(snapshotId, _); 
  		        newGlobalTrace = makeEvent(globalTrace, snapshotId, e);
  		        ghost_cell_mutate<Trace>(snapshotId, newGlobalTrace);
  		        split_fraction ghost_cell(snapshotId, newGlobalTrace) by 1/2;
  		        ghost_cell_mutate<Trace>(globalTraceId, newGlobalTrace);
  		        eventPredMonotonic(snapshot, globalTrace, snapshotId, e, pkePred);
                close valid_trace(newGlobalTrace, pkePred);
  		        snapshot_suffix_hold_event(newGlobalTrace, remSnapshotIds);
            } else {
                newGlobalTrace = write_event_helper(remSnapshotIds, e);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, newGlobalTrace);
            return newGlobalTrace;
    }
}
@*/

void *logEvent(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred) &*& 
        exists<ParameterizedEvent>(?e) &*& event_pred(owner, e, snap0) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        snap1 == makeEvent(_, owner, e) &*&
        PkeCtxt(pkePred); @*/
{
    //@ open TraceManagerMem(tm, owner, snap0, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap0, ?snapshotIds, ?globalTrace, pkePred);
    //@ Trace newGlobalTrace = write_event_helper(snapshotIds, e);
    //@ close locked_properties(cds, owner, newGlobalTrace, snapshotIds, newGlobalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, newGlobalTrace, pkePred);
    return tm;
}

/*@
lemma Trace write_message_helper(SnapIdList snapshotIds, int to, Term msg)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*&
        valid_trace(globalTrace, ?pkePred) &*&
        isPublishable(snapshot, msg, pkePred) == true &*&
        PkeCtxt(pkePred);
    ensures  ghost_cell<Trace>(globalTraceId, result) &*&
        [1/2]ghost_cell<Trace>(snapshotId, result) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, result) &*&
        valid_trace(result, pkePred) &*&
        result == makeMessage(globalTrace, to, snapshotId, msg) &*&
        traceLength(result) <= 1 + traceLength(globalTrace) &*&
        PkeCtxt(pkePred);
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            Trace newGlobalTrace;
  	        if (snapshotId == curSnapId) {
 			    merge_fractions ghost_cell(snapshotId, _); 
  		        newGlobalTrace = makeMessage(globalTrace, to, snapshotId, msg);
  		        ghost_cell_mutate<Trace>(snapshotId, newGlobalTrace);
  		        split_fraction ghost_cell(snapshotId, newGlobalTrace) by 1/2;
  		        ghost_cell_mutate<Trace>(globalTraceId, newGlobalTrace);
  		        snapshot_suffix_hold_adding_message(globalTrace, newGlobalTrace);          
  		        snapshot_suffix_hold_message(newGlobalTrace, remSnapshotIds);
                messageInvMonotonic(snapshot, globalTrace, to, snapshotId, msg, pkePred);
  		        close valid_trace(newGlobalTrace, pkePred);
            } else {
   	            newGlobalTrace = write_message_helper(remSnapshotIds, to, msg);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, newGlobalTrace);
            return newGlobalTrace;
    }
}
@*/

void *logSend(struct TraceManager *tm, int to)
/*@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred) &*&
        exists<Term>(?msg) &*&
        messageInv(to, owner, msg, snap0, pkePred) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        exists<Term>(msg) &*&
        isSuffix(snap0, snap1) == true &*&
        snap1 == makeMessage(_, to, owner, msg) &*&
        PkeCtxt(pkePred); @*/
{
    //@ open TraceManagerMem(tm, owner, snap0, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap0, ?snapshotIds, ?globalTrace, pkePred);
    //@ Trace newGlobalTrace = write_message_helper(snapshotIds, to, msg);
    //@ close locked_properties(cds, owner, newGlobalTrace, snapshotIds, newGlobalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, newGlobalTrace, pkePred);
    return tm;
}

/*@
lemma Trace write_nonce_helper(SnapIdList snapshotIds, Term nonce)
    requires  ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*&
        valid_trace(globalTrace, ?pkePred) &*&
        NonceUniqueResource(nonce) &*&
        isNonce(nonce) == true;
    ensures  ghost_cell<Trace>(globalTraceId, result) &*&
        [1/2]ghost_cell<Trace>(snapshotId, result) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, result) &*&
        valid_trace(result, pkePred) &*&
        result == makeNonce(globalTrace, nonce);
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
  	        Trace newGlobalTrace;
  	        if (snapshotId == curSnapId) {
 			    merge_fractions ghost_cell(snapshotId, _); 
  		        newGlobalTrace = makeNonce(globalTrace, nonce);
  		        ghost_cell_mutate<Trace>(snapshotId, newGlobalTrace);
  		        split_fraction ghost_cell(snapshotId, newGlobalTrace) by 1/2;
  		        ghost_cell_mutate<Trace>(globalTraceId, newGlobalTrace);
  		        close valid_trace(newGlobalTrace, pkePred);
  		        snapshot_suffix_hold_nonce(newGlobalTrace, remSnapshotIds);
            } else {
   	            newGlobalTrace = write_nonce_helper(remSnapshotIds, nonce);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, newGlobalTrace);
            return newGlobalTrace;
    }
}
@*/

void *logNonce(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snap0, ?pkePred) &*&
        NonceUniqueResource(?nonce) &*& isNonce(nonce) == true &*&
        canFlow(snap0, getNonceLabel(nonce), Readers(cons(owner, nil))) == true; @*/
/*@ ensures TraceManagerMem(tm, owner, ?snap1, pkePred) &*&
        isSuffix(snap0, snap1) == true &*&
        snap1 == makeNonce(_, nonce); @*/
{     
    //@ open TraceManagerMem(tm, owner, snap0, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap0, ?snapshotIds, ?globalTrace, pkePred);
    //@ Trace newGlobalTrace = write_nonce_helper(snapshotIds, nonce);     
    //@ close locked_properties(cds, owner, newGlobalTrace, snapshotIds, newGlobalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, newGlobalTrace, pkePred);
    return tm;
}

/*@
lemma void getPublicInv(Trace globalTrace, Trace snapshot)
    requires valid_trace(globalTrace, ?pkePred) &*& isSuffix(snapshot, globalTrace) == true;
    ensures  valid_trace(globalTrace, pkePred) &*& publicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot)), pkePred) == true;
{
    switch (globalTrace) {
        case root(root_terms):
            open valid_trace(globalTrace, pkePred); 
            close valid_trace(globalTrace, pkePred); 
        case makeEvent(t0, pr, e):
            open valid_trace(globalTrace, pkePred); 
            if (globalTrace != snapshot) {
                getPublicInv(t0, snapshot);
            } else {
                isSuffixReflexive(t0);
                getPublicInv(t0, t0);
            }
            close valid_trace(globalTrace, pkePred);
        case makeCorrupt(t0, id):
            open valid_trace(globalTrace, pkePred); 
            if (globalTrace != snapshot) {
                getPublicInv(t0, snapshot);
            } else {
                isSuffixReflexive(t0);
                getPublicInv(t0, t0);
            }
            close valid_trace(globalTrace, pkePred);
        case makeMessage(t0,to,from,term):
            open valid_trace(globalTrace, pkePred); 
            if (globalTrace != snapshot) {
                getPublicInv(t0, snapshot);
            } else {
                isSuffixReflexive(t0);
                getPublicInv(t0, t0);
            }
            close valid_trace(globalTrace, pkePred);
        case makeDropMessage(t0, to, from, term): 
            open valid_trace(globalTrace, pkePred); 
            if (globalTrace != snapshot) {
                getPublicInv(t0, snapshot);
            } else {
                isSuffixReflexive(t0);
                getPublicInv(t0, t0);
            }
            close valid_trace(globalTrace, pkePred);
        case makeNonce(t0, term):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPublicInv(t0, snapshot);
            } else {
                isSuffixReflexive(t0);
                getPublicInv(t0, t0);
            }
            close valid_trace(globalTrace, pkePred);      
        case makePublic(t0, term):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPublicInv(t0, snapshot);
            } else {
                isSuffixReflexive(t0);
                getPublicInv(t0, t0);
            }
            close valid_trace(globalTrace, pkePred);
    }
}

lemma void getPublicInvWrapper(SnapIdList snapshotIds)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*&
        valid_trace(globalTrace, ?pkePred);
    ensures  ghost_cell<Trace>(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        valid_trace(globalTrace, pkePred) &*&
        publicInv(getPublicTerms(snapshot), root(getPublicTerms(snapshot)), pkePred) == true; 
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            if (snapshotId == curSnapId) {
                merge_fractions ghost_cell(snapshotId, _); 
                getPublicInv(globalTrace, snapshot);
                split_fraction ghost_cell(snapshotId, snapshot) by 1/2;
            } else {
                getPublicInvWrapper(remSnapshotIds);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
    }
}
@*/

void findEntryWithPurePublicInvWithSnapConditional(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Trace>(?snap) &*& exists<Term>(?term) &*& exists<bool>(?cond) &*&
        isSuffix(snap, snapshot) == true &*&
        cond ? mem(term, getPublicTerms(snap)) == true : true; @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*& 
        isSuffix(snap, snapshot) == true &*&
        cond ? publicInv(getPublicTerms(snap), root(getPublicTerms(snap)), pkePred) == true : true; @*/
{
    //@ open TraceManagerMem(tm, owner, snapshot, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snapshot, ?snapshotIds, ?globalTrace, pkePred);
    /*@ 
    if (cond) {
        getPublicInvWrapper(snapshotIds);
    }
    @*/
    //@ close locked_properties(cds, owner, snapshot, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snapshot, pkePred);
    //@ getPublicTermsMonotonic(snap, snapshot);
}

/*@
lemma Trace getMsgInv(Trace globalTrace, Trace snapshot, int to, int from, Term msg)
    requires valid_trace(globalTrace, ?pkePred) &*& isSuffix(snapshot, globalTrace) == true &*&
        msgOccurs(msg, to, from, snapshot) == true;
    ensures  valid_trace(globalTrace, pkePred) &*& messageInv(to, from, msg, result, pkePred) == true &*&
        isSuffix(result, snapshot) == true;
{
    switch (globalTrace) {
        case root(root_terms): 
        case makeEvent(t0, pr, e):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getMsgInv(t0, snapshot, to, from, msg); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getMsgInv(t0, t0, to, from, msg);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeCorrupt(t0, id):
            open valid_trace(globalTrace, pkePred); 
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getMsgInv(t0, snapshot, to, from, msg); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getMsgInv(t0, t0, to, from, msg);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeMessage(t0, to1, from1, m):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getMsgInv(t0, snapshot, to, from, msg); 
            } else if (to1 == to && from1 == from && m == msg) {
                isSuffixReflexive(t0);
                ret = t0;
            } else {
                isSuffixReflexive(t0); 
                ret = getMsgInv(t0, t0, to, from, msg); 
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeDropMessage(t0, to1, from1, term): 
            open valid_trace(globalTrace, pkePred); 
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getMsgInv(t0, snapshot, to, from, msg); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getMsgInv(t0, t0, to, from, msg);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeNonce(t0, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getMsgInv(t0, snapshot, to, from, msg); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getMsgInv(t0, t0, to, from, msg);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makePublic(t0, term):
            open valid_trace(globalTrace, pkePred); 
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getMsgInv(t0, snapshot, to, from, msg); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getMsgInv(t0, t0, to, from, msg);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
    }
}

lemma Trace getMsgInvWrapper(SnapIdList snapshotIds, Trace givenSnap, Term msg, int to, int from)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*& 
        valid_trace(globalTrace, ?pkePred) &*&
        msgOccurs(msg, to, from, givenSnap) == true &*&
        isSuffix(givenSnap, snapshot) == true;
    ensures  ghost_cell<Trace>(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        valid_trace(globalTrace, pkePred) &*&
        messageInv(to, from, msg, result, pkePred) == true &*&
        isSuffix(result, givenSnap) == true; 
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            Trace ret;
            if (snapshotId == curSnapId) {
                merge_fractions ghost_cell(snapshotId, _); 
                isSuffixTransitive(givenSnap, snapshot, globalTrace);
                ret = getMsgInv(globalTrace, givenSnap, to, from, msg);
                split_fraction ghost_cell(snapshotId, snapshot) by 1/2;
            } else {
                ret = getMsgInvWrapper(remSnapshotIds, givenSnap, msg, to, from);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            return ret;
    }
}
@*/

#define IntPair pair<int, int>

void msgOccursImpliesMsgInvGhostArgsConditional(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Trace>(?snap) &*& exists<bool>(?cond) &*&
        isSuffix(snap, snapshot) == true &*&
        exists<IntPair>(?senderReceiverId) &*& exists<Term>(?msg) &*&
        (cond ? msgOccurs(msg, snd(senderReceiverId), fst(senderReceiverId), snap) == true : true) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, snapshot, pkePred) &*&
        (cond ? messageInv(snd(senderReceiverId), fst(senderReceiverId), msg, snap, pkePred) == true : true) &*&
        PkeCtxt(pkePred); @*/
{
    //@ int idSender = fst(senderReceiverId);
    //@ int idReceiver = snd(senderReceiverId);
    //@ open TraceManagerMem(tm, owner, snapshot, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snapshot, ?snapshotIds, ?globalTrace, pkePred);
    /*@
    if (cond) {
        Trace prev = getMsgInvWrapper(snapshotIds, snap, msg, idReceiver, idSender);
        messageInvMonotonic(prev, snap, idReceiver, idSender, msg, pkePred); 
    }
    @*/
    //@ close locked_properties(cds, owner, snapshot, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snapshot, pkePred);
}

void msgOccursImpliesMsgInvGhostArgs(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Trace>(?snap) &*&
        isSuffix(snap, snapshot) == true &*&
        exists<IntPair>(?senderReceiverIds) &*& exists<Term>(?msg) &*&
        msgOccurs(msg, snd(senderReceiverIds), fst(senderReceiverIds), snap) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, snapshot, pkePred) &*&
        messageInv(snd(senderReceiverIds), fst(senderReceiverIds), msg, snap, pkePred) == true &*&
        PkeCtxt(pkePred); @*/
{
    //@ close exists(true);
    msgOccursImpliesMsgInvGhostArgsConditional(tm);
}

void msgOccursImpliesMsgInv(struct TraceManager *tm, int idSender, int idReceiver)
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<Term>(?msg) &*&
        msgOccurs(msg, idReceiver, idSender, snap) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures TraceManagerMem(tm, owner, snap, pkePred) &*&
        messageInv(idReceiver, idSender, msg, snap, pkePred) == true &*&
        PkeCtxt(pkePred); @*/
{
    //@ close exists<Trace>(snap);
    //@ isSuffixReflexive(snap);
    //@ close exists<IntPair>(pair(idSender, idReceiver));
    msgOccursImpliesMsgInvGhostArgs(tm);
}

/*@
lemma Trace getPublicTermsInv(Trace globalTrace, Trace snapshot, Term t)
    requires valid_trace(globalTrace, ?pkePred) &*& isSuffix(snapshot, globalTrace) == true &*&
        mem(t, getTermsMadePublic(snapshot)) == true;
    ensures  valid_trace(globalTrace, pkePred) &*& isPublishable(result, t, pkePred) == true &*&
        isSuffix(result, snapshot) == true;
{
    switch (globalTrace) {
        case root(root_terms):
        case makeEvent(t0, pr, e):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) { 
                ret = getPublicTermsInv(t0, snapshot, t); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getPublicTermsInv(t0, t0, t);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeCorrupt(t0, id):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) { 
                ret = getPublicTermsInv(t0, snapshot, t); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getPublicTermsInv(t0, t0, t);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeMessage(t0,to1,from1,term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) { 
                ret = getPublicTermsInv(t0, snapshot, t); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getPublicTermsInv(t0, t0, t);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeDropMessage(t0, to1, from1, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) { 
                ret = getPublicTermsInv(t0, snapshot, t); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getPublicTermsInv(t0, t0, t);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeNonce(t0, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) { 
                ret = getPublicTermsInv(t0, snapshot, t); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getPublicTermsInv(t0, t0, t);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makePublic(t0, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret; 
            if (globalTrace != snapshot) {
                ret = getPublicTermsInv(t0, snapshot, t); 
            } else if (term == t) {
                isSuffixReflexive(t0); 
                ret = t0;
            } else {
                isSuffixReflexive(t0); 
                ret = getPublicTermsInv(t0, t0, t);
            }
            close valid_trace(globalTrace, pkePred);
            return ret; 
    }
}

lemma Trace getPublicTermsWrapper(SnapIdList snapshotIds, Trace givenSnap, Term term)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*& 
        valid_trace(globalTrace, ?pkePred) &*&
        mem(term, getTermsMadePublic(givenSnap)) == true &*&
        isSuffix(givenSnap, snapshot) == true;
    ensures  ghost_cell<Trace>(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        valid_trace(globalTrace, pkePred) &*&
        isPublishable(result, term, pkePred) == true &*&
        isSuffix(result, givenSnap) == true; 
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            Trace ret;
            if (snapshotId == curSnapId) {
                merge_fractions ghost_cell(snapshotId, _); 
                isSuffixTransitive(givenSnap, snapshot, globalTrace);
                ret = getPublicTermsInv(globalTrace, givenSnap, term);
                split_fraction ghost_cell(snapshotId, snapshot) by 1/2;
            } else {
                ret = getPublicTermsWrapper(remSnapshotIds, givenSnap, term);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            return ret;
    }
}
@*/

void madePublicTermImpliesPublishableSnapConditional(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Term>(?term) &*& exists<Trace>(?snap) &*& exists<bool>(?cond) &*&
        isSuffix(snap, snapshot) == true &*&
        cond ? mem(term, getTermsMadePublic(snap)) == true : true; @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*&
        isSuffix(snap, snapshot) == true &*&
        cond ? isPublishable(result, term, pkePred) == true : true; @*/
{
    //@ open TraceManagerMem(tm, owner, snapshot, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snapshot, ?snapshotIds, ?globalTrace, pkePred);
    //@ Trace result = snap;
    /*@
    if (cond) {
        result = getPublicTermsWrapper(snapshotIds, snap, term);
    } else {
        isSuffixReflexive(result);
    }
    @*/
    //@ close locked_properties(cds, owner, snapshot, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snapshot, pkePred);
    //@ close exists<Trace>(result);
}

void madePublicTermImpliesPublishableSnap(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Term>(?term) &*& exists<Trace>(?snap) &*&
        isSuffix(snap, snapshot) == true &*& mem(term, getTermsMadePublic(snap)) == true; @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*&
        isSuffix(snap, snapshot) == true &*&
        isPublishable(result, term, pkePred) == true; @*/
{
    //@ close exists(true);
    madePublicTermImpliesPublishableSnapConditional(tm);
}

void publicTermImpliesPublicInvWithSnapConditional(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Term>(?term) &*& exists<Trace>(?snap) &*& exists<bool>(?cond) &*&
        isSuffix(snap, snapshot) == true &*&
        cond ? mem(term, getPublicTerms(snap)) == true : true; @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*&
        cond ? publicInv(getPublicTerms(snap), result, pkePred) == true : true; @*/
{
    findEntryWithPurePublicInvWithSnapConditional(tm);
    //@ rootIsSuffix(snap, root(getPublicTerms(snap)));
    //@ close exists(root(getPublicTerms(snap)));
}

void publicTermImpliesPublicInvWithSnap(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Term>(?term) &*& exists<Trace>(?snap) &*&
        isSuffix(snap, snapshot) == true &*& mem(term, getPublicTerms(snap)) == true; @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*&
        exists<Trace>(?result) &*&
        isSuffix(result, snap) == true &*& publicInv(getPublicTerms(snap), result, pkePred) == true; @*/
{
    //@ close exists(true);
    publicTermImpliesPublicInvWithSnapConditional(tm);
}

/*@
lemma void getPublishableFromPublicInv(Term t, list<Term> root_terms, trace<EventParams> tr, PkePred pkePred)
    requires publicInv(root_terms, tr, pkePred) == true &*& mem(t, root_terms) == true;
    ensures  isPublishable(tr, t, pkePred) == true;
{
    switch (root_terms) {
        case nil: 
        case cons(x, xs):
            if (t != x) {
                getPublishableFromPublicInv(t, xs, tr, pkePred);
            }
    }
}

lemma void messagePayloadsMemLemma(trace<EventParams> tr, trace<EventParams> tr0, Term mTerm, Term term, int to, int from)
    requires mem(mTerm, getMessagePayloads(tr)) == true &*& tr == makeMessage(tr0,to,from,term) &*& mTerm != term;
    ensures  mem(mTerm, getMessagePayloads(tr0)) == true;
{
    // no body needed
}

lemma pair<int,int> getMessageSenderReceiver(trace<EventParams> tr, Term mTerm)
    requires mem(mTerm, getMessagePayloads(tr)) == true;
    ensures  msgOccurs(mTerm, snd(result), fst(result), tr) == true;
{
    switch (tr) {
        case root(root_terms): 
        case makeEvent(t0, pr, e): return getMessageSenderReceiver(t0, mTerm);
        case makeCorrupt(t0, id): return getMessageSenderReceiver(t0, mTerm);
        case makeMessage(t0,to,from,term):
            if (mTerm == term) {
                return pair(from, to);
            } else {
                messagePayloadsMemLemma(tr, t0, mTerm, term, to, from);   
                return getMessageSenderReceiver(t0, mTerm);
            }
        case makeDropMessage(t0, to, from, term): return getMessageSenderReceiver(t0, mTerm);
        case makeNonce(t0, term): return getMessageSenderReceiver(t0, mTerm);
        case makePublic(t0, term): return getMessageSenderReceiver(t0, mTerm);
    }
}
@*/

void attackerOnlyKnowsPublishableValuesWithSnap(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snapshot, ?pkePred) &*&
        exists<Trace>(?snap) &*& exists<Term>(?term) &*&
        attackerKnows(snap, term) == true &*& isSuffix(snap, snapshot) == true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snapshot, pkePred) &*& isPublishable(snap, term, pkePred) == true &*&
        PkeCtxt(pkePred); @*/
{
    //@ TermList publicTerms = getPublicTerms(snap);
	//@ TermList msgPayloads = getMessagePayloads(snap);
	//@ TermList publishedTerms = getTermsMadePublic(snap);
    //@ mem_append(term, append(publishedTerms, msgPayloads), publicTerms);
    //@ mem_append(term, publishedTerms, msgPayloads);

    // this is the condition under which we apply the `publicTermImpliesPublicInvWithSnap` lemma:
    //@ bool isPublicTerm = mem(term, getPublicTerms(snap));
    //@ close exists(isPublicTerm);
    //@ close exists(term);
    //@ close exists(snap);
	publicTermImpliesPublicInvWithSnapConditional(tm);
    //@ open exists<Trace>(?prev);
    /*@
    if (isPublicTerm) {
        getPublishableFromPublicInv(term, publicTerms, prev, pkePred);
		isPublishableMonotonic(prev, snap, term, pkePred);
    }
    @*/

    // this is the condition under which we apply the `msgOccursImpliesMsgInvGhostArgs` lemma:
    //@ bool isMsgTerm = !isPublicTerm && mem(term, msgPayloads);
    //@ close exists(isMsgTerm);
    //@ IntPair senderReceiverIds = pair(0, 0); // some default value
    /*@
    if (isMsgTerm) {
        senderReceiverIds = getMessageSenderReceiver(snap, term);
    }
    @*/
    //@ close exists(senderReceiverIds);
    //@ close exists(snap);
    //@ close exists(term);
    msgOccursImpliesMsgInvGhostArgsConditional(tm);

    // this is the condition under which we apply the `madePublicTermImpliesPublishableSnap` lemma:
    //@ bool isMadePublicTerm = !isPublicTerm && !isMsgTerm;
    //@ close exists(isMadePublicTerm);
    //@ close exists(term);
    //@ close exists(snap);
	madePublicTermImpliesPublishableSnapConditional(tm);
    //@ open exists<Trace>(?result);
    /*@
    if (isMadePublicTerm) {
        isPublishableMonotonic(result, snap, term, pkePred);
    }
    @*/
}

void secrecyLemma(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<Term>(?term) &*& exists<IntList>(?readers) &*&
        (isLabeled(term, snap, Readers(readers), pkePred) || containsCorruptId(getCorruptIds(snap), readers)) &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        Secrecy(term, snap, readers, pkePred) == true &*&
        exists<optiontype>(?result) &*&
        switch (result) {
            case some(y): return mem(y, getCorruptIds(snap)) && mem(y, readers);
            case none: return !attackerKnows(snap, term);
        } &*& PkeCtxt(pkePred); @*/
{
    //@ open TraceManagerMem(tm, owner, snap, pkePred);
    ///@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap, ?snapshotIds, ?globalTrace, pkePred);
    /*@
    if (attackerKnows(snap, term)) {
        list<int> corruptedIds = getCorruptIds(snap);
        if (containsCorruptId(corruptedIds, readers)) {
            switch (intersection(corruptedIds, readers)) {
                case nil:
                case cons(cID, xs):
                    mem_intersection(cID, corruptedIds, readers);
                    close exists(some(cID));              
            } 
        } else {
            list<int> corruptedIds2 = getCorruptIds(snap);
         	if (containsCorruptId(corruptedIds, readers)) {
         	    switch (intersection(corruptedIds2, readers)) {
            	    case nil:
            		case cons(cID, xs):
                        mem_intersection(cID, corruptedIds2, readers);
                        close exists(some(cID));          
         		} 
            } else {
                isSuffixReflexive(snap);
            	list<Term> publicTerms = getPublicTerms(snap);
		        list<Term> msgPayloads = getMessagePayloads(snap);
		        list<Term> publishedTerms = getTermsMadePublic(snap);
         	    mem_append(term, append(publishedTerms, msgPayloads), publicTerms);
         	    mem_append(term, publishedTerms, msgPayloads);
         	    if (mem(term, getPublicTerms(snap))) {
		            getPublicInvWrapper(snapshotIds);
      			    rootIsSuffix(snap, root(getPublicTerms(snap)));
        		    Trace prev = root(getPublicTerms(snap));
                    getPublishableFromPublicInv(term, publicTerms, prev, pkePred);
			        isPublishableMonotonic(prev, snap, term, pkePred);
			        isPublishable(snap, term, pkePred) == true;
		        } else if (mem(term, msgPayloads)) {
	        		IntPair senderReceiverIds = getMessageSenderReceiver(snap, term);
				    int from = fst(senderReceiverIds);
			        int to = snd(senderReceiverIds);
  				    Trace to_ret = getMsgInvWrapper(snapshotIds, snap, term, to, from);
                    isPublishableMonotonic(to_ret, snap, term, pkePred);
			    } else {
			        trace<EventParams> to_ret =  getPublicTermsWrapper(snapshotIds, snap, term);
		            isPublishableMonotonic(to_ret, snap, term, pkePred);
		        }
       	    }
        }
    } else {
        close exists(none);
    }
    @*/
    //@ close locked_properties(cds, owner, snap, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snap, pkePred);
}

/*@
lemma void getPureNonceInv(Trace globalTrace, Trace snapshot, Term nonce)
    requires valid_trace(globalTrace, ?pkePred) &*& isSuffix(snapshot, globalTrace) == true &*&
        onlyNonceOccurs(snapshot, nonce) == true;
    ensures  valid_trace(globalTrace, pkePred) &*& isNonce(nonce) == true;
{
    switch (globalTrace) {
        case root(root_terms):
        case makeEvent(t0, pr, e1):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPureNonceInv(t0, snapshot, nonce);
            } else { 
                isSuffixReflexive(t0); 
                getPureNonceInv(t0, t0, nonce);
            }
            close valid_trace(globalTrace, pkePred);
        case makeCorrupt(t0, id):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPureNonceInv(t0, snapshot, nonce);
            } else { 
                isSuffixReflexive(t0); 
                getPureNonceInv(t0, t0, nonce);
            }
            close valid_trace(globalTrace, pkePred);
        case makeMessage(t0, to1, from1, term):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPureNonceInv(t0, snapshot, nonce);
            } else { 
                isSuffixReflexive(t0); 
                getPureNonceInv(t0, t0, nonce);
            }
            close valid_trace(globalTrace, pkePred);
        case makeDropMessage(t0, to1, from1, term): 
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPureNonceInv(t0, snapshot, nonce);
            } else { 
                isSuffixReflexive(t0); 
                getPureNonceInv(t0, t0, nonce);
            }
            close valid_trace(globalTrace, pkePred);
        case makeNonce(t0, term):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPureNonceInv(t0, snapshot, nonce);
            } else if (nonce != term) {
                isSuffixReflexive(t0); 
                getPureNonceInv(t0, t0, nonce);
            }
            close valid_trace(globalTrace, pkePred);
        case makePublic(t0, term):
            open valid_trace(globalTrace, pkePred);
            if (globalTrace != snapshot) {
                getPureNonceInv(t0, snapshot, nonce);
            } else { 
                isSuffixReflexive(t0); 
                getPureNonceInv(t0, t0, nonce);
            }
            close valid_trace(globalTrace, pkePred);
    }
}

lemma void getNonceInvWrapper(SnapIdList snapshotIds, Trace givenSnap, Term nonce)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*& 
        valid_trace(globalTrace, ?pkePred) &*&
        onlyNonceOccurs(givenSnap, nonce) == true &*&
        isSuffix(givenSnap, snapshot) == true;
    ensures  ghost_cell<Trace>(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        valid_trace(globalTrace, pkePred) &*&
        isNonce(nonce) == true; 
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            Trace ret;
            if (snapshotId == curSnapId) {
                merge_fractions ghost_cell(snapshotId, _); 
                isSuffixTransitive(givenSnap, snapshot, globalTrace);
                getPureNonceInv(globalTrace, givenSnap, nonce);
                split_fraction ghost_cell(snapshotId, snapshot) by 1/2;
            } else {
                getNonceInvWrapper(remSnapshotIds, givenSnap, nonce);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            return;
    }
}
@*/

void nonceOccursImpliesRandInvConditional(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        exists<Term>(?nonce) &*& exists<bool>(?cond) &*&
        cond ? onlyNonceOccurs(snap, nonce) == true : true &*&
        PkeCtxt(pkePred); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        cond ? isNonce(nonce) == true : true &*&
        PkeCtxt(pkePred); @*/
{
    //@ open TraceManagerMem(tm, owner, snap, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap, ?snapshotIds, ?globalTrace, pkePred);
    //@ isSuffixReflexive(snap);
    /*@
    if (cond) {
        getNonceInvWrapper(snapshotIds, snap, nonce);
    }
    @*/
    //@ close locked_properties(cds, owner, snap, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snap, pkePred);
}

/*@
lemma Trace getPureEventInv(Trace globalTrace, Trace snapshot, int principal, ParameterizedEvent e)
    requires valid_trace(globalTrace, ?pkePred) &*& isSuffix(snapshot, globalTrace) == true &*&
        eventOccurs(snapshot, principal, e) == true;
    ensures  valid_trace(globalTrace, pkePred) &*& event_pure_pred_consistent(e, principal, result) == true &*&
        isSuffix(result, snapshot) == true &*&
        result == getEventTrace(snapshot, principal, e); 
{
    switch (globalTrace) {
        case root(root_terms):
        case makeEvent(t0, pr, e1):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getPureEventInv(t0, snapshot, principal, e); 
            } else if (pr == principal && e == e1) {
                open event_pred(principal, e, t0);
                close event_pred(principal, e, t0);
                isSuffixReflexive(t0);
                ret = t0;
            } else {
                isSuffixReflexive(t0); 
                ret = getPureEventInv(t0, t0, principal, e);
            }
            close valid_trace(globalTrace, pkePred);
            return ret;
        case makeCorrupt(t0, id):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getPureEventInv(t0, snapshot, principal, e); 
            } else { 
                isSuffixReflexive(t0); 
                ret = getPureEventInv(t0, t0, principal, e); 
            }
            close valid_trace(globalTrace, pkePred);
            return ret; 
        case makeMessage(t0, to1, from1, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getPureEventInv(t0, snapshot, principal, e); 
            } else { 
                isSuffixReflexive(t0);
                ret = getPureEventInv(t0, t0, principal, e);
            }
            close valid_trace(globalTrace, pkePred);
            return ret; 
        case makeDropMessage(t0, to1, from1, term): 
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getPureEventInv(t0, snapshot, principal, e);
            } else { 
                isSuffixReflexive(t0); 
                ret = getPureEventInv(t0, t0, principal, e);
            }
            close valid_trace(globalTrace, pkePred);
            return ret; 
        case makeNonce(t0, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getPureEventInv(t0, snapshot, principal, e);
            } else { 
                isSuffixReflexive(t0); 
                ret = getPureEventInv(t0, t0, principal, e);
            }
            close valid_trace(globalTrace, pkePred);
            return ret; 
        case makePublic(t0, term):
            open valid_trace(globalTrace, pkePred);
            Trace ret;
            if (globalTrace != snapshot) {
                ret = getPureEventInv(t0, snapshot, principal, e);
            } else { 
                isSuffixReflexive(t0); 
                ret = getPureEventInv(t0, t0, principal, e);
            }
            close valid_trace(globalTrace, pkePred);
            return ret; 
    }
}

lemma Trace getEventInvWrapper(SnapIdList snapshotIds, Trace givenSnap, int principal, ParameterizedEvent e)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*& 
        valid_trace(globalTrace, ?pkePred) &*&
        eventOccurs(givenSnap, principal, e) == true &*&
        isSuffix(givenSnap, snapshot) == true;
    ensures  ghost_cell<Trace>(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        valid_trace(globalTrace, pkePred) &*&
        event_pure_pred_consistent(e, principal, result) == true &*&
        isSuffix(result, givenSnap) == true &*&
        result == getEventTrace(givenSnap, principal, e); 
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            Trace ret;
            if (snapshotId == curSnapId) {
                merge_fractions ghost_cell(snapshotId, _); 
                isSuffixTransitive(givenSnap, snapshot, globalTrace);
                ret = getPureEventInv(globalTrace, givenSnap, principal, e);
                split_fraction ghost_cell(snapshotId, snapshot) by 1/2;
            } else {
                ret = getEventInvWrapper(remSnapshotIds, givenSnap, principal, e);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            return ret;
    }
}
@*/

void eventOccursImpliesEventInvConditional(struct TraceManager *tm)
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
{
    //@ open TraceManagerMem(tm, owner, snap, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap, ?snapshotIds, ?globalTrace, pkePred);
    //@ isSuffixReflexive(snap);
    //@ Trace ret = snap;
    /*@
    if (cond) {
        ret = getEventInvWrapper(snapshotIds, snap, principal, e);
        eventPurePredConsistentMonotonic(ret, snap, principal, e, pkePred);
    }
    @*/
    //@ close exists(ret);
    //@ close locked_properties(cds, owner, snap, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snap, pkePred);
}

/*@
lemma void uniqueEventsAreUniqueInternalWrapper(SnapIdList snapshotIds, int principal1, int principal2, ParameterizedEvent e1, ParameterizedEvent e2, int idx1, int idx2)
    requires ghost_cell<Trace>(?globalTraceId, ?globalTrace) &*&
        [1/2]ghost_cell<Trace>(?snapshotId, ?snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        mem(snapshotId, snapshotIds) == true &*& 
        valid_trace(globalTrace, ?pkePred) &*&
        eventOccursAt(snapshot, principal1, e1, idx1) == true &*& eventOccursAt(snapshot, principal2, e2, idx2) == true &*&
        eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*& isUnique(getEventType(e1)) == true &*&
        getEventType(e1) == getEventType(e2);
    ensures  ghost_cell<Trace>(globalTraceId, globalTrace) &*&
        [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
        [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        valid_trace(globalTrace, pkePred) &*&
        principal1 == principal2 &*& e1 == e2 &*& idx1 == idx2;
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapId, remSnapshotIds):
            open [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
            if (snapshotId == curSnapId) {
                merge_fractions ghost_cell(snapshotId, _);
                uniqueEventsAreUniqueAtInternal(globalTrace, snapshot, principal1, principal2, e1, e2, idx1, idx2);
                split_fraction ghost_cell(snapshotId, snapshot) by 1/2;
            } else {
                uniqueEventsAreUniqueInternalWrapper(remSnapshotIds, principal1, principal2, e1, e2, idx1, idx2);
            }
            close [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);
    }
}
@*/

void uniqueEventsAreUniqueAtConditional(struct TraceManager *tm)
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
{
    //@ open TraceManagerMem(tm, owner, snap, pkePred);
    //@ close exists(pkePred);
    acquire(tm->cds);
    //@ open locked_properties(?cds, owner, snap, ?snapshotIds, ?globalTrace, pkePred);
    /*@
    if (cond) {
        uniqueEventsAreUniqueInternalWrapper(snapshotIds, principal1, principal2, e1, e2, idx1, idx2);
    }
    @*/
    //@ close locked_properties(cds, owner, snap, snapshotIds, globalTrace, pkePred);
    release(tm->cds);
    //@ close TraceManagerMem(tm, owner, snap, pkePred);
    //@ leak Event1At(principal1, e1, idx1) &*& Event2At(principal2, e2, idx2);
}

void uniqueEventsAreUniqueConditional(struct TraceManager *tm)
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
{
    //@ int idx1 = eventOccursAtTimeLemma(snap, principal1, e1);
    //@ int idx2;
    /*@
    if (cond) {
        idx2 = eventOccursAtTimeLemma(snap, principal2, e2);
    }
    @*/
    //@ close Event1At(principal1, e1, idx1);
    //@ close Event2At(principal2, e2, idx2);
    uniqueEventsAreUniqueAtConditional(tm);
    //@ leak Event1(principal1, e1) &*& Event2(principal2, e2);
}

void uniqueEventsAreUnique(struct TraceManager *tm)
/*@ requires TraceManagerMem(tm, ?owner, ?snap, ?pkePred) &*&
        Event1(?principal1, ?e1) &*& Event2(?principal2, ?e2) &*&
        eventOccurs(snap, principal1, e1) == true &*&
        eventOccurs(snap, principal2, e2) == true &*&
        eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
        isUnique(getEventType(e1)) == true &*&
        getEventType(e1) == getEventType(e2); @*/
/*@ ensures  TraceManagerMem(tm, owner, snap, pkePred) &*&
        principal1 == principal2 &*& e1 == e2; @*/
{
    //@ close exists(true);
    uniqueEventsAreUniqueConditional(tm);
}
