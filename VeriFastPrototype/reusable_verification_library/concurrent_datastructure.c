#include "concurrent_datastructure.h"
#include <stdlib.h>


/*@
// `oldGlobalTrace` keeps track of the global trace at the time of acquiring the concurrent
// data structure. This enables us to express a precondition for `release` that checks
// that the global trace has been extended by at most 1 trace entry such that atomicity
// is guaranteed.
predicate oldGlobalTrace(Trace globalTrace) = true;

// This recursive predicate contains [1/2] permission to each ghost cell contained in `snapshotIds`.
predicate snapshot_perm_forall(SnapIdList snapshotIds, SnapList snapshots) =
    switch (snapshotIds) {
        case nil: return true;
        case cons(id, remIds):
            return switch (snapshots) {
                case nil: return false;
                case cons(snapshot, remSnapshots):
                    return ghost_cell<Trace>(id, snapshot) &*& mem(id, snapshotIds) == true &*& snapshot_perm_forall(remIds, remSnapshots);
            };
    };

// abstraction of permissions and properties needed by a given client (identified by `snapshotId`) to interact
// with the concurrent data structure.
predicate ConcurrentDataStructurePerClientMem(struct ConcurrentDataStructure *cds, SnapId snapshotId, Trace snapshot, PkePred pkePred) =
    // note that `f == 1/clientSize` holds but I'm not sure how to make VeriFast's typechecker happy
    [?f]cds->size |-> ?clientSize &*&
    [f]cds->mutex |-> ?l &*&
    [f/2]cds->snapshots |-> ?snapshotIds &*&
    distinct(snapshotIds) == true &*&
    mem(snapshotId, snapshotIds) == true &*&
    [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
    [f]mutex(l, mutex_invariant(cds, clientSize, pkePred)) &*&
    [f]malloc_block_ConcurrentDataStructure(cds);

// abstraction of permissions and properties given to a client (identified by `snapshotId`) after acquiring the concurrent
// data structure and that will be necessary to call `release`.
predicate ConcurrentDataStructurePerClientMemLocked(struct ConcurrentDataStructure *cds, SnapId snapshotId, SnapIdList snapshotIds, int threadId, PkePred pkePred) =
    // note that `f == 1/clientSize` holds but I'm not sure how to make VeriFast's typechecker happy
    [?f]cds->size |-> ?clientSize &*&
    [f]cds->mutex |-> ?l &*&
    [f/2]cds->snapshots |-> snapshotIds &*&
    [1/2]cds->snapshots |-> snapshotIds &*&
    distinct(snapshotIds) == true &*&
    mem(snapshotId, snapshotIds) == true &*&
    mutex_held(l, mutex_invariant(cds, clientSize, pkePred), threadId, f) &*&
    [f]malloc_block_ConcurrentDataStructure(cds);

lemma void snapshotIsSuffix(SnapId snapshotId, SnapIdList snapshotIds, Trace globalTrace)
    requires [?f]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        [?g]ghost_cell<Trace>(snapshotId, ?snapshot) &*&
        mem(snapshotId, snapshotIds) == true;
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
        [g]ghost_cell(snapshotId, snapshot) &*&
        isSuffix(snapshot, globalTrace) == true;
{
    switch (snapshotIds) {
        case nil:
        case cons(id, remSnapshotIds):
            open [f]snapshot_suffix_forall(snapshotIds, globalTrace);
            if (id == snapshotId) {
                // we perform a proof by contradiction as this saves
                // us from having to split the fractions after merging
                // them:
                if (!isSuffix(snapshot, globalTrace)) {
                    merge_fractions ghost_cell<Trace>(snapshotId, _);
                    assert false; // contradiction -- as expected
                }
            } else {
                snapshotIsSuffix(snapshotId, remSnapshotIds, globalTrace);
            }
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
    }
}

predicate ConcurrentDataStructureMem(struct ConcurrentDataStructure *cds, int clientSize, PkePred pkePred) =
    cds->size |-> clientSize &*&
    cds->mutex |-> ?l &*&
    [1/2]cds->snapshots |-> ?snapshotIds &*&
    [1/2]snapshot_perm_forall(snapshotIds, ?snapshots) &*&
    clientSize == length(snapshotIds) &*&
    clientSize == length(snapshots) &*&
    distinct(snapshotIds) == true &*&
    mutex(l, mutex_invariant(cds, clientSize, pkePred)) &*&
    malloc_block_ConcurrentDataStructure(cds);

lemma void newGhostCellHasDistinctId(SnapIdList snapshotIds, SnapId newId)
    requires [1/2]snapshot_perm_forall(snapshotIds, ?snapshots) &*&
        ghost_cell<Trace>(newId, ?snapshot) &*&
        distinct(snapshotIds) == true;
    ensures  [1/2]snapshot_perm_forall(snapshotIds, snapshots) &*&
        ghost_cell<Trace>(newId, snapshot) &*&
        distinct(cons(newId, snapshotIds)) == true;
{
    switch (snapshotIds) {
        case nil:
        case cons(curSnapshotId, remSnapshotIds):
            open [1/2]snapshot_perm_forall(snapshotIds, snapshots);
            if (curSnapshotId == newId) {
                merge_fractions ghost_cell(curSnapshotId, _);
                ghost_cell_fraction_info(curSnapshotId);
                assert false; // contradiction -- as expected
            } else {
                newGhostCellHasDistinctId(remSnapshotIds, newId);
            }
            close [1/2]snapshot_perm_forall(snapshotIds, snapshots);
    }
}
@*/

struct ConcurrentDataStructure *allocateConcurrentDataStructure(int clientSize)
/*@ requires exists<TermList>(?root_terms) &*&
    exists<PkePred>(?pkePred) &*&
    clientSize > 0 &*&
    publicInv(root_terms, root(root_terms), pkePred) == true; @*/
//@ ensures  ConcurrentDataStructureMem(result, clientSize, pkePred);
{
    struct ConcurrentDataStructure *cds = malloc(sizeof(struct ConcurrentDataStructure));
    if (cds == 0){
        abort();
    }
    //@ cds->snapshots = nil;
    //@ Trace initialTrace = root(root_terms);
    //@ SnapId globalTraceId = create_ghost_cell<Trace>(initialTrace);
    //@ cds->ghost_trace = globalTraceId;
    cds->size = clientSize;
    //@ close valid_trace(initialTrace, pkePred);

    int i = 0; 
    //@ close [1/2]snapshot_suffix_forall(nil, initialTrace);
    //@ close [1/2]snapshot_perm_forall(nil, nil);
        
    //@ SnapList snapshots = nil;
    for (; i< clientSize; i++)
    /*@ invariant cds->snapshots |-> ?snapshotIds &*&
        [1/2]snapshot_perm_forall(snapshotIds, snapshots) &*&
        i == length(snapshotIds) &*&
        i == length(snapshots) &*&
        i <= clientSize &*&
        [1/2]snapshot_suffix_forall(snapshotIds, initialTrace) &*&
        distinct(snapshotIds) == true; @*/
    {
        //@ SnapId nextSnapshotId = create_ghost_cell(initialTrace);
        //@ newGhostCellHasDistinctId(snapshotIds, nextSnapshotId);
        //@ SnapIdList newSnapshotIds = cons(nextSnapshotId, snapshotIds);
        //@ cds->snapshots = newSnapshotIds;
        //@ snapshots = cons(initialTrace, snapshots);
        //@ close [1/2]snapshot_perm_forall(newSnapshotIds, snapshots);
        //@ close [1/2]snapshot_suffix_forall(newSnapshotIds, initialTrace);
    }

    //@ close mutex_invariant(cds, clientSize, pkePred)();
    //@ close create_mutex_ghost_arg(mutex_invariant(cds,clientSize, pkePred));

    cds->mutex = create_mutex();

    //@ close ConcurrentDataStructureMem(cds, clientSize, pkePred);

    return cds;
}

/*@
lemma void convertConcurrentDataStructureMemHelper(struct ConcurrentDataStructure *cds, SnapIdList curSnapIds, SnapList curSnaps, real f)
    requires length(curSnapIds) == length(curSnaps) &*&
        [f]cds->size |-> ?clientSize &*&
        [f]cds->mutex |-> ?l &*&
        [f/2]cds->snapshots |-> ?snapshotIds &*&
        distinct(snapshotIds) == true &*&
        subset(curSnapIds, snapshotIds) == true &*&
        [1/2]snapshot_perm_forall(curSnapIds, curSnaps) &*&
        exists<PkePred>(?pkePred) &*&
        [f]mutex(l, mutex_invariant(cds, clientSize, pkePred)) &*&
        [f]malloc_block_ConcurrentDataStructure(cds);
    ensures  ConcurrentDataStructureAllClientMem(cds, curSnapIds, curSnaps, pkePred);
{
    switch (curSnapIds) {
        case nil:
            close ConcurrentDataStructureAllClientMem(cds, curSnapIds, curSnaps, pkePred);
            open [1/2]snapshot_perm_forall(curSnapIds, curSnaps);
            // we can unfortunately not compute a precise fraction as VeriFast
            // does not allow us to express that the permission fraction `f` within
            // the `ConcurrentDataStructurePerClientMem` predicate is `1/clientSize`.
            leak [_]cds->size |-> clientSize;
            leak [_]cds->mutex |-> l;
            leak [_]cds->snapshots |-> snapshotIds;
            leak [_]mutex(l, mutex_invariant(cds, clientSize, pkePred));
            leak [_]malloc_block_ConcurrentDataStructure(cds);
        case cons(id, remIds):
            switch (curSnaps) {
                case nil: // this case cannot occur
                case cons(snapshot, remSnapshots):
                    open [1/2]snapshot_perm_forall(curSnapIds, curSnaps);
                    convertConcurrentDataStructureMemHelper(cds, remIds, remSnapshots, f/2);
                    close ConcurrentDataStructurePerClientMem(cds, id, snapshot, pkePred);
                    close ConcurrentDataStructureAllClientMem(cds, curSnapIds, curSnaps, pkePred);
            }
    }
}

lemma void convertConcurrentDataStructureMem(struct ConcurrentDataStructure *cds, PkePred pkePred)
    requires ConcurrentDataStructureMem(cds, ?clientSize, pkePred);
    ensures  exists<SnapIdList>(?snapshotIds) &*&
        exists<SnapList>(?snapshots) &*&
        clientSize == length(snapshotIds) &*&
        clientSize == length(snapshots) &*&
        ConcurrentDataStructureAllClientMem(cds, snapshotIds, snapshots, pkePred);
{
    open ConcurrentDataStructureMem(cds, clientSize, pkePred);
    assert [1/2]cds->snapshots |-> ?snapshotIds;
    assert [1/2]snapshot_perm_forall(snapshotIds, ?snapshots);
    close exists(pkePred);
    convertConcurrentDataStructureMemHelper(cds, snapshotIds, snapshots, 1/1);
    close exists(snapshotIds);
    close exists(snapshots);
}
@*/

struct ConcurrentDataStructure *createConcurrentDataStructure(int clientSize)
/*@ requires exists<TermList>(?root_terms) &*&
    exists<PkePred>(?pkePred) &*&
    clientSize > 0 &*&
    publicInv(root_terms, root(root_terms), pkePred) == true; @*/
/*@ ensures  exists<SnapIdList>(?snapshotIds) &*&
        exists<SnapList>(?snapshots) &*&
        clientSize == length(snapshotIds) &*&
        clientSize == length(snapshots) &*&
        ConcurrentDataStructureAllClientMem(result, snapshotIds, snapshots, pkePred); @*/
{
    struct ConcurrentDataStructure *cds = allocateConcurrentDataStructure(clientSize);
    //@ convertConcurrentDataStructureMem(cds, pkePred);
    return cds;
}

void acquire(struct ConcurrentDataStructure *cds)
//@ requires ConcurrentDataStructurePerClientMem(cds, ?snapshotId, ?snapshot, ?pkePred);
/*@ ensures  ConcurrentDataStructurePerClientMemLocked(cds, snapshotId, ?snapshotIds, currentThread, pkePred) &*&
        locked_properties(cds, snapshotId, snapshot, snapshotIds, ?globalTrace, pkePred) &*&
        oldGlobalTrace(globalTrace); @*/
{
    //@ open ConcurrentDataStructurePerClientMem(cds, snapshotId, snapshot, pkePred);
    mutex_acquire(cds->mutex);
    //@ assert [_]cds->size |-> ?clientSize;
    //@ open mutex_invariant(cds, clientSize, pkePred)();
    //@ assert cds->ghost_trace |-> ?globalTraceId;
    //@ assert ghost_cell(globalTraceId, ?globalTrace);
    //@ assert [1/2]snapshot_suffix_forall(?snapshotIds, globalTrace);
    //@ close ConcurrentDataStructurePerClientMemLocked(cds, snapshotId, snapshotIds, currentThread, pkePred);
    //@ close oldGlobalTrace(globalTrace);
    //@ snapshotIsSuffix(snapshotId, snapshotIds, globalTrace);
    //@ close locked_properties(cds, snapshotId, snapshot, snapshotIds, globalTrace, pkePred);
}

void release(struct ConcurrentDataStructure *cds)
/*@ requires ConcurrentDataStructurePerClientMemLocked(cds, ?snapshotId, ?snapshotIds, currentThread, ?pkePred) &*&
        locked_properties(cds, snapshotId, ?snapshot, snapshotIds, ?globalTrace, pkePred) &*&
        oldGlobalTrace(?oldGlobalTrace) &*&
        // the following precondition expresses that at most one trace entry is appended such that
        // atomicity is guaranteed.
        (globalTrace == oldGlobalTrace || getPrev(globalTrace) == oldGlobalTrace); @*/
//@ ensures  ConcurrentDataStructurePerClientMem(cds, snapshotId, snapshot, pkePred);
{
    //@ open ConcurrentDataStructurePerClientMemLocked(cds, snapshotId, snapshotIds, currentThread, pkePred);
    //@ open locked_properties(cds, snapshotId, snapshot, snapshotIds, globalTrace, pkePred);
    //@ assert [_]cds->size |-> ?clientSize;
    //@ close mutex_invariant(cds, clientSize, pkePred)();
    mutex_release(cds->mutex);
    //@ open oldGlobalTrace(oldGlobalTrace);
    //@ close ConcurrentDataStructurePerClientMem(cds, snapshotId, snapshot, pkePred);
}

/*@
lemma void snapshot_suffix_hold_event(trace<EventParams> globalTrace, SnapIdList snapshotIds)
    requires [?f]snapshot_suffix_forall(snapshotIds, ?oldTrace) &*& globalTrace == makeEvent(oldTrace, _,_);
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace);
{
    switch (snapshotIds) {    
        case nil:
            open [f]snapshot_suffix_forall(snapshotIds, oldTrace); 
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
        case cons(id, remIds): 
            open [f]snapshot_suffix_forall(snapshotIds, oldTrace);
            snapshot_suffix_hold_event(globalTrace, remIds);
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
    }
}

lemma void snapshot_suffix_hold_message(trace<EventParams> globalTrace, SnapIdList snapshotIds)
    requires [?f]snapshot_suffix_forall(snapshotIds, ?oldTrace) &*& globalTrace == makeMessage(oldTrace, _,_,_);
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace);
{
    switch (snapshotIds) {    
        case nil:
            open [f]snapshot_suffix_forall(snapshotIds, oldTrace);
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
        case cons(id, remIds) : 
            open [f]snapshot_suffix_forall(snapshotIds, oldTrace);
            snapshot_suffix_hold_message(globalTrace, remIds);
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
    }
}

lemma void snapshot_suffix_hold_nonce(trace<EventParams> globalTrace, SnapIdList snapshotIds)
    requires [?f]snapshot_suffix_forall(snapshotIds, ?oldTrace) &*& globalTrace == makeNonce(oldTrace, _);
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace);
{
    switch (snapshotIds) {    
        case nil:
            open [f]snapshot_suffix_forall(snapshotIds, oldTrace); 
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
        case cons(id, remIds): 
            open [f]snapshot_suffix_forall(snapshotIds, oldTrace);
            snapshot_suffix_hold_nonce(globalTrace, remIds);
            close [f]snapshot_suffix_forall(snapshotIds, globalTrace);
    }
}
@*/
