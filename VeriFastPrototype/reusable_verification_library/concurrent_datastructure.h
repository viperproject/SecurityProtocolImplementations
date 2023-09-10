#ifndef CONCURRENT_DATASTRUCTURE
#define CONCURRENT_DATASTRUCTURE

//@#include "ghost_cells.gh"
#include "threading.h"
//@ #include "trace_entry.gh"
//@ #include "trace_invariant.gh"


#define SnapId int
#define SnapIdList list<SnapId>
#define SnapList list<Trace>
#define TermList list<Term>


struct ConcurrentDataStructure {
    int size;
    struct mutex *mutex;
    //@ SnapIdList snapshots; 
    //@ SnapId ghost_trace;
};

// On a high level, a single (globally shared) instance of the concurrent data structure
// should be created by calling `createConcurrentDataStructure` and specifying by how many
// clients this instance will be shared.
// This returns an instance of the `ConcurrentDataStructureAllClientMem` predicate, which
// contains one instance of the `ConcurrentDataStructurePerClientMem` predicate per specified
// client. Thus, a caller should distribute the predicate instances such that each client, i.e.
// protocol session, gets its `ConcurrentDataStructurePerClientMem` predicate instance.
// This predicate instance is then sufficient to interact with the concurrent data structure
// via calls to `acquire` and `release`.

/*@
// `oldGlobalTrace` keeps track of the global trace at the time of acquiring the concurrent
// data structure. This enables us to express a precondition for `release` that checks
// that the global trace has been extended by at most 1 trace entry such that atomicity
// is guaranteed.
predicate oldGlobalTrace(Trace globalTrace);

// This recursive predicate contains permission to each ghost cell storing a snapshot
// and ensures that each snapshot is a suffix of the global trace.
predicate snapshot_suffix_forall<t>(SnapIdList snapshotIds, Trace globalTrace) =
    switch (snapshotIds) {
        case nil: return true;
        case cons(id, remIds):
            return ghost_cell(id, ?snapshot) &*&
                isSuffix(snapshot, globalTrace) == true &*&
                snapshot_suffix_forall(remIds, globalTrace);
    };

// This recursive predicate contains [1/2] permission to each ghost cell contained in `snapshotIds`.
predicate snapshot_perm_forall(SnapIdList snapshotIds, SnapList snapshots);

// invariant of the mutex that contains full access to the ghost cell storing the global trace and [1/2] permissions
// to each ghost cell storing a snapshot.
predicate_ctor mutex_invariant(struct ConcurrentDataStructure *cds, int size, PkePred pkePred)() =
    cds->ghost_trace |-> ?globalTraceId &*& [1/2]cds->snapshots |-> ?snapshotIds &*& ghost_cell<Trace>(globalTraceId, ?globalTrace) &*& valid_trace(globalTrace, pkePred) 
    &*& [1/2]snapshot_suffix_forall(snapshotIds, globalTrace);

// abstraction of permissions and properties needed by a given client (identified by `snapshotId`) to interact
// with the concurrent data structure.
predicate ConcurrentDataStructurePerClientMem(struct ConcurrentDataStructure *cds, SnapId snapshotId, Trace snapshot, PkePred pkePred);

// abstracts over the permissions for each client, i.e., `ConcurrentDataStructurePerClientMem`.
predicate ConcurrentDataStructureAllClientMem(struct ConcurrentDataStructure *cds, SnapIdList snapshotIds, SnapList snapshots, PkePred pkePred) =
    switch (snapshotIds) {
        case nil: return true;
        case cons(id, remIds):
            return switch (snapshots) {
                case nil: return false; // express that `length(snapshotIds) <= length(snapshots)`
                case cons(snapshot, remSnapshots):
                    return ConcurrentDataStructurePerClientMem(cds, id, snapshot, pkePred) &*&
                        ConcurrentDataStructureAllClientMem(cds, remIds, remSnapshots, pkePred);
            };
    };

// abstraction of permissions and properties given to a client (identified by `snapshotId`) after acquiring the concurrent
// data structure and that will be necessary to call `release`.
predicate ConcurrentDataStructurePerClientMemLocked(struct ConcurrentDataStructure *cds, SnapId snapshotId, SnapIdList snapshotIds, int threadId, PkePred pkePred);

// abstraction of permissions and properties that a client obtains after acquiring the concurrent data structure and
// that are useful to interact and/or update the concurrent data structure's state.
predicate locked_properties(struct ConcurrentDataStructure *cds, SnapId snapshotId, Trace snapshot, SnapIdList snapshotIds, Trace globalTrace, PkePred pkePred) =  
    cds->ghost_trace |-> ?globalTraceId &*&
    ghost_cell<Trace>(globalTraceId, globalTrace) &*&
    valid_trace(globalTrace, pkePred) &*&
    [1/2]ghost_cell<Trace>(snapshotId, snapshot) &*&
    [1/2]snapshot_suffix_forall(snapshotIds, globalTrace) &*&
    mem(snapshotId, snapshotIds) == true &*&
    isSuffix(snapshot, globalTrace) == true;
@*/

// Creates an ConcurrentStructure Counter and return the permission
struct ConcurrentDataStructure *createConcurrentDataStructure(int clientSize);
/*@ requires exists<TermList>(?root_terms) &*&
    exists<PkePred>(?pkePred) &*&
    clientSize > 0 &*&
    publicInv(root_terms, root(root_terms), pkePred) == true; @*/
/*@ ensures  exists<SnapIdList>(?snapshotIds) &*&
        exists<SnapList>(?snapshots) &*&
        clientSize == length(snapshotIds) &*&
        clientSize == length(snapshots) &*&
        ConcurrentDataStructureAllClientMem(result, snapshotIds, snapshots, pkePred); @*/

void acquire(struct ConcurrentDataStructure *cds);
//@ requires ConcurrentDataStructurePerClientMem(cds, ?snapshotId, ?snapshot, ?pkePred);
/*@ ensures  ConcurrentDataStructurePerClientMemLocked(cds, snapshotId, ?snapshotIds, currentThread, pkePred) &*&
        locked_properties(cds, snapshotId, snapshot, snapshotIds, ?globalTrace, pkePred) &*&
        oldGlobalTrace(globalTrace); @*/

void release(struct ConcurrentDataStructure *cds);
/*@ requires ConcurrentDataStructurePerClientMemLocked(cds, ?snapshotId, ?snapshotIds, currentThread, ?pkePred) &*&
        locked_properties(cds, snapshotId, ?snapshot, snapshotIds, ?globalTrace, pkePred) &*&
        oldGlobalTrace(?oldGlobalTrace) &*&
        // the following precondition expresses that at most one trace entry is appended such that
        // atomicity is guaranteed.
        (globalTrace == oldGlobalTrace || getPrev(globalTrace) == oldGlobalTrace); @*/
//@ ensures  ConcurrentDataStructurePerClientMem(cds, snapshotId, snapshot, pkePred);

/*@
// adding an event to global trace preserves suffix
lemma void snapshot_suffix_hold_event(Trace globalTrace, SnapIdList snapshotIds);
    requires [?f]snapshot_suffix_forall(snapshotIds, ?oldTrace) &*& globalTrace == makeEvent(oldTrace, _,_);
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace);

// adding a message to global trace preserves suffix
lemma void snapshot_suffix_hold_message(Trace globalTrace, SnapIdList snapshotIds);
    requires [?f]snapshot_suffix_forall(snapshotIds, ?oldTrace) &*& globalTrace == makeMessage(oldTrace, _,_,_);
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace);

// adding a nonce to global trace preserves suffix
lemma void snapshot_suffix_hold_nonce(Trace globalTrace, SnapIdList snapshotIds);
    requires [?f]snapshot_suffix_forall(snapshotIds, ?oldTrace) &*& globalTrace == makeNonce(oldTrace, _);
    ensures  [f]snapshot_suffix_forall(snapshotIds, globalTrace);
@*/
#endif
