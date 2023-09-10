//@ #include "event_lemmas.gh"
//@ #include "nonce_lemmas.gh"
//@ #include "protocol_specific_event_lemma.gh"

/*@
lemma void eventUniqueContradiction(Term witness, int eventType)
    requires isUnique(eventType) == true &*&
        EventUniqueResource(witness, eventType) &*& EventUniqueResource(witness, eventType);
    ensures false;
{
    open EventUniqueResource(witness, eventType);
    open EventUniqueResource(witness, eventType);
    assert ghost_cell(?x, _);
    merge_fractions ghost_cell(x,_); 
    ghost_cell_fraction_info(x);
}

lemma void eventPurePredConsistentMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, int principal, ParameterizedEvent e, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& event_pure_pred_consistent(e, principal, t1) == true &*& PkeCtxt(pkePred);
    ensures event_pure_pred_consistent(e, principal, t2) == true &*& PkeCtxt(pkePred);
{
    int eventType;
    EventParams eventParams;
    switch (e) {
        case newEvent(type, params):
            eventType = type;
            eventParams = params;
    }
    eventPurePredMonotonic(t1, t2, principal, e, pkePred);
}

lemma void eventIsContradictionHelper(ParameterizedEvent e1, ParameterizedEvent e2, int principal1, int principal2, int idx2, Trace t1, Trace tr, PkePred pkePred)
    requires valid_trace(tr, pkePred) &*&
        event_pred(principal1, e1, t1) &*&
        eventOccursAt(tr, principal2, e2, idx2) == true &*&
        isUnique(getEventType(e1)) == true &*&
        eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
        getEventType(e1) == getEventType(e2);  
    ensures  valid_trace(tr, pkePred) &*&
        principal1 == principal2 &*&
        e1 == e2 &*&
        traceLength(t1) == idx2;
{
    int idx1 = traceLength(t1);
    switch (tr) {
        case root(rootTerms):
        case makeEvent(t0, p, eCurr):
            open valid_trace(tr, pkePred);  
            if (principal2 == p && e2 == eCurr && idx2 == traceLength(tr) - 1) {
                open event_pred(principal1, e1, t1);
                open event_pred(principal2, e2, t0);
                eventUniqueContradiction(eventUniquenessWitness(e1), getEventType(e1));
            } else {
                eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t1, t0, pkePred);
            }
            close valid_trace(tr, pkePred);
        case makeCorrupt(t0, id):
            open valid_trace(tr, pkePred); 
            eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t1, t0, pkePred); 
            close valid_trace(tr, pkePred); 
        case makeMessage(t0,to,from,term):
            open valid_trace(tr, pkePred); 
            eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t1, t0, pkePred);
            close valid_trace(tr, pkePred);
        case makeDropMessage(t0, to, from, term):
            open valid_trace(tr, pkePred);
            eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t1, t0, pkePred); 
            close valid_trace(tr, pkePred);
        case makeNonce(t0, term):
            open valid_trace(tr, pkePred);
            eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t1, t0, pkePred); 
            close valid_trace(tr, pkePred);
        case makePublic(t0, term):
            open valid_trace(tr, pkePred);
            eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t1, t0, pkePred); 
            close valid_trace(tr, pkePred);
    }
}

lemma void uniqueEventsAreUniqueAtWrapper(ParameterizedEvent e1, ParameterizedEvent e2, int principal1, int principal2, int idx1, int idx2, trace<EventParams> tr, PkePred pkePred)
    requires valid_trace(tr, pkePred) &*&
        eventOccursAt(tr, principal1, e1, idx1) == true &*&
        eventOccursAt(tr, principal2, e2, idx2) == true &*&
        isUnique(getEventType(e1)) == true &*&
        eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
        getEventType(e1) == getEventType(e2); 
    ensures  valid_trace(tr, pkePred) &*&
        principal1 == principal2 &*&
        e1 == e2 &*&
        idx1 == idx2;
{
    switch (tr) {
        case root(rootTerms):
        case makeEvent(t0, p, eCurr):
            open valid_trace(tr, pkePred);  
            if (e1 == e2 && principal1 == principal2 && idx1 == idx2) { 
                // this is the good case
            } else if (principal1 == p && e1 == eCurr && idx1 == traceLength(tr) - 1) {
                eventIsContradictionHelper(e1, e2, principal1, principal2, idx2, t0, t0, pkePred);
            } else if (principal2 == p && e2 == eCurr && idx2 == traceLength(tr) - 1) {
                eventIsContradictionHelper(e2, e1, principal2, principal1, idx1, t0, t0, pkePred);
            } else {
                uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, t0, pkePred);
            }
            close valid_trace(tr, pkePred);
        case makeCorrupt(t0, id):
            open valid_trace(tr, pkePred);
            uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, t0, pkePred);
            close valid_trace(tr, pkePred); 
        case makeMessage(t0,to,from,term):
            open valid_trace(tr, pkePred);
            uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, t0, pkePred);
            close valid_trace(tr, pkePred);
        case makeDropMessage(t0, to, from, term):
            open valid_trace(tr, pkePred);
            uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, t0, pkePred);
            close valid_trace(tr, pkePred);
        case makeNonce(t0, term):
            open valid_trace(tr, pkePred);
            uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, t0, pkePred);
            close valid_trace(tr, pkePred);
        case makePublic(t0, term):
            open valid_trace(tr, pkePred);
            uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, t0, pkePred);
            close valid_trace(tr, pkePred);
    }
}

lemma void uniqueEventsAreUniqueAtInternal(Trace globalTrace, Trace snapshot, int principal1, int principal2, ParameterizedEvent e1, ParameterizedEvent e2, int idx1, int idx2)
    requires valid_trace(globalTrace, ?pkePred) &*&
        isSuffix(snapshot, globalTrace) == true &*&
        eventOccursAt(snapshot, principal1, e1, idx1) == true &*&
        eventOccursAt(snapshot, principal2, e2, idx2) == true &*&
        isUnique(getEventType(e1)) == true &*&
        eventUniquenessWitness(e1) == eventUniquenessWitness(e2) &*&
        getEventType(e1) == getEventType(e2);
    ensures  valid_trace(globalTrace, pkePred) &*&
        principal1 == principal2 &*&
        e1 == e2 &*&
        idx1 == idx2;
{
    eventOccursAtMonotonic(snapshot, globalTrace, principal1, e1, idx1);
    eventOccursAtMonotonic(snapshot, globalTrace, principal2, e2, idx2);
    uniqueEventsAreUniqueAtWrapper(e1, e2, principal1, principal2, idx1, idx2, globalTrace, pkePred);
}
@*/
