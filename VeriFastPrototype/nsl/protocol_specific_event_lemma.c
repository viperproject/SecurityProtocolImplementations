//@ #include "protocol_specific_event_lemma.gh"
//@ #include "nsl_pke_pred.gh"
//@ #include "subset_helpers.gh"
//@ #include "term.gh"

// this file declares the event lemmas that must be shown by a protocol after instantiating
// this library


/*@
lemma void eventPurePredHelperMonotonic<t>(EventParams params, int type, int principal, trace<EventParams> tr, trace<EventParams> t2, PkePred pkePred)
    requires isSuffix(tr, t2) == true &*& event_pure_pred_helper(params, type, principal, tr) == true &*& PkeCtxt(pkePred);
    ensures event_pure_pred_helper(params, type, principal, t2) == true &*& PkeCtxt(pkePred);
{
    learnPkeCtxt(pkePred);
    switch (params) {
        case InitiateParams(a, b, na): 
        case RespondParams(a, b, na, nb): 
        case FinishIParams(a, b, na, nb):
            isLabeledMonotonic(na, tr, t2, Readers(cons(principal, cons(b, nil))), pkePred);
            if (isLabeled(nb, tr, Readers(cons(principal, cons(b, nil))), pkePred)) {
                isLabeledMonotonic(nb, tr, t2, Readers(cons(principal, cons(b, nil))), pkePred);
            }
            if (isPublishable(tr, nb, pkePred)) {
                isPublishableMonotonic(tr, t2, nb, pkePred);     
            }
            if (containsCorruptId(getCorruptIds(tr), cons(principal, cons(b, nil)))) {
                getCorruptIdsMonotonic(tr, t2); 
                subset_intersection_helper(getCorruptIds(tr), getCorruptIds(t2), cons(principal, cons(b, nil)));
            }
            if (eventOccurs(tr, b, newEvent(RESPOND, RespondParams(principal, b, na, nb)))) {
                eventOccursMonotonic(tr, t2, b, newEvent(RESPOND, RespondParams(principal, b, na, nb)));
            }
        case FinishRParams(a, b, na, nb):
            if (eventOccurs(tr, principal, newEvent(RESPOND, RespondParams(a, principal, na, nb)))) {
                eventOccursMonotonic(tr, t2, principal, newEvent(RESPOND, RespondParams(a, principal, na, nb)));
            }
            if (containsCorruptId(getCorruptIds(tr),cons(a, cons(principal, nil)))) {
                getCorruptIdsMonotonic(tr, t2); 
                subset_intersection_helper(getCorruptIds(tr), getCorruptIds(t2), cons(a, cons(principal, nil)));
            }
            if (eventOccurs(tr, a, newEvent(FINISHI,  FinishIParams(a, principal, na, nb)))) {
                eventOccursMonotonic(tr, t2, a, newEvent(FINISHI,  FinishIParams(a, principal, na, nb)));
            }
    }
}

lemma void eventPurePredMonotonic(Trace t1, Trace t2, int principal, ParameterizedEvent e, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& event_pure_pred(e, principal, t1) == true &*& PkeCtxt(pkePred);
    ensures event_pure_pred(e, principal, t2) == true &*& PkeCtxt(pkePred);
{
    switch (e) { 
        case newEvent(type, params):
            eventPurePredHelperMonotonic(params, type, principal, t1, t2, pkePred);
    }
}
@*/
