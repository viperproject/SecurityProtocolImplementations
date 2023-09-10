//@ #include "trace_invariant.gh"
//@ #include "protocol_specific_event_lemma.gh"

/*@
lemma void eventPredMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, int principal, ParameterizedEvent e, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& event_pred(principal, e, t1) &*& PkeCtxt(pkePred);
    ensures event_pred(principal, e, t2) &*& PkeCtxt(pkePred);
{
	open event_pred(principal, e, t1);
	eventPurePredMonotonic(t1, t2, principal, e, pkePred);
	close event_pred(principal, e, t2);
}

lemma void messageInvMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, int to, int from, Term term, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& messageInv(to, from, term,t1, pkePred) == true &*& PkeCtxt(pkePred);
    ensures  messageInv(to, from, term,t2, pkePred) == true &*& PkeCtxt(pkePred);
{
    isPublishableMonotonic(t1, t2, term, pkePred);
}
@*/
