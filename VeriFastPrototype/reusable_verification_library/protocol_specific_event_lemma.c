//@ #include "protocol_specific_event_lemma.gh"

/* PROTOCOL-SPECIFIC INSTANTIATION OF THIS LIBRARY MUST PROVE THE FOLLOWING LEMMA:
lemma void eventPurePredMonotonic(Trace t1, Trace t2, int principal, ParameterizedEvent e, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& event_pure_pred(e, principal, t1) == true &*& PkeCtxt(pkePred);
    ensures event_pure_pred(e, principal, t2) == true &*& PkeCtxt(pkePred);
{
    // protocol-specific proof
}
*/
