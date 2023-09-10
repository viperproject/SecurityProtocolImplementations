//@ #include "protocol_specific_pke_lemma.gh"

/* PROTOCOL-SPECIFIC INSTANTIATION OF THIS LIBRARY MUST PROVE THE FOLLOWING LEMMA:
lemma void pkeMonotonic(Trace t1, Trace t2, Term ptxt, Term pk, PkePred pkePred)
    requires isSuffix(t1, t2) == true && pkePred(t1, ptxt, pk) == true &*& PkeCtxt(pkePred);
    ensures pkePred(t2,  ptxt, pk) == true &*& PkeCtxt(pkePred);
{
    // protocol-specific proof
}
*/
