//@ #include "protocol_specific_definitions.gh"

/*@
// by verifying this lemma (as part of the library), we check that the
// `PROTOCOL_SPECIFIC_VERIFICATION` macro is indeed not set and thus
// ensure that we treat all protocol-specific (lemma, predicate, and
// fixpoint functions) as abstract.

lemma void protocol_verification_macro_unset_while_verifying_library()
    requires true;
    ensures true;
{
    #ifdef PROTOCOL_SPECIFIC_VERIFICATION 	
    assert false;
    #else
    assert true;
    #endif
}
@*/
