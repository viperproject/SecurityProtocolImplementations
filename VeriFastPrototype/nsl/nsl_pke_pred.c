//@ #include "nsl_pke_pred.gh"


/*@
// we give `PkeCtxt` here a body:
predicate PkeCtxt(PkePred p) =
    p == pkePred;

lemma void getPkeCtxt()
    requires true;
    ensures  PkeCtxt(pkePred);
{
    close PkeCtxt(pkePred);
}

lemma void leakPkeCtxt()
    requires PkeCtxt(pkePred);
    ensures  true;
{
    open PkeCtxt(pkePred);
}

lemma void learnPkeCtxt(PkePred p)
    requires PkeCtxt(p);
    ensures  PkeCtxt(p) &*& p == pkePred;
{
    open PkeCtxt(p);
    getPkeCtxt();
}

lemma void eventOccursImpliesEventOccursFinishI(Trace snap, int idA, int idB, Term naT, Term nbT)
    requires eventOccurs(snap, idA, newEvent(FINISHI, FinishIParams(idA, idB, naT, nbT))) == true;
    ensures  eventOccursFinishI(snap, idB, nbT) == true;
{
    switch(snap) {
        case root(root_terms):
        case makeEvent(t0, p, e):
            switch(e) {
                case newEvent(type, params):
                    if (!eventOccursFinishIHelper(params, idB, nbT, p) || type != FINISHI) {
                        eventOccursImpliesEventOccursFinishI(t0, idA, idB, naT, nbT);
                    }
            }
        case makeCorrupt(t0, id): eventOccursImpliesEventOccursFinishI(t0, idA, idB, naT, nbT);
        case makeMessage(t0, to, from, term): eventOccursImpliesEventOccursFinishI(t0, idA, idB, naT, nbT);
        case makeDropMessage(t0, to, from, term): eventOccursImpliesEventOccursFinishI(t0, idA, idB, naT, nbT);
        case makeNonce(t0, term): eventOccursImpliesEventOccursFinishI(t0, idA, idB, naT, nbT);
        case makePublic(t0, term): eventOccursImpliesEventOccursFinishI(t0, idA, idB, naT, nbT);
    }
}

lemma void eventOccursFinishIMonotonic(trace<EventParams> tr,trace<EventParams> tr2, int b, Term nb)
    requires isSuffix(tr, tr2) == true && eventOccursFinishI(tr, b, nb);
    ensures eventOccursFinishI(tr2, b, nb) == true;
{
    switch (tr2) {
        case root(root_terms): 
        case makeEvent(t0, pr, e):
            switch (e) {
                case newEvent(type, params): 
                    if (type == FINISHI && eventOccursFinishIHelper(params, b, nb, pr)) {
                        assert eventOccursFinishI(tr2, b, nb) == true;
                    } else if(tr2 != tr) {
                        eventOccursFinishIMonotonic(tr, t0, b, nb);
                    }
            };
        case makeCorrupt(t0, id):
            if (tr2 != tr) {
                eventOccursFinishIMonotonic(tr, t0, b, nb);
            }                                       
        case makeMessage(t0,to,from,term):
            if (tr2 != tr) {
                eventOccursFinishIMonotonic(tr, t0, b, nb);
            }  
        case makeDropMessage(t0, to, from, term):
            if (tr2 != tr) {
                eventOccursFinishIMonotonic(tr, t0, b, nb);
            }  
        case makeNonce(t0, term):
            if (tr2 != tr) {
                eventOccursFinishIMonotonic(tr, t0, b, nb);
            }  
        case makePublic(t0, term):
            if (tr2 != tr) {
                eventOccursFinishIMonotonic(tr, t0, b, nb);
            }  
    }
}

lemma void ppredMonotonic(Trace t1, Trace t2, Term plaintext, Term pk, int skOwner)
    requires isSuffix(t1, t2) == true && ppred(t1, plaintext, pk, skOwner) == true;
    ensures  ppred(t2, plaintext, pk, skOwner) == true;
{
    switch (plaintext) {
        case integer(value): 
        case stringTerm(str): 
        case encrypt(enc, pt): 
        case hash(term): 
        case publicKey(str_k):  
        case nonce(bytes, l): 
        case tuple2(term1, term2):
            if (isMsg3(plaintext, pk)) {
                eventOccursFinishIMonotonic(t1, t2, skOwner, term2);
            }
        case tuple3(term1, term2, term3):
            if (isMsg1(plaintext, pk)) {
                nonceOccursMonotonic(t1, t2, term2, Readers(cons(getInteger(term3), cons(skOwner, nil))));
                eventOccursMonotonic(t1, t2, getInteger(term3), newEvent(INITIATE, InitiateParams(getInteger(term3), skOwner, term2)));
            }
        case tuple4(term1, term2, term3, term4):  
    		if (isMsg2(plaintext, pk)) {
                nonceOccursMonotonic(t1, t2, term3, Readers(cons(skOwner, cons(getInteger(term4), nil)))) ;
                eventOccursMonotonic(t1, t2, getInteger(term4), newEvent(RESPOND, RespondParams(skOwner, getInteger(term4), term2, term3)));
            }
    } 
}

lemma void pkePredHelperMonotonic(Trace t1, trace<EventParams> t2,  Term plaintext, Term pk, Label l)
requires isSuffix(t1, t2) == true && pkePredHelper(t1, plaintext, pk, l) == true;
ensures  pkePredHelper(t2, plaintext, pk, l) == true;
{
    switch (l) {
        case Public: 
        case Readers(list_readers):
            switch (list_readers) {
                case nil: 
                case cons(x, xs):
                    if (ppred(t1,  plaintext, pk, x)) {
                        ppredMonotonic(t1, t2, plaintext, pk, x);
                    }
                    // if (pkePredHelper2(t1, plaintext, pk, xs)) {
                    //     pkePredHelper2Monotonic(t1, t2, plaintext, pk, xs);
                    // }
            };
    }
}

lemma void pkeMonotonic(Trace t1, Trace t2, Term ptxt, Term pk, PkePred pkePred)
    requires isSuffix(t1, t2) == true && pkePred(t1, ptxt, pk) == true &*& PkeCtxt(pkePred);
    ensures pkePred(t2,  ptxt, pk) == true &*& PkeCtxt(pkePred);
{
    open PkeCtxt(pkePred);
    pkePredHelperMonotonic(t1, t2, ptxt, pk, getSkLabel(pk));
    close PkeCtxt(pkePred);
}
@*/
