//@ #include "labeling.gh"
//@ #include "protocol_specific_pke_lemma.gh"
//@ #include "subset_helpers.gh"

/*@
lemma void canFlowInternalReflexive(Label l1, list<int>corruptIds)
    requires true;
    ensures canFlowInternal(l1, l1, corruptIds) == true;
{
    switch (l1) {
        case Public:
        case Readers(l1_readers):
    };
}

lemma void canFlowReflexive<t>(Label l1, trace<EventParams> t)
    requires true;
    ensures canFlow(t, l1, l1) == true;
{
    canFlowInternalReflexive(l1, getCorruptIds(t));
}

lemma void canFlowMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Label l1, Label l2)
    requires isSuffix(t1, t2) == true && canFlow(t1, l1, l2) == true;
    ensures  canFlow(t2, l1, l2) == true;
{
    switch (l1) {
        case Public:
            canFlow(t2, l1, l2);
        case Readers(l1_readers):
            switch (l2) {
  				case Public:
                    getCorruptIdsMonotonic(t1, t2);
  				    subset_intersection(getCorruptIds(t1), getCorruptIds(t2));                                               
                    subset_intersection_helper(getCorruptIds(t1), getCorruptIds(t2), l1_readers);
                case Readers(l2_readers): 
  				    getCorruptIdsMonotonic(t1, t2); 
  			        if (containsIds(l1_readers, l2_readers)) {
                        // no body needed
                    } else {
  			            getCorruptIdsMonotonic(t1, t2);
                        subset_intersection(getCorruptIds(t1), getCorruptIds(t2));
                        subset_intersection_helper(getCorruptIds(t1), getCorruptIds(t2), l1_readers);
  			        }
            }
    }
}

lemma void flowsToPublicCanFlow(trace<EventParams> tr, Label l1, Label l2)
    requires canFlow(tr, l1, Public) == true;
    ensures  canFlow(tr, l1, l2) == true;
{
    switch (l1) {
        case Public: 
        case Readers(l1_readers):
            switch (l2) {
   			    case Public: 
   				case Readers(l2_readers): 
   	        }
    }
}

lemma void canFlowTransitive(trace<EventParams> tr, Label l1, Label l2, Label l3)
    requires canFlow(tr, l1, l2) == true &*& canFlow(tr, l2, l3) == true; 
    ensures canFlow(tr, l1, l3) == true;
{
    switch(l1) {
        case Public:
            canFlowInternal(l1, l2, getCorruptIds(tr));
        case Readers(l1_readers):
            switch (l2) {
  			    case Public:
                    flowsToPublicCanFlow(tr, l1, l3);
  				case Readers(l2_readers):
                    switch (l3) {
  						case Public:
                            if (canFlow(tr, l2, Public) && canFlow(tr, l1, l2)) {
       							if(containsCorruptId(getCorruptIds(tr), l1_readers)) {
       								// no body needed				    
       							} else {
       								assert containsIds(l1_readers, l2_readers) == true;
       								assert subset(l2_readers, l1_readers) == true;
       								assert containsCorruptId(getCorruptIds(tr), l2_readers) == true;
       								switch (intersection(getCorruptIds(tr), l2_readers)) {
                 						case nil: 
                 						case cons(cID, xs):
                 							assert mem(cID, intersection(getCorruptIds(tr), l2_readers)) == true;
                 						    mem_intersection(cID, getCorruptIds(tr), l2_readers);
                 						    mem_subset(cID, l2_readers, l1_readers);
                 							mem_intersection(cID, getCorruptIds(tr), l1_readers);
       								        assert containsCorruptId(getCorruptIds(tr), l1_readers) == true;
       								        assert canFlow(tr, l1, l3) == true;
       							    }
       							}
    						}
  						case Readers(l3_readers): {
  							if (containsCorruptId(getCorruptIds(tr),l2_readers)) {
  							    if(containsCorruptId(getCorruptIds(tr), l1_readers)) {
  							        // no body needed
  							    } else if (containsIds(l1_readers, l2_readers)) {
  							        switch (intersection(getCorruptIds(tr), l2_readers)) {
                 						case nil: 
                 						case cons(cID, xs):
                 							assert mem(cID, intersection(getCorruptIds(tr), l2_readers)) == true;
                 						    mem_intersection(cID, getCorruptIds(tr), l2_readers);
                 						    assert mem(cID, getCorruptIds(tr)) == true;
                 						    mem_subset(cID, l2_readers, l1_readers);                 							   
                 							mem_intersection(cID, getCorruptIds(tr), l1_readers);
       								}
  							    }
  							} else if (containsIds(l2_readers, l3_readers)) {
  							    if (containsCorruptId(getCorruptIds(tr), l1_readers)) {
                                    // no body needed
  							    } else if (containsIds(l1_readers, l2_readers)){
  							        subset_trans(l3_readers, l2_readers, l1_readers);		
  							    }
  							}
  						}
  				    }
            };
    }
}

lemma void canFlowFlowsToPublic(trace<EventParams> tr, Label l1,Label l2) 
    requires canFlow(tr, l2, Public) && canFlow(tr, l1, l2);
    ensures canFlow(tr, l1,Public) == true;
{
    if (canFlow(tr, l2, Public) && canFlow(tr, l1, l2)) {
        canFlowTransitive(tr, l1, l2, Public);
    }
}

lemma void isValidMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term term, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& isValid(t1, term, pkePred) == true &*& PkeCtxt(pkePred);
    ensures  isValid(t2, term, pkePred) == true &*& PkeCtxt(pkePred);
{
    switch (term) {
        case integer(value): 
    	case stringTerm(str): 
        case encrypt(pk, plaintext):
            if (pkePred(t1, plaintext, pk) == true) {  
                pkeMonotonic(t1, t2, plaintext, pk, pkePred);
                assert pkePred(t2, plaintext, pk) == true;
            }
            if (canFlow(t1, getLabel(plaintext), Public) == true) {
                isValidMonotonic(t1, t2, plaintext, pkePred); 
                canFlowMonotonic(t1, t2, getLabel(plaintext), Public); 
            }
            isValidMonotonic(t1, t2, pk, pkePred); 
            isValidMonotonic(t1, t2, plaintext, pkePred); 
            canFlowMonotonic(t1, t2,getLabel(plaintext), getSkLabel(pk));
        case hash(ht):
            isValidMonotonic(t1, t2, ht, pkePred);
    	case publicKey(skKey):
            isValidMonotonic(t1, t2, skKey, pkePred); 
        case nonce(nt, l):
            onlyNonceOccursMonotonic(t1, t2, term);
        case tuple2(Term1, Term2):
            isValidMonotonic(t1, t2, Term1, pkePred); 
            isValidMonotonic(t1, t2, Term2, pkePred); 
        case tuple3(Term1, Term2, Term3):
            isValidMonotonic(t1, t2, Term1, pkePred); 
            isValidMonotonic(t1, t2, Term2, pkePred);
            isValidMonotonic(t1, t2, Term3, pkePred);
        case tuple4(Term1, Term2, Term3, Term4):
            isValidMonotonic(t1, t2, Term1, pkePred); 
            isValidMonotonic(t1, t2, Term2, pkePred);
            isValidMonotonic(t1, t2, Term4, pkePred);
            isValidMonotonic(t1, t2, Term3, pkePred); 
   }
}

lemma void isLabeledMonotonic(Term t, trace<EventParams> tr1, trace<EventParams> tr2, Label l, PkePred pkePred)
    requires isSuffix(tr1, tr2) == true &*& isLabeled(t, tr1, l, pkePred) == true &*& PkeCtxt(pkePred);
    ensures  isLabeled(t, tr2, l, pkePred) == true &*& PkeCtxt(pkePred);
{
    isValidMonotonic(tr1, tr2, t, pkePred);
}

lemma void isMsgMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term term, Label label, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& isMsg(t1, term, label, pkePred) == true &*& PkeCtxt(pkePred);
    ensures  isMsg(t2, term, label, pkePred) == true &*& PkeCtxt(pkePred);
{
    isValidMonotonic(t1, t2, term, pkePred);
	canFlowMonotonic(t1, t2, getLabel(term), label);
}

lemma void isMsgTransitive(trace<EventParams> tr, Term t1, Label l1, Label l2, PkePred pkePred)
    requires isMsg(tr, t1, l1, pkePred) && canFlow(tr, l1, l2);
    ensures isMsg(tr, t1, l2, pkePred) == true;
{
    canFlowTransitive(tr, getLabel(t1), l1, l2);
}

lemma void isPublishableMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2, Term term, PkePred pkePred)
    requires isSuffix(t1, t2) == true &*& isPublishable(t1, term, pkePred) == true &*& PkeCtxt(pkePred);
    ensures isPublishable(t2, term, pkePred) == true &*& PkeCtxt(pkePred);
{
    isMsgMonotonic(t1, t2, term, Public, pkePred);
}

lemma void isSecretKeyMonotonic(Trace tr1, Trace tr2, int id, Term skT, int c, PkePred pkePred)
    requires isSecretKey(tr1, id, skT, c, pkePred) == true &*& isSuffix(tr1, tr2) == true &*& c == 1 &*& PkeCtxt(pkePred);
    ensures  isSecretKey(tr2, id, skT, c, pkePred) == true &*& PkeCtxt(pkePred);
{
    isValidMonotonic(tr1, tr2, skT, pkePred);
}

lemma void isPublicKeyMonotonic(Trace tr1, Trace tr2, int id, Term skT, int c, PkePred pkePred)
  requires isPublicKey(tr1, id, publicKey(skT), skT, c, pkePred) == true &*& isSuffix(tr1, tr2) == true &*& c == 1 &*& PkeCtxt(pkePred);
  ensures  isPublicKey(tr2, id, publicKey(skT), skT, c, pkePred) == true &*& PkeCtxt(pkePred);  
{
    isPublishableMonotonic(tr1, tr2, publicKey(skT), pkePred);
}

lemma void ciphertextIsPublishable(trace<EventParams> t,  Term msg, Term pk, PkePred pkePred)
    requires canEncrypt(t, msg, pk, pkePred) || (isPublishable(t, msg, pkePred) && isPublishable(t, pk, pkePred));
    ensures isPublishable(t, encrypt(pk, msg), pkePred) == true;
{
    if (isPublishable(t, msg, pkePred) == true) {
        flowsToPublicCanFlow(t, getLabel(msg), getSkLabel(pk));
    }
}

lemma void canDecryptWithPublicSk(trace<EventParams> tr, Term ciphertext, Term sk, int skOwner, PkePred pkePred)
    requires isPublishable(tr, ciphertext, pkePred) && isPublishable(tr, sk, pkePred);
    ensures  canDecrypt(tr, ciphertext, sk, skOwner, pkePred) == true;
{
    // no body needed
}

lemma void decryptSatisfiesInvariant<t>(trace<EventParams> tr, Term msg, Term sk, int skOwner, PkePred pkePred)
    requires canDecrypt(tr, encrypt(publicKey(sk), msg), sk, skOwner, pkePred) == true;
    ensures  wasDecrypted(tr, msg, sk, skOwner, pkePred) == true;
{
    // no body needed
}

lemma void plaintextIsPublishableForPublicSk(trace<EventParams> tr, Term msg, Term sk, int skOwner, PkePred pkePred)
    requires isPublishable(tr, encrypt(publicKey(sk), msg), pkePred) && isPublishable(tr, sk, pkePred);
    ensures  isPublishable(tr, msg, pkePred) == true;
{
    Label plaintextLabel = getLabel(msg);
    Label skLabel = getLabel(sk);
    canFlowTransitive(tr, plaintextLabel, skLabel, Public);
}

lemma void publishableImpliesCorruption(trace<EventParams> t,  Term term, Label l, list<int> ids, PkePred pkePred)
    requires isPublishable(t, term, pkePred) && l == Readers(ids) && canFlow(t, l, getLabel(term));
    ensures  containsCorruptId(getCorruptIds(t), ids) == true;
{
    Label TermL = getLabel(term);
    list<int> corruptIds = getCorruptIds(t);
    assert canFlow(t, TermL, Public) == true;
    flowsToPublicCanFlow(t, TermL, l);
    canFlowTransitive(t, l, TermL, Public);
}
@*/
