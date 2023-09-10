//@ #include "nonce_lemmas.gh"

/*@
lemma void nonceUniqueContradiction(Term t)
    requires NonceUniqueResource(t) &*& NonceUniqueResource(t);
    ensures false;
{
    open NonceUniqueResource(t);
    open NonceUniqueResource(t);
    assert ghost_cell(?x, _);
    merge_fractions ghost_cell(x,_); 
    ghost_cell_fraction_info(x);
}

// proves a contradiction if you have 2 of the same Nonce Resources
lemma void uniqueHelper(trace<EventParams> tr, Term t, Label l, int i, PkePred pkePred)
    requires valid_trace(tr, pkePred) &*&
        NonceUniqueResource(t) &*&
        nonceAt(tr, t, l, i) == true;
    ensures  false; 
{
    switch (tr) {
        case root(root_terms): false;
        case makeEvent(t0, pr, e):
            open valid_trace(tr, pkePred);
            uniqueHelper(t0, t, l, i, pkePred);  
            close valid_trace(tr, pkePred);
        case makeCorrupt(t0, id):
            open valid_trace(tr, pkePred);
            uniqueHelper(t0, t, l, i, pkePred);    
            close valid_trace(tr, pkePred);
        case makeMessage(t0,to,from,term):  
            open valid_trace(tr, pkePred);
            uniqueHelper(t0, t, l, i, pkePred);    
            close valid_trace(tr, pkePred);
        case makeDropMessage(t0, to, from, term):   
            open valid_trace(tr, pkePred);
            uniqueHelper(t0, t, l, i, pkePred);  
            close valid_trace(tr, pkePred);
        case makeNonce(t0, term):
            open valid_trace(tr, pkePred);
            if (term == t && traceLength(tr) == i) {
    		    nonceUniqueContradiction(t);
    			assert false; // we have reached the expected contradiction     
    		} else {
   				uniqueHelper(t0, t, l, i, pkePred);  
 				close valid_trace(tr, pkePred); 
 			}                                           
        case makePublic(t0, term):
            open valid_trace(tr, pkePred);
            uniqueHelper(t0, t, l, i, pkePred);   
            close valid_trace(tr, pkePred);
    }
}

lemma void nonceUnique(trace<EventParams> tr, Term t, Label l, int i, int j, PkePred pkePred)
	requires valid_trace(tr, pkePred) &*&
		nonceAt(tr, t, l, i) == true &*&
		nonceAt(tr, t, l, j) == true;
	ensures  valid_trace(tr, pkePred) &*& i == j;
{
	switch (tr) {
		case root(root_terms): 
		case makeEvent(t0, pr, e):
			open valid_trace(tr, pkePred);
            nonceUnique(t0, t, l, i, j, pkePred);  
            close valid_trace(tr, pkePred);
		case makeCorrupt(t0, id):
			open valid_trace(tr, pkePred);
            nonceUnique(t0, t, l,  i, j, pkePred); 
            close valid_trace(tr, pkePred);
		case makeMessage(t0,to,from,term):
			open valid_trace(tr, pkePred);
            nonceUnique(t0, t, l, i, j, pkePred);  
            close valid_trace(tr, pkePred);
		case makeDropMessage(t0, to, from, term):
			open valid_trace(tr, pkePred);
            nonceUnique(t0, t, l, i, j, pkePred);  
            close valid_trace(tr, pkePred);
		case makeNonce(t0, term):
			open valid_trace(tr, pkePred);
            if (term == t) {
				if (i == j) {
    				close valid_trace(tr, pkePred); 
    			} else if (traceLength(tr) == i) {
    				uniqueHelper(t0, t, l, j, pkePred);
    			} else if (traceLength(tr) == j) {
    				uniqueHelper(t0, t, l, i, pkePred);
				} else {
    				nonceUnique(t0, t, l, i, j, pkePred);
 					close valid_trace(tr, pkePred); 
    			}
			} else {
   				nonceUnique(t0, t, l, i, j, pkePred);
 				close valid_trace(tr, pkePred); 
 			}                                           
		case makePublic(t0, term):
			open valid_trace(tr, pkePred); 
            nonceUnique(t0, t, l, i, j, pkePred);  
            close valid_trace(tr, pkePred);
	}
}
@*/
