//@ #include "trace_entry_helpers.gh"
//@ #include "subset_helpers.gh"


/*@
lemma void isSuffixReflexive<t>(trace<EventParams> t1)
    requires true;
    ensures  isSuffix(t1, t1) == true;
{
    switch (t1) {
        case root(root_terms):
        case makeEvent(t0, pr, e):
        case makeCorrupt(t0, id):
        case makeMessage(t0,to,from,term):
        case makeDropMessage(t0, to, from, term):
        case makeNonce(t0, term):
        case makePublic(t0, term):
    }
}

lemma void isSuffixTransitive<t>(trace<EventParams> t1, trace<EventParams> t2, trace<EventParams> t3)
    requires isSuffix(t1, t2) && isSuffix(t2, t3);
    ensures  isSuffix(t1, t3) == true;
{
    switch (t3) {
        case root(root_terms) :  
      	case makeEvent(t0, pr, e):
            if (t2 != t3) {
                isSuffixTransitive(t1, t2,  t0);
            }
      	case makeCorrupt(t0, id):
            if (t2 != t3) {
                isSuffixTransitive(t1, t2,  t0);
            }
      	case makeMessage(t0,to,from,term):
            if (t2 != t3) {
                isSuffixTransitive(t1, t2,  t0);
            }
      	case makeDropMessage(t0, to, from, term):
            if (t2 != t3) {
                isSuffixTransitive(t1, t2,  t0);
            }
      	case makeNonce(t0, term):
            if (t2 != t3) {
                isSuffixTransitive(t1, t2,  t0);
            }
      	case makePublic(t0, term):
            if (t2 != t3) {
                isSuffixTransitive(t1, t2,  t0);
            }
    }
}

lemma void rootIsSuffix<t>(trace<EventParams> tr, trace<EventParams> r)
    requires r == root(getPublicTerms(tr));
    ensures isSuffix(r, tr) == true;
{
    switch (tr) {
        case root(root_terms): 
        case makeEvent(t0, pr, e):
            rootIsSuffix(t0, r);
        case makeCorrupt(t0, id):
            rootIsSuffix(t0, r);
        case makeMessage(t0,to,from,term):
            rootIsSuffix(t0, r);
        case makeDropMessage(t0, to, from, term):
            rootIsSuffix(t0, r);
        case makeNonce(t0, term):
            rootIsSuffix(t0, r);
        case makePublic(t0, term):
            rootIsSuffix(t0, r);
    }
}

lemma void snapshot_suffix_hold_adding_message<t>(trace<EventParams> t1, trace<EventParams> bigger)
    requires bigger == makeMessage(t1, _,_,_);
    ensures  isSuffix(t1, bigger) == true;
{
    switch (bigger) {
        case root(root_terms):   
        case makeEvent(t0, pr, e): 
        case makeCorrupt(t0, id): 
        case makeMessage(t0,to,from,term):
            isSuffixReflexive(t1);
        case makeDropMessage(t0, to, from, term): 
        case makeNonce(t0, term): 
        case makePublic(t0, term): 
    }
}

lemma void eventOccursMonotonic(trace<EventParams> t1, trace<EventParams> t2, int principal, ParameterizedEvent e)
    requires isSuffix(t1, t2) == true &*& eventOccurs(t1, principal, e) == true;
    ensures eventOccurs(t2, principal, e) == true;
{
    switch (t2) {
        case root(root_terms): 
        case makeEvent(t0, p, eCurr):
            if (t2 != t1) {
                eventOccursMonotonic(t1, t0,  principal,e);
            } 
        case makeCorrupt(t0, id):
            if (t2 != t1) {
                eventOccursMonotonic(t1, t0,  principal,e);
            } 
        case makeMessage(t0,to,from,term):
            if (t2 != t1) {
                eventOccursMonotonic(t1, t0,  principal,e);
            } 
        case makeDropMessage(t0, to, from, term):
            if (t2 != t1) {
                eventOccursMonotonic(t1, t0,  principal,e);
            } 
        case makeNonce(t0, term):
            if (t2 != t1) {
                eventOccursMonotonic(t1, t0,  principal,e);
            } 
        case makePublic(t0, term):
            if (t2 != t1) {
                eventOccursMonotonic(t1, t0,  principal,e);
            } 
    }
}

lemma void eventOccursAtMonotonic(Trace t1, Trace t2, int principal, ParameterizedEvent e, int idx)
    requires isSuffix(t1, t2) == true &*& eventOccursAt(t1, principal, e, idx) == true;
    ensures  eventOccursAt(t2, principal, e, idx) == true;
{
    switch (t2) {
        case root(root_terms):
        case makeEvent(t0, p, eCurr):
            if (t2 != t1) {
                eventOccursAtMonotonic(t1, t0, principal, e, idx);
            } 
        case makeCorrupt(t0, id):
            if (t2 != t1) {
                eventOccursAtMonotonic(t1, t0, principal, e, idx);
            } 
        case makeMessage(t0,to,from,term):
            if (t2 != t1) {
                eventOccursAtMonotonic(t1, t0, principal, e, idx);
            } 
        case makeDropMessage(t0, to, from, term):
            if (t2 != t1) {
                eventOccursAtMonotonic(t1, t0, principal, e, idx);
            } 
        case makeNonce(t0, term):
            if (t2 != t1) {
                eventOccursAtMonotonic(t1, t0, principal, e, idx);
            } 
        case makePublic(t0, term):
            if (t2 != t1) {
                eventOccursAtMonotonic(t1, t0, principal, e, idx);
            } 
    }
}

lemma void eventOccursAtLemma(Trace t, int principal, ParameterizedEvent ev, int idx)
    requires eventOccursAt(t, principal, ev, idx) == true;
    ensures  eventOccurs(t, principal, ev) == true;
{
    switch (t) {
        case root(root_terms):
        case makeEvent(t0, p, eCurr):
            if (principal != p || ev != eCurr || idx != traceLength(t) - 1) {
                eventOccursAtLemma(t0, principal, ev, idx);
            }
        case makeCorrupt(t0, id):
            eventOccursAtLemma(t0, principal, ev, idx); 
        case makeMessage(t0,to,from,term):
            eventOccursAtLemma(t0, principal, ev, idx);
        case makeDropMessage(t0, to, from, term):
            eventOccursAtLemma(t0, principal, ev, idx);
        case makeNonce(t0, term):
            eventOccursAtLemma(t0, principal, ev, idx);
        case makePublic(t0, term):
            eventOccursAtLemma(t0, principal, ev, idx);
    }
}

lemma int eventOccursAtTimeLemma(Trace t, int principal, ParameterizedEvent ev)
    requires eventOccurs(t, principal, ev) == true;
    ensures  eventOccursAt(t, principal, ev, result) && result == eventOccursAtTime(t, principal, ev) - 1;
{
    switch (t) {
        case root(root_terms):
        case makeEvent(t0, p, eCurr):
            if (principal == p && ev == eCurr) {
                return traceLength(t) - 1;
            } else {
                return eventOccursAtTimeLemma(t0, principal, ev);
            }
        case makeCorrupt(t0, id):
            return eventOccursAtTimeLemma(t0, principal, ev);
        case makeMessage(t0,to,from,term):
            return eventOccursAtTimeLemma(t0, principal, ev);
        case makeDropMessage(t0, to, from, term):
            return eventOccursAtTimeLemma(t0, principal, ev);
        case makeNonce(t0, term):
            return eventOccursAtTimeLemma(t0, principal, ev);
        case makePublic(t0, term):
            return eventOccursAtTimeLemma(t0, principal, ev);
    }
}

lemma void onlyNonceOccursMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term t)
    requires isSuffix(t1, t2) == true && onlyNonceOccurs(t1, t) == true;
    ensures  onlyNonceOccurs(t2, t) == true;
{
    switch (t2) {
        case root(root_terms):
        case makeEvent(t0, pr, e):
            if (t1 != t2) {
                onlyNonceOccursMonotonic(t1, t0, t);
            }
        case makeCorrupt(t0, id):
            if (t1 != t2) {
                onlyNonceOccursMonotonic(t1, t0, t);
            }
        case makeMessage(t0,to,from,term):
            if (t1 != t2) {
                onlyNonceOccursMonotonic(t1, t0, t);
            }
        case makeDropMessage(t0, to, from, term):
            if (t1 != t2) {
                onlyNonceOccursMonotonic(t1, t0, t);
            }
        case makeNonce(t0, term):
            if (t1 != t2 && t != term) {
                onlyNonceOccursMonotonic(t1, t0, t);
            }
        case makePublic(t0, term):
            if (t1 != t2) {
                onlyNonceOccursMonotonic(t1, t0, t);
            }
    }
}

lemma void nonceOccursMonotonic(trace<EventParams> t1, trace<EventParams> t2, Term t, Label l)
    requires isSuffix(t1, t2) == true && nonceOccurs(t1, t, l) == true;
    ensures  nonceOccurs(t2, t, l) == true;
{
    onlyNonceOccursMonotonic(t1, t2, t);
}

lemma void containsCorruptIdMonotonic2<t>(list<t> corruptIds1, list<t> corruptIds2, list<t> ids)
    requires containsCorruptId(corruptIds1, ids) && subset(corruptIds1, corruptIds2);
    ensures  containsCorruptId(corruptIds2, ids) == true;
{
    subset_intersection_helper(corruptIds1, corruptIds2, ids);
}

lemma void getCorruptIdsMonotonic(trace<EventParams> t1, trace<EventParams> t2)
    requires isSuffix(t1, t2) == true;
    ensures  subset(getCorruptIds(t1), getCorruptIds(t2)) == true;
{
    switch (t2) {
        case root(root_terms):
            containsIds(getCorruptIds(t2), getCorruptIds(t1));
        case makeEvent(t0, p, e):
            if (t1 != t2) { 
                getCorruptIdsMonotonic(t1, t0); 
                subset_refl(getCorruptIds(t2));
                subset_trans(getCorruptIds(t1), getCorruptIds(t0), getCorruptIds(t2));
            } else {
                containsIds(getCorruptIds(t2), getCorruptIds(t1));
            }
        case makeCorrupt(t0, id):
            if (t1 != t2) { 
                getCorruptIdsMonotonic(t1, t0); 
                subset_refl(getCorruptIds(t2));
                subset_trans(getCorruptIds(t1), getCorruptIds(t0), getCorruptIds(t2));
            } else {
                containsIds(getCorruptIds(t2), getCorruptIds(t1));
            }
        case makeMessage(t0,to,from,term):
            if (t1 != t2) { 
                getCorruptIdsMonotonic(t1, t0); 
                assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                assert getCorruptIds(t2) == getCorruptIds(t0);
                subset_refl(getCorruptIds(t2));
                subset_trans(getCorruptIds(t1), getCorruptIds(t0), getCorruptIds(t2));
            } else {
                containsIds(getCorruptIds(t2), getCorruptIds(t1));
            }
        case makeDropMessage(t0, to, from, term):
            if (t1 != t2) { 
                getCorruptIdsMonotonic(t1, t0); 
                assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                assert getCorruptIds(t2) == getCorruptIds(t0);
                subset_refl(getCorruptIds(t2));
                subset_trans(getCorruptIds(t1), getCorruptIds(t0), getCorruptIds(t2));
            } else {
                containsIds(getCorruptIds(t2), getCorruptIds(t1));
            }
        case makeNonce(t0, term):
            if (t1 != t2) { 
                getCorruptIdsMonotonic(t1, t0); 
                assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                assert getCorruptIds(t2) == getCorruptIds(t0);
                subset_refl(getCorruptIds(t2));
                subset_trans(getCorruptIds(t1), getCorruptIds(t0), getCorruptIds(t2));
            } else {
                containsIds(getCorruptIds(t2), getCorruptIds(t1));
            }
        case makePublic(t0, term):
            if (t1 != t2) { 
                getCorruptIdsMonotonic(t1, t0); 
                assert (subset(getCorruptIds(t1), getCorruptIds(t0)) == true);
                assert getCorruptIds(t2) == getCorruptIds(t0);
                subset_refl(getCorruptIds(t2));
                subset_trans(getCorruptIds(t1), getCorruptIds(t0), getCorruptIds(t2));
            } else {
                containsIds(getCorruptIds(t2), getCorruptIds(t1));
            }
    }
}

lemma void msgOccursMonotonic<t>(Term t, int to, int from, trace<EventParams> tr, trace<EventParams> global_trace)
    requires isSuffix(tr, global_trace) && msgOccurs(t, to, from, tr);
    ensures msgOccurs(t, to, from, global_trace) == true;
{
    switch (global_trace) {
        case root(root_terms): 
        case makeEvent(t0, pr, e):
            if (global_trace != tr) {
                msgOccursMonotonic(t, to, from, tr, t0);
            }
        case makeCorrupt(t0, id):
            if (global_trace != tr) {
                msgOccursMonotonic(t, to, from, tr, t0);
            }
        case makeMessage(t0,to1,from1,term):
            if (t == term && to1 == to && from1 == from) {
                // no body needed
            } else if(global_trace != tr) {
                msgOccursMonotonic(t, to, from, tr, t0);
            }
      case makeDropMessage(t0, to1, from1, term):
        if (global_trace != tr) {
            msgOccursMonotonic(t, to, from, tr, t0);
        }
      case makeNonce(t0, term):
        if (global_trace != tr) {
            msgOccursMonotonic(t, to, from, tr, t0);
        }
      case makePublic(t0, term):
        if (global_trace != tr) {
            msgOccursMonotonic(t, to, from, tr, t0);
        }
     }
}

lemma void getPublicTermsMonotonic<t>(trace<EventParams> t1, trace<EventParams> t2)
    requires isSuffix(t1, t2) == true;
    ensures getPublicTerms(t1) == getPublicTerms(t2);
{
   switch(t2){
        case root(root_terms) : 
        case makeEvent(t0, pr, e):
            if (t1 != t2) {
                getPublicTermsMonotonic(t1, t0);
            }
        case makeCorrupt(t0, id):
            if (t1 != t2) {
                getPublicTermsMonotonic(t1, t0);
            }
        case makeMessage(t0,to,from,term):
            if (t1 != t2) {
                getPublicTermsMonotonic(t1, t0);
            }
        case makeDropMessage(t0, to, from, term):
            if (t1 != t2) {
                getPublicTermsMonotonic(t1, t0);
            }
        case makeNonce(t0, term):
            if (t1 != t2) {
                getPublicTermsMonotonic(t1, t0);
            }
        case makePublic(t0, term):
            if (t1 != t2) {
                getPublicTermsMonotonic(t1, t0);
            }
   }
}
@*/
