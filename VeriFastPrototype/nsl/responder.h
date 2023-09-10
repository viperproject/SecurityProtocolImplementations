#ifndef RESPONDER
#define RESPONDER

#include "labeled_library.h"


struct B {
    struct LabeledLib *labeledLib;
    int version;
    int idB; 
    char *pkB;
    unsigned int pkB_len;
    char *skB;
    unsigned int skB_len;
    int idA;
    char *pkA;
    unsigned int pkA_len;
    //@ Term skBT;
    //@ Term skAT;
};

/*@
predicate Mem(struct B* b, int version);
@*/

struct B *initB(struct IoLib *io_lib, struct TraceManager *tm, int initiator, int responder);
//@ requires IoLibMem(io_lib) &*& TraceManagerMem(tm, responder, ?snap0, pkePred);
//@ ensures  result != 0 ? Mem(result, 0) : emp;

bool runB(struct B* b);
//@ requires Mem(b, 1);
//@ ensures  result ? Mem(b, 3) : emp;
#endif
