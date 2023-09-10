#ifndef INITIATOR
#define INITIATOR

#include "labeled_library.h"


struct A {
    struct LabeledLib *labeledLib;
    int version;
    int idA; 
    char* pkA;
    unsigned int pkA_len;
    char* skA;
    unsigned int skA_len;
    int idB;
    char *pkB;
    unsigned int pkB_len;
    //@ Term skAT;
    //@ Term skBT;
};

/*@
predicate Mem(struct A* a, int version);
@*/

struct A *initA(struct IoLib *io_lib, struct TraceManager *tm, int initiator, int responder);
//@ requires IoLibMem(io_lib) &*& TraceManagerMem(tm, initiator, ?snap0, pkePred);
//@ ensures  result != 0 ? Mem(result, 0) : emp;

bool runA(struct A* a);
//@ requires Mem(a, 1);
//@ ensures  result ? Mem(a, 3) : emp;

#endif
