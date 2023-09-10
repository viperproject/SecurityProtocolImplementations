#ifndef IO
#define IO

#include <stdbool.h>
//@ #include "bytes.gh"
//@ #include "trace_entry.gh"
//@ #include "trace_entry_helpers.gh"


struct IoLib;

/*@
predicate IoLibMem(struct IoLib *lib;);
@*/

// provides functions that model the I/O operations.

// struct IoLib *createIoLibResponder(int peerId, int portNr);
struct IoLib *createIoLib(bool isInitiator, int peerId, char *responderAddress, int responderPort);
//@ requires [?f]string(responderAddress, ?addr_content) &*& 0 < responderPort;
//@ ensures  result != 0 ? IoLibMem(result) : emp;

void IoLib_free(struct IoLib *lib);

bool io_send(struct IoLib *lib, int idSender, int idReceiver, char *msg, unsigned int msg_len);
/*@ requires [?f]IoLibMem(lib) &*& exists<Trace>(?snap) &*&
        exists<Term>(?msgT) &*& [?g]chars(msg, msg_len, ?msgBytes) &*& gamma(msgT) == msgBytes &*&
        snap == makeMessage(_, idReceiver, idSender, msgT); @*/
/*@ ensures  [f]IoLibMem(lib) &*& exists<Trace>(snap) &*&
        exists<Term>(msgT) &*& [g]chars(msg, msg_len, msgBytes); @*/

char *io_receive(struct IoLib *lib, int idSender, int idReceiver, unsigned int *msg_len);
//@ requires [?f]IoLibMem(lib) &*& exists<Trace>(?snap) &*& *msg_len |-> _;
/*@ ensures  [f]IoLibMem(lib) &*& exists<Trace>(snap) &*& *msg_len |-> ?res_len &*&
        result != 0 ?
            (exists<Term>(?msgT) &*& chars(result, res_len, ?msgBytes) &*&
                malloc_block_chars(result, res_len) &*&
                gamma(msgT) == msgBytes &*&
                msgOccurs(msgT, idReceiver, idSender, snap) == true) :
            emp; @*/

void print_hex(char *desc, char *buf, unsigned int len);
//@ requires [?f]string(desc, ?desc_content) &*& [?g]chars(buf, len, ?lenBytes);
//@ ensures  [f]string(desc, desc_content) &*& [g]chars(buf, len, lenBytes);

#endif
