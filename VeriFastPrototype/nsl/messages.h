#ifndef MESSAGES
#define MESSAGES

#include "crypto.h"


struct Msg1 {
    char* Na;
    int idA;
};

struct Msg2 {
    char* Na;
    char* Nb;
    int idB;
};

struct Msg3 {
    char* Nb;
}; 

char *marshalMsg1(struct Msg1* msg, unsigned int *msg_len);
/*@ requires [?f]msg->Na |-> ?NaT &*& chars(NaT, NonceLength, ?msgBytes) &*&
        *msg_len |-> _ &*&
        [f]msg->idA |-> ?id; @*/
/*@ ensures  [f]msg->Na |-> NaT &*& chars(NaT, NonceLength, msgBytes) &*&
        *msg_len |-> ?res_len &*&
        [f]msg->idA |-> id &*&
        (result != 0 ?
            chars(result, res_len, ?resultBytes) &*&
                malloc_block_chars(result, res_len) &*&
                res_len >= 4 + NonceLength &*&
                resultBytes == tuple3B(integerB(1), msgBytes, integerB(id))
            : true); @*/
    
struct Msg1 *unmarshalMsg1(char *packet, unsigned int msg_len);
//@ requires [?f]chars(packet, msg_len, ?packetBytes);
/*@ ensures  [f]chars(packet, msg_len, packetBytes) &*&
        (result != 0 ?
            result->Na |-> ?NaT &*& chars(NaT, NonceLength, ?msgBytes) &*& malloc_block_chars(NaT, NonceLength) &*&
                result->idA |-> ?id &*&
                malloc_block_Msg1(result) &*&
                packetBytes == tuple3B(integerB(1), msgBytes, integerB(id))
            : emp);
 @*/

char *marshalMsg2(struct Msg2* msg, unsigned int *msg_len);
/*@ requires [?f]msg->Na |-> ?NaT &*& chars(NaT, NonceLength, ?naBytes) &*&
        [f]msg->Nb |-> ?NbT &*& chars(NbT, NonceLength, ?nbBytes) &*&
        *msg_len |-> _ &*&
        [f]msg->idB |-> ?id; @*/
/*@ ensures  [f]msg->Na |-> NaT  &*& chars(NaT, NonceLength, naBytes) &*&
        [f]msg->Nb |-> NbT &*& chars(NbT, NonceLength, nbBytes) &*&
        *msg_len |-> ?res_len &*&
        [f]msg->idB |-> id &*& 
        (result != 0 ?
            chars(result, res_len, ?resultBytes) &*&
                malloc_block_chars(result, res_len) &*&
                res_len >= 4 + 2*NonceLength &*&
                resultBytes == tuple4B(integerB(2), naBytes, nbBytes, integerB(id))
            : true); @*/
    
struct Msg2 *unmarshalMsg2(char *packet, unsigned int msg_len);
//@ requires [?f]chars(packet, msg_len, ?packetBytes);
/*@ ensures  [f]chars(packet, msg_len, packetBytes) &*&
        (result != 0 ?
            result->Na |-> ?Na &*& chars(Na, NonceLength, ?naBytes) &*& malloc_block(Na, NonceLength) &*&
                result->Nb |-> ?Nb &*& chars(Nb, NonceLength, ?nbBytes) &*& malloc_block(Nb, NonceLength) &*&
                result->idB |-> ?id &*&
                malloc_block_Msg2(result) &*&
                packetBytes == tuple4B(integerB(2), naBytes, nbBytes, integerB(id))
            : emp); @*/

char *marshalMsg3(struct Msg3* msg, unsigned int *msg_len);
/*@ requires [?f]msg->Nb |-> ?Nb &*& [?f2]chars(Nb, NonceLength, ?msgBytes) &*&
        *msg_len |-> _; @*/
/*@ ensures  [f]msg->Nb |-> Nb &*& [f2]chars(Nb, NonceLength, msgBytes) &*&
        *msg_len |-> ?res_len &*&
        (result != 0 ?
            chars(result, res_len, ?resultBytes) &*&
                malloc_block_chars(result, res_len) &*&
                res_len >= 4 + NonceLength &*&
                resultBytes == tuple2B(integerB(3), msgBytes)
            : true); @*/
    
struct Msg3 *unmarshalMsg3(char *packet, unsigned int msg_len);
//@ requires [?f]chars(packet, msg_len, ?packetBytes);
/*@ ensures  [f]chars(packet, msg_len, packetBytes) &*&
        (result != 0 ?
            result->Nb |-> ?Nb &*& chars(Nb, NonceLength, ?msgBytes) &*& malloc_block(Nb, NonceLength) &*&
                malloc_block_Msg3(result) &*&
                packetBytes == tuple2B(integerB(3), msgBytes)
            : emp); @*/

#endif
