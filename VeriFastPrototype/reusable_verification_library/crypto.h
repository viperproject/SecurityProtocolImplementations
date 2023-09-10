#ifndef CRYPTO
#define CRYPTO
#define NonceLength 24

//@ #include "bytes.gh"
//@ #include "event.gh"
//@ #include "term.gh"
//@ #include "trace_invariant.gh"


#define EventTypes list<int>

// Provides cryptographic functions whose specification follows our perfect cryptography assumptions

// returns a recursive predicate with a unique resources for every unique event. We add it
// as a recursive predicate since quantified permissions are not supported.
/*@
predicate eventUniquePointer(EventTypes event_types, Term nonce) =
    switch (event_types) {
        case nil:
            return true;
        case cons(event_type, xs):
            return EventUniqueResource(nonce, event_type) &*& eventUniquePointer(xs, nonce); 
    };
@*/

// in the following, we axiomatize functions typically provided by a cryptographic library.

char *createNonce();
//@ requires exists<EventTypes>(?eventTypes) &*& exists<Label>(?l) &*& distinct(eventTypes) == true;
/*@ ensures  result != 0 ?
        (chars(result, NonceLength, ?bytes_list) &*& malloc_block(result, NonceLength) &*& 
            eventUniquePointer(eventTypes, nonce(bytes_list, l)) &*&
            NonceUniqueResource(nonce(bytes_list, l)) &*&
            bytes_list == gamma(nonce(bytes_list, l))) :
        emp; @*/

struct keypair {
    char *pk;
    unsigned int pk_len;
    char *sk;
    unsigned int sk_len;
};

struct keypair *generatePkeKey();
//@ requires exists<Label>(?l);
/*@ ensures  result != 0 ?
        result->pk |-> ?pk &*& pk != 0 &*&
        result->pk_len |-> ?pk_len &*&
        result->sk |-> ?sk &*& sk != 0 &*&
        result->sk_len |-> ?sk_len &*&
        chars(pk, pk_len, ?abs_pk) &*& malloc_block(pk, pk_len) &*&
        chars(sk, sk_len, ?abs_sk) &*& malloc_block(sk, sk_len) &*&
        abs_pk == publicKeyB(abs_sk) &*&
        abs_sk == gamma(nonce(abs_sk, l)) &*&
        NonceUniqueResource(nonce(abs_sk, l)) &*&
        malloc_block_keypair(result) :
        emp; @*/

/** 
  * extracts an RSA private key (PKCS #1, ASN.1 DER format) from a
  * a base64 encoded string to a PKCS#8 unencrypted PrivateKeyInfo format.
  * The result can be easily turned into a EVP_PKEY by calling `i2d_PrivateKey`.
  */
char *parsePKCS1PrivateKey(const char *str, unsigned int *sk_len);
//@ requires [?f]string(str, ?str_content) &*& *sk_len |-> _;
//@ ensures  [f]string(str, str_content) &*& *sk_len |-> ?len &*& chars(result, len, ?res_bytes);

char *getPublicKey(char *sk, unsigned int sk_len, unsigned int *pk_len);
//@ requires [?f]chars(sk, sk_len, ?sk_bytes) &*& *pk_len |-> _;
//@ ensures  [f]chars(sk, sk_len, sk_bytes) &*& *pk_len |-> ?len &*& chars(result, len, ?res_bytes);

/** 
  * extracts an RSA public key (PKIX, ASN.1 DER format) from a
  * a base64 encoded string to a PKCS#8 unencrypted SubjectPublicKeyInfo format.
  * The result can be easily turned into a EVP_PKEY by calling `i2d_PublicKey`.
  */
char *parsePKIXPublicKey(const char *str, unsigned int *pk_len);
//@ requires [?f]string(str, ?str_content) &*& *pk_len |-> _;
//@ ensures  [f]string(str, str_content) &*& *pk_len |-> ?len &*& chars(result, len, ?res_bytes);

char *enc(char *msg, unsigned int msg_len, const char *pk, unsigned int pk_len, unsigned int *ciphertext_len);
//@ requires [?f]chars(msg, msg_len, ?msg_bytes) &*& [?g]chars(pk, pk_len, ?pk_bytes) &*& *ciphertext_len |-> _;
/*@ ensures  [f]chars(msg, msg_len, msg_bytes) &*& [g]chars(pk, pk_len, pk_bytes) &*& *ciphertext_len |-> ?ciphertextSize &*&
    result != 0 ? (chars(result, ciphertextSize, ?abs_ciphertext) &*&
        malloc_block_chars(result, ciphertextSize) &*&
        abs_ciphertext == encryptB(pk_bytes, msg_bytes)) : 
    emp; @*/

char *dec(char *ciphertext, unsigned int ciphertext_len, const char *sk, unsigned int sk_len, unsigned int *plaintext_len);
//@ requires [?f]chars(ciphertext, ciphertext_len, ?ciphertext_bytes) &*& [?g]chars(sk, sk_len, ?sk_bytes) &*& *plaintext_len |-> _;
/*@ ensures  [f]chars(ciphertext, ciphertext_len, ciphertext_bytes) &*& [g]chars(sk, sk_len, sk_bytes) &*& *plaintext_len |-> ?msgSize &*&
        result != 0 ? (chars(result, msgSize, ?msg_bytes) &*&
            malloc_block_chars(result, msgSize) &*&
            ciphertext_bytes == encryptB(publicKeyB(sk_bytes), msg_bytes)) :
        emp; @*/

#endif 
