#include "crypto.h"
#include <openssl/decoder.h>
#include <openssl/pem.h>
#include <openssl/rand.h>

// note that implementations in this file are trusted, i.e., not verified.

char *createNonce()
{
    unsigned char *res = malloc(NonceLength);
    if (res == NULL) {
        return NULL;
    }
    int success = RAND_bytes(res, NonceLength);
    if (success != 1) {
        free(res);
        return NULL;
    }
    return (char *)res;
}

struct keypair *generatePkeKey()
{
    struct keypair *res = malloc(sizeof(struct keypair));
    if (res == NULL) {
        return NULL;
    }

    EVP_PKEY *pkey = EVP_RSA_gen(4096);
    if (pkey == NULL) {
        free(res);
        return NULL;
    }

    // compute length and allocate corresponding memory for secret key
    int sk_len = i2d_PrivateKey(pkey, NULL);
    unsigned char *sk = malloc(sk_len);
    if (sk == NULL) {
        free(res);
        EVP_PKEY_free(pkey);
        return NULL;
    }
    // extract secret key
    unsigned char *tmp = sk;
    int bytes_written = i2d_PrivateKey(pkey, &tmp); // because `tmp` will be modified
    if (bytes_written != sk_len) {
        free(res);
        EVP_PKEY_free(pkey);
        free(sk);
        return NULL;
    }
    
    // compute length and allocate corresponding memory for public key
    int pk_len = i2d_PublicKey(pkey, NULL);
    unsigned char *pk = malloc(pk_len);
    if (pk == NULL) {
        free(res);
        EVP_PKEY_free(pkey);
        free(sk);
        return NULL;
    }
    // extract public key
    tmp = pk;
    bytes_written = i2d_PublicKey(pkey, &tmp); // because `tmp` will be modified
    if (bytes_written != pk_len) {
        free(res);
        EVP_PKEY_free(pkey);
        free(sk);
        free(pk);
        return NULL;
    }
    
    EVP_PKEY_free(pkey);
    res->pk = (char *)pk;
    res->pk_len = pk_len;
    res->sk = (char *)sk;
    res->sk_len = sk_len;
    return res;
}

// if result is non-NULL, it's a zero-terminated string of
// length (not counting the zero terminator) `(len + 2)/3*4 + 1`
char *base64Encode(const unsigned char *data, const unsigned int len) {
    unsigned int out_len = (len + 2)/3*4 + 1; // incl. padding to a number divisible by 4
    printf("len: %d, out_len: %d\n", len, out_len);
    char* res = malloc(out_len);
    if (res == NULL) { 
        return NULL;
    }
    int bytes_written = EVP_EncodeBlock((unsigned char *)res, data, len);
    if (bytes_written != out_len - 1) { // bytes_written does not include the NUL terminator
        free(res);
        return NULL;
    }
    return res;
}

// if result is non-NULL, it's a pointer to a buffer of size `strlen(str)/4*3`.
unsigned char *base64Decode(const char *str) {
    unsigned char* res = malloc(strlen(str)/4*3);
    if (res == NULL) {
        return NULL;
    }
    int bytes_written = EVP_DecodeBlock(res, (unsigned char *)str, strlen(str));
    if (bytes_written != strlen(str)/4*3) {
        free(res);
        return NULL;
    }
    return res;
}

/** 
  * extracts an RSA private key (PKCS #1, ASN.1 DER format) from a
  * a base64 encoded string to a PKCS#8 unencrypted PrivateKeyInfo format.
  * The result can be easily turned into a EVP_PKEY by calling `i2d_PrivateKey`.
  */
char *parsePKCS1PrivateKey(const char *str, unsigned int *sk_len) {
    unsigned char* decoded_bytes = base64Decode(str);
    if (decoded_bytes == NULL) {
        return NULL;
    }

    EVP_PKEY *pkey = NULL;
    const char *format = "DER";
    const char *structure = "type-specific";
    const char *keytype = "RSA";
    OSSL_DECODER_CTX *ctx = OSSL_DECODER_CTX_new_for_pkey(&pkey, format, structure,
                                                          keytype,
                                                          OSSL_KEYMGMT_SELECT_KEYPAIR,
                                                          NULL, NULL);
    if (ctx == NULL) {
        free(decoded_bytes);
        return NULL;
    }
    const unsigned char *const_decoded_bytes = decoded_bytes;
    size_t len = strlen(str)/4*3;
    int success = OSSL_DECODER_from_data(ctx, &const_decoded_bytes, &len);
    free(decoded_bytes);
    if (success != 1) {
        OSSL_DECODER_CTX_free(ctx);
        return NULL;
    }
    OSSL_DECODER_CTX_free(ctx);
    if (pkey == NULL) {
        return NULL;
    }
    // first compute length:
    *sk_len = i2d_PrivateKey(pkey, NULL);
    unsigned char *sk = malloc(*sk_len);
    if (sk == NULL) {
        EVP_PKEY_free(pkey);
        return NULL;
    }
    unsigned char *tmp = sk;
    int bytes_written = i2d_PrivateKey(pkey, &tmp); // because `tmp` will be modified
    EVP_PKEY_free(pkey);
    if (bytes_written != *sk_len) {
        free(sk);
        return NULL;
    }
    return (char *)sk;
}

char *getPublicKey(char *sk, unsigned int sk_len, unsigned int *pk_len)
{
    const unsigned char *u_sk = (const unsigned char *)sk;
    EVP_PKEY *pkey = d2i_PrivateKey(EVP_PKEY_RSA, NULL, &u_sk, sk_len);
    if (pkey == NULL) {
        return NULL;
    }
    // first compute length:
    *pk_len = i2d_PublicKey(pkey, NULL);
    unsigned char *pk = malloc(*pk_len);
    if (pk == NULL) {
        EVP_PKEY_free(pkey);
        return NULL;
    }
    unsigned char *tmp = pk;
    int bytes_written = i2d_PublicKey(pkey, &tmp); // because `tmp` will be modified
    EVP_PKEY_free(pkey);
    if (bytes_written != *pk_len) {
        free(pk);
        return NULL;
    }
    return (char *)pk;
}

/** 
  * extracts an RSA public key (PKIX, ASN.1 DER format) from a
  * a base64 encoded string to a PKCS#8 unencrypted SubjectPublicKeyInfo format.
  * The result can be easily turned into a EVP_PKEY by calling `i2d_PublicKey`.
  */
char *parsePKIXPublicKey(const char *str, unsigned int *pk_len) {
    unsigned char* decoded_bytes = base64Decode(str);
    if (decoded_bytes == NULL) {
        return NULL;
    }
    const unsigned char *const_decoded_bytes = decoded_bytes;
    EVP_PKEY *pkey = d2i_PUBKEY(NULL, &const_decoded_bytes, strlen(str)/4*3);
    free(decoded_bytes);
    if (pkey == NULL) {
        return NULL;
    }
    // first compute length:
    *pk_len = i2d_PublicKey(pkey, NULL);
    unsigned char *pk = malloc(*pk_len);
    if (pk == NULL) {
        EVP_PKEY_free(pkey);
        return NULL;
    }
    unsigned char *tmp = pk;
    int bytes_written = i2d_PublicKey(pkey, &tmp); // because `tmp` will be modified
    EVP_PKEY_free(pkey);
    if (bytes_written != *pk_len) {
        free(pk);
        return NULL;
    }
    return (char *)pk;
}

char *enc(char *msg, unsigned int msg_len, const char *pk, unsigned int pk_len, unsigned int *ciphertext_len)
{
    const unsigned char *u_pk = (const unsigned char *)pk;
    EVP_PKEY *pkey = d2i_PublicKey(EVP_PKEY_RSA, NULL, &u_pk, pk_len);
    if (pkey == NULL) {
        return NULL;
    }

    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new(pkey, NULL);
    if (ctx == NULL) {
        EVP_PKEY_free(pkey);
        return NULL;
    }

    int success = EVP_PKEY_encrypt_init(ctx);
    if (success != 1) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    success = EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING);
    if (success != 1) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    size_t len = 0;
    success = EVP_PKEY_encrypt(ctx, NULL, &len, (const unsigned char *)msg, msg_len);
    if (success != 1) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    unsigned char *ciphertext = malloc(len);
    if (ciphertext == NULL) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    success = EVP_PKEY_encrypt(ctx, ciphertext, &len, (const unsigned char *)msg, msg_len);
    EVP_PKEY_CTX_free(ctx);
    if (success != 1) {
        EVP_PKEY_free(pkey);
        free(ciphertext);
        return NULL;
    }

    *ciphertext_len = len;
    return (char *)ciphertext;
}

char *dec(char *ciphertext, unsigned int ciphertext_len, const char *sk, unsigned int sk_len, unsigned int *plaintext_len)
//@ requires [?f]chars(ciphertext, ?ciphertextSize, ?ciphertext_bytes) &*& [?g]chars(sk, SkLength, ?sk_bytes);
/*@ ensures  [f]chars(ciphertext, ciphertextSize, ciphertext_bytes) &*& [g]chars(sk, SkLength, sk_bytes) &*&
        result != 0 ? (chars(result, ?msgSize, ?msg_bytes) &*&
            malloc_block_chars(result, msgSize) &*&
            ciphertext_bytes == encryptB(publicKeyB(sk_bytes), msg_bytes)) :
        emp; @*/
{
    const unsigned char *u_sk = (const unsigned char *)sk;
    EVP_PKEY *pkey = d2i_PrivateKey(EVP_PKEY_RSA, NULL, &u_sk, sk_len);
    if (pkey == NULL) {
        return NULL;
    }
    
    EVP_PKEY_CTX *ctx = EVP_PKEY_CTX_new(pkey, NULL);
    if (ctx == NULL) {
        EVP_PKEY_free(pkey);
        return NULL;
    }

    int success = EVP_PKEY_decrypt_init(ctx);
    if (success != 1) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    success = EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING);
    if (success != 1) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    size_t len = 0;
    success = EVP_PKEY_decrypt(ctx, NULL, &len, (const unsigned char *)ciphertext, ciphertext_len);
    if (success != 1) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }

    unsigned char *plaintext = malloc(len);
    if (plaintext == NULL) {
        EVP_PKEY_CTX_free(ctx);
        EVP_PKEY_free(pkey);
        return NULL;
    }
    success = EVP_PKEY_decrypt(ctx, plaintext, &len, (const unsigned char *)ciphertext, ciphertext_len);
    EVP_PKEY_CTX_free(ctx);
    if (success != 1) {
        EVP_PKEY_free(pkey);
        free(plaintext);
        return NULL;
    }
    
    *plaintext_len = len;
    return (char *)plaintext;
}
