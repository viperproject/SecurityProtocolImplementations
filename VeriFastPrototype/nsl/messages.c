#include "messages.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <arpa/inet.h>


char *marshalMsg1(struct Msg1* msg, unsigned int *msg_len)
{
    *msg_len = sizeof(uint32_t) + NonceLength + sizeof(uint32_t);
    char *buf = malloc(*msg_len);
    if (buf == NULL) {
        return NULL;
    }

    *(uint32_t *)buf = htonl(1);
    memcpy(buf + sizeof(uint32_t), msg->Na, NonceLength);
    *(uint32_t *)(buf + sizeof(uint32_t) + NonceLength) = htonl((uint32_t)msg->idA);

    return buf;
}

struct Msg1 *unmarshalMsg1(char *packet, unsigned int msg_len)
{
    if (msg_len < sizeof(uint32_t) + NonceLength + sizeof(uint32_t)) {
        return NULL;
    }

    uint32_t tag = ntohl(*(uint32_t *)packet);
    if (tag != 1) {
        return NULL;
    }

    char *na = malloc(NonceLength);
    if (na == NULL) {
        return NULL;
    }

    memcpy(na, packet + sizeof(uint32_t), NonceLength);

    int idA = (int)ntohl(*(uint32_t *)(packet + sizeof(uint32_t) + NonceLength));

    struct Msg1 *msg1 = malloc(sizeof(struct Msg1));
    if (msg1 == NULL) {
        free(na);
        return NULL;
    }

    msg1->Na = na;
    msg1->idA = idA;

    return msg1;
}

char *marshalMsg2(struct Msg2* msg, unsigned int *msg_len)
{
    *msg_len = sizeof(uint32_t) + 2 * NonceLength + sizeof(uint32_t);
    char *buf = malloc(*msg_len);
    if (buf == NULL) {
        return NULL;
    }

    *(uint32_t *)buf = htonl(2);
    memcpy(buf + sizeof(uint32_t), msg->Na, NonceLength);
    memcpy(buf + sizeof(uint32_t) + NonceLength, msg->Nb, NonceLength);
    *(uint32_t *)(buf + sizeof(uint32_t) + 2 * NonceLength) = htonl((uint32_t)msg->idB);

    return buf;
}

struct Msg2 *unmarshalMsg2(char *packet, unsigned int msg_len)
{
    if (msg_len < sizeof(uint32_t) + 2 * NonceLength + sizeof(int)) {
        return NULL;
    }

    uint32_t tag = ntohl(*(uint32_t *)packet);
    if (tag != 2) {
        return NULL;
    }

    char *na = malloc(NonceLength);
    if (na == NULL) {
        return NULL;
    }

    memcpy(na, packet + sizeof(uint32_t), NonceLength);

    char *nb = malloc(NonceLength);
    if (nb == NULL) {
        free(na);
        return NULL;
    }

    memcpy(nb, packet + sizeof(uint32_t) + NonceLength, NonceLength);

    int idB = (int)ntohl(*(uint32_t *)(packet + sizeof(uint32_t) + 2 * NonceLength));

    struct Msg2 *msg2 = malloc(sizeof(struct Msg2));
    if (msg2 == NULL) {
        free(nb);
        free(na);
        return NULL;
    }

    msg2->Na = na;
    msg2->Nb = nb;
    msg2->idB = idB;

    return msg2;
}

char *marshalMsg3(struct Msg3* msg, unsigned int *msg_len)
{
    *msg_len = sizeof(uint32_t) + NonceLength;
    char *buf = malloc(*msg_len);
    if (buf == NULL) {
        return NULL;
    }

    *(uint32_t *)buf = htonl(3);
    memcpy(buf + sizeof(uint32_t), msg->Nb, NonceLength);

    return buf;
}

struct Msg3 *unmarshalMsg3(char *packet, unsigned int msg_len)
{
    if (msg_len < sizeof(uint32_t) + NonceLength) {
        return NULL;
    }

    uint32_t tag = ntohl(*(uint32_t *)packet);
    if (tag != 3) {
        return NULL;
    }

    char *nb = malloc(NonceLength);
    if (nb == NULL) {
        return NULL;
    }

    memcpy(nb, packet + sizeof(uint32_t), NonceLength);

    struct Msg3 *msg3 = malloc(sizeof(struct Msg3));
    if (msg3 == NULL) {
        free(nb);
        return NULL;
    }

    msg3->Nb = nb;

    return msg3;
}
