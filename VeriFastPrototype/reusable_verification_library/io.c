#include "io.h"
#include <stdio.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <string.h>


#define MAX_DATA_SIZE 1024

struct IoLib {
    int socket;
    int peerId; // currently, we only support a single peer
    bool isUdpServer;
    bool received_data;
    struct sockaddr peer_addr;
};

struct IoLib *createIoLib(bool isInitiator, int peerId, char *responderAddress, int responderPort)
{
    struct IoLib * res = malloc(sizeof(struct IoLib));
    if (res == NULL) {
        return NULL;
    }

    res->peerId = peerId;
    res->isUdpServer = !isInitiator;
    res->received_data = false;

    res->socket = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if (res->socket < 0) {
        free(res);
        return  NULL;
    }

    struct sockaddr_in server_addr;
    server_addr.sin_family = AF_INET;
    server_addr.sin_port = htons(responderPort);
    server_addr.sin_addr.s_addr = inet_addr(responderAddress);

    if (res->isUdpServer) {
        int success = bind(res->socket, (struct sockaddr*)&server_addr, sizeof(server_addr));
        if (success < 0) {
            free(res);
            return  NULL;
        }
    } else {
        memcpy(&(res->peer_addr), &server_addr, sizeof(struct sockaddr));
    }    

    return res;
}

void IoLib_free(struct IoLib *lib) {
    close(lib->socket);
    free(lib);
    lib = NULL;
}

bool io_send(struct IoLib *lib, int idSender, int idReceiver, char *msg, unsigned int msg_len)
{
    if (lib->peerId != idReceiver || (lib->isUdpServer && !lib->received_data)) {
        // peer does not match or we have not received any data yet and
        // thus do not know the peer's address
        return NULL;
    }

    unsigned int peer_addr_len = sizeof(lib->peer_addr);
    int sent_data = sendto(lib->socket, msg, msg_len, 0, &(lib->peer_addr), peer_addr_len);
    return sent_data >= 0;
}

char *io_receive(struct IoLib *lib, int idSender, int idReceiver, unsigned int *msg_len)
{
    if (lib->peerId != idSender) {
        // peer does not match
        return NULL;
    }

    char buf[MAX_DATA_SIZE];
    unsigned int peer_addr_len = sizeof(lib->peer_addr);
    int buf_len = recvfrom(lib->socket, buf, sizeof(buf), 0, &(lib->peer_addr), &peer_addr_len);
    if (buf_len < 0) {
        return NULL;
    }

    lib->received_data = true;

    char *data = malloc(buf_len);
    if (data == NULL) {
        return NULL;
    }

    memcpy(data, buf, buf_len);
    *msg_len = buf_len;
    return data;
}

void print_hex(char *desc, char *buf, unsigned int len)
{
    printf("%s: ", desc);
    for (int i = 0; i < len; i++) {
        printf("%02X", ((uint8_t *)buf)[i]);
    }
    printf("\n");
}
