#include <unistd.h>
#include <getopt.h>
#include <stdbool.h>
#include <stdlib.h>
#include "initiator.h"
#include "responder.h"

char *keypair_1_pk = "MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAvVMEI16XJOvbU1WjpnP/ne2ndS7zuFMgidUxrSVB6loHpt59ZBfhczjnl0ZkSOvbGmJrbAfqIjHs9oFwmZoTp/hgoJF0bXFbJZQixx79gt3SNwt9cqUvA0851lY00dYkfiqRM/rT9e6C0VAGuIWo/VOpf4zDIrYKwC4DbDQ6e+DyuNqgym+5PnAezo5wwqA05k7TRhq5fBIDuH5LepemMwz0uJmwascsU6KNXFVMrc+e8lu1uiBeELiXH2IliOw0GgoYxx26OLM8+o/uBLoHcxiprR3nXangHsr+3I7LyIZtRyOIycok1/XVj6Nch5bzWX53+7xrSC0P4OncNPIm++O7NOqLAE2kZfAzHrNA2oBu7wUDE4BVnvM9QG0KzTIY9QVQbawNzY+SzmpolkEvJ5AfvdtGQond/vgi8+DLZwyP5CH1mJMiT1TSFlPb8C17FuYdz3mHMgBM6Z/6edVcmeul4gujFcc+umodDpZqw24wdx+t3UStOwCArX/JMbSH9Zu17RdnwiPUK8cYa756rqzScJhIReZuDZgG2jqxWcr3IvJcrllDiwyhB/pELn9OFYRsd0QdHNA16GLwRZejmxJXp5OC9UVzViJ+O4NeW+Sx0tb5o0yIbBEUHY1Kl7Z519svRrXCKASk0EfAyWCcrY38TfyvmMNwspNrh3K/pnMCAwEAAQ==";
char *keypair_1_sk = "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";

char *keypair_2_pk = "MIICIjANBgkqhkiG9w0BAQEFAAOCAg8AMIICCgKCAgEAx+KThX2pDDgGcNzmDxBfldrN+v7sWoW3FDtszT0Bb/pqVh5Wa2FI8S+eO3SJgytj2B3Kj9GjGy9UqJNTBAJCcm/xkEVCvVQiSro0id+hTN7zSkIDYiUs01LxjF9eZ71715jeXLiNWQNBTaiLrRuvvhQeRSQ328UzKj5aGklgUxmI/9VWOngmELYdsPET/FdxkM0481a+G4o5D7wRZLxAk/EbeNB0ifi4VB4sysMFGX06330KtmJq3jH/jKIOLxu1+OwLT8CAPM/t/J3Vgerr9KBcnEmyIt91+1OJOAUhQGRx0VOnU3qR3WPRUaDrL/5XeozSd45wK2dFZlLcPQ6CSizVPe0lPNobwiwJ/GS3m5YT2EUlOvKdqRMK8n9I3stsaC3sVcFQRIwPmWqg5B7y4QO1vQfBMyz8rc1kxfwETo5so3IGPzxKQWkF4Az2wdKyljuRApAK5DgF4q7mLiCeGXofuBFp1KqWV5QLUKBxNKy5qCmbv+FarCG9f0X/vaCLMzX2qzwnGlMLHsXY5rwzmchtvS57qL992hYh/G0BPjO5mr+m87vJuZhX+4dVAc8h7XZZbOTaORVRXKnh7qJ4N0czF/e4bH0Qv6iaMWTEEKLjKmt8N09Zw3AVD9tD7feIgI6Rj9BfCItIcOYS9wYVRMuJBDtssFEXdmyBRGUe6ykCAwEAAQ==";
char *keypair_2_sk = "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";

struct Cli_Options {
    bool hasIsInitiator;
    bool isInitiator;
    bool hasAddress;
    char *address; // string containing an IPv4 address
    bool hasPort;
    int port;
    bool hasSk;
    char *sk;
    bool hasPk;
    char *pk;
};

void parsePort(struct Cli_Options *options) {
    options->port = atoi(optarg);
    options->hasPort = true;
}

bool parse(struct Cli_Options *options, int argc, char *argv[]) {
    const char *short_opt = "ia:p:s:k:";
    struct option long_opt[] =
    {
        {"isInitiator", no_argument, NULL, 'i'},
        {"address", required_argument, NULL, 'a'},
        {"port", required_argument, NULL, 'p'},
        {"privateKey", required_argument, NULL, 's'},
        {"peerPublicKey", required_argument, NULL, 'k'},
        {NULL, 0, NULL, 0}
    };

    int longindex;
    int c;
    while((c = getopt_long(argc, argv, short_opt, long_opt, &longindex)) != -1) {
        switch (c) {
            case -1: // no more options
                break;
            case 0: // long options
                switch (longindex) {
                    case 2:
                        parsePort(options);
                        break;
                    default:
                        return false;
                }
                break;
            case 'i':
                options->isInitiator = true;
                options->hasIsInitiator = true;
                break;
            case 'a':
                options->address = optarg;
                options->hasAddress = true;
                break;
            case 'p':
                parsePort(options);
                break;
            case 's':
                options->sk = optarg;
                options->hasSk = true;
                break;
            case 'k':
                options->pk = optarg;
                options->hasPk = true;
                break;
            default:
                return false;
        }
    }

    if (!options->hasIsInitiator) {
        options->isInitiator = false;
        options->hasIsInitiator = true;
    }

    return options->hasIsInitiator && options->hasAddress && options->hasPort && options->hasSk && options->hasPk;
}

int main(int argc, char *argv[]) {
    struct Cli_Options options;
    bool success = parse(&options, argc, argv);
    if (!success) {
        return 1;
    }
    
    const int initiatorId = 0;
    const int responderId = 1;
    struct TraceManager *tm = create_trace_managers(2);
    if (tm == NULL) {
        return 1;
    }

    struct IoLib *io_lib = createIoLib(options.isInitiator, options.isInitiator ? responderId : initiatorId, options.address, options.port);
    if (io_lib == NULL) {
        free(tm);
        return 1;
    }

    if (options.isInitiator) {
        struct A *a = malloc(sizeof(struct A));
        if (a == NULL) {
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        a->labeledLib = createLabeledLib(io_lib, tm, initiatorId);
        if(a->labeledLib == 0) {
            free(a);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        a->version = 1;
        a->idA = initiatorId;
        a->idB = responderId;

        unsigned int skA_len;
        char *skA = parsePKCS1PrivateKey(options.sk, &skA_len);
        if (skA == NULL) {
            free(a->labeledLib);
            free(a);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        unsigned int pkA_len;
        char *pkA = getPublicKey(skA, skA_len, &pkA_len);
        if (pkA == NULL) {
            free(skA);
            free(a->labeledLib);
            free(a);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        a->skA = skA;
        a->skA_len = skA_len;
        a->pkA = pkA;
        a->pkA_len = pkA_len;

        unsigned int pkB_len;
        char *pkB = parsePKIXPublicKey(options.pk, &pkB_len);
        if (pkB == NULL) {
            free(pkA);
            free(skA);
            free(a->labeledLib);
            free(a);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        a->pkB = pkB;
        a->pkB_len = pkB_len;

        bool success = runA(a);
        if (!success) {
            free(pkB);
            free(pkA);
            free(skA);
            free(a->labeledLib);
            free(a);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        free(pkB);
        free(pkA);
        free(skA);
        free(a->labeledLib);
        free(a);
    } else {
        struct B *b = malloc(sizeof(struct B));
        if (b == NULL) {
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        b->labeledLib = createLabeledLib(io_lib, tm, responderId);
        if(b->labeledLib == 0) {
            free(b);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        b->version = 1;
        b->idA = initiatorId;
        b->idB = responderId;

        unsigned int skB_len;
        char *skB = parsePKCS1PrivateKey(options.sk, &skB_len);
        if (skB == NULL) {
            free(b->labeledLib);
            free(b);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        unsigned int pkB_len;
        char *pkB = getPublicKey(skB, skB_len, &pkB_len);
        if (pkB == NULL) {
            free(skB);
            free(b->labeledLib);
            free(b);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        b->skB = skB;
        b->skB_len = skB_len;
        b->pkB = pkB;
        b->pkB_len = pkB_len;

        unsigned int pkA_len;
        char *pkA = parsePKIXPublicKey(options.pk, &pkA_len);
        if (pkA == NULL) {
            free(pkB);
            free(skB);
            free(b->labeledLib);
            free(b);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        b->pkA = pkA;
        b->pkA_len = pkA_len;

        bool success = runB(b);
        if (!success) {
            free(pkA);
            free(pkB);
            free(skB);
            free(b->labeledLib);
            free(b);
            IoLib_free(io_lib);
            free(tm);
            return 1;
        }

        free(pkA);
        free(pkB);
        free(skB);
        free(b->labeledLib);
        free(b);
    }

    IoLib_free(io_lib);
    free(tm);

    return 0;
}
