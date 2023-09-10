# Gobra commit f21fe70
FROM ghcr.io/viperproject/gobra@sha256:0e7419455a3648d006e8a9957380e94c1a8e52d2d4b1ce2425af852dc275fb29

RUN apt-get update && \
	apt-get install -y \
    wget \
    jq

# install go
RUN mkdir tmp && \
    cd tmp && \
    wget https://go.dev/dl/go1.17.3.linux-amd64.tar.gz && \
    rm -rf /usr/local/go && tar -C /usr/local -xzf go1.17.3.linux-amd64.tar.gz && \
    cd ../ && \
    rm -rf tmp

# add Go to path:
ENV PATH="${PATH}:/usr/local/go/bin"

COPY casestudies/wireguard/.modules-precedence ./.modules-precedence
COPY casestudies/wireguard/conn ./conn
COPY casestudies/wireguard/device ./device
COPY casestudies/wireguard/endpoint ./endpoint
COPY casestudies/wireguard/initiator ./initiator
COPY casestudies/wireguard/ipc ./ipc
COPY casestudies/wireguard/library ./library
COPY casestudies/wireguard/log ./log
COPY casestudies/wireguard/replay ./replay
COPY casestudies/wireguard/responder ./responder
COPY casestudies/wireguard/tai64n ./tai64n
COPY casestudies/wireguard/tun ./tun
COPY casestudies/wireguard/verification ./verification
COPY casestudies/wireguard/go.mod .
COPY casestudies/wireguard/go.sum .
COPY casestudies/wireguard/main.go .
COPY casestudies/wireguard/README.md .
COPY casestudies/wireguard/docker/compile.sh .
COPY casestudies/wireguard/docker/test.sh .
COPY casestudies/wireguard/docker/verify.sh .
COPY casestudies/wireguard/load-modules.sh .

# copy the reusable verification library
COPY ReusableVerificationLibrary ./ReusableVerificationLibrary

# point Go to local copy of the library:
RUN go mod edit -replace github.com/viperproject/ReusableProtocolVerificationLibrary=./ReusableVerificationLibrary

# load modules and manually add symlink to reusable verification library:
RUN ./load-modules.sh && \
    mkdir -p .modules/github.com/viperproject && \
    ln -s $PWD/ReusableVerificationLibrary .modules/github.com/viperproject/ReusableProtocolVerificationLibrary

# compile to trigger download of dependent Go packages:
RUN ./compile.sh

# disable entry point specified by the Gobra base container:
ENTRYPOINT []
