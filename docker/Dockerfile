# Gobra commit f21fe70
FROM ghcr.io/viperproject/gobra@sha256:0e7419455a3648d006e8a9957380e94c1a8e52d2d4b1ce2425af852dc275fb29

RUN apt-get update && \
	apt-get install -y \
    curl \
    gcc \
    wget \
    jq \
    build-essential \
    checkinstall \
    zlib1g-dev

# install openssl
RUN mkdir tmp && \
    cd tmp && \
    wget https://www.openssl.org/source/openssl-3.1.3.tar.gz && \
    tar xvf openssl-3.1.3.tar.gz && \
    cd openssl-3.1.3 && \
    ./config && \
    make && \
    make install && \
    ldconfig && \
    cd ../../ && \
    rm -rf tmp

# install go
RUN mkdir tmp && \
    cd tmp && \
    wget https://go.dev/dl/go1.17.3.linux-amd64.tar.gz && \
    rm -rf /usr/local/go && tar -C /usr/local -xzf go1.17.3.linux-amd64.tar.gz && \
    cd ../ && \
    rm -rf tmp

# add Go to path:
ENV PATH="${PATH}:/usr/local/go/bin"

# install VeriFast
ARG VERIFAST_VERSION=21.04
RUN mkdir tmp && \
    cd tmp && \
    curl -q -s -S -L --create-dirs -o VeriFast.zip https://github.com/verifast/verifast/releases/download/$VERIFAST_VERSION/verifast-$VERIFAST_VERSION-linux.tar.gz && \
    tar xzf VeriFast.zip && \
    # this creates a folder called 'verifast-$VERIFAST_VERSION'
    mv verifast-$VERIFAST_VERSION /usr/local && \
    cd ../ && \
    rm -rf tmp

# add VeriFast to path:
ENV PATH="${PATH}:/usr/local/verifast-$VERIFAST_VERSION/bin"
ENV VERIFAST_BIN="/usr/local/verifast-$VERIFAST_VERSION/bin"

RUN mkdir C && mkdir Go

# copy the reusable verification library
COPY ReusableVerificationLibrary ./Go/ReusableVerificationLibrary

ENV ReusableVerificationLibrary=/gobra/Go/ReusableVerificationLibrary

# copy DH
copy casestudies/dh ./Go/dh

# point Go to local copy of the library:
RUN cd ./Go/dh && \
    go mod edit -replace github.com/viperproject/ReusableProtocolVerificationLibrary=$ReusableVerificationLibrary

# load modules and manually add symlink to reusable verification library:
RUN cd ./Go/dh && \
    ./load-modules.sh "../.modules" && \
    mkdir -p ../.modules/github.com/viperproject && \
    ln -s $ReusableVerificationLibrary ../.modules/github.com/viperproject/ReusableProtocolVerificationLibrary

# compile to trigger download of dependent Go packages:
RUN cd ./Go/dh && \
    ./compile.sh

# copy NSL
copy casestudies/nsl ./Go/nsl

# point Go to local copy of the library:
RUN cd ./Go/nsl && \
    go mod edit -replace github.com/viperproject/ReusableProtocolVerificationLibrary=$ReusableVerificationLibrary

# load modules and manually add symlink to reusable verification library:
RUN cd ./Go/nsl && \
    ./load-modules.sh "../.modules"
    # mkdir -p .modules/github.com/viperproject && \
    # ln -s $ReusableVerificationLibrary .modules/github.com/viperproject/ReusableProtocolVerificationLibrary

# compile to trigger download of dependent Go packages:
RUN cd ./Go/nsl && \
    ./compile.sh

# copy WireGuard
copy casestudies/wireguard ./Go/wireguard
# RUN mkdir wireguard
# COPY casestudies/wireguard/.modules-precedence ./Go/wireguard/.modules-precedence
# COPY casestudies/wireguard/conn ./Go/wireguard/conn
# COPY casestudies/wireguard/device ./Go/wireguard/device
# COPY casestudies/wireguard/endpoint ./Go/wireguard/endpoint
# COPY casestudies/wireguard/initiator ./Go/wireguard/initiator
# COPY casestudies/wireguard/ipc ./Go/wireguard/ipc
# COPY casestudies/wireguard/library ./Go/wireguard/library
# COPY casestudies/wireguard/log ./Go/wireguard/log
# COPY casestudies/wireguard/replay ./Go/wireguard/replay
# COPY casestudies/wireguard/responder ./Go/wireguard/responder
# COPY casestudies/wireguard/tai64n ./Go/wireguard/tai64n
# COPY casestudies/wireguard/tun ./Go/wireguard/tun
# COPY casestudies/wireguard/verification ./Go/wireguard/verification
# COPY casestudies/wireguard/go.mod ./Go/wireguard
# COPY casestudies/wireguard/go.sum ./Go/wireguard
# COPY casestudies/wireguard/main.go ./Go/wireguard
# COPY casestudies/wireguard/README.md ./Go/wireguard
# COPY casestudies/wireguard/docker/compile.sh ./Go/wireguard
# COPY casestudies/wireguard/docker/test.sh ./Go/wireguard
# COPY casestudies/wireguard/docker/verify.sh ./Go/wireguard
# COPY casestudies/wireguard/load-modules.sh ./Go/wireguard
RUN mv ./Go/wireguard/docker/compile.sh ./Go/wireguard && \
    mv ./Go/wireguard/docker/test.sh ./Go/wireguard && \
    mv ./Go/wireguard/docker/verify.sh ./Go/wireguard

# point Go to local copy of the library:
RUN cd ./Go/wireguard && \
    go mod edit -replace github.com/viperproject/ReusableProtocolVerificationLibrary=$ReusableVerificationLibrary

# load modules and manually add symlink to reusable verification library:
RUN cd ./Go/wireguard && \
    ./load-modules.sh && \
    mkdir -p .modules/github.com/viperproject && \
    ln -s $ReusableVerificationLibrary .modules/github.com/viperproject/ReusableProtocolVerificationLibrary

# compile to trigger download of dependent Go packages:
RUN cd ./Go/wireguard && \
    ./compile.sh

# copy the reusable verification library
COPY VeriFastPrototype/reusable_verification_library ./C/reusable_verification_library

# copy NSL
COPY VeriFastPrototype/nsl ./C/nsl

# copy shell scripts
COPY docker/*.sh ./

# set library paths correctly such that compiling and executing the C NSL implementation
# works:
ENV LD_LIBRARY_PATH="/usr/local/openssl/lib:${LD_LIBRARY_PATH}"
ENV LD_LIBRARY_PATH="/usr/local/lib64:${LD_LIBRARY_PATH}"

# install a code editor for convenience:
RUN apt-get install -y vim

# remove some unneeded folders that come with the base image:
RUN rm -r evaluation
RUN rm -r tutorial-examples

RUN mv Go Go-orig && \
    mv C C-orig

RUN mkdir Go && \
    mkdir C

# disable entry point specified by the Gobra base container:
# ENTRYPOINT []
ENTRYPOINT cp -r Go-orig/. Go/ && \
    cp -r C-orig/. C/ && \
    /bin/bash
