# A Generic Methodology for the Modular Verification of Security Protocol Implementations

[![Artifact](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/artifact.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/artifact.yml?query=branch%3Amain)

[![Reusable Verification Library](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/library.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/library.yml?query=branch%3Amain)
[![Reusable Verification Library for VeriFast](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/verifast-library.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/verifast-library.yml?query=branch%3Amain)

[![NSL Case Study](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/nsl.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/nsl.yml?query=branch%3Amain)
[![DH Case Study](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/dh.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/dh.yml?query=branch%3Amain)
[![WireGuard Case Study](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/wireguard.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/wireguard.yml?query=branch%3Amain)
[![NSL Case Study for VeriFast](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/verifast-nsl.yml/badge.svg?branch=main)](https://github.com/viperproject/SecurityProtocolImplementations/actions/workflows/verifast-nsl.yml?query=branch%3Amain)

This is the artifact for the paper "A Generic Methodology for the Modular Verification of Security Protocol Implementations", published at ACM CCS '23 [[published version]](https://doi.org/10.1145/3576915.3623105) [[extended version]](https://arxiv.org/abs/2212.02626).
This artifact has been archived on Zenodo (DOI: [10.5281/zenodo.8330913](https://doi.org/10.5281/zenodo.8330913)). The paper can be cited as follows (for BibTeX):
```BibTex
@InProceedings{ArquintSchwerhoffMehtaMueller23,
  author = {Arquint, Linard and Schwerhoff, Malte and Mehta, Vaibhav and M\"uller, Peter},
  title = {A Generic Methodology for the Modular Verification of Security Protocol Implementations},
  year = {2023},
  isbn = {9798400700507},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  booktitle = {Proceedings of the 2023 ACM SIGSAC Conference on Computer and Communications Security},
  pages = {1377-1391},
  numpages = {15},
  keywords = {protocol implementation verification, symbolic security, separation logic, automated verification, injective agreement, forward secrecy},
  location = {Copenhagen, Denmark},
  series = {CCS '23},
  doi = {10.1145/3576915.3623105},
  url = {https://doi.org/10.1145/3576915.3623105},
  urltext = {Publisher},
  url1 = {https://pm.inf.ethz.ch/publications/ArquintSchwerhoffMehtaMueller23.pdf},
  url1text = {PDF},
  abstract = {Security protocols are essential building blocks of modern IT systems. Subtle flaws in their design or implementation may compromise the security of entire systems. It is, thus, important to prove the absence of such flaws through formal verification. Much existing work focuses on the verification of protocol *models*, which is not sufficient to show that their *implementations* are actually secure. Verification techniques for protocol implementations (e.g., via code generation or model extraction) typically impose severe restrictions on the used programming language and code design, which may lead to sub-optimal implementations. In this paper, we present a methodology for the modular verification of strong security properties directly on the level of the protocol implementations. Our methodology leverages state-of-the-art verification logics and tools to support a wide range of implementations and programming languages. We demonstrate its effectiveness by verifying memory safety and security of Go implementations of the Needham-Schroeder-Lowe, Diffie-Hellman key exchange, and WireGuard protocols, including forward secrecy and injective agreement for WireGuard. We also show that our methodology is agnostic to a particular language or program verifier with a prototype implementation for C.}
}
```

## Structure
- `ReusableVerificationLibrary` contains the Gobra sources that constitute the Reusable Verification Library
- `casestudies/nsl` contains the sources of the NSL case study. The implementation consists of separate packages for the initiator, initiator2 (using a slightly different code structure), and responder role. The main package sets up communication via Go channels and executes the two protocol roles as threads (using Goroutines)
- `casestudies/dh` contains the sources of the DH case study, which follows a similar structure as the NSL case study and consists of packages for the initiator and responder roles.
- `casestudies/wireguard` contains the sources of the WireGuard case study. The role implementations are mainly located in the `initiator` and `responder` packages. The trace invariants are defined in `verification/common` and `verification/labellemma` contains the WireGuard-specific lemmas and their proofs.
- `VeriFastPrototype` contains the C sources of our prototype for VeriFast. The prototype demonstrates that (1) a concurrent data structure can be built on top of VeriFast's built-in mutex offering the same local snapshots as our Reusable Verification Library, (2) a parameterized trace invariant in the form of a separation logic predicate can be defined, and (3) several lemmas, such as the uniqueness of events or the secrecy lemma, can be proven using the trace invariant. Furthermore, implementations in C of the NSL initiator & responder demonstrate that we can instantiate and use the Reusable Verification Library for VeriFast to prove secrecy and injective agreement, i.e., the same security properties as for the implementation in Go using Gobra.


## Artifact Docker image
The artifact docker image includes both reusable verification libraries and all case studies. Furthermore, it contains all dependencies to compile and verify the libraries and case studies.

### Set-up
We require an installation of Docker. The following steps have been tested on macOS 14.0 with the latest version of Docker Desktop, which is at time of writing 4.24.2 and comes with version 24.0.6 of the Docker CLI.

#### Installation
- We recommend to adapt the Docker settings to provide sufficient resources to Docker. We have tested our artifact on a 2019 16-inch MacBook Pro with 2.3 GHz 8-Core Intel Core i9 running macOS Sonoma 14.0 and configured Docker to allocate up 16 cores (which includes 8 virtual cores), 6 GB of memory, and 1 GB of swap memory.
- Navigate to a convenient folder, in which directories can be created for the purpose of running this artifact.
- Open a shell at this folder location.
- Create two new folders named `Go-sync` and `C-sync` by executing:
	```
    mkdir Go-sync && mkdir C-sync
    ```
- Download and start the Docker image containing our artifact by executing the following command:
    ```
    docker run -it --volume $PWD/C-sync:/gobra/C --volume $PWD/Go-sync:/gobra/Go ghcr.io/viperproject/securityprotocolimplementations-artifact:latest
    ```
	Note that this command results in the Docker container writing files to the two folders `Go-sync` and `C-sync` on your host machine.
	Thus, make sure that these folders are indeed empty and previous modifications that you have made to files in these folders have been saved elsewhere!
- The Docker command above not only starts a Docker container and provides you with a shell within this container but it also synchronizes all files constituting our artifact with the two folders `Go-sync` and `C-sync` on your host machine. I.e., the local folders `Go-sync` and `C-sync` are synchronized with `/gobra/Go` and `/gobra/C` within the Docker container, respectively.

#### Usage
The Docker image provides several ready-to-use scripts in the `/gobra` directory:
- `verify-library.sh`: Verifies the reusable verification library in Go using the Gobra program verifier.
- `verify-c-library.sh`: Verifies the prototype of the reusable verification library in C using the VeriFast program verifier.
- `verify-nsl.sh`: Verifies the Needham-Schroeder-Lowe (NSL) case study in Go using Gobra, which includes verifying the initiator and responder implementations, protocol-specific lemmas, and the trace invariant.
- `verify-nsl-alternative.sh`: Verifies an alternative implementation of the NSL initiator that is composed of several methods to demonstrate that our methodology is agnostic of the structure of implementations.
- `verify-dh.sh`: Verifies the signed Diffie-Hellman (DH) case study in Go using Gobra, which includes verifying the initiator and responder implementations, protocol-specific lemmas, and the trace invariant.
- `verify-wireguard.sh`: Verifies the WireGuard VPN protocol case study using Gobra, which includes verifying the initiator and responder implementations, protocol-specific lemmas, and the trace invariant.
- `verify-c-nsl.sh`: Verifies the Needham-Schroeder-Lowe (NSL) case study in C using VeriFast, which includes verifying the initiator and responder implementations, protocol-specific lemmas, and the trace invariant.
- `test-nsl.sh`: Compiles and executes the NSL case study in Go and prints the random numbers obtained by the initiator and responder. 
- `test-dh.sh`: Compiles and executes the DH case study in Go and prints the shared DH secrets computed by the initiator and responder. 
- `test-wireguard.sh`: Compiles and executes the WireGuard case study in Go, which establishes a VPN connection and exchanges some ASCII messages.
- `test-c-nsl.sh`: Compiles and executes the NSL case study in C and prints the random numbers obtained by the initiator and responder. 

Maintainer: [Linard Arquint](https://linardarquint.com)
