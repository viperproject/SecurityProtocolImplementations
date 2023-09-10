package library

import (
	device "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/device"
	tai64n "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/tai64n"

	//@ ev "github.com/viperproject/ReusableProtocolVerificationLibrary/event"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/label"
	//@ ll "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary"
	lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
	//@ p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ . "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
	//@ u "github.com/viperproject/ReusableProtocolVerificationLibrary/usage"
	//@ common "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/verification/common"
)


// we assume here that these keys have been created before the implementations are executed
// i.e. are already recorded on the trace
// the functions in this file are simple getters that retrieve these values from some secure
// storage

//@ trusted
//@ requires acc(LibMem(libState), 1/16)
//@ requires llib.Mem()
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(b1)
//@ ensures  llib.Mem()
//@ ensures  llib.ImmutableState() == old(llib.ImmutableState())
//@ ensures  llib.Snapshot() == old(llib.Snapshot())
//@ ensures  ok ==> lib.Abs(b1) == gamma(skT)
//@ ensures  ok ==> common.GetWgLabeling().IsSecretKey(llib.Snapshot(), principalId(own), skT, labeling.KeyTypeDh(), common.WgKey)
func (libState *LibraryState) GetLtKBio(own uint32 /*@, ghost llib *ll.LabeledLibrary @*/) (ok bool, b1 lib.ByteString /*@, ghost skT Term @*/) {
	ok = true
	b1 = libState.dev.StaticIdentity.PrivateKey[:]
	return
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16)
//@ requires llib.Mem()
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(b1)
//@ ensures  llib.Mem()
//@ ensures  llib.ImmutableState() == old(llib.ImmutableState())
//@ ensures  llib.Snapshot() == old(llib.Snapshot())
//@ ensures  ok ==> lib.Abs(b1) == gamma(ltpkT)
//@ ensures  ok ==> common.GetWgLabeling().IsPublicKeyExistential(llib.Snapshot(), principalId(other), ltpkT, labeling.KeyTypeDh(), common.WgKey)
func (libState *LibraryState) GetLtpKBio(other uint32 /*@, ghost llib *ll.LabeledLibrary @*/) (ok bool, b1 lib.ByteString /*@, ghost ltpkT Term @*/) {
	ok = true
	b1 = libState.dev.Peer.Handshake.RemoteStatic[:]
	return
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16)
//@ requires llib.Mem()
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(b1)
//@ ensures  llib.Mem()
//@ ensures  llib.ImmutableState() == old(llib.ImmutableState())
//@ ensures  llib.Snapshot() == old(llib.Snapshot())
//@ ensures  ok ==> lib.Abs(b1) == gamma(kT)
//@ ensures  ok ==> common.GetWgLabeling().IsLabeled(llib.Snapshot(), kT, label.Public())
func (libState *LibraryState) GetPsKBio(a uint32, b uint32 /*@, ghost llib *ll.LabeledLibrary @*/) (ok bool, b1 ByteString /*@, ghost kT Term @*/) {
	ok = true
	b1 = libState.dev.Peer.Handshake.PresharedKey[:]
	return
}

//@ trusted
//@ ensures  lib.Mem(res) && lib.Size(res) == 12
//@ ensures  lib.Abs(res) == gamma(tsT)
// we assume that the timestamp is a public string (by casting `res` to string):
//@ ensures  tsT.IsString()
func Timestamp() (res ByteString /*@, tsT Term @*/) {
	var array [12]byte = tai64n.Now()
	return array[:]
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16) && lib.Mem(msg)
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(msg) && lib.Size(msg) == old(lib.Size(msg))
//@ ensures  mac1 == gamma(mac1T)
//@ ensures  (old(lib.Abs(msg)) == tuple7B(getTupleElemB(b, 0),getTupleElemB(b, 1),getTupleElemB(b, 2),getTupleElemB(b, 3),getTupleElemB(b, 4),zeroStringB(16),zeroStringB(16)) ==> lib.Abs(msg) == tuple7B(getTupleElemB(b, 0),getTupleElemB(b, 1),getTupleElemB(b, 2),getTupleElemB(b, 3),getTupleElemB(b, 4),mac1,zeroStringB(16)))
// we assume that mac1 is a public string
// note that we make no additional assumptions (as we do not model it with its own term)
//@ ensures  mac1T.IsString()
func (libState *LibraryState) AddMac1(msg ByteString /*@, ghost b Bytes @*/) /*@ (ghost mac1 Bytes, ghost mac1T Term) @*/ {
	// first, compute key that will be used for MACing (could be precomputed)
	// note that the peer's public key (instead of own one) is used in the derivation
	var macKey [KeySize]byte
	ComputeHash(macKey[:], []byte(device.WGLabelMAC1), libState.dev.Peer.Handshake.RemoteStatic[:])

	// set MAC1
	startMac1 := len(msg) - 2*MacSize
	mac1Slice := msg[startMac1 : startMac1+MacSize]
	ComputeMac(mac1Slice, macKey[:], msg[:startMac1]) // MAC all request fields except MAC1 and MAC2
	tmpMac1 := make([]byte, MacSize)
	copy(tmpMac1, mac1Slice)
	//@ mac1 = tmpMac1
	return
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16) && lib.Mem(msg)
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(msg) && lib.Size(msg) == old(lib.Size(msg))
//@ ensures  mac2 == gamma(mac2T)
//@ ensures  (old(lib.Abs(msg)) == tuple7B(getTupleElemB(b, 0),getTupleElemB(b, 1),getTupleElemB(b, 2),getTupleElemB(b, 3),getTupleElemB(b, 4),getTupleElemB(b, 5),zeroStringB(16)) ==> lib.Abs(msg) == tuple7B(getTupleElemB(b, 0),getTupleElemB(b, 1),getTupleElemB(b, 2),getTupleElemB(b, 3),getTupleElemB(b, 4),getTupleElemB(b, 5),mac2))
// we assume that mac2 is a public string
// note that we make no additional assumptions (as we do not model it with its own term)
//@ ensures  mac2T.IsString()
func (libState *LibraryState) AddMac2(msg ByteString /*@, ghost b Bytes @*/) /*@ (ghost mac2 Bytes, ghost mac2T Term) @*/ {
	// MAC2 is not set as we assume that the system is not under load
	startMac2 := len(msg) - MacSize
	mac2Slice := msg[startMac2:]
	tmpMac2 := make([]byte, MacSize)
	copy(tmpMac2, mac2Slice)
	//@ mac2 = tmpMac2
	return
}

//@ trusted
func GetCounter(counter uint64) (res uint64) {
	return counter
}
