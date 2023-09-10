package library

import (
	errors "errors"
	device "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/device"

	lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
)


//@ trusted
//@ requires acc(LibMem(libState), 1/16) && acc(lib.Mem(msg), 1/16)
//@ requires tm.gamma(msgT) == lib.Abs(msg)
//@ requires snapshot.isMessageAt(idSender, idReceiver, msgT)
//@ ensures  acc(LibMem(libState), 1/16) && acc(lib.Mem(msg), 1/16)
func (libState *LibraryState) Send(idSender, idReceiver p.Principal, msg lib.ByteString /*@, ghost msgT tm.Term, ghost snapshot tr.TraceEntry @*/) (err error) {
	err = libState.sendBuffer(msg)
	return
}

//@ trusted
// TODO: require that msg is readable by current principal
//@ requires acc(LibMem(libState), 1/16) && acc(lib.Mem(msg), 1/16)
//@ ensures  acc(LibMem(libState), 1/16) && acc(lib.Mem(msg), 1/16)
func (libState *LibraryState) ConsumePacket(msg lib.ByteString) {
	libState.output <- msg
}

/**
 * Sends a raw buffer via network to the peer
 */
//@ trusted
func (libState *LibraryState) sendBuffer(buffer []byte) error {
	if libState.endpoint == nil {
		return errors.New("no known endpoint for peer")
	}

	return libState.dev.Net.Bind.Send(buffer, libState.endpoint)
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16) && lib.Mem(msg)
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(res) && lib.Size(res) >= old(lib.Size(msg))
//@ ensures  lib.Abs(res) == old(lib.Abs(msg))
func (libState *LibraryState) PadMsg(msg lib.ByteString) (res lib.ByteString) {
	paddingSize := device.CalculatePaddingSize(len(msg), int(libState.dev.Mtu))
	var paddingZeros [device.PaddingMultiple]byte
	res = append(msg, paddingZeros[:paddingSize]...)
	return
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16) && lib.Mem(msg)
//@ ensures  acc(LibMem(libState), 1/16) && lib.Mem(msg) && lib.Size(msg) == old(lib.Size(msg))
//@ ensures  lib.Mem(mac1) && lib.Mem(mac2)
//@ ensures  old(lib.Abs(msg)) == tm.tuple7B(tm.getTupleElemB(b, 0),tm.getTupleElemB(b, 1),tm.getTupleElemB(b, 2),tm.getTupleElemB(b, 3),tm.getTupleElemB(b, 4),tm.zeroStringB(16),tm.zeroStringB(16)) ==> lib.Abs(msg) == tm.tuple7B(tm.getTupleElemB(b, 0),tm.getTupleElemB(b, 1),tm.getTupleElemB(b, 2),tm.getTupleElemB(b, 3),tm.getTupleElemB(b, 4),lib.Abs(mac1),lib.Abs(mac2))
func (libState *LibraryState) AddMacs(msg lib.ByteString /*@, ghost b tm.Bytes @*/) (mac1, mac2 lib.ByteString) {
	// first, compute key that will be used for MACing (could be precomputed)
	// note that the peer's public key (instead of own one) is used in the derivation
	var macKey [KeySize]byte
	ComputeHash(macKey[:], []byte(device.WGLabelMAC1), libState.dev.Peer.Handshake.RemoteStatic[:])

	// set MAC1
	startMac1 := len(msg) - 2*MacSize
	mac1Slice := msg[startMac1 : startMac1+MacSize]
	ComputeMac(mac1Slice, macKey[:], msg[:startMac1]) // MAC all request fields except MAC1 and MAC2
	mac1 = make([]byte, MacSize)
	copy(mac1, mac1Slice)

	// MAC2 is not set as we assume that the system is not under load
	mac2Slice := msg[startMac1+MacSize:]
	mac2 = make([]byte, MacSize)
	copy(mac2, mac2Slice)
	return
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16)
//@ ensures  acc(LibMem(libState), 1/16)
//@ trusted
func (libState *LibraryState) Println(msg string) {
	libState.dev.Log.Verbosef(msg)
}
