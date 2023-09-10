package library

import (
	fmt "fmt"
	conn "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/conn"
	device "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/device"
	lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
)


type ByteString = lib.ByteString

type LibraryState struct {
	dev      *device.Device
	endpoint conn.Endpoint
	input    <-chan []byte
	output   chan<- []byte
}

//@ trusted
func NewLibraryState(d *device.Device) (libState LibraryState, args HandshakeArguments, ok bool) {
	localIndex, ok := RandUint32()
	if !ok {
		return
	}

	libState = LibraryState{
		dev:      d,
		endpoint: d.Peer.Endpoint,
		input:    d.InputChannel,
		output:   d.OutputChannel,
	}

	args = HandshakeArguments{
		PresharedKey: d.Peer.Handshake.PresharedKey[:],
		PrivateKey:   d.StaticIdentity.PrivateKey[:],
		LocalStatic:  d.StaticIdentity.PublicKey[:],
		LocalIndex:   localIndex,
		RemoteStatic: d.Peer.Handshake.RemoteStatic[:],
	}
	return
}

const MacSize int = 16
const NonceSize int = 12
const KeySize int = 32
const HashSize int = 32

type Request struct {
	Type      uint32
	Sender    uint32     // sid_I
	Ephemeral ByteString // epk_I    len == 32
	Static    ByteString // c_pk_I   len == 32 + 16
	Timestamp ByteString // c_ts     len == 12 + 16
	MAC1      ByteString //          len == 16
	MAC2      ByteString //          len == 16
}

type Response struct {
	Type      uint32
	Sender    uint32     // sid_R
	Receiver  uint32     // sid_I
	Ephemeral ByteString // epk_R    len == 32
	Empty     ByteString // c_empty  len == 0 + 16
	MAC1      ByteString //          len == 16
	MAC2      ByteString //          len == 16
}

type Message struct {
	Type     uint32
	Receiver uint32
	Nonce    uint64
	Payload  ByteString
}

type Handshake struct {
	ChainHash       ByteString // hN          len == 32
	ChainKey        ByteString // cN          len == 32
	LocalEphemeral  ByteString // ek_self     len == 32
	RemoteIndex     uint32     // sid_other
	RemoteEphemeral ByteString // epk_other   len == 32
}

type HandshakeArguments struct {
	PresharedKey ByteString // psk             len == 32
	PrivateKey   ByteString // k_self          len == 32
	LocalIndex   uint32     // sid_self        len == 32
	LocalStatic  ByteString // pk_self         len == 32
	RemoteStatic ByteString // pk_other        len == 32
}

type Connection struct {
	Nonce       uint64
	SendKey     ByteString
	RecvKey     ByteString
	RemoteIndex uint32
}

/* predicates and pure functions */

//@ trusted
//@ requires acc(lib.Mem(b1), 1/200) && acc(lib.Mem(b2), 1/200)
//@ ensures res == (lib.Abs(b1) == lib.Abs(b2))
//@ pure
func IsEqual(b1, b2 ByteString) (res bool) {
	s1, s2 := lib.Size(b1), lib.Size(b2)
	if s1 != s2 {
		return false
	}
	for i := 0; i < s1; i++ {
		if b1[i] != b2[i] {
			return false
		}
	}
	return true
}

/*@
pred LibMem(libState *LibraryState)

ghost
pure func principalId(id uint32) (res p.Id) {
	return p.principalId(Principal(id))
}
@*/

// we perform an injective uint32 to string conversion
//@ trusted
//@ decreases _
//@ ensures forall id2 uint32 :: id != id2 ==> res != Principal(id2)
//@ pure
func Principal(id uint32) (res p.Principal) {
	return fmt.Sprint(id)
}

/*@
pred RequestMem(request *Request) {
	acc(request) && lib.Mem(request.Ephemeral) && lib.Mem(request.Static) && lib.Mem(request.Timestamp) &&
	lib.Size(request.Ephemeral) == 32 && lib.Size(request.Static) == 48 && lib.Size(request.Timestamp) == 28 &&
	(request.MAC1 != nil ==> lib.Mem(request.MAC1) && lib.Size(request.MAC1) == 16) &&
	(request.MAC2 != nil ==> lib.Mem(request.MAC2) && lib.Size(request.MAC2) == 16)
}

ghost
requires acc(RequestMem(request), _)
ensures res == (unfolding acc(RequestMem(request), _) in lib.SafeAbs(request.MAC1,16))
pure func RequestMac1(request *Request) (res tm.Bytes)

ghost
requires acc(RequestMem(request), _)
ensures res == (unfolding acc(RequestMem(request), _) in lib.SafeAbs(request.MAC2,16))
pure func RequestMac2(request *Request) (res tm.Bytes)


ghost
requires acc(RequestMem(request), _)
ensures  res == (unfolding acc(RequestMem(request), _) in tm.tuple7B(tm.integer32B(request.Type),tm.integer32B(request.Sender),lib.Abs(request.Ephemeral),lib.Abs(request.Static),lib.Abs(request.Timestamp),lib.SafeAbs(request.MAC1,16),lib.SafeAbs(request.MAC2,16)))
pure func RequestAbs(request *Request) (res tm.Bytes)

pred ResponseMem(response *Response) {
	acc(response) && lib.Mem(response.Ephemeral) && lib.Mem(response.Empty) &&
	lib.Size(response.Ephemeral) == 32 && lib.Size(response.Empty) == 16 &&
	(response.MAC1 != nil ==> lib.Mem(response.MAC1) && lib.Size(response.MAC1) == 16) &&
	(response.MAC2 != nil ==> lib.Mem(response.MAC2) && lib.Size(response.MAC2) == 16)
}

ghost
requires acc(ResponseMem(response), _)
ensures res == (unfolding acc(ResponseMem(response), _) in lib.Abs(response.Ephemeral))
pure func ResponseEpkR(response *Response) (res tm.Bytes)

ghost
requires acc(ResponseMem(response), _)
ensures res == (unfolding acc(ResponseMem(response), _) in lib.SafeAbs(response.MAC1,16))
pure func ResponseMac1(response *Response) (res tm.Bytes)

ghost
requires acc(ResponseMem(response), _)
ensures res == (unfolding acc(ResponseMem(response), _) in lib.SafeAbs(response.MAC2,16))
pure func ResponseMac2(response *Response) (res tm.Bytes)

ghost
requires acc(ResponseMem(response), _)
pure func ResponseAbs(response *Response) (res tm.Bytes) {
	return unfolding acc(ResponseMem(response), _) in tm.tuple7B(tm.integer32B(response.Type),tm.integer32B(response.Sender),tm.integer32B(response.Receiver),lib.Abs(response.Ephemeral),lib.Abs(response.Empty),lib.SafeAbs(response.MAC1,16),lib.SafeAbs(response.MAC2,16))
}

pred ConnectionMem(conn *Connection) {
	acc(conn) && lib.Mem(conn.SendKey) && lib.Mem(conn.RecvKey) &&
	lib.Size(conn.SendKey) == 32 && lib.Size(conn.RecvKey) == 32
}

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in lib.Abs(conn.SendKey))
pure func ConnectionSendKey(conn *Connection) (res tm.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in lib.Abs(conn.RecvKey))
pure func ConnectionRecvKey(conn *Connection) (res tm.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in tm.integer32B(conn.RemoteIndex))
pure func ConnectionSidI(conn *Connection) (res tm.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in tm.integer64B(conn.Nonce))
pure func ConnectionNonce(conn *Connection) (res tm.Bytes)

ghost
requires acc(ConnectionMem(conn), _)
ensures res == (unfolding acc(ConnectionMem(conn), _) in conn.Nonce)
pure func ConnectionNonceVal(conn *Connection) (res uint64)

pred HandshakeArgsMem(args *HandshakeArguments) {
	acc(args) &&lib. Mem(args.PresharedKey) && lib.Mem(args.PrivateKey) && lib.Mem(args.LocalStatic) && lib.Mem(args.RemoteStatic) &&
	lib.Size(args.PresharedKey) == 32 && lib.Size(args.PrivateKey) == 32 && lib.Size(args.LocalStatic) == 32 && lib.Size(args.RemoteStatic) == 32 &&
	lib.Abs(args.LocalStatic) == tm.expB(tm.generatorB(), lib.Abs(args.PrivateKey))
}
@*/
