package library

import (
	rand "crypto/rand"
	binary "encoding/binary"
	device "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/device"

	blake2s "golang.org/x/crypto/blake2s"
	chacha20poly1305 "golang.org/x/crypto/chacha20poly1305"

	bytes "bytes"
	subtle "crypto/subtle"

	//@ . "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	//@ by "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
)


const wireguardString string = "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s"
const preludeString string = "WireGuard v1 zx2c4 Jason@zx2c4.com"

//@ trusted
//@ requires n >= 0
//@ ensures  Mem(res) && Size(res) == n
func NewByteString(n int) (res ByteString) {
	return make([]byte, n)
}

//@ trusted
//@ ensures Mem(res)
//@ ensures Abs(res) == by.infoBytesB()
func WireGuardBytes() (res ByteString) {
	return []byte(wireguardString)
}

//@ trusted
//@ ensures Mem(res)
//@ ensures Abs(res) == by.prologueBytesB()
func PreludeBytes() (res ByteString) {
	return []byte(preludeString)
}

/* crypto */

// res == hash(data) && len(res) == 32
//@ trusted
//@ requires acc(Mem(data), 1/16)
//@ ensures  acc(Mem(data), 1/16) && Mem(res) && Size(res) == 32
//@ ensures  Abs(res) == by.hashB(Abs(data))
func ComputeSingleHash(data ByteString) (res ByteString) {
	temp := blake2s.Sum256(data)
	return temp[:]
}

// dst == hash(h, data) && len(dst) == 32
//@ trusted
//@ requires Mem(dst) && acc(Mem(h), 1/16) && acc(Mem(data), 1/16)
//@ requires Size(dst) == 32 && Size(h) == 32
//@ ensures  Mem(dst) && acc(Mem(h), 1/16) && acc(Mem(data), 1/16)
//@ ensures  Size(dst) == 32
//@ ensures  Abs(dst) == by.hashB(by.tuple2B(Abs(h), Abs(data)))
func ComputeHash(dst, h, data ByteString) {
	hash, _ := blake2s.New256(nil)
	hash.Write(h[:])
	hash.Write(data)
	hash.Sum(dst[:0])
	hash.Reset()
}

// h == hash(old(h), data) && len(h) == 32
//@ trusted
//@ requires Mem(h) && acc(Mem(data), 1/16)
//@ requires Size(h) == 32
//@ ensures  Mem(h) && acc(Mem(data), 1/16)
//@ ensures  Size(h) == 32
//@ ensures  Abs(h) == by.hashB(by.tuple2B(old(Abs(h)), Abs(data)))
func ComputeHashInplace(h, data ByteString) {
	hash, _ := blake2s.New256(nil)
	hash.Write(h[:])
	hash.Write(data)
	hash.Sum(h[:0])
	hash.Reset()
}

// dst == kdf1(c, data) && len(dst) == 32
//@ trusted
//@ requires Mem(dst) && acc(Mem(c), 1/16) && acc(Mem(data), 1/16)
//@ requires Size(dst) == 32 && Size(c) == 32
//@ ensures  Mem(dst) && acc(Mem(c), 1/16) && acc(Mem(data), 1/16)
//@ ensures  Size(dst) == 32
//@ ensures  Abs(dst) == by.kdf1B(by.tuple2B(Abs(c), Abs(data)))
func ComputeKDF1(dst, c, data ByteString) {
	device.KDF1Slice(dst, c, data)
}

// h == KDF1(old(h), data) && len(h) == 32
//@ trusted
//@ requires Mem(h) && acc(Mem(data), 1/16)
//@ requires Size(h) == 32
//@ ensures  Mem(h) && acc(Mem(data), 1/16)
//@ ensures  Size(h) == 32
//@ ensures  Abs(h) == by.kdf1B(by.tuple2B(old(Abs(h)), Abs(data)))
func ComputeKDF1Inplace(h, data ByteString) {
	device.KDF1Slice(h, h, data)
}

// t0 = kdf1(key, input) && len(t0) == 32
// t1 = kdf2(key, input) && len(t1) == 32
//@ trusted
//@ requires Mem(t0) && Mem(t1) && acc(Mem(key), 1/16)
//@ requires input != nil ==> acc(Mem(input), 1/16)
//@ requires Size(t0) == 32 && Size(t1) == 32 && Size(key) == 32
//@ ensures  Mem(t0) && Mem(t1) && acc(Mem(key), 1/16)
//@ ensures  input != nil ==> acc(Mem(input), 1/16)
//@ ensures  Size(t0) == 32 && Size(t1) == 32
//@ ensures  input != nil ==> Abs(t0) == by.kdf1B(by.tuple2B(Abs(key), Abs(input)))
//@ ensures  input != nil ==> Abs(t1) == by.kdf2B(by.tuple2B(Abs(key), Abs(input)))
//@ ensures  input == nil ==> Abs(t0) == by.kdf1B(Abs(key))
//@ ensures  input == nil ==> Abs(t1) == by.kdf2B(Abs(key))
func ComputeKDF2(t0, t1, key, input ByteString) {
	device.KDF2Slice(t0, t1, key, input)
}

// chainKey = kdf1(old(chainKey), input) && len(chainKey) == 32
// t1 = kdf2(old(chainKey), input) && len(t1) == 32
//@ trusted
//@ requires Mem(t1) && Mem(chainKey) && acc(Mem(input), 1/16)
//@ requires Size(t1) == 32 && Size(chainKey) == 32
//@ ensures  Mem(t1) && Mem(chainKey) && acc(Mem(input), 1/16)
//@ ensures  Size(t1) == 32 && Size(chainKey) == 32
//@ ensures  Abs(chainKey) == by.kdf1B(by.tuple2B(old(Abs(chainKey)), Abs(input)))
//@ ensures  Abs(t1) == by.kdf2B(by.tuple2B(old(Abs(chainKey)), Abs(input)))
func ComputeKDF2Inplace(t1, chainKey, input ByteString) {
	device.KDF2Slice(chainKey, t1, chainKey, input)
}

// chainkey = kdf1(old(chainKey), input) && len(chainKey) == 32
// t1 = kdf2(old(chainKey), input) && len(t1) == 32
// t2 = kdf3(old(chainKey), input) && len(t2) == 32
//@ trusted
//@ requires Mem(t1) && Mem(t2) && Mem(chainKey) && acc(Mem(input), 1/16)
//@ requires Size(t1) == 32 && Size(t2) == 32 && Size(chainKey) == 32
//@ ensures  Mem(t1) && Mem(t2) && Mem(chainKey) && acc(Mem(input), 1/16)
//@ ensures  Size(t1) == 32 && Size(t2) == 32 && Size(chainKey) == 32
//@ ensures  Abs(chainKey) == by.kdf1B(by.tuple2B(old(Abs(chainKey)), Abs(input)))
//@ ensures  Abs(t1) == by.kdf2B(by.tuple2B(old(Abs(chainKey)), Abs(input)))
//@ ensures  Abs(t2) == by.kdf3B(by.tuple2B(old(Abs(chainKey)), Abs(input)))
func ComputeKDF3Inplace(t1, t2, chainKey, input ByteString) {
	device.KDF3Slice(chainKey, t1, t2, chainKey, input)
}

//@ trusted
//@ requires Mem(dst) && acc(Mem(key), 1/16) && acc(Mem(data), 1/16)
//@ requires Size(dst) == 16 && Size(key) == 32
//@ ensures  Mem(dst) && acc(Mem(key), 1/16) && acc(Mem(data), 1/16)
//@ ensures  Size(dst) == 16
func ComputeMac(dst, key, data ByteString) {
	mac, _ := blake2s.New128(key)
	mac.Write(data)
	mac.Sum(dst[:0])
	mac.Reset()
}

// pk == g^sk && len(pk) == 32
//@ trusted
//@ requires acc(Mem(sk), 1/16) && Size(sk) == 32
//@ ensures  acc(Mem(sk), 1/16) && Mem(pk) && Size(pk) == 32
//@ ensures  Abs(pk) == by.expB(by.generatorB(),Abs(sk))
func PublicKey(sk ByteString) (pk ByteString) {
	var noiseSK device.NoisePrivateKey
	copy(noiseSK[:], sk)
	temp := noiseSK.PublicKey()
	return temp[:]
}

// ss == pk^sk && len(ss) == 32
//@ trusted
//@ requires acc(Mem(sk), 1/16) && acc(Mem(pk), 1/16) && Size(sk) == 32 && Size(pk) == 32
//@ ensures  acc(Mem(sk), 1/16) && acc(Mem(pk), 1/16) && Mem(ss) && Size(ss) == 32
//@ ensures  Abs(ss) == by.expB(Abs(pk), Abs(sk))
func ComputeSharedSecret(sk, pk ByteString) (ss ByteString) {
	var noiseSK device.NoisePrivateKey
	copy(noiseSK[:], sk)
	var noisePK device.NoisePublicKey
	copy(noisePK[:], pk)
	temp := noiseSK.SharedSecret(noisePK)
	return temp[:]
}

//@ trusted
//@ requires acc(Mem(pk1), 1/16) && acc(Mem(pk2), 1/16)
//@ ensures  acc(Mem(pk1), 1/16) && acc(Mem(pk2), 1/16)
//@ ensures  res == (Abs(pk1) == Abs(pk2))
func EqualsSlice(pk1, pk2 ByteString) (res bool) {
	return subtle.ConstantTimeCompare(pk1, pk2) == 1
}

//@ trusted
func RandUint32() (v uint32, success bool) {
	var integer [4]byte
	_, err := rand.Read(integer[:])
	// Arbitrary endianness; both are intrinsified by the Go compiler.
	return binary.LittleEndian.Uint32(integer[:]), err == nil
}

//@ trusted
//@ ensures Mem(nonce) && Size(nonce) == 12
//@ ensures Abs(nonce) == by.zeroStringB(12)
func ZeroNonce() (nonce ByteString) {
	nonce = make([]byte, 12)
	return
}

//@ trusted
//@ requires Mem(arr)
//@ ensures  Mem(arr) && Size(arr) == old(Size(arr))
func SetZero(arr ByteString) {
	for i := range arr {
		arr[i] = 0
	}
}

//@ trusted
//@ requires acc(Mem(val), 1/16)
//@ ensures  acc(Mem(val), 1/16)
func IsZero(val ByteString) bool {
	accumulator := 1
	for _, b := range val {
		accumulator &= subtle.ConstantTimeByteEq(b, 0)
	}
	return accumulator == 1
}

// alpha(res) == Nonce(nonce) && len(res) == 12
//@ trusted
//@ ensures Mem(res) && Size(res) == 12
//@ ensures Abs(res) == by.integer64B(nonce)
func NonceToBytes(nonce uint64) (res ByteString) {
	var nonceBytes [chacha20poly1305.NonceSize]byte
	binary.LittleEndian.PutUint64(nonceBytes[4:], nonce)
	return nonceBytes[:]
}

//@ trusted
//@ requires Mem(payload)
//@ ensures  Mem(res) && Size(res) == old(Size(payload)) + 16
func CombineMsg(t uint32, sid uint32, nonce uint64, payload ByteString) (res ByteString) {
	res = make([]byte, 16+len(payload))
	binary.LittleEndian.PutUint32(res[0:4], t)
	binary.LittleEndian.PutUint32(res[4:8], sid)
	binary.LittleEndian.PutUint64(res[8:16], nonce)
	copy(res[16:], payload)
	return res[:]
}

//@ trusted
//@ requires acc(RequestMem(req), 1/16)
//@ ensures  acc(RequestMem(req), 1/16) && Mem(res) && Size(res) == 148
//@ ensures  RequestAbs(req) == Abs(res)
func MarshalRequest(req *Request) (res ByteString) {
	var buff [device.MessageInitiationSize]byte
	writer := bytes.NewBuffer(buff[:0])

	temp := &device.MessageInitiation{}
	temp.Type = req.Type
	temp.Sender = req.Sender
	copy(temp.Ephemeral[:], req.Ephemeral[:])
	copy(temp.Static[:], req.Static[:])
	copy(temp.Timestamp[:], req.Timestamp[:])
	copy(temp.MAC1[:], req.MAC1[:])
	copy(temp.MAC2[:], req.MAC2[:])

	binary.Write(writer, binary.LittleEndian, temp)
	return writer.Bytes()
}

//@ trusted
//@ requires acc(Mem(packet), 1/16)
//@ ensures  acc(Mem(packet), 1/16)
//@ ensures  ok ==> Size(packet) == 148 && RequestMem(req)
//@ ensures  ok ==> Abs(packet) == RequestAbs(req)
func UnmarshalRequest(packet ByteString) (req *Request, ok bool) {
	msgType := getMsgType(packet)
	if msgType != device.MessageInitiationType {
		return nil, false
	} else if len(packet) != device.MessageInitiationSize {
		return nil, false
	}

	reader := bytes.NewReader(packet)
	temp := &device.MessageInitiation{}
	err := binary.Read(reader, binary.LittleEndian, temp)
	ok = err == nil
	if ok {
		req = &Request{
			Type:      temp.Type,
			Sender:    temp.Sender,
			Ephemeral: temp.Ephemeral[:],
			Static:    temp.Static[:],
			Timestamp: temp.Timestamp[:],
			MAC1:      temp.MAC1[:],
			MAC2:      temp.MAC2[:],
		}
	}
	return
}

//@ trusted
//@ requires acc(ResponseMem(response), 1/16)
//@ ensures  acc(ResponseMem(response), 1/16) && Mem(res) && Size(res) == 92
//@ ensures  Abs(res) == ResponseAbs(response)
func MarshalResponse(response *Response) (res ByteString) {
	var buff [device.MessageResponseSize]byte
	writer := bytes.NewBuffer(buff[:0])

	temp := &device.MessageResponse{}
	temp.Type = response.Type
	temp.Sender = response.Sender
	temp.Receiver = response.Receiver
	copy(temp.Ephemeral[:], response.Ephemeral[:])
	copy(temp.Empty[:], response.Empty[:])
	copy(temp.MAC1[:], response.MAC1[:])
	copy(temp.MAC2[:], response.MAC2[:])

	binary.Write(writer, binary.LittleEndian, temp)
	return writer.Bytes()
}

//@ trusted
//@ requires acc(Mem(packet), 1/16)
//@ ensures  acc(Mem(packet), 1/16)
//@ ensures  ok ==> Size(packet) == 92 && ResponseMem(response)
//@ ensures  ok ==> Abs(packet) == ResponseAbs(response)
func UnmarshalResponse(packet ByteString) (response *Response, ok bool) {
	msgType := getMsgType(packet)
	if msgType != device.MessageResponseType {
		return nil, false
	} else if len(packet) != device.MessageResponseSize {
		return nil, false
	}

	// unmarshal
	reader := bytes.NewReader(packet)
	temp := &device.MessageResponse{}
	err := binary.Read(reader, binary.LittleEndian, temp)
	ok = err == nil
	if ok {
		response = &Response{
			Type:      temp.Type,
			Sender:    temp.Sender,
			Receiver:  temp.Receiver,
			Ephemeral: temp.Ephemeral[:],
			Empty:     temp.Empty[:],
			MAC1:      temp.MAC1[:],
			MAC2:      temp.MAC2[:],
		}
	}
	return
}

//@ trusted
//@ requires acc(message, 1/16) && acc(Mem(message.Payload), 1/16) && Size(message.Payload) >= 16
//@ ensures  acc(message, 1/16) && acc(Mem(message.Payload), 1/16) && Mem(res) && Size(res) == Size(message.Payload) + 16
//@ ensures  Abs(res) == by.tuple4B(by.integer32B(message.Type),by.integer32B(message.Receiver),by.integer64B(message.Nonce),Abs(message.Payload))
func MarshalMessage(message *Message) (res ByteString) {
	var buff []byte = make([]byte, len(message.Payload)+16)

	fieldType := buff[0:4]
	fieldReceiver := buff[4:8]
	fieldNonce := buff[8:16]

	binary.LittleEndian.PutUint32(fieldType, message.Type)
	binary.LittleEndian.PutUint32(fieldReceiver, message.Receiver)
	binary.LittleEndian.PutUint64(fieldNonce, message.Nonce)
	copy(buff[16:], message.Payload)

	return buff
}

//@ trusted
//@ requires acc(Mem(packet), 1/16)
//@ ensures  acc(Mem(packet), 1/16)
//@ ensures  ok ==> Size(packet) >= 16 && acc(message) && Mem(message.Payload) && Size(message.Payload) == Size(packet) - 16
//@ ensures  ok ==> Abs(packet) == by.tuple4B(by.integer32B(message.Type),by.integer32B(message.Receiver),by.integer64B(message.Nonce),Abs(message.Payload))
func UnmarshalMessage(packet ByteString) (message *Message, ok bool) {
	msgType := getMsgType(packet)
	if msgType != device.MessageTransportType {
		return nil, false
	} else if len(packet) < device.MessageTransportSize {
		return nil, false
	}

	receiver := binary.LittleEndian.Uint32(
		packet[device.MessageTransportOffsetReceiver:device.MessageTransportOffsetCounter],
	)

	nonce := binary.LittleEndian.Uint64(
		packet[device.MessageTransportOffsetCounter:device.MessageTransportOffsetContent],
	)

	message = &Message{
		Type:     device.MessageTransportType,
		Receiver: receiver,
		Nonce:    nonce,
		Payload:  make([]byte, len(packet)-device.MessageTransportOffsetContent),
	}

	sizePayload := copy(message.Payload, packet[device.MessageTransportOffsetContent:])

	ok = len(packet) == sizePayload+device.MessageTransportOffsetContent
	return
}
