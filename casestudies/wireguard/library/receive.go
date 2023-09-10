package library

import (
	bytes "bytes"
	binary "encoding/binary"
	device "github.com/viperproject/ProtocolVerificationCaseStudies/wireguard/device"

	ipv4 "golang.org/x/net/ipv4"
	ipv6 "golang.org/x/net/ipv6"

	lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
)


//@ trusted
//@ requires acc(LibMem(libState), 1/16)
//@ ensures  acc(LibMem(libState), 1/16)
//@ ensures  err == nil ==> lib.Mem(packet) && tm.gamma(msgT) == lib.Abs(packet)
//@ ensures  err == nil ==> snapshot.messageOccurs(idSender, idReceiver, msgT)
func (libState *LibraryState) Receive(idSender, idReceiver p.Principal /*@, ghost snapshot tr.TraceEntry @*/) (packet lib.ByteString, err error /*@, ghost msgT tm.Term @*/) {
	packet, err = libState.receiveBuffer()
	return
}

//@ trusted
//@ requires acc(LibMem(libState), 1/16)
//@ ensures  acc(LibMem(libState), 1/16)
//@ ensures  ok ==> lib.Mem(res) && tm.gamma(term) == lib.Abs(res)
func (libState *LibraryState) GetPacket() (res lib.ByteString, ok bool /*@, ghost term tm.Term @*/) {
	res, ok = <-libState.input
	return
}

//@ trusted
func (libState *LibraryState) ReceiveRequest() (req *Request, ok bool) {
	packet, err := libState.receiveBuffer()
	ok = err == nil
	if !ok {
		return
	}

	msgType := getMsgType(packet)
	if msgType != device.MessageInitiationType {
		return nil, false
	} else if len(packet) != device.MessageInitiationSize {
		return nil, false
	}

	// unmarshal
	reader := bytes.NewReader(packet)
	temp := &device.MessageInitiation{}
	err = binary.Read(reader, binary.LittleEndian, temp)
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
func (libState *LibraryState) ReceiveResponse() (response *Response, ok bool) {
	packet, err := libState.receiveBuffer()
	ok = err == nil
	if !ok {
		return
	}

	msgType := getMsgType(packet)
	if msgType != device.MessageResponseType {
		return nil, false
	} else if len(packet) != device.MessageResponseSize {
		return nil, false
	}

	// unmarshal
	reader := bytes.NewReader(packet)
	temp := &device.MessageResponse{}
	err = binary.Read(reader, binary.LittleEndian, temp)
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
func (libState *LibraryState) ReceiveMessage() (response *Message, ok bool) {
	packet, err := libState.receiveBuffer()
	ok = err == nil
	if !ok {
		return
	}

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

	response = &Message{
		Type:     device.MessageTransportType,
		Receiver: receiver,
		Nonce:    nonce,
		Payload:  make([]byte, len(packet)-device.MessageTransportOffsetContent),
	}

	sizePayload := copy(response.Payload, packet[device.MessageTransportOffsetContent:])

	ok = len(packet) == sizePayload+device.MessageTransportOffsetContent
	return
}

//@ trusted
func (libState *LibraryState) receiveBuffer() ([]byte, error) {
	var buffer [device.MaxMessageSize]byte
	switch libState.dev.IP {
	case ipv4.Version:
		size, _, err := libState.dev.Net.Bind.ReceiveIPv4(buffer[:])
		packet := buffer[:size]
		return packet, err
	case ipv6.Version:
		size, _, err := libState.dev.Net.Bind.ReceiveIPv6(buffer[:])
		packet := buffer[:size]
		return packet, err
	default:
		panic("invalid IP version")
	}
}

//@ trusted
func getMsgType(packet []byte) uint32 {
	return binary.LittleEndian.Uint32(packet[:4])
}
