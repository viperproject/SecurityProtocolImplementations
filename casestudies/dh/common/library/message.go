package library

import (
	"encoding/binary"
	"errors"
	"fmt"
	"math"
	. "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	//@ . "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
)


const Msg2Tag uint32 = 0
const Msg3Tag uint32 = 1

type Msg1 struct {
	X []byte
}

type Msg2 struct {
	IdA string
	IdB string
	X []byte
	Y []byte
}

type Msg3 struct {
	IdA string
	IdB string
	X []byte
	Y []byte
}

/*@
pred (m *Msg1) Mem() {
	acc(m) && Mem(m.X)
}

pred (m *Msg2) Mem() {
	acc(m) && Mem(m.X) && Mem(m.Y)
}

pred (m *Msg3) Mem() {
	acc(m) && Mem(m.Y) && Mem(m.X)
}
@*/

//@ trusted
//@ preserves acc(msg1.Mem(), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == (unfolding acc(msg1.Mem(), 1/16) in Abs(msg1.X))
func MarshalMsg1(msg1 *Msg1) (res []byte, err error) {
	res = make([]byte, len(msg1.X))
	copy(res, msg1.X)
	return res, nil
}

//@ trusted
//@ preserves acc(Mem(data), 1/16)
//@ ensures err == nil ==> res.Mem()
//@ ensures err == nil ==> Abs(data) == (unfolding acc(res.Mem(), 1/16) in Abs(res.X))
func UnmarshalMsg1(data []byte) (res *Msg1, err error) {
	if len(data) < DHHalfKeyLength {
		return nil, errors.New("msg1 is too short")
	}

	X := data[:DHHalfKeyLength]

	return &Msg1{X: X}, nil
}

//@ trusted
//@ preserves acc(msg2.Mem(), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == (unfolding acc(msg2.Mem(), 1/16) in tuple5B(integer32B(Msg2Tag), stringB(msg2.IdB), stringB(msg2.IdA), Abs(msg2.X), Abs(msg2.Y)))
func MarshalMsg2(msg2 *Msg2) (res []byte, err error) {
	idA := []byte(msg2.IdA)
	idB := []byte(msg2.IdB)
	idALen := len(idA)
	idBLen := len(idB)
	if idALen > math.MaxUint32 || idBLen > math.MaxUint32 {
		return nil, errors.New("id is too long")
	}
	res = make([]byte, 12 + idALen + idBLen)
	binary.BigEndian.PutUint32(res[:4], Msg2Tag)
	// note that idB occurs before idA in the 2nd message:
	binary.BigEndian.PutUint32(res[4:8], uint32(idBLen))
	binary.BigEndian.PutUint32(res[8:12], uint32(idALen))
	copy(res[12:12+idBLen], idB)
	copy(res[12+idBLen:12+idBLen+idALen], idA)
	res = append(res, msg2.X...)
	return append(res, msg2.Y...), nil
}

//@ trusted
//@ preserves acc(Mem(data), 1/16)
//@ ensures err == nil ==> res.Mem()
//@ ensures err == nil ==> Abs(data) == (unfolding acc(res.Mem(), 1/16) in tuple5B(integer32B(Msg2Tag), stringB(res.IdB), stringB(res.IdA), Abs(res.X), Abs(res.Y)))
func UnmarshalMsg2(data []byte) (res *Msg2, err error) {
	dataLen := len(data)
	if dataLen < 2 * DHHalfKeyLength + 12 {
		return nil, errors.New("msg2 is too short")
	}
	if dataLen > math.MaxUint32 {
		return nil, errors.New("msg2 is too long")
	}

	tag := binary.BigEndian.Uint32(data[:4])
	// note that idB occurs before idA in the 2nd message:
	idBLen := binary.BigEndian.Uint32(data[4:8])
	idALen := binary.BigEndian.Uint32(data[8:12])
	if uint32(dataLen) < 2 * DHHalfKeyLength + 12 + idBLen + idALen {
		return nil, errors.New("msg2 is too short")
	}
	idB := string(data[12:12+idBLen])
	idA := string(data[12+idBLen:12+idBLen+idALen])
	X := data[12+idBLen+idALen:(DHHalfKeyLength + 12+idBLen+idALen)]
	Y := data[(DHHalfKeyLength + 12+idBLen+idALen):(2 * DHHalfKeyLength + 12+idBLen+idALen)]

	if tag != Msg2Tag {
		return nil, errors.New("unexpected message tag in msg2")
	}

	return &Msg2{IdA: idA, IdB: idB, X: X, Y: Y}, nil
}

//@ trusted
//@ preserves acc(msg3.Mem(), 1/16)
//@ ensures err == nil ==> Mem(res)
//@ ensures err == nil ==> Abs(res) == (unfolding acc(msg3.Mem(), 1/16) in tuple5B(integer32B(Msg3Tag), stringB(msg3.IdA), stringB(msg3.IdB), Abs(msg3.Y), Abs(msg3.X)))
func MarshalMsg3(msg3 *Msg3) (res []byte, err error) {
	idA := []byte(msg3.IdA)
	idB := []byte(msg3.IdB)
	idALen := len(idA)
	idBLen := len(idB)
	if idALen > math.MaxUint32 || idBLen > math.MaxUint32 {
		return nil, errors.New("id is too long")
	}
	res = make([]byte, 12 + idALen + idBLen)
	binary.BigEndian.PutUint32(res[:4], Msg3Tag)
	binary.BigEndian.PutUint32(res[4:8], uint32(idALen))
	binary.BigEndian.PutUint32(res[8:12], uint32(idBLen))
	copy(res[12:12+idALen], idA)
	copy(res[12+idALen:12+idALen+idBLen], idB)
	// note that Y occurs before X in the 3rd message:
	res = append(res, msg3.Y...)
	return append(res, msg3.X...), nil
}

//@ trusted
//@ preserves acc(Mem(data), 1/16)
//@ ensures err == nil ==> res.Mem()
//@ ensures err == nil ==> Abs(data) == (unfolding acc(res.Mem(), 1/16) in tuple5B(integer32B(Msg3Tag), stringB(res.IdA), stringB(res.IdB), Abs(res.Y), Abs(res.X)))
func UnmarshalMsg3(data []byte) (res *Msg3, err error) {
	dataLen := len(data)
	if dataLen < 2 * DHHalfKeyLength + 12 {
		return nil, errors.New("msg3 is too short")
	}
	if dataLen > math.MaxUint32 {
		return nil, errors.New("msg3 is too long")
	}

	tag := binary.BigEndian.Uint32(data[:4])
	idALen := binary.BigEndian.Uint32(data[4:8])
	idBLen := binary.BigEndian.Uint32(data[8:12])
	if uint32(dataLen) < 2 * DHHalfKeyLength + 12 + idALen + idBLen {
		return nil, errors.New("msg3 is too short")
	}
	idA := string(data[12:12+idALen])
	idB := string(data[12+idALen:12+idALen+idBLen])
	// note that Y occurs before X in the 3rd message:
	Y := data[12+idBLen+idALen:(DHHalfKeyLength + 12+idBLen+idALen)]
	X := data[(DHHalfKeyLength + 12+idBLen+idALen):(2 * DHHalfKeyLength + 12+idBLen+idALen)]

	if tag != Msg3Tag {
		return nil, errors.New("unexpected message tag in msg3")
	}

	return &Msg3{IdA: idA, IdB: idB, X: X, Y: Y}, nil
}

//@ trusted
//@ decreases
//@ preserves acc(Mem(sharedSecret), 1/16)
func PrintInitiatorSuccess(sharedSecret ByteString) {
	fmt.Println("A has successfully finished the protocol run")
	fmt.Println("Shared secret: ", sharedSecret)
}

//@ trusted
//@ decreases
//@ preserves acc(Mem(sharedSecret), 1/16)
func PrintResponderSuccess(sharedSecret ByteString) {
	fmt.Println("B has successfully finished the protocol run")
	fmt.Println("Shared secret: ", sharedSecret)
}
