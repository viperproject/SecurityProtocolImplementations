// Diffie-Hellman key exchange

// Tamarin:
// A∶ knows(sk(A),pk(B))
// B∶ knows(sk(B),pk(A))
// A∶ fresh(x)
// 1: A -> B∶ g^x
// B∶ fresh(y)
// 2: B -> A∶ sign(⟨0, B, A, g^x, g^y⟩, sk(b))
// 3: A -> B∶ sign(⟨1, A, B, g^y, g^x⟩, sk(a))

// we prove secrecy and injective agreement on (g^x)^y.


package main

import (
	"sync"
	chanCom "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/channelcommunication"
	lib "github.com/viperproject/ReusableProtocolVerificationLibrary/labeledlibrary/library"
	//@ "github.com/viperproject/ReusableProtocolVerificationLibrary/labeling"
	"github.com/viperproject/ProtocolVerificationCaseStudies/dh/initiator"
	"github.com/viperproject/ProtocolVerificationCaseStudies/dh/responder"
	//@ common "github.com/viperproject/ProtocolVerificationCaseStudies/dh/common"
	//@ p "github.com/viperproject/ReusableProtocolVerificationLibrary/principal"
	//@ tm "github.com/viperproject/ReusableProtocolVerificationLibrary/term"
	//@ tr "github.com/viperproject/ReusableProtocolVerificationLibrary/trace"
	//@ tri "github.com/viperproject/ReusableProtocolVerificationLibrary/traceinvariant"
	//@ tman "github.com/viperproject/ReusableProtocolVerificationLibrary/tracemanager"
)

/*@
// TODO make it ghost
decreases
ensures res == tr.makeRoot(set[tm.Term]{})
func getRootTrace() (res tr.TraceEntry)

// TODO make it ghost
decreases
ensures res == tm.zeroString(0)
func getDefaultTerm() (res tm.Term)
@*/

// we can't show termination in Gobra (yet) as we cannot discharge the proof
// obligation that `wg.Wait(...)` eventually returns.
func main() {
	//@ root := getRootTrace()
	//@ defaultTerm := getDefaultTerm()
	a, b, err := initPrincipals(/*@ root, defaultTerm @*/)
	if err == nil {
		// wait for the following go routines
		wg := &sync.WaitGroup{}
		//@ wg.Init()
		wg.Add(2 /*@, writePerm, PredTrue!<!>@*/)
		//@ fold PredTrue!<!>()
		//@ wg.GenerateTokenAndDebt(PredTrue!<!>)
		//@ wg.Start(1/2, PredTrue!<!>)
		// run in parallel:
		go workerA(wg, a /*@, defaultTerm @*/)
		go workerB(wg, b /*@, defaultTerm @*/)
		//@ wg.SetWaitMode(1/2, 1/2)
		wg.Wait(/*@ 1/1, seq[pred()]{ } @*/)
		lib.Println("Program has ended")
	} else {
		lib.Println("Initialization failed")
	}
}

//@ requires root == tr.makeRoot(set[tm.Term]{})
//@ requires defaultTerm == tm.zeroString(0)
//@ ensures err == nil ==> a.Mem(defaultTerm, defaultTerm) && a.Vers(defaultTerm, defaultTerm) == 1
//@ ensures err == nil ==> b.Mem(defaultTerm, defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm, defaultTerm) == 1
// TODO remove these two dummy arguments and make them ghost
func initPrincipals(/*@ root tr.TraceEntry, defaultTerm tm.Term @*/) (a *initiator.A, b *responder.B, err error) {
	pInitiator := "Initiator"
	//@ initiatorId := p.NewPrincipalId(pInitiator)
	pResponder := "Responder"
	//@ responderId := p.NewPrincipalId(pResponder)
	//@ ctx := common.GetDhContext() // TODO make ghost
	l := lib.NewLibrary(pInitiator, pResponder)
	com := chanCom.NewChannelCommunication(pInitiator, pResponder)
	//@ initManager, respManager := createManagers(root, defaultTerm, ctx, initiatorId, responderId)
	a, err = initiator.InitA(l, com, pInitiator, pResponder /*@, initManager, defaultTerm @*/)
	if (err == nil) {
		//@ unfold acc(a.Mem(defaultTerm, defaultTerm), 1/2)
		//@ unfold acc(a.llib.Mem(), 1/2)
		//@ respManager.SetSnapshot(initManager, ctx, responderId, initiatorId)
		//@ fold acc(a.llib.Mem(), 1/2)
		//@ fold acc(a.Mem(defaultTerm, defaultTerm), 1/2)
		b, err = responder.InitB(l, com, pInitiator, pResponder /*@, respManager, defaultTerm @*/)
	}
	if (err == nil) {
		//@ unfold a.Mem(defaultTerm, defaultTerm)
		//@ unfold a.llib.Mem()
		//@ unfold acc(b.Mem(defaultTerm, defaultTerm, defaultTerm), 1/2)
		//@ unfold acc(b.llib.Mem(), 1/2)
		//@ initManager.SetSnapshot(respManager, ctx, initiatorId, responderId)
		//@ fold acc(b.llib.Mem(), 1/2)
		//@ fold acc(b.Mem(defaultTerm, defaultTerm, defaultTerm), 1/2)
		//@ fold a.llib.Mem()
		//@ a.llib.ApplyMonotonicity()
		//@ fold a.Mem(defaultTerm, defaultTerm)
	}
	if err == nil {
		// the following assert stmt is necessary to avoid triggering a bug in Silicon:
		//@ assert a.Vers(defaultTerm, defaultTerm) == 0
		//@ unfold a.Mem(defaultTerm, defaultTerm)
		//@ unfold b.Mem(defaultTerm, defaultTerm, defaultTerm)
		a.PkB = b.PkB
		//@ a.SkBT = b.SkBT
		a.Version = 1
		b.PkA = a.PkA
		//@ b.SkAT = a.SkAT
		b.Version = 1
		//@ fold a.Mem(defaultTerm, defaultTerm)
		//@ fold b.Mem(defaultTerm, defaultTerm, defaultTerm)
	}
	return
}

/*@
// TODO make ghost
decreases
requires initiatorId != responderId
requires root == tr.makeRoot(set[tm.Term]{})
requires defaultTerm == tm.zeroString(0)
requires ctx.Props()
ensures  initManager.Mem(ctx, initiatorId)
ensures  respManager.Mem(ctx, responderId)
ensures  initManager.ImmutableState(ctx, initiatorId) == respManager.ImmutableState(ctx, responderId)
func createManagers(root tr.TraceEntry, defaultTerm tm.Term, ctx common.DhContext, initiatorId, responderId p.Id) (initManager, respManager *tman.TraceManager) {
	clients := []p.Id { initiatorId, responderId }
	fold tri.validTrace(ctx, root)
	managers := tman.NewTraceManager(ctx, clients, root, perm(1)/2)
	initManager = managers[clients[0]]
	respManager = managers[clients[1]]
}
@*/

//@ requires wg.UnitDebt(PredTrue!<!>)
//@ requires a.Mem(defaultTerm, defaultTerm) && a.Vers(defaultTerm, defaultTerm) == 1
func workerA(wg *sync.WaitGroup, a *initiator.A /*@, defaultTerm tm.Term @*/) {
	err /*@, naT, nbT @*/ := initiator.RunA(a /*@, defaultTerm @*/)
	if err != nil {
		lib.Println("An error occurred in A")
	}
	//@ fold PredTrue!<!>()
	//@ wg.PayDebt(PredTrue!<!>)
	wg.Done()
}

//@ requires wg.UnitDebt(PredTrue!<!>)
//@ requires b.Mem(defaultTerm, defaultTerm, defaultTerm) && b.Vers(defaultTerm, defaultTerm, defaultTerm) == 1
func workerB(wg *sync.WaitGroup, b *responder.B /*@, defaultTerm tm.Term @*/) {
	err /*@, naT, nbT, sharedSecretT @*/ := responder.RunB(b /*@, defaultTerm @*/)
	if err != nil {
		lib.Println("An error occurred in B")
	}
	//@ fold PredTrue!<!>()
	//@ wg.PayDebt(PredTrue!<!>)
	wg.Done()
}
