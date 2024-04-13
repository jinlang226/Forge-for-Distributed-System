#lang forge/temporal

option max_tracelength 20
option solver MiniSatProver -- the only solver we support that extracts cores
option logtranslation 1 -- enable translation logging
option coregranularity 1 -- tell the solver how granular cores should be
option core_minimization rce -- tell the solver which algorithm to use to reduce core size


//jw: note that there is only one proposer and multiple acceptors.

// Phase 1. 
// (a) A proposer selects a proposal number n and 
//     sends a prepare request with number n to 
//     a majority of acceptors.
// (b) If an acceptor receives a prepare request with number n greater than 
//     that of any prepare request to which it has already responded, then it responds to 
//     the request with a promise not to accept any more proposals numbered less than n and 
//     with the highest-numbered proposal (if any) that it has accepted.

// Phase 2. 
// (a) If the proposer receives a response to its prepare requests (numbered n) from 
//     a majority of acceptors, then it sends an accept request to each of those acceptors 
//     for a proposal numbered n with a value v, where v is the value of the highest-numbered 
//     proposal among the responses, or is any value if the responses reported no proposals.
// (b) If an acceptor receives an accept request for a proposal numbered n, 
//     it accepts the proposal unless it has already responded to a prepare 
//     request having a number greater than n.


one sig DistributedSystem {
    acceptorA: one Acceptor,
    //acceptor ABC 
    // (acceptorA.ready? and acceptorB.ready?) || (accB and acceptorC.ready? )
    acceptorB: one Acceptor,
    acceptorC: one Acceptor,
    proposerA: one Proposer,
    proposerB: one Proposer
}

abstract sig Steps {}
one sig prepareStep, acceptStep, decideStep extends Steps {}

abstract sig Value{}
one sig valInit, valA, valB, valC extends Value {}

abstract sig Bool {}
one sig True, False extends Bool {}

pred DistributedSystemInit[d: DistributedSystem] {
    // all a: Acceptor | initAcceptor[a]
    initAcceptor[d.acceptorA]
    initAcceptor[d.acceptorB]
    initAcceptor[d.acceptorC]
    initProposer[d.proposerA]
    initProposer[d.proposerB]
    d.proposerB.proposalNumber = d.proposerA.proposalNumber + 1
}

pred DistributedSystemWF {
    # Acceptor = 3
    # DistributedSystem.proposerA = 1
    # DistributedSystem.proposerB = 1
    # Proposer = 2
    # DistributedSystem.acceptorA = 1
    # DistributedSystem.acceptorB = 1
    # DistributedSystem.acceptorC = 1
    (not DistributedSystem.acceptorA = DistributedSystem.acceptorB)
    (not DistributedSystem.acceptorC = DistributedSystem.acceptorB)
    (not DistributedSystem.acceptorA = DistributedSystem.acceptorC) 
    (not DistributedSystem.proposerA = DistributedSystem.proposerB)
}

sig Acceptor {
    var acceptedNumber: one Int,
    var acceptedValue: one Value,
    var ready: one Bool
}

pred initAcceptor[a: Acceptor] {
    // a.acceptedNumber = 1 //jw: this round number could be adjusted 
    a.acceptedValue = valInit
    a.ready = False
}

sig Proposer {
    var proposalNumber: one Int,
    var proposalValue: one Value,
    var count: one Int //prepare count
}

pred initProposer[p: Proposer] {
    p.proposalValue = valInit
    p.count = 0 //number of acceptors responded during prepare phase
}

// Phase 1. 
// (a) A proposer selects a proposal number n and 
//     sends a prepare request with number n to 
//     a majority of acceptors.
// (b) If an acceptor receives a prepare request with number n greater than 
//     that of any prepare request to which it has already responded, then it responds to 
//     the request with a promise not to accept any more proposals numbered less than n and 
//     with the highest-numbered proposal (if any) that it has accepted.

pred prepare[d: DistributedSystem, someAcceptor: Acceptor, someProposer: Proposer] {
    frameNoOtherProposerChange[someProposer]
    frameNoOtherAcceptorChange[someAcceptor]
    (someAcceptor.acceptedNumber <= someProposer.proposalNumber)
        =>
            (
                someAcceptor.acceptedNumber' = someProposer.proposalNumber' and
                someAcceptor.acceptedValue' = someProposer.proposalValue and
                someAcceptor.ready' = True and
                someProposer.count' = add[someProposer.count, 1] and
                someProposer.proposalNumber' = someProposer.proposalNumber and 
                someProposer.proposalValue' = someProposer.proposalValue 
            )
        else 
            (
                someAcceptor.acceptedNumber' = someAcceptor.acceptedNumber and
                someAcceptor.acceptedValue' = someAcceptor.acceptedValue and
                someAcceptor.ready' = False and
                someProposer.count' = someProposer.count and
                someProposer.proposalNumber' = add[someProposer.proposalNumber, 1] and
                someProposer.proposalValue' = someAcceptor.acceptedValue
            )
}

pred frameNoOtherAcceptorChange[someAcceptor: Acceptor] {
    all v: Acceptor-someAcceptor | {
        v.acceptedNumber' = v.acceptedNumber 
        v.acceptedValue' = v.acceptedValue
        v.ready' = v.ready
    }
}

pred frameNoOtherProposerChange[someProposer: Proposer] {
    all v: Proposer-someProposer | {
        v.proposalNumber' = v.proposalNumber
        v.proposalValue' = v.proposalValue
        v.count' = v.count
    }
}


// Phase 2. 
// (a) If the proposer receives a response to its prepare requests (numbered n) from 
//     a majority of acceptors, then it sends an accept request to each of those acceptors 
//     for a proposal numbered n with a value v, where v is the value of the highest-numbered 
//     proposal among the responses, or is any value if the responses reported no proposals.
// (b) If an acceptor receives an accept request for a proposal numbered n, 
//     it accepts the proposal unless it has already responded to a prepare 
//     request having a number greater than n.

pred accept[d: DistributedSystem, v: Value, someProposer: Proposer] { 
    someProposer.proposalNumber' = someProposer.proposalNumber
    someProposer.count' = someProposer.count
    someProposer.proposalValue' = v
    frameNoOtherProposerChange[someProposer]
    // d.someProposer.count > 1  //more than half. jw todo: modify 
    acceptHelper[d, someProposer]
}

pred acceptHelper[d: DistributedSystem, p: Proposer] {
     ((d.acceptorA.ready = True and d.acceptorB.ready = True) or (d.acceptorB.ready = True and d.acceptorC.ready = True) or (d.acceptorA.ready = True and d.acceptorC.ready = True))
        => (
            acceptorChangeValue[d, p] 
        )
        else (
            acceptorStaySame[d] 
        )
}

pred acceptorChangeValue[d: DistributedSystem, p: Proposer] {
    d.acceptorA.acceptedNumber' = p.proposalNumber and
    d.acceptorA.acceptedValue' = p.proposalValue' and
    d.acceptorA.ready' = d.acceptorA.ready and
    d.acceptorB.acceptedNumber' = p.proposalNumber and
    d.acceptorB.acceptedValue' = p.proposalValue' and
    d.acceptorB.ready' = d.acceptorB.ready and
    d.acceptorC.acceptedNumber' = p.proposalNumber and
    d.acceptorC.acceptedValue' = p.proposalValue' and
    d.acceptorC.ready' = d.acceptorC.ready
}

pred acceptorStaySame[d: DistributedSystem] {
    d.acceptorA.acceptedNumber' = d.acceptorA.acceptedNumber and
    d.acceptorA.acceptedValue' = d.acceptorA.acceptedValue and
    d.acceptorA.ready' = d.acceptorA.ready and
    d.acceptorB.acceptedNumber' = d.acceptorB.acceptedNumber and
    d.acceptorB.acceptedValue' = d.acceptorB.acceptedValue and
    d.acceptorB.ready' = d.acceptorB.ready and
    d.acceptorC.acceptedNumber' = d.acceptorC.acceptedNumber and
    d.acceptorC.acceptedValue' = d.acceptorC.acceptedValue and
    d.acceptorC.ready' = d.acceptorC.ready
}

pred doNothing[d: DistributedSystem] {
    // DistributedSystem.finalValue' = DistributedSystem.finalValue
    all a: Acceptor | {
        a.acceptedNumber' = a.acceptedNumber
        a.acceptedValue' = a.acceptedValue
        a.ready' = a.ready
    }
    all p: Proposer | {
        p.proposalNumber' = p.proposalNumber
        p.proposalValue' = p.proposalValue
        p.count' = p.count
    }
}

pred anyTransition[d: DistributedSystem] {
    // (one a: DistributedSystem.acceptors | (a.ready = False and prepare[DistributedSystem, a]))
    // or
    (acceptorA.ready = False and prepare[DistributedSystem, acceptorA])
    or
    (acceptorB.ready = False and prepare[DistributedSystem, acceptorB])
    or
    (acceptorC.ready = False and prepare[DistributedSystem, acceptorC])
    or
    accept[d, (valA + valB + valC)]
    or
    doNothing[DistributedSystem]
}


-- Only one value can be chosen. 
-- Only values proposed can be chosen. 
pred safety[d: DistributedSystem] {
    DistributedSystemWF
    (all a: Acceptor | {
        a.acceptedValue in (valA + valB + valC) 
    }) 
    // => 
    // ((all a: Acceptor | (d.proposer.proposalValue = a.acceptedValue))
    // and d.proposer.proposalValue in (valA + valB + valC) )
}

pred invariant[d: DistributedSystem] {
    safety[d]

    -- if all acceptors have accepted a value, then the proposer has proposed that value
    // (all a: Acceptor | 
    //     a.acceptedValue in (valA + valB + valC) )
    //     => 
    //     (all a: Acceptor | {
    //         // (a.acceptedNumber >= d.proposer.proposalNumber) and
    //             d.proposer.proposalValue in (valA + valB + valC) 
    //     }) 

    -- if thAcceptor have not accepted a value, then they are not ready
    (all a: Acceptor | {
        a.acceptedValue = valInit 
    }) 
    => 
    (all a: Acceptor | {
        a.ready = False
    })   

    -- if the proposer has not proposed a value, then its count is less than majority
    // (d.proposer.proposalValue = valInit) => (d.proposer.count < 2) //jw todo: hard code right now
}

// test expect {
//     initStep: { 
//         DistributedSystemInit[DistributedSystem]
//         implies invariant[DistributedSystem]
//     } 
//     is theorem 

//     // inductiveStep: {
//     //     anyTransition[DistributedSystem] and
//     //     invariant[DistributedSystem] 
//     //     implies next_state invariant[DistributedSystem] 
//     // } 
//     // is theorem

//     // invImpliesSafety: { 
//     //     invariant[DistributedSystem] 
//     //     implies safety[DistributedSystem] 
//     // }
//     // is theorem //jw: `is theorem` not sat 
// }

-- test liveness
// test expect { 
//     liveness_check: { 
//       -- start in initial state 
//         DistributedSystemInit[DistributedSystem]
//       -- `always` use a transition in every state
//         always {
//             (some a: DistributedSystem.acceptors | anyTransition[DistributedSystem]) 
//         }
//         implies
//         always {
//             {eventually {some a: DistributedSystem.acceptors | a.acceptedValue in (valA + valB + valC)}} 
//         }
//     }
//     is sat
// }



-- valid values: hybrid (fast, not always minimal),
-- rce (slower, complete)

-- visualization
run {
    DistributedSystemInit[DistributedSystem]
    always { 
        some step: Steps| { 
            {
                step = prepareStep and 
                prepare[DistributedSystem, DistributedSystem.acceptorA, DistributedSystem.proposerA]
            }
            or
            {
                step = prepareStep and 
                prepare[DistributedSystem, DistributedSystem.acceptorB, DistributedSystem.proposerA]
            }
            or
            {
                step = prepareStep and 
                prepare[DistributedSystem, DistributedSystem.acceptorC, DistributedSystem.proposerA]
            }
            or
            {
                step = prepareStep and 
                prepare[DistributedSystem, DistributedSystem.acceptorA, DistributedSystem.proposerB]
            }
            or
            {
                step = prepareStep and 
                prepare[DistributedSystem, DistributedSystem.acceptorB, DistributedSystem.proposerB]
            }
            or
            {
                step = prepareStep and 
                prepare[DistributedSystem, DistributedSystem.acceptorC, DistributedSystem.proposerB]
            }
            or
            {
                step = acceptStep and 
                accept[DistributedSystem, valB, DistributedSystem.proposerA] // specifically choose valB
            }
            or
            {doNothing[DistributedSystem]}
        } 
        DistributedSystemWF
    }
    eventually {all a: Acceptor | a.acceptedValue = valB}

    // -- manually run the following steps
    // cannot get the same result
    // always {
    //     DistributedSystemWF
    // }
    // prepare[DistributedSystem, DistributedSystem.acceptorA, DistributedSystem.proposerA]
    // and next_state 
    // {
    //     prepare[DistributedSystem, DistributedSystem.acceptorC, DistributedSystem.proposerB]
    //     and {
    //         next_state 
    //         {
    //             // prepare[DistributedSystem, DistributedSystem.acceptorB]
    //             // and {
    //             //     next_state 
    //             //     {
    //                     accept[DistributedSystem, valB, DistributedSystem.proposerA]
    //             //     }
    //             // }
    //         }
    //     }
    // }

    // proposer number < acceptor number
    // DistributedSystem.proposer.proposalNumber = 0 
    // one a: Acceptor | (prepare[DistributedSystem, a] and a.acceptedNumber = 1)
    // and next_state 
    // {
    //     one a: Acceptor | (a.ready = False and prepare[DistributedSystem, a] and a.acceptedNumber = 2)
    //     and {
    //         next_state 
    //         {
    //             one a: Acceptor | (a.ready = False and prepare[DistributedSystem, a] and a.acceptedNumber = 2)
    //             // accept[DistributedSystem, valB] 
    //             and {
    //                 next_state 
    //                 {
    //                     one a: Acceptor | (prepare[DistributedSystem, a])
    //                     // accept[DistributedSystem, valB] 
    //                     and {
    //                         next_state 
    //                         {
    //                             accept[DistributedSystem, valB] 
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }
}  
