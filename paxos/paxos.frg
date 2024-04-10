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
    acceptors: set Acceptor,
    proposer: one Proposer
    // ,
    // var finalValue: one Value
}

abstract sig Steps {}
one sig prepareStep, acceptStep, decideStep extends Steps {}

abstract sig Value{}
one sig valInit, valA, valB, valC extends Value {}

abstract sig Bool {}
one sig True, False extends Bool {}

pred DistributedSystemInit[d: DistributedSystem] {
    all a: d.acceptors | initAcceptor[a]
    initProposer[d.proposer]
}

pred DistributedSystemWF[d: DistributedSystem] {
    
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
    var count: one Int, //prepare count
    var acceptedCount: one Int
}

pred initProposer[p: Proposer] {
    // p.proposalNumber = 0
    p.proposalValue = valInit
    p.count = 0 //number of acceptors responded during prepare phase
    p.acceptedCount = 0
}

// Phase 1. 
// (a) A proposer selects a proposal number n and 
//     sends a prepare request with number n to 
//     a majority of acceptors.
// (b) If an acceptor receives a prepare request with number n greater than 
//     that of any prepare request to which it has already responded, then it responds to 
//     the request with a promise not to accept any more proposals numbered less than n and 
//     with the highest-numbered proposal (if any) that it has accepted.

pred prepare[d: DistributedSystem, someAcceptor: Acceptor] {
    d.proposer.acceptedCount = d.proposer.acceptedCount'
    frameNoOtherChange[someAcceptor]
    (someAcceptor.acceptedNumber <= d.proposer.proposalNumber)
        =>
            (
                someAcceptor.acceptedNumber' = d.proposer.proposalNumber' and
                someAcceptor.acceptedValue' = d.proposer.proposalValue and
                someAcceptor.ready' = True and
                d.proposer.count' = add[d.proposer.count, 1] and
                d.proposer.proposalNumber' = d.proposer.proposalNumber and 
                d.proposer.proposalValue' = d.proposer.proposalValue 
            )
        else 
            (
                someAcceptor.acceptedNumber' = someAcceptor.acceptedNumber and
                someAcceptor.acceptedValue' = someAcceptor.acceptedValue and
                someAcceptor.ready' = False and
                d.proposer.count' = d.proposer.count and
                d.proposer.proposalNumber' = add[d.proposer.proposalNumber, 1] and
                d.proposer.proposalValue' = someAcceptor.acceptedValue
            )
}

pred frameNoOtherChange[someAcceptor: Acceptor] {
    all v: Acceptor-someAcceptor | {
        v.acceptedNumber' = v.acceptedNumber 
        v.acceptedValue' = v.acceptedValue
        v.ready' = v.ready
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

pred accept[d: DistributedSystem, v: Value] { 
    d.proposer.proposalNumber' = d.proposer.proposalNumber
    d.proposer.count' = d.proposer.count
    d.proposer.proposalValue' = v
    d.proposer.count > 1  //more than half. todo: modify 
    all a: d.acceptors| {
        (d.proposer.proposalNumber >= a.acceptedNumber
            => (
                a.acceptedNumber' = d.proposer.proposalNumber and 
                a.acceptedValue' = d.proposer.proposalValue' and 
                a.ready' = a.ready and
                d.proposer.acceptedCount' = add[d.proposer.acceptedCount, 2] //todo: hard code right now
            )
            else (
                a.acceptedNumber' = a.acceptedNumber and 
                a.acceptedValue' = a.acceptedValue and 
                a.ready' = a.ready and 
                d.proposer.acceptedCount' = d.proposer.acceptedCount
            ))
    }
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
        p.acceptedCount' = p.acceptedCount
    }
}

pred anyTransition[d: DistributedSystem] {
    (one a: DistributedSystem.acceptors | (a.ready = False and prepare[DistributedSystem, a]))
    or
    accept[d, (valA + valB + valC)]
    or
    doNothing[DistributedSystem]
}


// Only one value can be chosen. 
// Only values proposed can be chosen. 
pred safety[d: DistributedSystem] {
    // # Proposer = # d.proposer
    // # Proposer = 1
    // # Acceptor = # d.acceptors
    (all a: d.acceptors | {
        a.acceptedValue in (valA + valB + valC) 
    }) 
    => 
    (all a: d.acceptors | {
        (d.proposer.proposalValue = a.acceptedValue)
    }) 
}

pred invariant[d: DistributedSystem] {
    // DistributedSystemWF[d]
    safety[d]
    (all a: d.acceptors | 
        a.acceptedValue in (valA + valB + valC) )
        => 
        (all a: d.acceptors | {
            (a.acceptedNumber >= d.proposer.proposalNumber) and
                d.proposer.proposalValue in (valA + valB + valC) 
        }) 

    (all a: d.acceptors | {
        a.acceptedValue = valInit 
    }) 
    => 
    (all a: d.acceptors | {
        a.ready = False
    })   
}

test expect {
    initStep: { 
        DistributedSystemInit[DistributedSystem]
        implies invariant[DistributedSystem]
    } 
    is sat 

    inductiveStep: {
        anyTransition[DistributedSystem] and
        invariant[DistributedSystem] 
        implies next_state invariant[DistributedSystem] 
    } 
    is sat

    invImpliesSafety: { 
        invariant[DistributedSystem] 
        implies safety[DistributedSystem] 
    }
    is sat //jw: is theorem not sat 
}

-- test liveness
test expect { 
    liveness_check: { 
      -- (Fill in) start in initial state 
        DistributedSystemInit[DistributedSystem]
      -- (Fill in) `always` use a transition in every state
        always {
            (some a: DistributedSystem.acceptors | anyTransition[DistributedSystem]) 
        }
        implies
        always {
            {eventually {some a: DistributedSystem.acceptors | a.acceptedValue in (valA + valB + valC)}} 
        }
    }
    is sat
}



-- valid values: hybrid (fast, not always minimal),
-- rce (slower, complete)

-- visualization
// run {
//     DistributedSystemInit[DistributedSystem]
    // always { 
    //     some step: Steps| { 
    //         {
    //             step = prepareStep and 
    //             (one a: DistributedSystem.acceptors | (a.ready = False and prepare[DistributedSystem, a]))
    //         }
    //         or
    //         {
    //             step = acceptStep and 
    //             accept[DistributedSystem, valB] // specifically choose valB
    //         }
    //         or
    //         {doNothing[DistributedSystem]}
    //     } 
    //     DistributedSystemWF[DistributedSystem]
    //     # Proposer = 1
    //     # Acceptor = 3 
    //     # DistributedSystem.acceptors = 3
    //     # DistributedSystem.proposer = 1
    // }
    // eventually {all a: DistributedSystem.acceptors | a.acceptedValue = valB}

    // -- manually run the following steps
    // always {
    //     # DistributedSystem.acceptors = 3
    //     # DistributedSystem.proposer = 1
    //     # Proposer = 1
    //     # Acceptor = 3 
    // }
    // one a: DistributedSystem.acceptors | prepare[DistributedSystem, a]
    // and next_state 
    // {
    //     one a: DistributedSystem.acceptors | (a.ready = False and prepare[DistributedSystem, a])
    //         and {
    //             next_state 
    //             {
    //                 accept[DistributedSystem, valB]
    //             }
    //         }
    // }

    // proposer number < acceptor number
    // DistributedSystem.proposer.proposalNumber = 0 
    // one a: DistributedSystem.acceptors | (prepare[DistributedSystem, a] and a.acceptedNumber = 1)
    // and next_state 
    // {
    //     one a: DistributedSystem.acceptors | (a.ready = False and prepare[DistributedSystem, a] and a.acceptedNumber = 2)
    //     and {
    //         next_state 
    //         {
    //             one a: DistributedSystem.acceptors | (a.ready = False and prepare[DistributedSystem, a] and a.acceptedNumber = 2)
    //             // accept[DistributedSystem, valB] 
    //             and {
    //                 next_state 
    //                 {
    //                     one a: DistributedSystem.acceptors | (prepare[DistributedSystem, a])
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
// }  
