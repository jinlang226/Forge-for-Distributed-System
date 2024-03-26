#lang forge/temporal

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
    proposer: one Proposer,
    var finalValue: one Value
}

abstract sig Steps {}
one sig prepareStep, acceptStep, decideStep extends Steps {}

abstract sig Value{}
one sig valInit, valA, valB extends Value {}

abstract sig Bool {}
one sig True, False extends Bool {}

pred DistributedSystemInit[d: DistributedSystem] {
    # Proposer = 1
    # Acceptor = 3
    # d.acceptors = 3
    # d.proposer = 1
    # d.finalValue = 1
    all a: d.acceptors | initAcceptor[a]
    initProposer[d.proposer]
    d.finalValue = valInit
}

pred DistributedSystemWF[d: DistributedSystem] {
    # finalValue = 1
    # Proposer = 1
    # Acceptor = 3 
    # d.acceptors = 3
    # d.proposer = 1
    // d.proposer.proposalNumber >= 0
    // d.proposer.proposalNumber <= 7
    // all a: d.acceptors | (a.acceptedNumber >= 0 and a.acceptedNumber <= 7)
}

sig Acceptor {
    var acceptedNumber: one Int,
    var acceptedValue: one Value,
    var ready: one Bool
}

pred initAcceptor[a: Acceptor] {
    a.acceptedNumber = 0 // this round number could be adjusted 
    a.acceptedValue = valInit
    a.ready = False
}

sig Proposer {
    var proposalNumber: one Int,
    var proposalValue: one Value,
    var count: one Int
}

pred initProposer[p: Proposer] {
    p.proposalNumber = 0
    p.proposalValue = valInit
    p.count = 0 //number of acceptors responded
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
    d.finalValue = d.finalValue'
    d.finalValue in (valA + valB)
        => d.proposer.proposalNumber = d.proposer.proposalNumber'
        else d.proposer.proposalNumber' = add[d.proposer.proposalNumber, 1]
    d.proposer.proposalValue' = d.proposer.proposalValue
    
    all ac: d.acceptors - someAcceptor | 
        ac.acceptedNumber < d.proposer.proposalNumber' =>
            (ac.acceptedNumber' = d.proposer.proposalNumber' and
            ac.acceptedValue' = ac.acceptedValue and
            d.proposer.count' = add[d.proposer.count, 2] and //jw: #ac is not correct
            (d.proposer.proposalNumber' > ac.acceptedNumber 
                => ac.ready' = True
                else ac.ready' = False))
        else
            (ac.acceptedNumber' = ac.acceptedNumber and
            ac.acceptedValue' = ac.acceptedValue and
            ac.ready' = ac.ready and
            d.proposer.count' = d.proposer.count)
    someAcceptor.acceptedNumber' = someAcceptor.acceptedNumber 
    someAcceptor.acceptedValue' = someAcceptor.acceptedValue
    someAcceptor.ready' = someAcceptor.ready
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
    d.finalValue' = d.finalValue
    d.proposer.proposalNumber' = d.proposer.proposalNumber
    d.proposer.proposalValue' = v
    d.proposer.count' = d.proposer.count  
    all a: d.acceptors | 
        a.ready = True 
            => (
                    a.acceptedNumber' = d.proposer.proposalNumber' and 
                    a.acceptedValue' = d.proposer.proposalValue' and 
                    a.ready' = a.ready
                )
            else 
                (
                    a.acceptedNumber' = a.acceptedNumber and 
                    a.acceptedValue' = a.acceptedValue and 
                    a.ready' = a.ready
                )
}

pred decide[d: DistributedSystem] {
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
    (Proposer.count >= 2 and d.proposer.proposalValue in (valA + valB)) 
        => d.finalValue' in (valA + valB) 
        else d.finalValue = d.finalValue'
}

pred doNothing {
    DistributedSystem.finalValue' = DistributedSystem.finalValue
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
    (some a: DistributedSystem.acceptors | prepare[DistributedSystem, a])
    or
    accept[d, (valA + valB)]
    or
    // decide[d]
    // or
    doNothing
}


option max_tracelength 20
option solver MiniSatProver -- the only solver we support that extracts cores
option logtranslation 1 -- enable translation logging
option coregranularity 1 -- tell the solver how granular cores should be
option core_minimization rce -- tell the solver which algorithm to use to reduce core size
-- valid values: hybrid (fast, not always minimal),
-- rce (slower, complete)


// Only one value can be chosen 
// Only values proposed can be chosen. 
// If this weren't a requirement, 
// you could construct a rather silly yet still correct consensus algorithm 
// in which all computers instantly agree on some predefined value.
pred safety[d: DistributedSystem] {
    # d.finalValue = 1
    d.proposer.proposalValue = valInit <=> d.finalValue = valInit
    d.proposer.proposalValue in (valA + valB) => d.finalValue = d.proposer.proposalValue
    d.finalValue in (valA + valB) => d.proposer.proposalValue = d.finalValue
}

// all proposal identifiers are unique
// the value of the proposal sent to a majority of computers 
// must equal the value of the proposal with the largest identifier less than 
// i accepted by any of the computers.
pred invariant[d: DistributedSystem] {
    DistributedSystemWF[d]
    safety[d]
    (all a: d.acceptors | 
        a.acceptedValue in (valA + valB) => 
            (
                a.acceptedNumber >= d.proposer.proposalNumber and
                d.proposer.proposalValue in (valA + valB) 
            ))
}

test expect {
    initStep: { 
        DistributedSystemInit[DistributedSystem]
        implies invariant[DistributedSystem]
    } 
    is theorem

    inductiveStep: {
        anyTransition[DistributedSystem] and
        invariant[DistributedSystem] 
        implies next_state invariant[DistributedSystem] 
    } 
    is theorem

    invImpliesSafety: { 
        invariant[DistributedSystem] 
        implies safety[DistributedSystem] 
    }
    is theorem
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
            {eventually {some a: DistributedSystem.acceptors | a.acceptedValue in (valA + valB)}} and
            {eventually DistributedSystem.finalValue in (valA + valB)}
        }
    }
    is sat
}

-- visualization
// run {
//     DistributedSystemInit[DistributedSystem]
//     always { 
//         some step: Steps| { 
//             {
//                 step = prepareStep and 
//                 (some a: DistributedSystem.acceptors | prepare[DistributedSystem, a])
//             }
//             or
//             {
//                 step = acceptStep and 
//                 accept[DistributedSystem, valB]
//             }
//             or
//             {
//                 step = decideStep and 
//                 decide[DistributedSystem]
//             }
//             or
//             {doNothing}
//         } 
//         DistributedSystemWF[DistributedSystem]
//     }
//     eventually {(some a: DistributedSystem.acceptors | a.acceptedValue = valB) and DistributedSystem.finalValue = valB}
//     // eventually 
//     -- manually run the following steps
//     // some a: DistributedSystem.acceptors | prepare[DistributedSystem, a]
//     // next_state 
//     // {
//     //     accept[DistributedSystem, valB]
//     //     and {
//     //         next_state 
//     //         {
//     //             decide[DistributedSystem]
//     //             and {
//     //                 next_state {
//     //                     doNothing
//     //                 }
//     //             }
//     //         }
//     //     }
//     // }
// }  