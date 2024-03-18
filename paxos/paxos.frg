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
    proposer: one Proposer
}

abstract sig Steps {}
one sig prepareStep, acceptStep extends Steps {}

abstract sig Value{}
one sig valInit, valA, valB extends Value {}

abstract sig Bool {}
one sig True, False extends Bool {}

pred DistributedSystemInit[d: DistributedSystem] {
    #d.acceptors = 3
    #d.proposer = 1
    // half count = 2
    all a: d.acceptors | initAcceptor[a]
    initProposer[d.proposer]
}

pred DistributedSystemWF[d: DistributedSystem] {
    #Proposer = 1
}

sig Acceptor {
    var acceptedNumber: one Int,
    var acceptedValue: one Value,
    var ready: one Bool
}

pred initAcceptor[a: Acceptor] {
    a.acceptedNumber = 0
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

pred prepare[d: DistributedSystem, v: Value, someAcceptor: Acceptor] { //jw: how to represent a list of accepotor?
    d.proposer.proposalNumber' = add[d.proposer.proposalNumber, 1]
    d.proposer.proposalValue' = v 
    
    d.proposer.proposalNumber' > someAcceptor.acceptedNumber 
        => (someAcceptor.acceptedNumber' = d.proposer.proposalNumber' and 
            someAcceptor.acceptedValue' = v and 
            d.proposer.count' = add[d.proposer.count, 1] 
            and someAcceptor.ready' = True
            )
        else 
            (
            someAcceptor.acceptedNumber' = someAcceptor.acceptedNumber and 
            someAcceptor.acceptedValue' = someAcceptor.acceptedValue and 
            d.proposer.count' = d.proposer.count  
            and someAcceptor.ready' = False
            )
    all a: d.acceptors - someAcceptor |
        a.acceptedNumber' = a.acceptedNumber and
        a.acceptedValue' = a.acceptedValue and
        a.ready' = a.ready 
}

pred accept[d: DistributedSystem] {
    (no a: d.acceptors | 
        a.acceptedNumber < d.proposer.proposalNumber
            => (a.acceptedValue = d.proposer.proposalValue)
            else //find the value of the largest acceptor ID
                ((some a: d.acceptors | a.acceptedNumber = max[Acceptor.acceptedNumber] => a.acceptedValue = d.proposer.proposalValue') and
                (all a: d.acceptors | a.acceptedValue' = d.proposer.proposalValue')))
}

pred doNothing {
    
}


// visualization
option max_tracelength 20
run {
    DistributedSystemInit[DistributedSystem]
    always { 
        // some step: Steps| { 
        //     {
        //         step = proposerPrepareStep and 
        //         proposerPrepare[DistributedSystem]
        //     }
        //     or
        //     {doNothing}
        // } 
        DistributedSystemWF[DistributedSystem]
    }
    some v: Value | (one a: DistributedSystem.acceptors | prepare[DistributedSystem,v,a])
    // next_state 
    // {
    //     accept[DistributedSystem]
        
    //     some h: DistributedSystem.hosts | doAccept[h] 
    //     and
    //     {next_state 
    //         {
    //             some h: DistributedSystem.hosts | doGrant[h]
    //             and {
    //                 next_state {
    //                     some h: DistributedSystem.hosts | doAccept[h] and {
    //                         next_state {
    //                             some h: DistributedSystem.hosts | doGrant[h] 
    //                         }
    //                     } 
    //                 }
    //             }
    //         }
    //     }
    // }
    // forall b : b true or b false
    // type error? 
}  