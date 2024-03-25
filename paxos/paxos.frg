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
    #Acceptor = 3 
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

// Phase 1. 
// (a) A proposer selects a proposal number n and 
//     sends a prepare request with number n to 
//     a majority of acceptors.
// (b) If an acceptor receives a prepare request with number n greater than 
//     that of any prepare request to which it has already responded, then it responds to 
//     the request with a promise not to accept any more proposals numbered less than n and 
//     with the highest-numbered proposal (if any) that it has accepted.

pred prepare[d: DistributedSystem, someAcceptor: Acceptor] {
    d.proposer.proposalNumber' = add[d.proposer.proposalNumber, 1]
    d.proposer.proposalValue' = d.proposer.proposalValue
    
    all ac: d.acceptors - someAcceptor | 
        ac.acceptedNumber' = d.proposer.proposalNumber'and
        ac.acceptedValue' = ac.acceptedValue and
        d.proposer.count' = add[d.proposer.count, #ac] and //jw: # is not correct
        (d.proposer.proposalNumber' > ac.acceptedNumber 
            => ac.ready' = True
            else ac.ready' = False)
    
    someAcceptor.acceptedNumber' = someAcceptor.acceptedNumber 
    someAcceptor.acceptedValue' = someAcceptor.acceptedValue
    someAcceptor.ready' = False
}

// Phase 2. 
// (a) If the proposer receives a response to its prepare requests (numbered n) from 
//     a majority of acceptors, then it sends an accept request to each of those acceptors 
//     for a proposal numbered n with a value v, where v is the value of the highest-numbered 
//     proposal among the responses, or is any value if the responses reported no proposals.
// (b) If an acceptor receives an accept request for a proposal numbered n, 
//     it accepts the proposal unless it has already responded to a prepare 
//     request having a number greater than n.

pred accept[d: DistributedSystem, v: Value] { //jw: how to represent a list of accepotor?
    d.proposer.proposalNumber' = d.proposer.proposalNumber
    d.proposer.proposalValue' = v
    d.proposer.count' = d.proposer.count  
    all a: d.acceptors | //a.ready = True jw: if exceeds majority
    //         => (
                    a.acceptedNumber' = d.proposer.proposalNumber' and 
                    a.acceptedValue' = d.proposer.proposalValue' and 
                    a.ready' = a.ready
            //     )
            // else 
            //     (
            //         a.acceptedNumber' = a.acceptedNumber and 
            //         a.acceptedValue' = a.acceptedValue and 
            //         a.ready' = a.ready
            //     )
}

pred doNothing {
    all a: Acceptors | {
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


// visualization
option max_tracelength 20
option solver MiniSatProver -- the only solver we support that extracts cores
option logtranslation 1 -- enable translation logging
option coregranularity 1 -- tell the solver how granular cores should be
option core_minimization rce -- tell the solver which algorithm to use to reduce core size
-- valid values: hybrid (fast, not always minimal),
-- rce (slower, complete)
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
    // some v: Value | (one a: DistributedSystem.acceptors | prepare[DistributedSystem,v,a])
    some a: DistributedSystem.acceptors | prepare[DistributedSystem, a] //jw: error if change some to one
    next_state 
    {
        accept[DistributedSystem, valB]
        
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
    }
    // forall b : b true or b false
    // type error? 
}  