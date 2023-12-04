#lang forge

-- Message
---------------------------------------------------------------------------------
abstract sig Vote {}
one sig NoneVote, Yes, No extends Vote {}

abstract sig Decision {}
one sig NoneDecision, Commit, Abort extends Decision {}

sig Message {
    None,
    VoteReqMsg,
    VoteMsg: pfunc Int -> Vote,  
    DecisionMsg: one Decision   
}   

sig MessageOps {
    recv: one Message,
    send: one Message
}

-- DistributedSystem
---------------------------------------------------------------------------------
sig DistributedSystem {
   Coordinator: one CoordinatorHost,
   Participant: pfunc Int -> ParticipantHost
}

pred DistributedSystemWF[d: DistributedSystem] {
    #d.Coordinator >= 0
    d.Coordinator.participantCount = #(d.Participant)
    all i: Int | i < #(d.Participant) implies {
        d.Participant[i].hostId = i //error
    }
    coordWellformed[d.Coordinator]
}

pred DistributedSystemInit[d: DistributedSystem] {
    DistributedSystemWF[d]
    coordInit[d.Coordinator]
    all i: Int | i < #(d.Participant) implies {
        ptcpInit[d.Participant[i]]
    }
}

pred DistributedSystemNext[d0: DistributedSystem, d1: DistributedSystem, msgOps: MessageOps] {
    DistributedSystemWF[d0]
    DistributedSystemWF[d1]

    //match case coordinator / participant variable
}

-- CoordinatorHost
---------------------------------------------------------------------------------
sig CoordinatorHost {
    participantCount: one Int,
    coordDecision: one Decision,
    votes: pfunc Int -> Vote 
    -- seq: https://alloytools.org/quickguide/seq.html seems not support in forge
}

// pred CoordNext[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps] {
//     exists step | CoordNextStep[v0, v1, msgOps, step]
// }

// pred CoordNextStep[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps, step: CoordStep] {
        // todo: match case
        // error unbound identifier
//     all s: step | 
//         (s = coordSendReq implies coordSendReq[v0, v1, msgOps]) and
//         (s = coordLearnVote implies coordLearnVote[v0, v1, msgOps]) and
//         (s = coordDecideStep implies coordDecideStep[v0, v1, msgOps, d])
// }

pred coordWellformed[h: CoordinatorHost] {
    // h.participantCount = #(h.votes)
    all h: CoordinatorHost | let uniqueKeys = { x: Int | some y: Int | x->y in h.votes } |
        #uniqueKeys = h.participantCount
}

pred coordInit[v: CoordinatorHost] {
    coordWellformed[v]
    // No votes recorded yet
    all v: CoordinatorHost | let uniqueKeys = { x: Int | some y: Int | x->y in v.votes } |
        #uniqueKeys = v.participantCount
    all i: Int | i < #(v.votes) implies i -> NoneVote in v.votes 
    // No decision recorded yet
    v.coordDecision = NoneDecision
}

pred coordSendReq[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps] {
    coordWellformed[v0]
    msgOps.send = VoteReqMsg
    msgOps.recv = None
    v0 = v1
}

pred coordLearnVote[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps] {
    coordWellformed[v0]
    msgOps.send = None
    -- votes: pfunc Int -> Int //vote seq 
    msgOps.recv = VoteMsg[hostId]
     
    hostId < v0.participantCount
    // v1.votes[hostId] = votePref
    v1 = v0.(votes = v0.votes[hostId = VoteMsg[hostId]])      
}

pred coordDecideStep[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps, d: coordDecision] {
    coordWellformed[v0]
    all hostId: Int | hostId < v0.participantCount implies {
        v0.votes[hostId] != NoneVote
    }
    d = 
        (all hostId: Int | hostId < v0.participantCount implies {
            v0.votes[hostId] = Commit
        }) => Commit
        else Abort
    v1 = v0.(decision = d)
    msgOps.send = DecisionMsg[d]
    msgOps.recv = None
    
}

-- ParticipantHost
---------------------------------------------------------------------------------
sig ParticipantHost {
    hostId: one Int, 
    preference: one Vote,   
    decision: one Decision
}

// pred PtcpNext[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps] {
//     exists step | PtcpNextStep[v0, v1, msgOps, step]
// }


// pred PtcpNextStep[v0: ParticipantHost, v1: ParticipantHost, msgOps: MessageOps, step: PtcpStep] {
//     // Vote: ptcpVote,
//     // LearnDecision: ptcpLearnDecision
//todo: match case
//     all s: step | 
//         (s = ptcpVote implies ptcpVote[v0, v1, msgOps]) and
//         (s = ptcpLearnDecision implies ptcpLearnDecision[v0, v1, msgOps])
// }

pred ptcpInit[v: ParticipantHost] {
    v.decision = NoneDecision
}

pred ptcpVote[v0: ParticipantHost, v1: ParticipantHost, msgOps: MessageOps] {
    hostId = v0.hostId
    VoteMsg[hostId] = v0.preference
    msgOps.send = VoteMsg[hostId] 
    msgOps.recv = VoteReqMsg
    v0.hostId = v1.hostId
    v0.preference = v1.preference
    v1.decision = 
        (v0.preference = NoneVote) => NoneDecision
        else v0.decision
}

pred ptcpLearnDecision[v0: ParticipantHost, v1: ParticipantHost, msgOps: MessageOps] {
    msgOps.send = None
    // msgOps.recv = DecisionMsg[decision]
    // v1.decision = decision
    some d: DecisionMsg | d in msgOps.recv and v1.decision = d.decision

    v0.hostId = v1.hostId
    v0.preference = v1.preference
}

-- Two Phase Commit
---------------------------------------------------------------------------------
one sig twoPC {
    DistributedSystemTraces: pfunc Int -> DistributedSystem
}

pred starting[d: DistributedSystem] {
    DistributedSystemInit[d]
}

pred traces {
    #(twoPC.DistributedSystemTraces) > 0
    starting[twoPC.DistributedSystemTraces[0]]
    msgOps = 
    all i: Int | 0 < i < #(twoPC.DistributedSystemTraces) - 1 implies {
        DistributedSystemNext[twoPC.DistributedSystemTraces[i], twoPC.DistributedSystemTraces[i + 1], msgOps]
    }
    /*
    // init
    trace[0].Coordinator.coordDecision = NoneDecision
    trace[0].Coordinator.participantCount = 1
    trace[0].Coordinator.votes[0] = NoneVote
    trace[0].Participant[0].hostId = 0
    trace[0].Participant[0].preference = Yes
    trace[0].Participant[0].decision = NoneDecision

    //send vote req
    MessageOps(send:= Some(VOTE_REQ), recv:= None)
    trace[1].Coordinator.coordDecision = NoneDecision
    trace[1].Coordinator.participantCount = 1
    trace[1].Coordinator.votes[0] = NoneVote
    trace[1].Participant[0].hostId = 0
    trace[1].Participant[0].preference = Yes
    trace[1].Participant[0].decision = NoneDecision

    //participant reply Vote preference
    MessageOps(send:= Some(Message.VOTE(Yes, 0)), recv:= Some(VOTE_REQ))
    trace[2].Coordinator.coordDecision = NoneDecision
    trace[2].Coordinator.participantCount = 1
    trace[2].Coordinator.votes[0] = Yes
    trace[2].Participant[0].hostId = 0
    trace[2].Participant[0].preference = NoneVote
    trace[2].Participant[0].decision = NoneDecision

    //host receive votes from participant
    MessageOps(send:= None, recv:= Some(Message.VOTE(Yes, 0)))
    trace[3].Coordinator.coordDecision = NoneDecision
    trace[3].Coordinator.participantCount = 1
    trace[3].Coordinator.votes[0] = Yes
    trace[3].Participant[0].hostId = 0
    trace[3].Participant[0].preference = Yes
    trace[3].Participant[0].decision = NoneDecision

    //host make and send decision
    MessageOps(send:= Some(Message.DECISION(Commit)), recv:= None); 
    trace[4].Coordinator.coordDecision = Commit
    trace[4].Coordinator.participantCount = 1
    trace[4].Coordinator.votes[0] = Yes
    trace[4].Participant[0].hostId = 0
    trace[4].Participant[0].preference = Yes
    trace[4].Participant[0].decision = NoneDecision

    // participant receive decision
    MessageOps(send:= None, recv:= Some(Message.DECISION(Decision.Commit))
    trace[5].Coordinator.coordDecision = Commit
    trace[5].Coordinator.participantCount = 1
    trace[5].Coordinator.votes[0] = Yes
    trace[5].Participant[0].hostId = 0
    trace[5].Participant[0].preference = Yes
    trace[5].Participant[0].decision = Commit
    */



}

run {
    traces
} for exactly 20 twoPC, 3 Int for {next is linear}

