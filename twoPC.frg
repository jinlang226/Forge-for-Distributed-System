#lang forge

-- Message
---------------------------------------------------------------------------------
abstract sig Vote {}
one sig NoneVote, Yes, No extends Vote {}

abstract sig Decision {}
one sig NoneDecision, Commit, Abort extends Decision {}

sig VoteMsgPair {
    sender: one Int, 
    VoteChoice: one Vote
}

sig Message {
    NoneMessage,
    VoteReqMsg,
    // VoteMsg: pfunc Int -> Vote,  
    VoteMsg: one VoteMsgPair,  
    DecisionMsg: one Decision   
}   

sig MessageOps {
    recv: one Message,
    send: one Message
}

-- DistributedSystem
---------------------------------------------------------------------------------
abstract sig Steps {}
one sig coordSendReqStep, coordLearnVoteStep, coordDecideStep, ptcpVoteStep, ptcpLearnDecisionStep extends Steps {}

sig DistributedSystem {
   Coordinator: one CoordinatorHost,
   Participant: pfunc Int -> ParticipantHost
}

pred DistributedSystemWF[d: DistributedSystem] {
    #d.Coordinator >= 0
    d.Coordinator.participantCount = #(d.Participant)
    all i: Int | i < #(d.Participant) implies {
       (d.Participant[i]).hostId = i 
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

pred DistributedSystemNext[d0: DistributedSystem, d1: DistributedSystem, step: Steps, send: Message, recv: Message, hostId: Int, decision: Decision] {
    DistributedSystemWF[d0]
    DistributedSystemWF[d1]
    some step: coordSendReqStep | 
       coordSendReq[d0.Coordinator, d1.Coordinator, send, recv] 
    // some step: coordLearnVoteStep | 
    //    coordLearnVote[d0.Coordinator, d1.Coordinator, send, recv]
    // some step: coordDecideStep | 
    //    coordDecide[d0.Coordinator, d1.Coordinator, send, recv, decision]
    // some step: ptcpVoteStep |
    //     ptcpVote[d0.Participant[hostId], d1.Participant[hostId], send, recv]
    // some step: ptcpLearnDecisionStep |
    //     ptcpLearnDecision[d0.Participant[hostId], d1.Participant[hostId], send, recv]
}

-- CoordinatorHost
---------------------------------------------------------------------------------
sig CoordinatorHost {
    participantCount: one Int,
    coordDecision: one Decision,
    votes: pfunc Int -> Vote 
    -- seq: https://alloytools.org/quickguide/seq.html seems not support in forge
}

pred coordWellformed[h: CoordinatorHost] {
    h.participantCount = #(h.votes)
    // all h: CoordinatorHost | let uniqueKeys = { x: Int | some y: Int | x->y in h.votes } |
    //     #uniqueKeys = h.participantCount
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

pred coordSendReq[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message] {
    coordWellformed[v0]
    send = VoteReqMsg
    recv = NoneMessage
    v0 = v1
}

pred coordLearnVote[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message] {
    coordWellformed[v0]
    send = NoneMessage
    -- votes: pfunc Int -> Vote 
    // recv = VoteMsg[hostId]
    recv = VoteMsg
     
    VoteMsg.sender < v0.participantCount
    // v1.votes[hostId] = votePref
    all v1:Int - VoteMsgPair.sender | v1.votes[v1] = v0.votes[v1]
    v1.votes[sender] = recv.VoteMsg.VoteChoice
    // v1 = v0.(votes = v0.votes[sender = VoteChoice])      
}

pred coordDecide[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message, d: coordDecision] {
    coordWellformed[v0]
    all hostId: Int | hostId < v0.participantCount implies {
        v0.votes[hostId] != NoneVote
    }
    // d = 
    (all hostId: Int | hostId < v0.participantCount implies {
        v0.votes[hostId] = Commit
    }) => d = Commit
    else d = Abort
    v1.decision = d
    // v1 = v0.(decision = d)
    Decision = d
    send = DecisionMsg
    recv = NoneMessage
    
}

-- ParticipantHost
---------------------------------------------------------------------------------
sig ParticipantHost {
    hostId: one Int, 
    preference: one Vote,   
    decision: one Decision
}

pred ptcpInit[v: ParticipantHost] {
    v.decision = NoneDecision
}

pred ptcpVote[v0: ParticipantHost, v1: ParticipantHost, send: Message, recv: Message] {
    // hostId = v0.hostId
    VoteMsg[v0.hostId] = v0.preference
    send = VoteMsg
    recv = VoteReqMsg
    v0.hostId = v1.hostId
    v0.preference = v1.preference
    
    (v0.preference = NoneVote) => v1.decision = NoneDecision
    else v1.decision = v0.decision
}

pred ptcpLearnDecision[v0: ParticipantHost, v1: ParticipantHost, send: Message, recv: Message] {
    send = NoneMessage
    recv = DecisionMsg
    v1.decision = DecisionMsg.Decision

    v0.hostId = v1.hostId
    v0.preference = v1.preference
}

-- Two Phase Commit
---------------------------------------------------------------------------------
one sig twoPC {
    DistributedSystemTraces: pfunc Int -> DistributedSystem
}

pred starting[d: DistributedSystemTraces] {
    #(d) = 6 
    // init
    (d[0].Coordinator).coordDecision = NoneDecision
    (d[0].Coordinator).participantCount = 1
    (d[0].Coordinator).votes[0] = NoneVote
    (d[0].Participant[0]).hostId = 0
    (d[0].Participant[0]).preference = Yes
    (d[0].Participant[0]).decision = NoneDecision

    //send vote req
    // MessageOps(send:= Some(VOTE_REQ), recv:= None);
    // network.sentMsgs:= {VOTE_REQ}
    (d[1].Coordinator).coordDecision = NoneDecision
    (d[1].Coordinator).participantCount = 1
    (d[1].Coordinator).votes[0] = NoneVote
    (d[1].Participant[0]).hostId = 0
    (d[1].Participant[0]).preference = Yes
    (d[1].Participant[0]).decision = NoneDecision

    //participant reply Vote preference
    // network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes}
    // MessageOps(send:= VoteMsg[0]=Yes, recv:= VoteReqMsg))
    (d[2].Coordinator).coordDecision = NoneDecision
    (d[2].Coordinator).participantCount = 1
    (d[2].Coordinator).votes[0] = Yes
    (d[2].Participant[0]).hostId = 0
    (d[2].Participant[0]).preference = NoneVote
    (d[2].Participant[0]).decision = NoneDecision

    //host receive votes from participant
    // network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes}
    // MessageOps(send:= NoneMessage, recv:= VoteMsg[0]=Yes)
    (d[3].Coordinator).coordDecision = NoneDecision
    (d[3].Coordinator).participantCount = 1
    (d[3].Coordinator).votes[0] = Yes
    (d[3].Participant[0]).hostId = 0
    (d[3].Participant[0]).preference = Yes
    (d[3].Participant[0]).decision = NoneDecision

    //host make and send decision
    // network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes, Commit}
    // MessageOps(send:= commit, recv:= NoneMessage); 
    (d[4].Coordinator).coordDecision = Commit
    (d[4].Coordinator).participantCount = 1
    (d[4].Coordinator).votes[0] = Yes
    (d[4].Participant[0]).hostId = 0
    (d[4].Participant[0]).preference = Yes
    (d[4].Participant[0]).decision = NoneDecision

    // participant receive decision
    // network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes, Commit}
    // MessageOps(send:= NoneMessage, recv:= Commit)
    (d[5].Coordinator).coordDecision = Commit
    (d[5].Coordinator).participantCount = 1
    (d[5].Coordinator).votes[0] = Yes
    (d[5].Participant[0]).hostId = 0
    (d[5].Participant[0]).preference = Yes
    (d[5].Participant[0]).decision = Commit


    // DistributedSystemInit[twoPC.d[0]]
    // all i: Int | {
    //     0 < i < #(twoPC.d) - 1 implies 
    //     DistributedSystemNext[twoPC.d[i], twoPC.d[i + 1], msgOps] // todo
    // }
    DistributedSystemNext[d[0], d[1], coordSendReqStep, VoteReqMsg, NoneMessage, -1, NoneDecision]
    // DistributedSystemNext[d[1], d[2], ptcpVoteStep, Yes, VoteReqMsg, 0, NoneDecision]

    // all row, col: Int | {
    //     (row < 0 or row > 2 or col < 0 or col > 2) implies
    //     no b.board[row][col]
    // }

    // all i: Int | 0 < i < #(twoPC.Networks) - 1 implies {
    //     NetworkNext[twoPC.Networks[i], twoPC.Networks[i + 1], msgOps]
    // }


}

run {
    starting[twoPC.DistributedSystemTraces]  
} 

