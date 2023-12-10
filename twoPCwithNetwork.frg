#lang forge

-- Message
---------------------------------------------------------------------------------
abstract sig Vote {}
one sig NoneVote, Yes, No extends Vote {}

abstract sig Decision {}
one sig NoneDecision, Commit, Abort extends Decision {}

sig Message {
    NoneMessage,
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

pred step {
    some c: CoordinatorHost | 
        coordSendReq[p] or
        coordLearnVote[p] or 
        coordDecideStep[p]
}

pred coordWellformed[h: CoordinatorHost] {
    h.participantCount = #(h.votes)
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
    msgOps.recv = NoneMessage
    v0 = v1
}

pred coordLearnVote[v0: CoordinatorHost, v1: CoordinatorHost, msgOps: MessageOps] {
    coordWellformed[v0]
    msgOps.send = NoneMessage
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
    msgOps.recv = NoneMessage
    
}

-- ParticipantHost
---------------------------------------------------------------------------------
sig ParticipantHost {
    hostId: one Int, 
    preference: one Vote,   
    decision: one Decision
}

pred step {
    some p: ParticipantHost | 
        ptcpVote[p] or
        ptcpLearnDecision[p] 
}

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
    msgOps.send = NoneMessage
    // msgOps.recv = DecisionMsg[decision]
    // v1.decision = decision
    some d: DecisionMsg | d in msgOps.recv and v1.decision = d.decision

    v0.hostId = v1.hostId
    v0.preference = v1.preference
}

-- Network
---------------------------------------------------------------------------------
sig Network {
    sentMsg: pfunc Int -> MessageOps
}

pred NetworkInit[v: Network] {
    all i: Int | i < #(v.sentMsg) implies {
        (v.sentMsg[i]).send = NoneMessage 
        (v.sentMsg[i]).recv = NoneMessage
    }
}

pred NetworkNext[v0: Network, v1: Network, msgOps: MessageOps] {
    (msgOps != NoneMessage) => v1.sentMsg = v0.sentMsg + msgOps and msgOps.recv in v0.sentMsg
}

-- Two Phase Commit
---------------------------------------------------------------------------------
one sig twoPC {
    DistributedSystemTraces: pfunc Int -> DistributedSystem,
    // Networks: pfunc Int -> Network
    //DistributedSystemTraces: pfunc Int -> DistributedSystem -> Network
}

pred starting[d: DistributedSystem, n: Network] {
    DistributedSystemInit[d]
    // NetworkInit[n]
}

/*

-------------------------------------------------------------------------------

-- Reinforce the need for a loop by naming this predicate "lasso", not just "trace"
pred lasso {
    init            -- start in the initial state
    always step     -- in every state, take a forward transition
}

-- TN: I removed fairness here, because it's not needed under the way
-- the liveness property is currently phrased (only triggering an obligation 
-- once a process is *Waiting*), given that both processes are always interested. 

-------------------------------------------------------------------------------
-- Visualization
-- Show a valid lasso trace where no process remains disinterested forever.
-------------------------------------------------------------------------------

run {
  lasso  
  all p: Process | eventually World.loc[p] != Disinterested
}
*/

pred traces {
    #(twoPC.DistributedSystemTraces) > 0
    // #(twoPC.Networks) > 0 
    starting[twoPC.DistributedSystemTraces[0], twoPC.Networks[0]]
    
    /*
    // init
    network.sentMsgs:= {}
    DistributedSystemTraces[0].Coordinator.coordDecision = NoneDecision
    DistributedSystemTraces[0].Coordinator.participantCount = 1
    DistributedSystemTraces[0].Coordinator.votes[0] = NoneVote
    DistributedSystemTraces[0].Participant[0].hostId = 0
    DistributedSystemTraces[0].Participant[0].preference = Yes
    DistributedSystemTraces[0].Participant[0].decision = NoneDecision

    //send vote req
    MessageOps(send:= VOTE_REQ, recv:= NoneMessage)
    network.sentMsgs:= {VOTE_REQ}
    DistributedSystemTraces[1].Coordinator.coordDecision = NoneDecision
    DistributedSystemTraces[1].Coordinator.participantCount = 1
    DistributedSystemTraces[1].Coordinator.votes[0] = NoneVote
    DistributedSystemTraces[1].Participant[0].hostId = 0
    DistributedSystemTraces[1].Participant[0].preference = Yes
    DistributedSystemTraces[1].Participant[0].decision = NoneDecision

    //participant reply Vote preference
    network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes}
    MessageOps(send:= VoteMsg[0]=Yes, recv:= VoteReqMsg))
    DistributedSystemTraces[2].Coordinator.coordDecision = NoneDecision
    DistributedSystemTraces[2].Coordinator.participantCount = 1
    DistributedSystemTraces[2].Coordinator.votes[0] = Yes
    DistributedSystemTraces[2].Participant[0].hostId = 0
    DistributedSystemTraces[2].Participant[0].preference = NoneVote
    DistributedSystemTraces[2].Participant[0].decision = NoneDecision

    //host receive votes from participant
    network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes}
    MessageOps(send:= NoneMessage, recv:= VoteMsg[0]=Yes)
    DistributedSystemTraces[3].Coordinator.coordDecision = NoneDecision
    DistributedSystemTraces[3].Coordinator.participantCount = 1
    DistributedSystemTraces[3].Coordinator.votes[0] = Yes
    DistributedSystemTraces[3].Participant[0].hostId = 0
    DistributedSystemTraces[3].Participant[0].preference = Yes
    DistributedSystemTraces[3].Participant[0].decision = NoneDecision

    //host make and send decision
    network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes, Commit}
    MessageOps(send:= commit, recv:= NoneMessage); 
    DistributedSystemTraces[4].Coordinator.coordDecision = Commit
    DistributedSystemTraces[4].Coordinator.participantCount = 1
    DistributedSystemTraces[4].Coordinator.votes[0] = Yes
    DistributedSystemTraces[4].Participant[0].hostId = 0
    DistributedSystemTraces[4].Participant[0].preference = Yes
    DistributedSystemTraces[4].Participant[0].decision = NoneDecision

    // participant receive decision
    network.sentMsgs:= {VoteReqMsg, VoteMsg[0]=Yes, Commit}
    MessageOps(send:= NoneMessage, recv:= Commit)
    DistributedSystemTraces[5].Coordinator.coordDecision = Commit
    DistributedSystemTraces[5].Coordinator.participantCount = 1
    DistributedSystemTraces[5].Coordinator.votes[0] = Yes
    DistributedSystemTraces[5].Participant[0].hostId = 0
    DistributedSystemTraces[5].Participant[0].preference = Yes
    DistributedSystemTraces[5].Participant[0].decision = Commit
    */

    // all i: Int | 0 < i < #(twoPC.DistributedSystemTraces) - 1 implies {
    //     DistributedSystemNext[twoPC.DistributedSystemTraces[i], twoPC.DistributedSystemTraces[i + 1], msgOps]
    // }

    // all i: Int | 0 < i < #(twoPC.Networks) - 1 implies {
    //     NetworkNext[twoPC.Networks[i], twoPC.Networks[i + 1], msgOps]
    // }


}

run {
    traces
} for exactly 20 twoPC, 3 Int for {next is linear} 

