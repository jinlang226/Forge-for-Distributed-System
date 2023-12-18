#lang forge

/*
  Two-phase commit protocol

  (I1) coordinator sends query to all participants and waits until all replied
  (I2) participants execute the transaction up to commit point (undo, redo logs)
  (I3) participants reply with Yes or No 

  if coordinator got Yes from all participants,
  (Y1) 
  ...

  if coordinator got a No:
  (N1) 
  ...
  

  Not modeling:
    * timeouts 
    * ... what else?

*/

-- Message
---------------------------------------------------------------------------------
abstract sig Vote {}
-- "one": disallow multiple "Yes" objects in the world, etc.
--  we can still have multiple _uses_ of the single canonical Yes, etc.
one sig NoneVote, Yes, No extends Vote {} 

abstract sig Decision {}
one sig NoneDecision, Commit, Abort extends Decision {}

-- Different types of message used in the protocol; each can have different
-- fields that reflect its purpose and contents.
abstract sig Message { }
sig NoneMessage extends Message {} -- represents a missing message/response
sig VoteReqMsg extends Message {}  -- step 1 (coordinator sends)
sig VoteMsg extends Message {      -- step 2 (participant sends)
    sender: one ParticipantHost, 
    voteChoice: one Vote
}    
sig DecisionMsg extends Message { -- step 3 (coordinator sends) 
    decision: one Decision
} 

-- E.g., in first step coordinator will send a VoteReqMsg, but will have received nothing
// sig MessageOps {
//     recv: one Message, -- Note option to make this "lone", not have NoneMessage
//     send: one Message
// }

-- Steps of the protocol
abstract sig Steps {}
one sig CoordSendReqStep, CoordLearnVoteStep, CoordDecideStep, 
        PtcpVoteStep, PtcpLearnDecisionStep extends Steps {}

-- DistributedSystem
---------------------------------------------------------------------------------

-- Represents a state of our distributed system
sig DistributedSystem {
   coordinator: one CoordinatorHost, -- should be just identities...
   participants: set ParticipantHost

  -- EXAMPLE: ... and all the STATE is in this sig 
  -- (temporal forge does this differently, and perhaps more conveniently :-))
//    votes: func (CoordinatorHost -> ParticipantHost) -> Vote -- for each participant, what is its vote?

}

pred DistributedSystemWF[d: DistributedSystem] {
    //#d.coordinator >= 0
    d.coordinator.participantCount = #(d.participants)
    // all i: Int | i < #(d.Participant) implies {
    //    (d.Participant[i]).hostId = i 
    // }
    coordWellformed[d.coordinator]
}

-- Startup state
pred DistributedSystemInit[d: DistributedSystem] {
    DistributedSystemWF[d]       -- start in a well-formed state
    coordInit[d.coordinator]     -- coordinator will be in start state
    all p: d.participants | {    -- all participants also in start state
        ptcpInit[p]
    }
}

-- transition relation: d0 --(step, send, recv, phost, decision)--> d1
pred DistributedSystemNext[d0: DistributedSystem, d1: DistributedSystem, 
                           step: Steps, send: Message, recv: Message, phost: ParticipantHost, 
                           decision: Decision] {
    -- beware: this *ENFORCES* that the post-state is well-formed, rather than 
    --   checking that the protocol maintains well-formedness. 
    // DistributedSystemWF[d0]
    // DistributedSystemWF[d1]

    step = CoordSendReqStep => {
        coordSendReq[d0.coordinator, d1.coordinator, send, recv]
    }
    
    step = CoordLearnVoteStep => {
        coordLearnVote[d0.coordinator, d1.coordinator, send, recv]
    } //error

    step = CoordDecideStep and (no ptcpHost: ParticipantHost | (d0.coordinator).votes[ptcpHost] = NoneVote) => {
        coordDecide[d0.coordinator, d1.coordinator, send, recv]
    }

    step = PtcpVoteStep => {
        ptcpVote[d0.participants, d1.participants, send, recv]
    } 

    step = PtcpLearnDecisionStep => {
        ptcpLearnDecision[d0.participants, d1.participants, send, recv]
    }
}

-- CoordinatorHost
---------------------------------------------------------------------------------
sig CoordinatorHost {
    participantCount: one Int,
    coordDecision: one Decision,
    -- func: TOTAL function, all participants have a vote in the function (even NoneVote)
    -- pfunc: PARTIAL function, some participants may have no entry
    -- NOTE: this choice (func) enforces that there are no unused participants
    votes: func ParticipantHost -> Vote -- for each participant, what is its vote?

    -- seq: https://alloytools.org/quickguide/seq.html seems not support in forge
    -- TN: the `seq` keyword is unsupported, but you can use a pred with 
    --    all ch: CoordinatorHost | isSeqOf[ch.votes, Vote]
}

pred coordWellformed[h: CoordinatorHost] {
    h.participantCount = #(h.votes)
    // all h: CoordinatorHost | let uniqueKeys = { x: Int | some y: Int | x->y in h.votes } |
    //     #uniqueKeys = h.participantCount
}

pred coordInit[v: CoordinatorHost] {
    -- Note this is also maybe a property to check, rather than a constraint to 
    -- *enforce*; we already enforce it in the initial state pred anyway.
    // coordWellformed[v]

    // No votes recorded yet
    // all v: CoordinatorHost | let uniqueKeys = { x: Int | some y: Int | x->y in v.votes } |
    //     #uniqueKeys = v.participantCount

    -- This "lookup" is a join that asks for the set of votes for *all* ParticipantHosts
    v.votes[ParticipantHost] = NoneVote 
    // No decision recorded yet
    v.coordDecision = NoneDecision
}

pred coordSendReq[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message] {
    //coordWellformed[v0]
    send = VoteReqMsg
    recv = NoneMessage
    v0 = v1
}

pred coordLearnVote[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message] {
    // coordWellformed[v0]
    send = NoneMessage
    recv = VoteMsg
    // recv.sender = ParticipantHost
    // recv.voteChoice = Vote
    v1.votes[VoteMsg.sender] = VoteMsg.voteChoice
    v0.votes[VoteMsg.sender] = NoneVote
    v0.coordDecision = NoneDecision
    v1.coordDecision = v0.coordDecision
    v1.participantCount = v0.participantCount
    // votes: func ParticipantHost -> Vote  
    // participantCount: one Int,
    // coordDecision: one Decision,
}

pred coordDecide[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message] {
    v0.votes = v1.votes
    v0.participantCount = v1.participantCount
    no ptcpHost: ParticipantHost | v0.votes[ptcpHost] = No => v1.coordDecision = Commit
    some ptcpHost: ParticipantHost | v0.votes[ptcpHost] = No => v1.coordDecision = Abort 
    v0.coordDecision = NoneDecision
    DecisionMsg.decision = v1.coordDecision

    send = DecisionMsg
    recv = NoneMessage
}

-- ParticipantHost
---------------------------------------------------------------------------------
sig ParticipantHost {
    preference: one Vote,
    -- Forge won't let you have 2 sigs with the same field name
    participantDecision: one Decision
}

pred ptcpInit[v: ParticipantHost] {
    -- v.preference is unconstrained (non-deterministic)
    v.preference in (Yes + No)
    v.participantDecision = NoneDecision
}

pred ptcpVote[v0: ParticipantHost, v1: ParticipantHost, send: Message, recv: Message] {
    // hostId = v0.hostId
    VoteMsg.sender = v0
    VoteMsg.voteChoice = v0.preference
    send = VoteMsg
    recv = VoteReqMsg
    v0.preference = v1.preference
    v0.participantDecision = NoneDecision
    v1.participantDecision = v0.participantDecision
}

pred ptcpLearnDecision[v0: ParticipantHost, v1: ParticipantHost, send: Message, recv: Message] {
    // send = NoneMessage
    // recv = DecisionMsg
    // v1.participantDecision = DecisionMsg.decision
    // v0.participantDecision = NoneDecision
    v0.preference = v1.preference
}

-- Two Phase Commit
---------------------------------------------------------------------------------

-- Represents a run of the protocol
one sig TwoPC {
    startState: one DistributedSystem, -- IMPORTANT: these are _states_
    nextState: pfunc DistributedSystem -> DistributedSystem
}
-- NOTE: add {nextState is linear} to run

pred successfulRun {

    -- Initial state is really an initial state
    no ds: DistributedSystem | TwoPC.nextState[ds] = TwoPC.startState
    DistributedSystemInit[TwoPC.startState]

    //pred DistributedSystemNext[d0: DistributedSystem, d1: DistributedSystem, 
                        //    step: Steps, send: Message, recv: Message, phost: ParticipantHost, 
                        //    decision: Decision]
    -- "hard coding" the transition. Could instead say that always this pred is used
    // send vote req
    DistributedSystemNext[TwoPC.startState, TwoPC.nextState[TwoPC.startState], 
                          CoordSendReqStep, VoteReqMsg, NoneMessage, none, NoneDecision]
    
    //participant reply Vote preference
    // sndState = TwoPC.nextState[TwoPC.startState] //question... Is there better way to do this?
    DistributedSystemNext[TwoPC.nextState[TwoPC.startState], TwoPC.nextState[TwoPC.nextState[TwoPC.startState]], 
                          PtcpVoteStep, VoteMsg, VoteReqMsg, none, NoneDecision]
    
    // //host receive votes from participant
    // // thdState = TwoPC.nextState[sndState]
    // DistributedSystemNext[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]], TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]], 
    //                       CoordLearnVoteStep, NoneMessage, VoteMsg, none, NoneDecision]
    // // VoteMsg.sender = TwoPC.nextState[TwoPC.nextState[TwoPC.startState]].Participant
    // // VoteMsg.voteChoice = v0.preference

    // //host make and send decision
    // DistributedSystemNext[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]], TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]], 
    //                       CoordDecideStep, DecisionMsg, NoneMessage, none, NoneDecision]

    // // participant receive decision
    // DistributedSystemNext[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]], TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]]], 
    //                       PtcpLearnDecisionStep, NoneMessage, DecisionMsg, none, NoneDecision]

    //#(d) = 6  
    // init
    /*
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
*/

    // DistributedSystemInit[twoPC.d[0]]
    // all i: Int | {
    //     0 < i < #(twoPC.d) - 1 implies 
    //     DistributedSystemNext[twoPC.d[i], twoPC.d[i + 1], msgOps] // todo
    // }
    
    // VoteMsgPair.sender = 0
    // VoteMsgPair.VoteChoice = Yes
    // DistributedSystemNext[d[1], d[2], ptcpVoteStep, VoteMsgPair, VoteReqMsg, 0, NoneDecision]

    // all row, col: Int | {
    //     (row < 0 or row > 2 or col < 0 or col > 2) implies
    //     no b.board[row][col]
    // }

    // all i: Int | 0 < i < #(twoPC.Networks) - 1 implies {
    //     NetworkNext[twoPC.Networks[i], twoPC.Networks[i + 1], msgOps]
    // }
}

run {
    successfulRun
} for {nextState is linear}

-- TN: what are the scopes on the sigs? (default will be 3--4)

