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
   participants: one ParticipantHost

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
    ptcpInit[d.participants]     -- participants will be in start state
}

-- transition relation: d0 --(step, send, recv, phost, decision)--> d1
pred DistributedSystemNext[d0: DistributedSystem, d1: DistributedSystem, 
                           step: Steps, send: Message, recv: Message] {
                            //, phost: ParticipantHost, 
                        //    decision: Decision
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

    step = CoordDecideStep and ((d0.coordinator).votes[ParticipantHost] != NoneVote) => {
        coordDecide[d0.coordinator, d1.coordinator, send, recv]
    }

    step = PtcpVoteStep => {
        ptcpVote[d0.participants, d1.participants, send, recv]
    } 

    step = PtcpLearnDecisionStep and (DecisionMsg.decision != NoneDecision) => { 
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
    v.participantCount = 1
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
    // v0.votes[VoteMsg.sender] = NoneVote
    v0.coordDecision = NoneDecision
    v1.coordDecision = v0.coordDecision
    v1.participantCount = 1 // error
    v0.participantCount = 1
    // votes: func ParticipantHost -> Vote  
    // participantCount: one Int,
    // coordDecision: one Decision,
}

pred coordDecide[v0: CoordinatorHost, v1: CoordinatorHost, send: Message, recv: Message] {
    v1.participantCount = 1 // error
    v0.participantCount = 1
    v0.votes = v1.votes
    // v0.participantCount = v1.participantCount
    v0.votes[ParticipantHost] = Yes => v1.coordDecision = Commit
    v0.votes[ParticipantHost] = No => v1.coordDecision = Abort 
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
    // v.preference in (Yes + No)
    v.preference = No 
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
    v1.participantDecision = NoneDecision
}

pred ptcpLearnDecision[v0: ParticipantHost, v1: ParticipantHost, send: Message, recv: Message] {
    send = NoneMessage
    recv = DecisionMsg
    
    // v1.participantDecision = DecisionMsg.decision
    v0.preference = v1.preference
    // v0.participantDecision = NoneDecision
    // v1.participantDecision = Abort 
    // DecisionMsg.decision = Commit => v1.participantDecision = Commit
    // DecisionMsg.decision = Abort => v1.participantDecision = Abort 
    // DecisionMsg.decision = Abort 
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
                          CoordSendReqStep, VoteReqMsg, NoneMessage]
    
    //participant reply Vote preference
    // sndState = TwoPC.nextState[TwoPC.startState] //question... Is there better way to do this?
    DistributedSystemNext[TwoPC.nextState[TwoPC.startState], TwoPC.nextState[TwoPC.nextState[TwoPC.startState]], 
                          PtcpVoteStep, VoteMsg, VoteReqMsg]
    
    // //host receive votes from participant
    // // thdState = TwoPC.nextState[sndState]
    DistributedSystemNext[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]], TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]], 
                          CoordLearnVoteStep, NoneMessage, VoteMsg]
    // // VoteMsg.sender = TwoPC.nextState[TwoPC.nextState[TwoPC.startState]].Participant
    // // VoteMsg.voteChoice = v0.preference

    // //host make and send decision
    DistributedSystemNext[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]], TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]], 
                          CoordDecideStep, DecisionMsg, NoneMessage]

    // // participant receive decision
    DistributedSystemNext[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]], TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]]], 
                          PtcpLearnDecisionStep, NoneMessage, DecisionMsg]

}

run {
    successfulRun
} for exactly 6 DistributedSystem for {nextState is linear}
// for exactly 10 Board, 3 Int for {next is linear}

-- TN: what are the scopes on the sigs? (default will be 3--4)

