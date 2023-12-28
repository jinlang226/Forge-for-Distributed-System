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
        coordSendReq[d0, d1, send, recv]
    }
    
    step = CoordLearnVoteStep => {
        coordLearnVote[d0, d1, send, recv]
    } 

    step = CoordDecideStep and ((d0.coordinator).votes[ParticipantHost] != NoneVote) => {
        coordDecide[d0, d1, send, recv]
    }

    step = PtcpVoteStep => {
        ptcpVote[d0, d1, send, recv]
    } 

    step = PtcpLearnDecisionStep and (DecisionMsg.decision != NoneDecision) => { //and (DecisionMsg.decision != NoneDecision)
    //and (DecisionMsg.decision != NoneDecision)
        ptcpLearnDecision[d0, d1, send, recv]
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
    h.participantCount = 1 
}

pred coordInit[v: CoordinatorHost] {
    v.votes[ParticipantHost] = NoneVote 
    v.coordDecision = NoneDecision
    v.participantCount = 1
}

pred coordSendReq[v0: DistributedSystem, v1: DistributedSystem, send: Message, recv: Message] {
    //coordWellformed[v0]
    // messages
    send = VoteReqMsg
    recv = NoneMessage

    // coordinator
    v0.coordinator = v1.coordinator
    (v0.coordinator).votes = (v1.coordinator).votes
    (v0.coordinator).participantCount = 1
    (v1.coordinator).participantCount = 1

    // participant
    v0.participants = v1.participants
    (v1.participants).preference = (v0.participants).preference
}

pred coordLearnVote[v0: DistributedSystem, v1: DistributedSystem, send: Message, recv: Message] {
    // coordWellformed[v0]

    // messages 
    send = NoneMessage
    recv = VoteMsg

    // coordinator
    (v0.coordinator).votes[VoteMsg.sender] = NoneVote
    (v1.coordinator).votes[VoteMsg.sender] = VoteMsg.voteChoice
    (v1.coordinator).coordDecision = (v0.coordinator).coordDecision
    (v0.coordinator).participantCount = 1
    (v1.coordinator).participantCount = 1

    // participant
    v0.participants = v1.participants
    (v1.participants).preference = (v0.participants).preference
}

pred coordDecide[v0: DistributedSystem, v1: DistributedSystem, send: Message, recv: Message] {
    // coordinator
    (v0.coordinator).votes = (v1.coordinator).votes
    (v0.coordinator).participantCount = 1
    (v1.coordinator).participantCount = 1
    (v0.coordinator).votes[ParticipantHost] = Yes => (v1.coordinator).coordDecision = Commit //issue
    (v0.coordinator).votes[ParticipantHost] = No => (v1.coordinator).coordDecision = Abort 
    (v0.coordinator).coordDecision = NoneDecision

    // participant
    (v1.participants).preference = (v0.participants).preference
    DecisionMsg.decision = (v1.coordinator).coordDecision
    
    // messages
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
    // v.preference = No 
    v.participantDecision = NoneDecision 
}

pred ptcpVote[v0: DistributedSystem, v1: DistributedSystem, send: Message, recv: Message] {
    // messages 
    VoteMsg.sender = (v0.participants)
    VoteMsg.voteChoice = (v0.participants).preference
    send = VoteMsg
    recv = VoteReqMsg

    // participant    
    (v0.participants)= (v1.participants)
    (v1.participants).preference = (v0.participants).preference
    (v1.participants).participantDecision = (v0.participants).participantDecision
    
    // coordinator
    v0.coordinator = v1.coordinator
}

pred ptcpLearnDecision[v0: DistributedSystem, v1: DistributedSystem, send: Message, recv: Message] {
    // messages 
    send = NoneMessage
    recv = DecisionMsg

    // participant
    (v1.participants).preference = (v0.participants).preference
    (v0.participants).participantDecision = NoneDecision
    DecisionMsg.decision = Commit => (v1.participants).participantDecision = Commit
    DecisionMsg.decision = Abort => (v1.participants).participantDecision = Abort 
    
    // coordinator
    v0.coordinator = v1.coordinator
}

-- Two Phase Commit
---------------------------------------------------------------------------------
-- Represents a run of the protocol
one sig TwoPC {
    startState: one DistributedSystem, -- IMPORTANT: these are _states_
    nextState: pfunc DistributedSystem -> DistributedSystem
}
-- NOTE: add {nextState is linear} to run

pred successfulRun[start: DistributedSystem, ds0: DistributedSystem, ds1: DistributedSystem, ds2: DistributedSystem, 
                    ds3: DistributedSystem, ds4: DistributedSystem, decision: DecisionMsg, vote: VoteMsg] {

    -- Initial state is really an initial state
    no ds: DistributedSystem | TwoPC.nextState[ds] = start 
    DistributedSystemInit[start]

    -- "hard coding" the transition. Could instead say that always this pred is used
    // send vote req
    DistributedSystemNext[start, ds0, 
                          CoordSendReqStep, VoteReqMsg, NoneMessage]
    
    //participant reply Vote preference
    DistributedSystemNext[ds0, ds1,
                          PtcpVoteStep, VoteMsg, VoteReqMsg]
    
    //host receive votes from participant
    DistributedSystemNext[ds1, ds2, 
                          CoordLearnVoteStep, NoneMessage, VoteMsg]

    //host make and send decision
    DistributedSystemNext[ds2, ds3, 
                          CoordDecideStep, DecisionMsg, NoneMessage]

    // participant receive decision
    DistributedSystemNext[ds3, ds4, 
                          PtcpLearnDecisionStep, NoneMessage, DecisionMsg]
}

run {
    successfulRun[TwoPC.startState,
                    TwoPC.nextState[TwoPC.startState], 
                    TwoPC.nextState[TwoPC.nextState[TwoPC.startState]],
                    TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]],
                    TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]], 
                    TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.nextState[TwoPC.startState]]]]],
                    DecisionMsg,
                    VoteMsg
                    ]
                    
} for exactly 6 DistributedSystem, 2 ParticipantHost, 1 DecisionMsg, 1 VoteMsg for {nextState is linear}

-- TN: what are the scopes on the sigs? (default will be 3--4)

