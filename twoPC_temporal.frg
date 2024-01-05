#lang forge/temporal 

-- This requires Forge 2.10 or later; you may need to update. 
-- (If you prefer not to, just change the above to #lang forge and uncomment the below)
-- option problem_type temporal

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

-- Steps of the protocol
abstract sig Steps {}
one sig CoordSendReqStep, CoordLearnVoteStep, CoordDecideStep, 
        PtcpVoteStep, PtcpLearnDecisionStep extends Steps {}

-- DistributedSystem
---------------------------------------------------------------------------------

-- Represents the current state of our distributed system
-- There is only one such state at any moment, and the roles of each node are constant.
one sig DistributedSystem {
   -- In temporal mode, these are now stable identities. 
   coordinator: one CoordinatorHost,
   participants: set ParticipantHost
}

pred DistributedSystemWF[d: DistributedSystem] {
    d.coordinator.participantCount = #(d.participants)
    coordWellformed[d.coordinator]
}

-- Startup state: notice the state index is implicit; the DistributedSystem is constant over time.
pred DistributedSystemInit[d: DistributedSystem] {
    DistributedSystemWF[d]       -- start in a well-formed state
    coordInit[d.coordinator]     -- coordinator will be in start state
    all p: d.participants | {    -- all participants also in start state
        ptcpInit[p]
    }
}

-- CoordinatorHost
---------------------------------------------------------------------------------

-- In temporal mode, this is a stable entity, but some of its fields are `var`iable over time.
sig CoordinatorHost {
    participantCount: one Int,  -- not variable
    var coordDecision: one Decision,
    var votes: func ParticipantHost -> Vote -- for each participant, what is its vote?
}

pred coordWellformed[h: CoordinatorHost] {
    h.participantCount = #(h.votes)
}

pred coordInit[v: CoordinatorHost] {
    // No votes recorded yet
    // all v: CoordinatorHost | let uniqueKeys = { x: Int | some y: Int | x->y in v.votes } |
    //     #uniqueKeys = v.participantCount

    -- This "lookup" is a join that asks for the set of votes for *all* ParticipantHosts
    v.votes[ParticipantHost] = NoneVote 
    // No decision recorded yet
    v.coordDecision = NoneDecision
}

pred coordSendReq[v: CoordinatorHost, send: Message, recv: Message] {
    send = VoteReqMsg
    recv = NoneMessage
    -- As written before, this changed no state whatsoever, meaning that it could be 
    -- left out, repeated, etc. So adding that the coordinator has no decision yet and 
    -- nobody has reported their vote successfully. 
    v.coordDecision = NoneDecision -- GUARD
    all ph: ParticipantHost | v.votes[ph] = NoneVote -- GUARD
    -- How will the participants learn of the request? We need to change their state, too. 
    -- (Let's assume they just receive the message.)
    all ph: ParticipantHost | ph.lastReceivedRequestFrom' = v
}

pred coordLearnVote[v: CoordinatorHost, send: Message, recv: Message] {
    v.coordDecision = NoneDecision -- GUARD
    send = NoneMessage -- GUARD
    recv = VoteMsg -- GUARD
    v.votes[VoteMsg.sender] = NoneVote -- GUARD
    // recv.sender = ParticipantHost
    // recv.voteChoice = Vote

    v.votes'[VoteMsg.sender] = VoteMsg.voteChoice -- EFFECT
    v.coordDecision' = v.coordDecision -- prime = in next state
    v.participantCount' = v.participantCount -- prime = in next state

    -- NOTE: if we forget to constrain a var field, its value becomes non-deterministic.
}

// pred coordDecide[v: CoordinatorHost, send: Message, recv: Message] {
//     send = DecisionMsg -- GUARD
//     recv = NoneMessage -- GUARD
//     v.coordDecision = NoneDecision -- GUARD
    
//     -- Beware associativity here; let's add parentheses to be sure. We'll also use if/else.
//     (no ptcpHost: ParticipantHost | v.votes[ptcpHost] = No) 
//         =>   v.coordDecision = Commit
//         else v.coordDecision = Abort 
    
//     -- Not sure what to do with this.
//     --DecisionMsg.decision = v1.coordDecision

//     v.participantCount' = v.participantCount -- EFFECT (FRAME)
//     v.votes' = v.votes -- EFFECT (FRAME)
// }

-- ParticipantHost
---------------------------------------------------------------------------------

-- In temporal mode, a stable entity, but some fields may be `var`iable over time
sig ParticipantHost {
    preference: one Vote, -- leaving this non-variable 
    -- Forge won't let you have 2 sigs with the same field name
    var participantDecision: one Decision, -- but this will change after vote is requested
    var lastReceivedRequestFrom: lone CoordinatorHost -- have they received a request?
}

pred ptcpInit[v: ParticipantHost] {
    -- v.preference is unconstrained (non-deterministic)
    v.preference in (Yes + No)
    v.participantDecision = NoneDecision
    no v.lastReceivedRequestFrom
}

// pred ptcpVote[v: ParticipantHost, send: Message, recv: Message] {
//     // hostId = v0.hostId

//     send = VoteMsg
//     recv = VoteReqMsg
//     v.participantDecision = NoneDecision

// -- TODO
//     VoteMsg.sender = v
//     VoteMsg.voteChoice = v.preference
    
//     v.preference' = v.preference 
//     v.participantDecision' = v.participantDecision
// }

// pred ptcpLearnDecision[v: ParticipantHost, send: Message, recv: Message] {
//     // send = NoneMessage
//     // recv = DecisionMsg
//     // v1.participantDecision = DecisionMsg.decision
//     // v0.participantDecision = NoneDecision
//     v.preference' = v.preference
// }

-- Two Phase Commit
---------------------------------------------------------------------------------

-- This transition causes the system to "stutter", allowing us to see traces that exhibit 
-- deadlocks, etc. The key is that we frame _every var field_ to remain the same.
pred doNothing {
    all ch: CoordinatorHost | {
        ch.coordDecision' = ch.coordDecision
        ch.votes' = ch.votes
    }
    all ph: ParticipantHost | {
        ph.participantDecision' = ph.participantDecision
        ph.lastReceivedRequestFrom' = ph.lastReceivedRequestFrom
    }
    -- TODO: did I miss anything?

}

run {
    -- Start in an initial state (there's only one DistributedSystem, so we can use the type name safely)
    DistributedSystemInit[DistributedSystem]
    -- Always follow the transition relation. Restrict to the first two for now.
    always {
        some step: Steps, send: Message, recv: Message, phost: ParticipantHost, decision: Decision | {
            -- NOTE: Beware; don't use the steps in the transition functions as guards / update them, 
            -- otherwise the distributed system becomes extremely well-behaved 
            {step = CoordSendReqStep and coordSendReq[DistributedSystem.coordinator, send, recv]}
            or
            {step = CoordLearnVoteStep and coordLearnVote[DistributedSystem.coordinator, send, recv]}
            // or 
            // {doNothing}
            // or 
            // {step = CoordDecideStep and 
            //  (no ptcpHost: ParticipantHost | (DistributedSystem.coordinator).votes[ptcpHost] = NoneVote) and
            //  coordDecide[DistributedSystem.coordinator, send, recv]}
            // or
            // {step = PtcpVoteStep and ptcpVote[DistributedSystem.participants, send, recv]} 
            // or 
            // {step = PtcpLearnDecisionStep and ptcpLearnDecision[DistributedSystem.participants, send, recv]}
    
        } 
    }

    -- Narrow scope of traces; we want to see something interesting!
    -- Note: I don't quite understand what the recv field is for?
    eventually coordSendReq[DistributedSystem.coordinator, VoteReqMsg, NoneMessage]
} 
-- We no longer need the "is linear"

