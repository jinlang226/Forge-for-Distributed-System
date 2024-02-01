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
// abstract sig Message { }
// sig NoneMessage extends Message {} -- represents a missing message/response
// sig VoteReqMsg extends Message {}  -- step 1 (coordinator sends)
// sig VoteMsg extends Message {      -- step 2 (participant sends)
//     sender: one ParticipantHost, 
//     voteChoice: one Vote
// }    
// sig DecisionMsg extends Message { -- step 3 (coordinator sends) 
//     decision: one Decision
// } 

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
    -- This "lookup" is a join that asks for the set of votes for *all* ParticipantHosts
    v.votes[ParticipantHost] = NoneVote 
    // No decision recorded yet
    v.coordDecision = NoneDecision
}

// STEP 1
pred coordSendReq[v: CoordinatorHost] {
    -- As written before, this changed no state whatsoever, meaning that it could be 
    -- left out, repeated, etc. So adding that the coordinator has no decision yet and 
    -- nobody has reported their vote successfully. 
    v.coordDecision = NoneDecision -- GUARD
    all ph: ParticipantHost | v.votes[ph] = NoneVote -- GUARD
    -- How will the participants learn of the request? We need to change their state, too. 
    -- (Let's assume they just receive the message.)
    all ph: ParticipantHost | ph.lastReceivedRequestFrom' = v -- ACTION
    all ph: ParticipantHost | ph.participantDecision' = ph.participantDecision -- FRAME

    frameNoCoordinatorChange
    // v.lastReceivedRequestFrom' = v.lastReceivedRequestFrom -- FRAME
    // frameNoOtherParticipantChange[v] -- FRAME

}

-- STEP 3
// pred coordLearnVote[v: CoordinatorHost] {
//     v.coordDecision = NoneDecision -- GUARD
//     v.votes[VoteMsg.sender] = NoneVote -- GUARD
    
//     // recv.sender = ParticipantHost
//     // recv.voteChoice = Vote

//     v.votes'[VoteMsg.sender] = VoteMsg.voteChoice -- EFFECT
//     v.coordDecision' = v.coordDecision -- prime = in next state
//     v.participantCount' = v.participantCount -- prime = in next state
//     // frameNoOtherParticipantChange[v]

//     -- NOTE: if we forget to constrain a var field, its value becomes non-deterministic.
// }

pred coordDecide[v: CoordinatorHost] {
    v.coordDecision = NoneDecision -- GUARD
    
    -- Beware associativity here; let's add parentheses to be sure. We'll also use if/else.
    (no ptcpHost: ParticipantHost | v.votes[ptcpHost] = No) 
        =>   (v.coordDecision)' = Commit 
        else (v.coordDecision)' = Abort 

    v.participantCount' = v.participantCount -- EFFECT (FRAME)
    v.votes' = v.votes -- EFFECT (FRAME)
    all ph: ParticipantHost | ph.lastReceivedRequestFrom' = ph.lastReceivedRequestFrom -- ACTION
    all ph: ParticipantHost | ph.participantDecision' = ph.participantDecision -- FRAME
    // all ph: ParticipantHost | ph.participantDecision' = (v.coordDecision)' //this works
    // frameNoOtherParticipantChange[v]
}

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

// STEP 2
pred ptcpVote[v: ParticipantHost] {
    v.participantDecision = NoneDecision -- GUARD
    v.lastReceivedRequestFrom = CoordinatorHost -- received a request
    -- not var, so don't need a frame
    --v.preference' = v.preference 

    -- abstract out network for now; direct change to CoordinatorHost
    --frameNoCoordinatorChange
    
    all ph: ParticipantHost-v | {
        (CoordinatorHost.votes[ph])' = CoordinatorHost.votes[ph] 
    }
    CoordinatorHost.votes[v] = NoneVote 
    (CoordinatorHost.votes[v])' = v.preference -- ACTION (direct, no network)
    CoordinatorHost.coordDecision' = CoordinatorHost.coordDecision -- FRAME
    v.participantDecision' = v.participantDecision -- FRAME
    v.lastReceivedRequestFrom' = v.lastReceivedRequestFrom -- FRAME
    frameNoOtherParticipantChange[v] -- FRAME
}

--------------------------------------------
-- Framing helpers
-- NOTE WELL: if we add additional `var` fields, we need to add them here.
pred frameNoCoordinatorChange {
    CoordinatorHost.coordDecision' = CoordinatorHost.coordDecision
    CoordinatorHost.votes' = CoordinatorHost.votes 
}
pred frameNoOtherParticipantChange[ph: ParticipantHost] {
    all v: ParticipantHost-ph | {
        v.participantDecision' = v.participantDecision 
        v.lastReceivedRequestFrom' = v.lastReceivedRequestFrom 
    }
}
--------------------------------------------

pred ptcpLearnDecision[v: ParticipantHost] {
    v.lastReceivedRequestFrom = CoordinatorHost 
    v.participantDecision = NoneDecision 
    (v.participantDecision)' = CoordinatorHost.coordDecision
    (v.lastReceivedRequestFrom)' = v.lastReceivedRequestFrom  
    
    CoordinatorHost.coordDecision in (Abort + Commit)
    frameNoCoordinatorChange 
    frameNoOtherParticipantChange[v]
}

-- Two Phase Commit
---------------------------------------------------------------------------------

-- This transition causes the system to "stutter", allowing us to see traces that exhibit 
-- deadlocks, etc. The key is that we frame _every var field_ to remain the same.
pred doNothing {
    -- not t1_enabled and not t2_enabled and ...
    all ch: CoordinatorHost | {
        ch.coordDecision' = ch.coordDecision
        ch.votes' = ch.votes
    }
    all ph: ParticipantHost | {
        ph.participantDecision' = ph.participantDecision
        ph.lastReceivedRequestFrom' = ph.lastReceivedRequestFrom
    }
}


// 2PC should satisfy the Atomic Commit specification:

// AC-1: All processes that reach a decision reach the same one.
// forall h1, h2 | ValidParticipantId(v, h1) && ValidParticipantId(v, h2) ::
//   ParticipantVars(v, h1).decision.Some? && ParticipantVars(v, h2).decision.Some? ==>
//     ParticipantVars(v, h1).decision.value == ParticipantVars(v, h2).decision.value
pred ac1[d: DistributedSystem] {
    all h1, h2: d.participants | {
        h1.participantDecision != NoneDecision and h2.participantDecision != NoneDecision
    } => {
        h1.participantDecision = h2.participantDecision
    }
}

// AC-3: If any host has a No preference, then the decision must be Abort.
// Any host with a No preference forces an abort.
// (exists hostid:HostId ::
//    && ValidParticipantId(v, hostid)
//    && ParticipantVars(v, hostid).c.preference.No?)
// ==> forall h:HostId | ValidParticipantId(v, h) && ParticipantVars(v, h).decision.Some? ::
//     ParticipantVars(v, h).decision.value == Abort
pred ac3[d: DistributedSystem] {
    some h: d.participants | h.preference = No
    => {
        all h1: d.participants | {
            h1.participantDecision != NoneDecision 
        } => {
            h1.participantDecision = Abort
            and
            (d.coordinator).coordDecision = Abort
            and
            h1.lastReceivedRequestFrom = d.coordinator
        }
    }
}

// AC-4: If all processes prefer Yes, then the decision must be Commit.
// If every host has a Yes preference we must commit.
// (forall hostid:HostId | ValidParticipantId(v, hostid) ::
//    ParticipantVars(v, hostid).c.preference.Yes?)
// => forall h:HostId | ValidParticipantId(v, h) && ParticipantVars(v, h).decision.Some? ::
//     ParticipantVars(v, h).decision.value == Commit
pred ac4[d: DistributedSystem] {
    all h: d.participants | h.preference = Yes
    => {
        all h1: d.participants | {
            h1.participantDecision != NoneDecision 
        } => {
            h1.participantDecision = Commit and
            (d.coordinator).coordDecision = Commit
              and
            h1.lastReceivedRequestFrom = d.coordinator
        }
    }
}

pred safty[d: DistributedSystem] {
    ac1[d] and 
    ac3[d] and 
    ac4[d]
}


pred invariant[d: DistributedSystem] {
    // safty[d] 
    // and 
    // coordinatorDecisionReflectsPreferences[d] 
    // and
    (all h1: d.participants | 
    (((d.coordinator).votes[h1] != NoneVote) => (d.coordinator).votes[h1] = h1.preference)) 
    // and   
    // (all h1: d.participants | ((no h1.lastReceivedRequestFrom) and(h1.participantDecision = NoneDecision) and (d.coordinator.coordDecision = NoneDecision) and (d.coordinator.votes[h1] = NoneVote))
    //     => (all h: d.participants | (h.participantDecision = NoneDecision) and d.coordinator.coordDecision = NoneDecision) )
    // and
    // (all h1: d.participants | (h1.preference = Yes)
    //     =>  (h1.participantDecision = Commit)
    //     else (h1.participantDecision = Abort) )

    and 
    (all h1: d.participants | {
        h1.preference in (Yes + No) 
    } )
}

pred anyTransition[d: DistributedSystem, ph: ParticipantHost] {
    coordSendReq[d.coordinator] or
    coordDecide[d.coordinator] or
    ptcpVote[ph] or
    ptcpLearnDecision[ph] 
    or
    doNothing
}

option max_tracelength 2
test expect {
    initStep: { 
        #(DistributedSystem.coordinator) = 1  
        # CoordinatorHost = 1
        DistributedSystemInit[DistributedSystem]
        not invariant[DistributedSystem]
    } 
    is unsat


    inductiveStep: {
        #(DistributedSystem.coordinator) = 1  
        # CoordinatorHost = 1
        some ph: DistributedSystem.participants | { 
            anyTransition[DistributedSystem, ph] 
        }
        invariant[DistributedSystem]
        not next_state invariant[DistributedSystem] 
    } 
    is unsat

    //init and always next and eventually not safe
    inductiveStepTwo: {  
        #(DistributedSystem.coordinator) = 1  
        # CoordinatorHost = 1
        DistributedSystemInit[DistributedSystem] 
        always (some ph: DistributedSystem.participants | { 
            // next_state anyTransition[DistributedSystem, ph] //doNothing fails
            next_state coordSendReq[DistributedSystem.coordinator] //pass
            // next_state coordDecide[DistributedSystem.coordinator]  //pass 
            // next_state ptcpVote[ph] //pass 
            // next_state ptcpLearnDecision[ph] //pass 
            // next_state doNothing //fails
        })
        eventually not invariant[DistributedSystem]
    }
    is unsat
    
}

// option max_tracelength 10
// run {
//     -- Start in an initial state (there's only one DistributedSystem, so we can use the type name safely)
//     DistributedSystemInit[DistributedSystem]
//     -- Always follow the transition relation. Restrict to the first two for now.
//     always {
//         some step: Steps| { 
//             -- NOTE: Beware; don't use the steps in the transition functions as guards / update them, 
//             -- otherwise the distributed system becomes extremely well-behaved 
//             {step = CoordSendReqStep and coordSendReq[DistributedSystem.coordinator]}
//             or 
//             {step = PtcpVoteStep and {some ph: DistributedSystem.participants |  {ptcpVote[ph]}}} 
//             or 
//             {doNothing}
//             or 
//             {
//                 step = CoordDecideStep 
//                 and 
//                 (no ptcpHost: ParticipantHost | (DistributedSystem.coordinator).votes[ptcpHost] = NoneVote) 
//                 and
//                 coordDecide[DistributedSystem.coordinator]
//             }
//             or
//             {   
//                 step = PtcpLearnDecisionStep 
//                 // and 
//                 // (DistributedSystem.coordinator).coordDecision in (Abort + Commit)
//                 and
//                 {some ph: DistributedSystem.participants | {ptcpLearnDecision[ph]}} 
//             } 
    
//         } 
//     }

//     -- Narrow scope of traces; we want to see something interesting!
//     -- Note: I don't quite understand what the recv field is for?
//     -- Start state: step 1 
//     // coordSendReq[DistributedSystem.coordinator] 
//     -- 2nd state: step 2  (next_state in Forge ~= LTL X ~= Alloy 6 after)
//     // next_state {some ph: DistributedSystem.participants | ptcpVote[ph]}
//     // next_state next_state {some ph: DistributedSystem.participants | ptcpVote[ph]}
//     // -- 4th state: step 4
//     // next_state next_state next_state  {coordDecide[DistributedSystem.coordinator]}
//     // next_state next_state next_state next_state {some ph: DistributedSystem.participants | ptcpLearnDecision[ph]}
//     // next_state next_state next_state next_state next_state {some ph: DistributedSystem.participants | ptcpLearnDecision[ph]}


//     // eventually coordSendReq[DistributedSystem.coordinator] 
//     // eventually {some ph: DistributedSystem.participants | ptcpVote[ph]}
//     // // eventually {some ph: DistributedSystem.participants | ptcpVote[ph]}
//     // eventually  {coordDecide[DistributedSystem.coordinator]}
//     // eventually {some ph: DistributedSystem.participants | ptcpLearnDecision[ph]}
//     eventually {all ph: DistributedSystem.participants | ph.participantDecision in (Abort + Commit)} 
//     // eventually {some ph: DistributedSystem.participants | ptcpLearnDecision[ph]}
//     -- Make sure we didn't break something!
//     # ParticipantHost > 1 
// } 
// -- We no longer need the "is linear"