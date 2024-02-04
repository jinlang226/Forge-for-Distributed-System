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
// jw: I added a `InitNoneDecision` below to represent the initial state. 
// This is because I need to distinguish between the initial state and VoteReqStep. 
// Otherwise, forge seems have trouble to prove the InitStep
one sig InitNoneDecision, NoneDecision, Commit, Abort extends Decision {} 
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
    #(d.coordinator) = 1  
    # CoordinatorHost = 1
    #(d.participants) = 2
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
    -- This "lookup" is a join that asks for the set of votes for *all* ParticipantHosts
    v.votes[ParticipantHost] = NoneVote // No votes recorded yet
    v.coordDecision = InitNoneDecision // No decision recorded yet
}

// STEP 1
pred coordSendReq[v: CoordinatorHost] {
    -- As written before, this changed no state whatsoever, meaning that it could be 
    -- left out, repeated, etc. So adding that the coordinator has no decision yet and 
    -- nobody has reported their vote successfully. 
    v.coordDecision = InitNoneDecision 
    v.coordDecision' = NoneDecision -- GUARD 
    all ph: ParticipantHost | v.votes[ph] = NoneVote -- GUARD
    -- How will the participants learn of the request? We need to change their state, too. 
    -- (Let's assume they just receive the message.)
    all ph: ParticipantHost | ph.lastReceivedRequestFrom' = v -- ACTION
    all ph: ParticipantHost | ph.participantDecision' = ph.participantDecision -- FRAME
    CoordinatorHost.votes' = CoordinatorHost.votes 
}

// STEP 3
pred coordDecide[v: CoordinatorHost] {
    v.coordDecision = NoneDecision -- GUARD
    no ptcpHost: ParticipantHost | (DistributedSystem.coordinator).votes[ptcpHost] = NoneVote
    -- Beware associativity here; let's add parentheses to be sure. We'll also use if/else.
    ((all ptcpHost: ParticipantHost | v.votes[ptcpHost] = Yes))
        =>  (v.coordDecision)' = Commit 
        else (v.coordDecision)' = Abort 
    v.participantCount' = v.participantCount -- EFFECT (FRAME)
    v.votes' = v.votes -- EFFECT (FRAME)
    all ph: ParticipantHost | ph.lastReceivedRequestFrom' = ph.lastReceivedRequestFrom -- ACTION
    all ph: ParticipantHost | ph.participantDecision' = ph.participantDecision -- FRAME
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
    --v.preference' = v.preference  -- not var, so don't need a frame 

    -- abstract out network for now; direct change to CoordinatorHost
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

// STEP 4
pred ptcpLearnDecision[v: ParticipantHost] {
    v.lastReceivedRequestFrom = CoordinatorHost 
    v.participantDecision = NoneDecision 
    (v.participantDecision)' = CoordinatorHost.coordDecision
    (v.lastReceivedRequestFrom)' = v.lastReceivedRequestFrom  
    CoordinatorHost.coordDecision in (Abort + Commit)
    frameNoCoordinatorChange 
    frameNoOtherParticipantChange[v]
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
pred ac1[d: DistributedSystem] {
    all h1, h2: d.participants | {
        h1.participantDecision in (Commit + Abort) and h2.participantDecision in (Commit + Abort)
    } => {
        h1.participantDecision = h2.participantDecision
        h2.participantDecision = d.coordinator.coordDecision
    }
}

// AC-3: If any host has a No preference, then the decision must be Abort.
pred ac3[d: DistributedSystem] {
    (not (all ptcpHost: ParticipantHost | ptcpHost.preference= Yes) and (no ptcpHost: ParticipantHost | d.coordinator.votes[ptcpHost] = NoneVote))
    => {
        all h1: d.participants | {
            h1.participantDecision in (Abort + Commit)
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
pred ac4[d: DistributedSystem] {
    (all h: d.participants | h.preference = Yes)
    => {
        all h1: d.participants | {
            h1.participantDecision in (Abort + Commit)
        } => {
            h1.participantDecision = Commit and
            (d.coordinator).coordDecision = Commit
              and
            h1.lastReceivedRequestFrom = d.coordinator
        }
    }
}

pred safety[d: DistributedSystem] {
    ac1[d] and 
    ac3[d] and 
    ac4[d]
}

pred anyTransition[d: DistributedSystem, ph: ParticipantHost] {
    coordSendReq[d.coordinator] or
    coordDecide[d.coordinator] or
    ptcpVote[ph] or
    ptcpLearnDecision[ph] 
    or
    doNothing
}

pred invariant[d: DistributedSystem] {
    DistributedSystemWF[d] and
    safety[d] and 
    (all h: d.participants | ((d.coordinator).votes[h] != NoneVote => (d.coordinator).votes[h] = h.preference)) 
    and 
    (all h: d.participants | h.preference in (Yes + No))
    and
    (all h: d.participants | h.participantDecision = Commit =>
        (h.lastReceivedRequestFrom = d.coordinator and
        (all h2: d.participants | (d.coordinator.votes[h2] = Yes))))
    and
    (all h: d.participants | h.participantDecision =  Abort =>
        ((h.lastReceivedRequestFrom = d.coordinator) and
        (no ptcpHost: ParticipantHost | d.coordinator.votes[ptcpHost] = NoneVote) and 
        (not (all ptcpHost: ParticipantHost | d.coordinator.votes[ptcpHost] = Yes))
        ))
    
    and (all h: d.participants | h.lastReceivedRequestFrom != d.coordinator
        => h.participantDecision = NoneDecision and
            d.coordinator.votes[h] = NoneVote and
            d.coordinator.coordDecision = InitNoneDecision)
    and (all h: d.participants | h.lastReceivedRequestFrom = d.coordinator 
        => d.coordinator.coordDecision != InitNoneDecision and 
                h.participantDecision != InitNoneDecision)
    and
    (d.coordinator.coordDecision = Commit =>
        (ParticipantHost.lastReceivedRequestFrom = d.coordinator and
        (all h: d.participants | d.coordinator.votes[h] = Yes)))
    and
    (d.coordinator.coordDecision = Abort =>
        ((ParticipantHost.lastReceivedRequestFrom = d.coordinator) and
        (no ptcpHost: ParticipantHost | d.coordinator.votes[ptcpHost] = NoneVote) and 
        (not (all ptcpHost: ParticipantHost | d.coordinator.votes[ptcpHost] = Yes))
        ))
    and
    (all h: d.participants | h.participantDecision in (Abort + Commit) =>
        d.coordinator.coordDecision = h.participantDecision)
}

option max_tracelength 2
test expect {
    initStep: { 
        DistributedSystemInit[DistributedSystem]
        not invariant[DistributedSystem]
    } 
    is unsat

    inductiveStep: {
        (some ph: DistributedSystem.participants | { 
            anyTransition[DistributedSystem, ph] 
        }) and
        invariant[DistributedSystem] and
        not next_state invariant[DistributedSystem] 
    } 
    is unsat

    invImpliesSafety: { 
        invariant[DistributedSystem] and
        not safety[DistributedSystem] 
    }
    is unsat
}

// option max_tracelength 20
// run {
//     -- Start in an initial state (there's only one DistributedSystem, so we can use the type name safely)
//     DistributedSystemInit[DistributedSystem]
//     -- Always follow the transition relation. Restrict to the first two for now.
//     always {
//         some step: Steps| { 
//             -- NOTE: Beware; don't use the steps in the transition functions as guards / update them, 
//             -- otherwise the distributed system becomes extremely well-behaved 
//             {
//                 step = CoordSendReqStep and coordSendReq[DistributedSystem.coordinator] 
//             }
//             or 
//             {
//                 step = PtcpVoteStep and {some ph: DistributedSystem.participants |  {ptcpVote[ph]}}
//             } 
//             or 
//             {doNothing}
//             or 
//             {
//                 step = CoordDecideStep and 
//                 // (no ptcpHost: ParticipantHost | (DistributedSystem.coordinator).votes[ptcpHost] = NoneVote) and
//                 coordDecide[DistributedSystem.coordinator]
//             }
//             or
//             {   
//                 step = PtcpLearnDecisionStep and
//                 {some ph: DistributedSystem.participants | {ptcpLearnDecision[ph]}} 
//             } 
//         } 
//     }

//     eventually {all ph: DistributedSystem.participants | ph.participantDecision in (Abort + Commit)} 
//     -- Make sure we didn't break something!
//     // # ParticipantHost =3 
// }  -- We no longer need the "is linear"
