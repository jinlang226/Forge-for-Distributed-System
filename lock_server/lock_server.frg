#lang forge/temporal 

// Build a distributed lock server
// First, there is no central server that coordinates the activity.
// Second, the hosts can communicate only via asynchronous messages; a single
// state machine transition cannot simultaneously read or update the state of
// two hosts.

// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1, while all other nodes with an epoch of 0 (and not
// holding the lock). A node that holds the lock can "grant" it to another
// node by sending them a "Grant" message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’s
// epoch number.

abstract sig HostSteps {}
one sig DoAcceptStep extends HostSteps {}
one sig DoGrantStep extends HostSteps {
    recipient: lone Host
}

abstract sig HoldsLock {}
one sig HoldsLockTrue, HoldsLockFalse extends HoldsLock {}

one sig MessageOps {
    send: lone Message,
    recv: lone Message
}

sig Message {
    dest: lone Int,
    msgEpoch: lone Int
}

one sig DistributedSystem {
    hosts: set Host,
    network: one Network
}

pred DistributedSystemInit[d: DistributedSystem] {
    DistributedSystemWF[d] 
    
    all h: d.hosts | HostInit[h]
    NetworkInit[d.network]
    no DoGrantStep.recipient 
}

pred DistributedSystemWF[d: DistributedSystem] {
    all h: d.hosts | #d.hosts.holdsLock & HoldsLockTrue <= 1
    # d.hosts = # Host
    # Host = 3
    all h: d.hosts | HostWF[h]
    // all h: d.hosts | HostWF[h]
    //   && network.c.numHosts == |hosts|
}


sig Network {
    var sentMsg: set Message
}

pred NetworkInit[n: Network] {
    no n.sentMsg 
    // no Message
}

sig Host {
    // numHosts: one Int, //Constant
    // myId: one Int, //Constant
    var holdsLock: one HoldsLock,
    var epoch: one Int
}

pred HostInit[h: Host] {
    HostWF[h]
    (h.holdsLock = HoldsLockTrue)
        =>  (h.epoch = 1)
        else (h.holdsLock = HoldsLockFalse and h.epoch = 0)
}

pred HostWF[h: Host] {
    h.holdsLock = HoldsLockTrue
        implies (all h1: DistributedSystem.hosts-h | h.epoch > h1.epoch)
}

pred validHostId[id : Int] {
    id >= 0 && id < # DistributedSystem.hosts
}

// ghost predicate DoGrant(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step)
//     requires step.DoGrantStep?
//   {
//     var recipient := step.recipient;
//     && v.holdsLock == true
//     && msgOps.recv.None?
//     && ValidHostId(v.c.numHosts, recipient) // Doesn't actually affect safety, but does affect liveness! if we grant to msgOps nonexistent host, no further steps will occur.
//     && msgOps.send == Some(Grant(recipient, v.epoch + 1))
//     && v'.holdsLock == false
//     && v'.epoch == v.epoch
//
    // var holdsLock: one bool, 
    // var epoch: one Int
//   }
pred doGrant[h: Host] {
    h.holdsLock = HoldsLockTrue
    h.holdsLock' = HoldsLockFalse
    h.epoch' = h.epoch
    frameNoOtherHostChange[h]
    // no MessageOps.recv
    // MessageOps.send.dest = DoGrantStep.recipient
    // MessageOps.send.msgEpoch = h.epoch + 1
    // Network.sentMsg' = Network.sentMsg + MessageOps.send
} 

//   ghost predicate DoAccept(v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step)
//     requires step.DoAcceptStep?
//   {
//     && msgOps.recv.Some?
//     && msgOps.recv.value.dest == v.c.myId
//     && msgOps.recv.value.epoch > v.epoch
//     && msgOps.send == None
//     && v'.epoch == msgOps.recv.value.epoch
//     && v'.holdsLock == true
//   }

pred doAccept[h: Host] {
    h.epoch' > h.epoch  
    (h.holdsLock)' = HoldsLockTrue
    h.holdsLock in (HoldsLockTrue + HoldsLockFalse)
    all v: Host-h | {
        v.holdsLock = HoldsLockFalse
    } 
    frameNoOtherHostChange[h]
}

pred frameNoOtherHostChange[h: Host] {
    all v: Host-h | {
        v.holdsLock' = v.holdsLock 
        v.epoch' = v.epoch 
    }
}

// visualization
option max_tracelength 10
run {
    DistributedSystemInit[DistributedSystem]
    // always {
    //     some step: HostSteps| { 
    //         {
    //             step = DoGrantStep and (some h: DistributedSystem.hosts |  {doGrant[h]} )
    //             // and 
    //             // {some h1, h2: DistributedSystem.hosts |  
    //             //     {doGrant[h1] and h2 = DoGrantStep.recipient}
    //             // }
    //         }
    //         or 
    //         {
    //             step = DoAcceptStep and {some h: DistributedSystem.hosts |  {doAccept[h]}}
    //         } 
    //     } 
    //     DistributedSystemWF[DistributedSystem]
    // }
    // always DistributedSystemWF[DistributedSystem]
    // some h: DistributedSystem.hosts |  {doAccept[h]} 
    some h1, h2: DistributedSystem.hosts |  {doAccept[h1] } 
    // next_state {
    //     some h: DistributedSystem.hosts |  {doAccept[h]} 
    // }
    // next_state next_state{
    //     some h: DistributedSystem.hosts |  {doGrant[h]} 
    // }
    // next_state next_state next_state {
    //     some h: DistributedSystem.hosts |  {doAccept[h]} 
    // }
    
    
    // eventually {some dh: DistributedSystem.hosts |  dh.holdsLock = HoldsLockTrue and dh.epoch >= 1} 
}  