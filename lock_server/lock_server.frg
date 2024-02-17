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
one sig DoGrantStep, DoAcceptStep extends HostSteps {}

abstract sig HoldsLock {}
one sig HoldsLockTrue, HoldsLockFalse extends HoldsLock {}

// one sig Message {
//     send: lone MessageOps,
//     recv: lone MessageOps
// }

// sig MessageOps {
//     dest: one Int,
//     msgEpoch: one Int
// }

one sig DistributedSystem {
    hosts: set Host//,
}

pred DistributedSystemInit[d: DistributedSystem] {
    // DistributedSystemWF[d] 
    # d.hosts = 3
    all h: d.hosts | #d.hosts.holdsLock & HoldsLockTrue = 1
    all h: d.hosts | HostInit[h]
    // exists h | h.holdsLock = HoldsLockTrue and h.epoch = 1
    
}

// pred DistributedSystemWF[d: DistributedSystem] {
      // host and network constants have the correct parameters from the global
      // distributed system
    //   && (forall id | ValidHostId(id) ::
    //         // every host knows its id (and ids are unique)
    //         && hosts[id].c.numHosts == |hosts|
    //         && hosts[id].c.myId == id)
    //   && network.c.numHosts == |hosts|
    // all h : d.hosts | validHostId[h.myId] 
    //     implies (h.)
    // (d.hosts).numHosts = 3
    // # d.hosts = 3
// }

sig Host {
    // numHosts: one Int, //Constant
    // myId: one Int, //Constant
    var holdsLock: one HoldsLock,
    var epoch: one Int,
    var lastReceivedRequestFrom: lone Host
}

pred HostInit[h: Host] {
    (h.holdsLock = HoldsLockTrue)
        =>  (h.epoch = 1)
        else (h.holdsLock = HoldsLockFalse and h.epoch = 0)
    // exists h | h.holdsLock = HoldsLockTrue and h.epoch = 1
    // #g.holdsLock & True = 1 
    no h.lastReceivedRequestFrom
}

// pred HostWF[h: Host] {
//     h.numHosts = # DistributedSystem.hosts
// }

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
    h'.holdsLock = HoldsLockTrue
    frameNoOtherHostChange[h]
}

pred frameNoOtherHostChange[h: Host] {
    all v: Host-h | {
        v.holdsLock' = v.holdsLock 
        v.epoch' = v.epoch 
    }
}

// visualization
option max_tracelength 2
run {
    DistributedSystemInit[DistributedSystem]
    // always {
        // some step: HostSteps| { 
        //     {
        //         step = DoGrantStep and {some h: DistributedSystem.hosts |  {doGrant[h]}}
        //     }
            // or 
            // {
            //     step = DoAcceptStep and {some h: DistributedSystem.hosts |  {doAccept[h]}}
            // } 
        // } 
    // }
    // eventually {some dh: DistributedSystem.hosts |  dh.holdsLock = 1 and dh.epoch >= 1} 
}  