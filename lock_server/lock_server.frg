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
one sig DoGrantStep extends HostSteps {} 

abstract sig HoldsLock {}
one sig HoldsLockTrue, HoldsLockFalse extends HoldsLock {}

one sig Network {
    msg: set Message
}

sig Message {
    dest: lone Host,
    msgEpoch: lone Int
}

one sig DistributedSystem {
    hosts: set Host,
    network: one Network
}

pred DistributedSystemInit[d: DistributedSystem] {
    # d.hosts = # Host
    # Host = 3
    all h: d.hosts | HostWF[h]
    one h: d.hosts | (h.holdsLock = HoldsLockTrue and Network.msg.dest = h) // all h: d.hosts | #d.hosts.holdsLock & HoldsLockTrue = 1 
    all h: d.hosts | HostInit[h]
    NetworkInit[d.network]
}

pred DistributedSystemWF[d: DistributedSystem] {
    lone h: d.hosts | h.holdsLock = HoldsLockTrue  // all h: d.hosts | #d.hosts.holdsLock & HoldsLockTrue <= 1
    # d.hosts = # Host
    # Host = 3
    all h: d.hosts | HostWF[h]
    # Network.msg = # Message
}

sig Host {
    var holdsLock: one HoldsLock,
    var epoch: one Int
}

pred HostInit[h: Host] {
    HostWF[h]
    (h.holdsLock = HoldsLockTrue)
        =>  (h.epoch = 1)
        else (h.holdsLock = HoldsLockFalse and h.epoch = 0)
}

pred NetworkInit[n: network] {
    // Network.msg.msgEpoch = -1
    // # Network.msg = 1
    // # Message = 1
    n.msg = {} //jw: how to initialize a empty set?
}

pred HostWF[h: Host] {
    h.holdsLock = HoldsLockTrue
        implies (all h1: DistributedSystem.hosts-h | h.epoch > h1.epoch)
}

pred validHostId[id : Int] {
    id >= 0 && id < # DistributedSystem.hosts
}

pred doGrant[h: Host] {
    h.holdsLock = HoldsLockTrue
    h.holdsLock' = HoldsLockFalse
    h.epoch' = h.epoch
    frameNoOtherHostChange[h]
    (all h1: DistributedSystem.hosts-h | h1.epoch < h.epoch)
    Network.msg = Network.msg'
    // sendMsg[add[h.epoch, 1]]
} 

pred sendMsg[e: Int] {
    //with the effect of adding the message to the network
    some m: Message | {
        m.msgEpoch = e and
        (one h: DistributedSystem.hosts | m.dest = h) and
        (Network.msg + m  = Network.msg') and
        (m not in Network.msg)
    } //jw: how to add a message?
}

pred recvMsg[m: Message] {
    //with the guard that the message must be on the network
    m in Network.msg
    all h: DistributedSystem.hosts | {
        m.msgEpoch > h.epoch
    }
}

pred doAccept[h: Host] {
    some m: Network.msg | (recvMsg[m] and m.dest = h and h'.epoch = m.msgEpoch)
    // recvMsg[m] 
    // m.dest = h
    // h'.epoch = m.msgEpoch
    h.epoch < h'.epoch
    // h.epoch' = add[h.epoch, 2] // jw: It is ideal to add to message 
    h.holdsLock = HoldsLockFalse
    h.holdsLock' = HoldsLockTrue
    all v: Host-h | {
        v.holdsLock = HoldsLockFalse and 
        v.epoch < h.epoch'
    } 
    frameNoOtherHostChange[h]
    (all h1: DistributedSystem.hosts |  h1.holdsLock = HoldsLockFalse) 
    (some h1: DistributedSystem.hosts-h | h1.epoch >= h.epoch)
}

pred frameNoOtherHostChange[h: Host] {
    all v: Host-h | {
        v.holdsLock' = v.holdsLock 
        v.epoch' = v.epoch 
    }
}

pred doNothing {
    all h: Host | {
        h.holdsLock' = h.holdsLock
        h.epoch' = h.epoch
    }
}

// visualization
option max_tracelength 20
run {
    DistributedSystemInit[DistributedSystem]
    // always {
    //     some step: HostSteps| { 
    //         {
    //             step = DoGrantStep and 
    //             (some h: DistributedSystem.hosts |  
    //                 { h.holdsLock = HoldsLockTrue and 
    //                 doGrant[h]} 
    //             )
    //         }
    //         or 
    //         {
    //             step = DoAcceptStep and 
    //             {some h: DistributedSystem.hosts |  
    //                 {doAccept[h]} 
    //             }  
    //         } 
    //         or
    //         {doNothing}
    //     } 
    //     DistributedSystemWF[DistributedSystem]
    // }

    always DistributedSystemWF[DistributedSystem]
    some h: DistributedSystem.hosts | doGrant[h]
    // next_state {
    //     x and 
    //     {next_state 
    //         {y 
    //             // and {
    //             //     next_state {
    //             //         ...
                    
    //             //     }
    //             // }
    //         }
    //     }
    
    // }
    
    // eventually {some dh: DistributedSystem.hosts |  (dh.holdsLock = HoldsLockTrue and dh.epoch > 1)} 
}  