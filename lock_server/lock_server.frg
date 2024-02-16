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

one sig DistributedSystem {
    hosts: set Host
}

pred DistributedSystemWF[d: DistributedSystem] {
    all h: d.hosts | HostWF[h]
    # d.hosts > 0 
}

sig Host {
    numHosts: one Int, //Constant
    myId: one Int, //Constant
    holdsLock: one bool, 
    epoch: one Int
}

pred HostInit[h: Host] {
    (h.myId = 0)
        =>  (h.holdsLock = true & h.epoch = 1)
        else (h.holdsLock = false & h.epoch = 0)
}

pred HostWF[h: Host] {
    h.numHosts = # DistributedSystem.hosts
}

pred validHostId[id : Int] {
    id >= 0 && id < DistributedSystem.hosts.numHosts
}


// visualization
option max_tracelength 20
run {
    DistributedSystemInit[DistributedSystem]
    always {
        some step: Steps| { 
            {
                step = CoordSendReqStep and coordSendReq[DistributedSystem.coordinator] 
            }
            or 
            {
                step = PtcpVoteStep and {some ph: DistributedSystem.participants |  {ptcpVote[ph]}}
            } 
        } 
    }
    eventually {all ph: DistributedSystem.participants | ph.participantDecision in (Abort + Commit)} 
}  