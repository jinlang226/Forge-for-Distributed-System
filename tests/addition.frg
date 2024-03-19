#lang forge/temporal 

one sig DistributedSystem {
    var n: one Int
}

pred DistributedSystemInit[d: DistributedSystem] {
    d.n = 0
}

pred plusOne[d: DistributedSystem] {
    d.n' = add[d.n, 1]
}


pred doNothing[d: DistributedSystem] {
    d = d'
}

option max_tracelength 10
run {
    DistributedSystemInit[DistributedSystem]
    always {
        plusOne[DistributedSystem]
        or 
        doNothing[DistributedSystem]
    }
    eventually {
        DistributedSystem.n = 6
    }
}  
