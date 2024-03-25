#lang forge/temporal 

abstract sig Value{}
one sig A, B, C extends Value {}

one sig DistributedSystem {
    var v: one Value
}

pred DistributedSystemInit[d: DistributedSystem] {
    d.v = A
}

pred succ[d: DistributedSystem] {
    (d.v = A and d.v' = B) or (d.v = B and d.v' = C)
}

pred doNothing[d: DistributedSystem] {
    d.v = d.v'
}

option max_tracelength 10
// expected: v = A to v = B, and then v = C
// behavior: v = A to v = C
run {
    DistributedSystemInit[DistributedSystem]
    always {
        succ[DistributedSystem]
        or 
        doNothing[DistributedSystem]
    }
    eventually { 
        DistributedSystem.v = C
    }
}  
