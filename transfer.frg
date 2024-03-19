#lang forge/temporal 

abstract sig Value{}
one sig A, B, C extends Value {}

one sig DistributedSystem {
    v: one Value
}

pred DistributedSystemInit[d: DistributedSystem] {
    d.v = A
}

pred transfer[d: DistributedSystem] {
    d.v' in Value
}

pred doNothing[d: DistributedSystem] {
    d = d'
}

option max_tracelength 10
run {
    DistributedSystemInit[DistributedSystem]
    always {
        transfer[DistributedSystem]
        or 
        doNothing[DistributedSystem]
    }
    eventually { //will not be UNSAT if comment out `eventually`
        DistributedSystem.v = B
    }
}  
