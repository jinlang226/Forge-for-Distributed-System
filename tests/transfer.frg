#lang forge/temporal 

abstract sig Value{}
one sig A, B, C extends Value {}

one sig DistributedSystem {
    var v: one Value
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

option max_tracelength 20
test expect { 
    add: { 
        DistributedSystemInit[DistributedSystem]
        always {
            transfer[DistributedSystem]
            or 
            doNothing[DistributedSystem]
        }
        eventually { 
            DistributedSystem.v = B
        }
    }
    is sat
}

// option max_tracelength 10
// run {
//     DistributedSystemInit[DistributedSystem]
//     always {
//         transfer[DistributedSystem]
//         or 
//         doNothing[DistributedSystem]
//     }
//     eventually { 
//         DistributedSystem.v = B
//     }
// }  
