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

option max_tracelength 20
test expect { 
    add: { 
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
    is sat
}

// option max_tracelength 10
// run {
//     DistributedSystemInit[DistributedSystem]
//     always {
//         plusOne[DistributedSystem]
//         or 
//         doNothing[DistributedSystem]
//     }
//     plusOne[DistributedSystem]
//     eventually {
//         DistributedSystem.n = 3
//     }
//     eventually {
//         DistributedSystem.n = 6
//     }
// }  
