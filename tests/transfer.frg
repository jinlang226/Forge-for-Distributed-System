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
    // expected: the example should be SAT with the doNothing transition
    // the behavior: SAT as expected
    succWithDoNothing: { 
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

    // expected: the example should be UNSAT without the doNothing transition
    // the behavior: gives me counter example, with v changes from A to B, and stays at B forever
    succWithoutDoNothing: { 
        DistributedSystemInit[DistributedSystem]
        always {
            transfer[DistributedSystem]
        }
        eventually { 
            DistributedSystem.v = B
        }
    }
    is unsat 
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
