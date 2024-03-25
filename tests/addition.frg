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
    d.n = d.n'
}

option max_tracelength 20
test expect { 
    // expected: the example should be SAT with the doNothing transition
    // result: SAT as expected
    addWithDoNothing: { 
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

    // expected: the example should be UNSAT without the doNothing transition
    // result: gives me counter example, with n increase from 0, 1, 2, ..., 7, -8, -7, ..., -1, and then loop back to 0
    addWithoutDoNothing: { 
        DistributedSystemInit[DistributedSystem]
        always {
            plusOne[DistributedSystem]
        }
        eventually { 
            DistributedSystem.n = 6
        }
    }
    is unsat
}

option max_tracelength 10


// expected: SAT with a trace 0, 1, 2, 3, 4, 5, 6
// result: SAT, but the model goes 0, 6
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


// expected: SAT with n increasing from 0 to 6
// result: SAT, but the model goes 0, 1, 6, 3
run {
    DistributedSystemInit[DistributedSystem]
    always {
        plusOne[DistributedSystem]
        or 
        doNothing[DistributedSystem]
    }
    plusOne[DistributedSystem]
    eventually {
        DistributedSystem.n = 3
    }
    eventually {
        DistributedSystem.n = 6
    }
}  
