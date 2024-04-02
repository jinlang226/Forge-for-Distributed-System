When I run the code, forge gives me the error message: 

```
Forge version: 3.4
 branch: main
 commit: 2c44e46d
 timestamp: Mon Apr 1 09:17:16 2024 -0400
To report issues with Forge, please visit https://report.forge-fm.org
Unsat core available (8 formulas):
core path: (0 0 0 0)
core path: (0 0 0 1)

Core(part 1/8): [/Users/jinlang/Desktop/todo/forge-develop/Forge-for-Distributed-System/paxos/paxos.frg:214:8 (span 85)] (#Proposer = 1 && #Acceptor = 3 => #finalValue = 1 && #Proposer = 1 && #DistributedSystem.finalValue = 1 && (DistributedSystem.proposer.proposalValue = valInit => DistributedSystem.finalValue = valInit) && (DistributedSystem.finalValue = valInit => DistributedSystem.proposer.proposalValue = valInit))
list-ref: index too large for list
  index: 1
  in: '((=> (&& (&& (int= (card (Sig Proposer)) 1) (int= (card (Sig Acceptor)) 3) (int= (card (join (Sig DistributedSystem) (Relation acceptors))) 3) (int= (card (join (Sig DistributedSystem) (Relation proposer))) 1) (int= (card (join (Sig DistributedSystem) )
  context...:
   /Users/jinlang/Forge/forge/send-to-kodkod.rkt:391:4: pretty-core
   /Users/jinlang/Forge/forge/send-to-kodkod.rkt:348:2: get-next-model
   /Users/jinlang/Forge/forge/lazy-tree.rkt:29:0: get-value
   /opt/homebrew/Cellar/minimal-racket/8.11.1/share/racket/collects/racket/contract/private/arrow-higher-order.rkt:379:33
   /Users/jinlang/Desktop/todo/forge-develop/Forge-for-Distributed-System/paxos/paxos.frg:213:4
   body of (submod "/Users/jinlang/Desktop/todo/forge-develop/Forge-for-Distributed-System/paxos/paxos.frg" execs)

Finished running.
```

I suppose this is because the racket error `list-ref: index too large for list`

I looked at `send-to-kodkod.rkt`. I think this occurred in line 400:

```
[else
             (fprintf (current-error-port) "Core(part ~a/~a): [UNKNOWN] ~a~n" (@+ idx 1) max
                fmla-or-id)]))
```

However, I don’t know why since I don’t know much about racket.

I think Forge should be able to tell me whether it can verify the model by saying it is UNSAT or not; however, now Forge just outputs 1/8 core.



