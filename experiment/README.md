## Model Checking TPaxos with TLA+

An experiment of model checking the consensus algorithm TPaxos in paper [PaxosStore@VLDB2017](http://www.vldb.org/pvldb/vol10/p1730-lin.pdf). We introduce a variant of TPaxos, TPaxosAP, and check the consistency of TPaxos and TPaxosAP. Meanwhile we build the refinement relation from TPaxos to Voting, from TPaxos to EagerVoting(an algorithm equals to Voting) and check the correctness of the relation. The project includes three experiments:

- TPaxos and TPaxosAP satisfies Consistency.
- TPaxos refines Voting, TPaxosAP refines EagerVoting.
- EagerVoting refines Consensus.

### Requirements

- Linux with JDK 8.
- Some [tlaps](http://tla.msr-inria.inria.fr/tlaps/content/Home.html) modules. 

### TLC Parameters

- Participant: {p1, p2, p3} and {p1, p2, p3, p4, p5}
- Value: {v1, v2} and {v1, v2, v3, v4}
- Ballot(redefines Nat): 1..2 and1..3
- Quorum(subset of Participant): {{p1, p2}, {p1, p3}, {p2, p3}, {p1, p2, p3}} or {{p1, p2, p3}, {p1, p2, p4}, {p1, p2, p5}, {p1, p3, p4}, {p1, p3, p5}, {p1, p4, p5}, {p2, p3, p4}, {p2, p3, p5}, {p2, p4, p5}, {p3, p4, p5}, {p1, p2, p3, p4}, {p1, p2, p3, p5}, {p1, p2, p4, p5}, {p1, p3, p4, p5}, {p2, p3, p4, p5}, {p1, p2, p3, p4, p5}}

### TLC model checking setting

- Participant、Value: Symmetric Set
- worker = 10
- heap > 40g
- profile: off
- state constrain: exist model checking when distinct states get to 100000000.

### How to run

```
# Usage Note: "make" is identical to "make run".
$make
```

