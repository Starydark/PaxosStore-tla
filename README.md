# Paxosstore-tla

A project of using <a href="http://lamport.azurewebsites.net/tla/tla.html">TLA<sup>+</sup></a> to model check and  prove the correctness of the consensus algorithm in the [PaxosStore@VLDB2017](http://www.vldb.org/pvldb/vol10/p1730-lin.pdf) paper and the open-source [Tencent/paxosstore](https://github.com/Tencent/paxosstore).

### Specification

While constructing specification of the consensus algorithm TPaxos in PaxosStore, we uncover a crucial but sutble detail in TPaxos which is not fully clarified, called TPaxosAP. We verify the correctness of both TPaxos and TPaxosAP, and  establish the refinement mappings from TPaxos to Voting and from TPaxosAP to EagerVoting(equivalent to Voting).

#### Module

- TPaxos.tla: the specification of the TPaxos.
- TPaxosAP.tla: the specification of the variant of TPaxos.
- TPaxosWithVotes.tla: the refinement mapping of TPaxos refining Voting.
- TPaxosAPWithVotes.tla: the refinement mapping of TPaxosAP refining EagerVoting.
- EagerVoting.tla: a specification that is equivalent to Voting.  
- Voting.tla: a specification introduced by Lamport in paper [Byzantizing Paxos by Refinement](http://lamport.azurewebsites.net/pubs/web-byzpaxos.pdf).
- Consensus.tla: a specification that implemented by Voting.

#### Refinement relation

![RefinementRelation](./specification/fig/RefinementRelation.png)

### [Theorem Proving](./theorem%20proving/)

We prove the correctness of TPaxos using <a href="http://tla.msr-inria.inria.fr/tlaps/content/Home.html">TLAPS</a>(a internal proof system of TLA+). While writing the proof of TPaxos, we make some small changes on the specification which won't introduce additional rules but only made our proof not too complicated.

### Experiment

We prove the refinement relation using the method of model checking. The details refers to [experiment](./experiment).


### Others
PS. [here](https://github.com/JYwellin/CRDT-TLA) is a similar work that provides a framework to specify and verify CRDT Protocols using TLA+.

