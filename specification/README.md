## TLA+ Module

#### Module

- [TPaxos.tla](./TPaxos.tla): the specification of the TPaxos.
- [TPaxosAP.tla](./TPaxosAP.tla): the specification of the variant of TPaxos.
- [TPaxosWithVotes.tla](./TPaxosWithVotes.tla): the refinement mapping of TPaxos refining Voting.
- [TPaxosAPWithVotes.tla]((./TPaxosAPWithVotes.tla)): the refinement mapping of TPaxosAP refining EagerVoting.
- [EagerVoting.tla](./EagerVoting.tla): a specification that is equivalent to Voting.  
- [Voting.tla](./Voting.tla): a specification introduced by Lamport in paper [Byzantizing Paxos by Refinement](http://lamport.azurewebsites.net/pubs/web-byzpaxos.pdf).
- [Consensus.tla](./Consensus.tla): a specification that implemented by Voting.

#### Refinement relation

![RefinementRelation](./fig/RefinementRelation.png)