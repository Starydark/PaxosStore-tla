-------------------- MODULE UniversalPaxosStoreWithVotes --------------------
(*
Extend UniversalPaxosStore with an explicit record of votes
that have been accepted by participants.
This is used to demonstrate that UniversalPaxosStore refines EagerVoting.
*)
EXTENDS UniversalPaxosStore, TLC
-----------------------------------------------------------------------------
VARIABLE votes

TypeOKV ==
    /\ TypeOK
    /\ votes \in [Participant -> SUBSET (Ballot \X Value)]
-----------------------------------------------------------------------------
InitV ==
    /\ Init
    /\ votes = [p \in Participant |-> {}]
    
PrepareV(p, b) ==
    /\ Prepare(p, b)
    /\ UNCHANGED votes

UpdateStateV(q, p, pp) ==
    /\ UpdateState(q, p, pp)
    /\ IF state[q][q].maxBal <= pp.maxVBal \* accept
       THEN /\ votes' = [votes EXCEPT ![q] = @ \cup {<<pp.maxVBal, pp.maxVVal>>}]
            /\ PrintT(state[q][q].maxBal)
            /\ PrintT(pp.maxVBal)
       ELSE UNCHANGED votes

OnMessageV(q) == 
    \E m \in msgs : 
        /\ q \in m.to
        /\ LET p == m.from
           IN  UpdateStateV(q, p, m.state[p]) \* replacing UpdateState
        /\ IF \/ m.state[q].maxBal < state'[q][q].maxBal
              \/ m.state[q].maxVBal < state'[q][q].maxVBal
           THEN Send([from |-> q, to |-> {m.from}, state |-> state'[q]]) 
           ELSE UNCHANGED msgs

AcceptV(p, b, v) ==
    /\ Accept(p, b, v)
    /\ votes' = [votes EXCEPT ![p] = @ \cup {<<b, v>>}] \* accept
-----------------------------------------------------------------------------
NextV == \E p \in Participant : \/ OnMessageV(p)
                                \/ \E b \in Ballot : \/ PrepareV(p, b)
                                                     \/ \E v \in Value : AcceptV(p, b, v)
SpecV == InitV /\ [][NextV]_<<vars, votes>>
-----------------------------------------------------------------------------
(*
UniversalPaxosStore refines EagerVoting.
*)
maxBal == [p \in Participant |-> state[p][p].maxBal]

EV == INSTANCE EagerVoting 
        WITH Acceptor <- Participant, 
                \* votes <- [p \in Participant |-> votes[p] \ {<<-1, None>>}],
               maxBal <- [p \in Participant |-> state[p][p].maxBal]
THEOREM SpecV => EV!Spec
=============================================================================
\* Modification History
\* Last modified Wed Aug 14 15:15:14 CST 2019 by hengxin
\* Created Wed Aug 14 14:05:06 CST 2019 by hengxin