-------------------- MODULE OneVaulePerBallotPaxosStore --------------------
(*
Specification of the consensus protocol in PaxosStore.

See [PaxosStore@VLDB2017](https://www.vldb.org/pvldb/vol10/p1730-lin.pdf) 
by Tencent.

In this version (adapted from "UniversalPaxosStore.tla"):

- Adding
*)
EXTENDS Integers, FiniteSets
-----------------------------------------------------------------------------
Max(m, n) == IF m > n THEN m ELSE n
-----------------------------------------------------------------------------
CONSTANTS 
    Participant,  \* the set of partipants
    Value         \* the set of possible input values for Participant to propose
           
None == CHOOSE b : b \notin Value

Quorum == {Q \in SUBSET Participant : Cardinality(Q) * 2 = Cardinality(Participant) + 1}
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Participant
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
-----------------------------------------------------------------------------
State == [maxBal: Ballot \cup {-1},
         maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}]

InitState == [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None]
(*
For simplicity, in this specification, we choose to send the complete state
of a participant each time. When receiving such a message, the participant 
processes only the "partial" state it needs.
*)
Message == [from: Participant, to : SUBSET Participant, state: [Participant -> State]]
-----------------------------------------------------------------------------
VARIABLES 
    state,  \* state[p][q]: the state of q \in Participant from the view of p \in Participant
    bals,   \* the subset of Ballot consisting of b \in Ballot such that Accept(_, b, _)
    msgs    \* the set of messages that have been sent

vars == <<state, bals, msgs>>
          
TypeOK == 
    /\ state \in [Participant -> [Participant -> State]]
    /\ bals \subseteq Ballot
    /\ msgs \subseteq Message

Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
Init == 
    /\ state = [p \in Participant |-> [q \in Participant |-> InitState]] 
    /\ bals = {}
    /\ msgs = {}
(*
p \in Participant starts the prepare phase by issuing a ballot b \in Ballot.
*)
Prepare(p, b) == 
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
    /\ Send([from |-> p, to |-> Participant, state |-> state'[p]])                 
    /\ UNCHANGED bals
(*
q \in Participant updates its own state state[q] according to the actual state
pp of p \in Participant extracted from a message m \in Message it receives. 
This is called by OnMessage(q).

Note: pp is m.state[p]; it may not be equal to state[p][p] at the time 
UpdateState is called.
*)
UpdateState(q, p, pp) == 
    state' = [state EXCEPT 
                ![q][p].maxBal = Max(@, pp.maxBal),
                ![q][p].maxVBal = Max(@, pp.maxVBal),
                ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal 
                                  THEN pp.maxVVal ELSE @,
                ![q][q].maxBal = Max(@, pp.maxBal),
                ![q][q].maxVBal = IF state[q][q].maxBal <= pp.maxVBal 
                                  THEN pp.maxVBal ELSE @,  \* make promise
                ![q][q].maxVVal = IF state[q][q].maxBal <= pp.maxVBal
                                  THEN pp.maxVVal ELSE @]  \* accept
(*
q \in Participant receives and processes a message in Message.
*)
OnMessage(q) == 
    /\ \E m \in msgs : 
          /\ q \in m.to
          /\ LET p == m.from
             IN  UpdateState(q, p, m.state[p])
          /\ IF \/ m.state[q].maxBal < state'[q][q].maxBal
                \/ m.state[q].maxVBal < state'[q][q].maxVBal
             THEN Send([from |-> q, to |-> {m.from}, state |-> state'[q]]) 
             ELSE UNCHANGED msgs
    /\ UNCHANGED bals             
(*
p \in Participant starts the accept phase by issuing the ballot b \in Ballot
with value v \in Value.
*)
Accept(p, b, v) == 
    /\ b \notin bals
    /\ \E Q \in Quorum : \A q \in Q : state[p][q].maxBal = b
    /\ \/ \A q \in Participant : state[p][q].maxVBal = -1 \* free to pick its own value
       \/ \E q \in Participant : \* v is the value with the highest maxVBal
            /\ state[p][q].maxVVal = v 
            /\ \A r \in Participant: state[p][q].maxVBal >= state[p][r].maxVBal
    /\ state' = [state EXCEPT ![p][p].maxVBal = b,
                              ![p][p].maxVVal = v]
    /\ Send([from |-> p, to |-> Participant, state |-> state'[p]])
    /\ bals' = bals \cup {b}
---------------------------------------------------------------------------
Next == \E p \in Participant : \/ OnMessage(p)
                               \/ \E b \in Ballot : \/ Prepare(p, b)
                                                    \/ \E v \in Value : Accept(p, b, v)
Spec == Init /\ [][Next]_vars
---------------------------------------------------------------------------
ChosenP(p) == \* the set of values chosen by p \in Participant
    {v \in Value : \E b \in Ballot : 
                       \E Q \in Quorum: \A q \in Q: /\ state[p][q].maxVBal = b
                                                    /\ state[p][q].maxVVal = v}
chosen == UNION {ChosenP(p) : p \in Participant}

Consistency == Cardinality(chosen) <= 1         
THEOREM Spec => []Consistency
=============================================================================
\* Modification History
\* Last modified Mon Aug 05 15:11:26 CST 2019 by hengxin
\* Created Mon Aug 05 15:01:11 CST 2019 by hengxin
