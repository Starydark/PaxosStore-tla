------------------------------ MODULE TPaxos --------------------------------
(*
Specification of the consensus protocol in PaxosStore.

See [PaxosStore@VLDB2017](https://www.vldb.org/pvldb/vol10/p1730-lin.pdf) 
by Tencent.

In this version (adopted from "PaxosStore.tla"):

- Client-restricted config (Ballot)
- Message types (i.e., "Prepare", "Accept", "ACK") are deleted.
No state flags (such as "Prepare", "Wait-Prepare", "Accept", "Wait-Accept"
are needed.
- Choose value from a quorum in Accept.
*)
EXTENDS Integers, FiniteSets
-----------------------------------------------------------------------------
Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
-----------------------------------------------------------------------------
CONSTANTS 
    Participant,  \* the set of partipants
    Value         \* the set of possible input values for Participant to propose
           
None == CHOOSE b : b \notin Value
NP == Cardinality(Participant) \* number of p \in Participants

Quorum == {Q \in SUBSET Participant : Cardinality(Q) * 2 >= NP + 1}
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Participant
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

PIndex == CHOOSE f \in [Participant -> 1 .. NP] : Injective(f)
Bals(p) == {b \in Ballot : b % NP = PIndex[p] - 1} \* allocate ballots for each p \in Participant
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
    msgs    \* the set of messages that have been sent

vars == <<state, msgs>>
          
TypeOK == 
    /\ state \in [Participant -> [Participant -> State]]
    /\ msgs \subseteq Message

Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
Init == 
    /\ state = [p \in Participant |-> [q \in Participant |-> InitState]] 
    /\ msgs = {}
(*
p \in Participant starts the prepare phase by issuing a ballot b \in Ballot.
*)
Prepare(p, b) == 
    /\ state[p][p].maxBal < b
    /\ b \in Bals(p)
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
    /\ Send([from |-> p, to |-> Participant, state |-> state'[p]])                 
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
    \E m \in msgs : 
        /\ q \in m.to
        /\ LET p == m.from
           IN  UpdateState(q, p, m.state[p])
        /\ IF \/ m.state[q].maxBal < state'[q][q].maxBal
              \/ m.state[q].maxVBal < state'[q][q].maxVBal
           THEN Send([from |-> q, to |-> {m.from}, state |-> state'[q]]) 
           ELSE UNCHANGED msgs
(*
p \in Participant starts the accept phase by issuing the ballot b \in Ballot
with value v \in Value.
*)
Accept(p, b, v) == 
    /\ b \in Bals(p)
    /\ state[p][p].maxBal = b \*corresponding the first conjunction in Voting
    /\ state[p][p].maxVBal < b \* correspongding the second conjunction in Voting
    /\ \E Q \in Quorum : \* pick the value from the quorum
       /\ \A q \in Q : state[p][q].maxBal = b
       /\ \/ \A q \in Q : state[p][q].maxVBal = -1 \* free to pick its own value
          \/ \E q \in Q : \* v is the value with the highest maxVBal in the quorum
                /\ state[p][q].maxVVal = v
                /\ \A r \in Q : state[p][q].maxVBal >= state[p][r].maxVBal
    \*choose the value from all the local state
    (*/\ \/ \A q \in Participant : state[p][q].maxVBal = -1 \* free to pick its own value
       \/ \E q \in Participant : \* v is the value with the highest maxVBal
            /\ state[p][q].maxVVal = v 
            /\ \A r \in Participant: state[p][q].maxVBal >= state[p][r].maxVBal
    *)
    /\ state' = [state EXCEPT ![p][p].maxVBal = b,
                              ![p][p].maxVVal = v]
    /\ Send([from |-> p, to |-> Participant, state |-> state'[p]])
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
\* Last modified Sun Sep 01 12:54:07 CST 2019 by pure_
\* Last modified Wed Jul 31 15:00:12 CST 2019 by hengxin
\* Last modified Mon Jun 03 21:26:09 CST 2019 by stary
\* Last modified Wed May 09 21:39:31 CST 2018 by dell
\* Created Mon Apr 23 15:47:52 GMT+08:00 2018 by pure_