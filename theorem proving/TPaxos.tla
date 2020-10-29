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
EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------
Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
-----------------------------------------------------------------------------
CONSTANTS 
    Participant,  \* the set of partipants
    Value         \* the set of possible input values for Participant to propose
           
None == CHOOSE b : b \notin Value

LEMMA NoneNotAValue == None \notin Value
BY NoSetContainsEverything DEF None

NP == Cardinality(Participant) \* number of p \in Participants

Quorum == {Q \in SUBSET Participant : Cardinality(Q) * 2 >= NP + 1}
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Participant
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
AllBallot == Ballot \cup {-1}
AllValue == Value \cup {None}
MaxBallot == Cardinality(Ballot) - 1

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
Message == [from: Participant,
            to : SUBSET Participant,
            state: [Participant -> [maxBal: Ballot \cup {-1},
                                    maxVBal: Ballot \cup {-1},
                                    maxVVal: Value \cup {None}]]]
-----------------------------------------------------------------------------
VARIABLES 
    state,  \* state[p][q]: the state of q \in Participant from the view of p \in Participant
    msgs    \* the set of messages that have been sent

vars == <<state, msgs>>
          
TypeOK == 
    /\ state \in [Participant -> [Participant -> State]]
\*    /\ \A p \in Participant: state[p] \in [Participant -> State]
\*    /\ \A p \in Participant, q \in Participant:
\*            /\ state[p][q].maxBal \in AllBallot
\*            /\ state[p][q].maxVBal \in AllBallot
\*            /\ state[p][q].maxVVal \in AllValue
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
    /\ b \in Bals(p)
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
    /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])                 
(*
q \in Participant updates its own state state[q] according to the actual state
pp of p \in Participant extracted from a message m \in Message it receives. 
This is called by OnMessage(q).
Note: pp is m.state[p]; it may not be equal to state[p][p] at the time 
UpdateState is called.
*)
UpdateState(q, p, pp) == 
    LET maxB == Max(state[q][q].maxBal, pp.maxBal)
        maxBV == IF (maxB <= pp.maxVBal)
                    THEN pp.maxVBal
                    ELSE state[q][q].maxVBal
        maxVV == IF (maxB <= pp.maxVBal)
                    THEN pp.maxVVal
                    ELSE state[q][q].maxVVal
       new_state_qq == [maxBal |-> maxB, 
                        maxVBal |-> maxBV, 
                        maxVVal |-> maxVV]
       new_state_qp == [maxBal |->  Max(state[q][p].maxBal, pp.maxBal),
                        maxVBal |-> Max(state[q][p].maxVBal, pp.maxVBal),
                        maxVVal |-> (IF (state[q][p].maxVBal =< pp.maxVBal)
                                        THEN pp.maxVVal
                                        ELSE state[q][p].maxVVal)]
    IN  state' = 
          [state EXCEPT
              ![q] = [ state[q] EXCEPT
                          ![q] = new_state_qq,
                          ![p] = new_state_qp
                      ] 
           ]
\*        [state EXCEPT 
\*            ![q] = [state[q] EXCEPT 
\*                       ![q] = [state[q][q] EXCEPT 
\*                                 !.maxBal = maxB, \* make promise first and then accept
\*                                 !.maxVBal = (IF (maxB <= pp.maxVBal)  \* accept
\*                                             THEN pp.maxVBal ELSE @), 
\*                                 !.maxVVal = (IF (maxB <= pp.maxVBal)  \* accept
\*                                             THEN pp.maxVVal ELSE @)
\*                                 !.maxVBal = IF 
\*                                                (
\*                                                state[q][q].maxBal <= pp.maxVBal 
\*                                                /\ pp.maxBal <= pp.maxVBal
\*                                                )
\*                                             THEN pp.maxVBal ELSE @,
\*                                 !.maxVVal = IF (
\*                                                state[q][q].maxBal <= pp.maxVBal 
\*                                                /\ pp.maxBal <= pp.maxVBal
\*                                                )
\*                                             THEN pp.maxVVal ELSE @
\*                               ],
\*                      ![p] = [state[q][p] EXCEPT 
\*                                !.maxBal = Max(@, pp.maxBal),
\*                                !.maxVBal = Max(@, pp.maxVBal),
\*                                !.maxVVal = (IF (state[q][p].maxVBal < pp.maxVBal)
\*                                            THEN pp.maxVVal ELSE @)
\*                              ]
\*                    ] 
\*         ]
\*    
    
\*                  ![q][p].maxBal = Max(@, pp.maxBal),
\*                  ![q][p].maxVBal = Max(@, pp.maxVBal),
\*                  ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal 
\*                                    THEN pp.maxVVal ELSE @,
\*                  ![q][q].maxBal = maxB, \* make promise first and then accept
\*                  ![q][q].maxVBal = IF maxB <= pp.maxVBal  \* accept
\*                                    THEN pp.maxVBal ELSE @, 
\*                  ![q][q].maxVVal = IF maxB <= pp.maxVBal  \* accept
\*                                    THEN pp.maxVVal ELSE @]  
(*
q \in Participant receives and processes a message in Message.
*)
OnMessage(q) == 
    \E m \in msgs : 
        /\ q \in m.to
        /\ LET p == m.from
           IN  UpdateState(q, p, m.state[p])
        /\ LET qm == [from |-> m.from, to |-> m.to \ {q}, state |-> m.state] \*remove q from to
               nm == [from |-> q, to |-> {m.from}, state |-> state'[q]] \*new message to reply
           IN  IF \/ m.state[q].maxBal < state'[q][q].maxBal
                  \/ m.state[q].maxVBal < state'[q][q].maxVBal
                 THEN msgs' = msgs \cup {nm}
                 ELSE UNCHANGED msgs
\*               THEN msgs' = (msgs \ {m}) \cup {qm, nm}
\*               ELSE msgs' = (msgs \ {m}) \cup {qm}
(*
p \in Participant starts the accept phase by issuing the ballot b \in Ballot
with value v \in Value.
*)
Accept(p, b, v) == 
    /\ b \in Bals(p)
    /\ ~ \E m \in msgs: m.state[m.from].maxBal = b /\ m.state[m.from].maxVBal = b
    /\ state[p][p].maxBal = b \*corresponding the first conjunction in Voting
    /\ state[p][p].maxVBal # b \* correspongding the second conjunction in Voting
    /\ \E Q \in Quorum : 
       /\ \A q \in Q : state[p][q].maxBal = b
       \* pick the value from the quorum
       /\ \/ \A q \in Q : state[p][q].maxVBal = -1 \* free to pick its own value
\*          \/ \E q \in Q : \* v is the value with the highest maxVBal in the quorum
\*                /\ state[p][q].maxVVal = v
          \/ \E c \in 0..(b-1):
              /\ \A r \in Q: state[p][r].maxVBal =< c
              /\ \E r \in Q: /\ state[p][r].maxVBal = c
                             /\ state[p][r].maxVVal = v
\*                /\ \A r \in Q : state[p][q].maxVBal >= state[p][r].maxVBal
    \*choose the value from all the local state
\*    /\ \/ \A q \in Participant : state[p][q].maxVBal = -1 \* free to pick its own value
\*       \/ \E q \in Participant : \* v is the value with the highest maxVBal
\*            /\ state[p][q].maxVVal = v 
\*            /\ \A r \in Participant: state[p][q].maxVBal >= state[p][r].maxVBal
\*    /\ state' = [state EXCEPT ![p][p].maxVBal = b,
\*                              ![p][p].maxVVal = v]
    /\ state' = [state EXCEPT ![p] = [state[p] EXCEPT 
                                        ![p] = [state[p][p] EXCEPT !.maxVBal = b,
                                                                   !.maxVVal = v]]]
    /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])
---------------------------------------------------------------------------
Next == \E p \in Participant : \/ OnMessage(p)
                               \/ \E b \in Ballot : \/ Prepare(p, b)
                                                    \/ \E v \in Value : Accept(p, b, v)
Spec == Init /\ [][Next]_vars
---------------------------------------------------------------------------
VotedForIn(a, b, v) == \E m \in msgs:
                            /\ m.from = a
                            /\ m.state[a].maxBal = b
                            /\ m.state[a].maxVBal = b
                            /\ m.state[a].maxVVal = v

ChosenIn(b, v) == \E Q \in Quorum:
                    \A a \in Q: VotedForIn(a, b, v)
                    
Chosen(v) == \E b \in Ballot: ChosenIn(b, v)

ChosenP(p) == \* the set of values chosen by p \in Participant
    {v \in Value : \E b \in Ballot : 
                       \E Q \in Quorum: \A q \in Q: /\ state[p][q].maxVBal = b
                                                    /\ state[p][q].maxVVal = v}

chosen == UNION {ChosenP(p) : p \in Participant}

Consistency == \*Cardinality(chosen) <= 1   
   \A v1, v2 \in Value: Chosen(v1) /\ Chosen(v2) => (v1 = v2)

---------------------------------------------------------------------------
WontVoteIn(a, b) == /\ \A v \in Value: ~ VotedForIn(a, b, v)
                    /\ state[a][a].maxBal > b

SafeAt(b, v) == 
        \A c \in 0..(b-1):
            \E Q \in Quorum:
                \A a \in Q: VotedForIn(a, c, v) \/ WontVoteIn(a, c)

---------------------------------------------------------------------------
MsgInv == 
    \A m \in msgs:
        LET p == m.from
            curState == m.state[p]
         IN /\ curState.maxBal >= curState.maxVBal
            /\ curState.maxBal # curState.maxVBal 
                => /\ curState.maxBal =< state[p][p].maxBal
                   /\ \A c \in (curState.maxVBal + 1)..(curState.maxBal - 1):
                        ~ \E v \in Value: VotedForIn(p, c, v)
            /\ curState.maxBal = curState.maxVBal \* exclude (-1,-1,None)
                => /\ SafeAt(curState.maxVBal, curState.maxVVal)
                   /\ \A ma \in msgs: (ma.state[ma.from].maxBal = curState.maxBal
                                       /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                    => ma.state[ma.from].maxVVal = curState.maxVVal
            /\\/ /\ curState.maxVVal \in Value
                 /\ curState.maxVBal \in Ballot
                 /\ VotedForIn(m.from, curState.maxVBal, curState.maxVVal)
              \/ /\ curState.maxVVal = None
                 /\ curState.maxVBal = -1
            /\ curState.maxBal \in Ballot
            /\ m.from \notin m.to
            /\ \A q \in Participant: /\ m.state[q].maxVBal <= state[q][q].maxVBal
                                     /\ m.state[q].maxBal <= state[q][q].maxBal
AccInv ==
    \A a \in Participant:
        /\ (state[a][a].maxVBal = -1) <=> (state[a][a].maxVVal = None)
        /\ \A q \in Participant: state[a][q].maxVBal <= state[a][q].maxBal
        /\ (state[a][a].maxVBal >= 0) => VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)
        /\ \A c \in Ballot: c > state[a][a].maxVBal 
            => ~ \E v \in Value: VotedForIn(a, c, v)
        /\ \A q \in Participant:
            /\ state[a][a].maxBal >= state[q][a].maxBal
            /\ state[a][a].maxVBal >= state[q][a].maxVBal
        /\ \A q \in Participant: 
                state[a][q].maxBal \in Ballot
                        => \E m \in msgs:
                              /\ m.from = q 
                              /\ m.state[q].maxBal = state[a][q].maxBal
                              /\ m.state[q].maxVBal = state[a][q].maxVBal
                              /\ m.state[q].maxVVal = state[a][q].maxVVal

Inv == MsgInv /\ AccInv /\ TypeOK
--------------------------------------------------------------------------
LEMMA VotedInv == 
        MsgInv /\ TypeOK =>
            \A a \in Participant, b \in Ballot, v \in Value:
                VotedForIn(a, b, v) => SafeAt(b, v)
BY DEFS MsgInv, VotedForIn, Message, TypeOK

LEMMA MaxBigger == \A a \in Ballot \cup {-1}, b \in Ballot: Max(a, b) >= a /\ Max(a, b) >= b
BY DEFS Ballot, Max

LEMMA MaxTypeOK == \A a \in AllBallot, b \in Ballot: Max(a, b) \in Ballot
BY DEFS AllBallot, Ballot, Max

LEMMA UpdateStateBiggerProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in 
                [maxBal: Ballot \cup {-1},
                maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}],
                UpdateState(q, p, pp), TypeOK
     PROVE  /\ state'[q][q].maxBal \in AllBallot
            /\ state'[q][q].maxBal >= state[q][q].maxBal
BY DEFS UpdateState, Max, TypeOK, AllBallot, Ballot, State

LEMMA UpdateStateTypeOKProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State,
                UpdateState(q, p, pp), TypeOK
     PROVE state' \in [Participant -> [Participant -> State]]
<1> USE DEFS AllBallot, Ballot, TypeOK, State, Message, AllValue
<1>1. /\ state'[q][q].maxBal \in AllBallot
      /\ state'[q][q].maxVBal \in AllBallot 
      /\ state'[q][q].maxVVal \in AllValue
      /\ state'[q][p].maxBal \in AllBallot
      /\ state'[q][p].maxVBal \in AllBallot
      /\ state'[q][p].maxVVal \in AllValue
  BY DEFS UpdateState, Max
<1>3. state'[q][q] \in State /\ state'[q][p] \in State
  BY <1>1 DEFS UpdateState
<1>4. state[q] \in [Participant -> State] /\ state[q][q] \in State /\ state[q][p] \in State
  OBVIOUS
<1>5. state'[q] \in [Participant -> State]
  BY <1>3, <1>4 DEFS UpdateState
<1> QED
  BY <1>5 DEFS UpdateState

LEMMA OnMessageBiggerProperty ==
     ASSUME NEW q \in Participant, OnMessage(q), TypeOK
     PROVE  state'[q][q].maxBal >= state[q][q].maxBal
<1>1 PICK m \in msgs: OnMessage(q)!(m)
  BY DEFS OnMessage
<1>2. UpdateState(q, m.from, m.state[m.from])
  BY <1>1 DEFS OnMessage
<1> QED
  BY <1>2, UpdateStateBiggerProperty DEFS OnMessage, TypeOK, Message

LEMMA MsgNotLost == Next /\ TypeOK => 
        \A m \in msgs, b1 \in Ballot, p1 \in Participant, v1 \in Value: 
                       /\ m.from = p1
                       /\ m.state[p1].maxBal = b1
                       /\ m.state[p1].maxVBal = b1
                       /\ m.state[p1].maxVVal = v1
                       => m \in msgs'
<1> USE DEFS TypeOK, Ballot, State, Send
<1>1. ASSUME NEW pp \in Participant, NEW bb \in Ballot,
             Prepare(pp, bb), TypeOK
      PROVE \A m \in msgs: m \in msgs'
  BY <1>1 DEFS Prepare
<1>2. ASSUME NEW pp \in Participant, NEW bb \in Ballot, NEW vv \in Value,
             Accept(pp, bb, vv)
      PROVE \A m \in msgs: m \in msgs'
  BY <1>2 DEFS Accept
<1>3. ASSUME NEW pp \in Participant, OnMessage(pp), NEW m \in msgs,
             NEW b1 \in Ballot, NEW p1 \in Participant, NEW v1 \in Value,
             m.from = p1, m.state[p1].maxBal = b1, m.state[p1].maxVBal = b1,
             m.state[p1].maxVVal = v1
      PROVE m \in msgs'
  <2> PICK mm \in msgs: OnMessage(pp)!(mm)
    BY <1>3 DEFS OnMessage
  <2>1 CASE \/ mm.state[pp].maxBal < state'[pp][pp].maxBal
            \/ mm.state[pp].maxVBal < state'[pp][pp].maxVBal
   BY <2>1 DEFS OnMessage
  <2>2 CASE ~ (\/ mm.state[pp].maxBal < state'[pp][pp].maxBal
            \/ mm.state[pp].maxVBal < state'[pp][pp].maxVBal)
    BY <2>2 DEFS OnMessage
  <2> QED
    BY <1>3, <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3 DEFS Next

LEMMA VotedOnce == 
        MsgInv => \A a1, a2 \in Participant, b \in Ballot, v1, v2 \in Value:
                VotedForIn(a1, b, v1) /\ VotedForIn(a2, b, v2) => (v1 = v2)
BY DEFS MsgInv, VotedForIn
--------------------------------------------------------------------------

LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' =>
                            \A v \in Value, b \in Ballot:
                               SafeAt(b, v) => SafeAt(b, v)'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                        NEW b \in Ballot, NEW v \in Value,
                        SafeAt(b, v)
                 PROVE  SafeAt(b, v)'
    OBVIOUS
<1> USE DEFS Send, Ballot, TypeOK, State, AllBallot, AllValue
<1>1. ASSUME NEW pp \in Participant, NEW bb \in Ballot, Prepare(pp, bb), TypeOK
      PROVE SafeAt(b, v)'
  <2> DEFINE mm == [from |-> pp, to |-> Participant \ {pp}, state |-> state'[pp]]
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
    BY <1>1 DEFS VotedForIn, Prepare
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    BY <1>1 DEFS Prepare, Inv
  <2>3. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        ~ VotedForIn(p1, b1, v1) => ~ VotedForIn(p1, b1, v1)'
    <3>a. /\ state[pp][pp].maxVBal \in AllBallot
          /\ state'[pp][pp].maxVBal \in AllBallot
          /\ state[pp][pp].maxBal \in AllBallot
          /\ state'[pp][pp].maxBal \in AllBallot
      BY DEFS Prepare, Inv
    <3>1. mm \in msgs'
      BY <1>1 DEF Prepare
    <3>2. /\ mm.state[pp].maxBal > state[pp][pp].maxBal
          /\ mm.state[pp].maxVBal = state[pp][pp].maxVBal
      BY <1>1 DEF Prepare
    <3>3. mm.state[pp].maxBal # mm.state[pp].maxVBal
      <4>1. state[pp][pp].maxBal >= state[pp][pp].maxVBal
        BY DEFS Inv, AccInv
      <4>2. mm.state[pp].maxBal > mm.state[pp].maxVBal
        BY <3>a, <3>2, <4>1 DEFS Inv, MsgInv
      <4> QED
        BY <4>2 
    <3> QED
      BY <1>1, <3>1, <3>3 DEFS Prepare, VotedForIn, Inv
  <2>4. \A p1 \in Participant, b1 \in Ballot:
        WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <2>2, <2>3 DEFS Prepare, WontVoteIn
  <2>5. QED    
   BY <1>1, <2>1, <2>4, QuorumAssumption DEFS Prepare, SafeAt
<1>2. ASSUME NEW pp \in Participant, NEW bb \in Ballot, NEW vv \in Value,
             Accept(pp, bb, vv)
      PROVE SafeAt(b, v)'
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
    BY <1>2 DEFS VotedForIn, Accept
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    BY <1>2 DEFS Accept
  <2>3. ASSUME NEW p1 \in Participant, NEW b1 \in Ballot, NEW v1 \in Value,
               WontVoteIn(p1, b1), VotedForIn(p1, b1, v1)'
        PROVE FALSE
    <3> PICK mm \in msgs':/\ mm.from = p1
                          /\ mm.state[p1].maxBal = b1
                          /\ mm.state[p1].maxVBal = b1
                          /\ mm.state[p1].maxVVal = v1
      BY <2>3 DEFS VotedForIn
    <3>1. mm \in msgs'
      BY <2>3 DEFS VotedForIn
    <3>2. mm \notin msgs
      BY <2>3 DEFS WontVoteIn, VotedForIn
    <3>3. p1 = pp 
      BY <1>2, <3>1, <3>2 DEFS Accept
    <3>4. mm = [from |-> pp, to |-> Participant \ {pp},
                   state |-> (state')[pp]]
          /\ state'[pp][pp].maxVBal = bb
      BY <1>2, <3>1, <3>2 DEFS Accept
    <3>5. b1 = bb
      BY <1>2, <3>1, <3>2, <3>4 DEFS Accept, Inv
    <3> QED
      BY <1>2, <2>3, <3>3, <3>5 DEFS Accept, WontVoteIn, VotedForIn, Inv
  <2>4. \A p1 \in Participant, b1 \in Ballot:
        WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <1>2, <2>2, <2>3 DEFS Accept, WontVoteIn
  <2> QED
    BY <1>2, <2>1, <2>4, QuorumAssumption DEF Accept, SafeAt
<1>3. ASSUME NEW pp \in Participant, OnMessage(pp), TypeOK'
      PROVE SafeAt(b, v)'
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
\*    BY <1>3 DEFS VotedForIn, OnMessage, UpdateState, Max
   <3>1. SUFFICES ASSUME NEW p1 \in Participant, NEW b1 \in Ballot, 
                       NEW v1 \in Value, VotedForIn(p1, b1, v1)
                PROVE VotedForIn(p1, b1, v1)'
       OBVIOUS
   <3>2. PICK m \in msgs:
               /\ m.from = p1
               /\ m.state[p1].maxBal = b1
               /\ m.state[p1].maxVBal = b1
               /\ m.state[p1].maxVVal = v1
     BY <3>1 DEFS VotedForIn
   <3>3. m \in msgs'
     BY <1>3, <3>1, <3>2, MsgNotLost DEFS Inv
   <3> QED
     BY <3>1, <3>2, <3>3 DEFS VotedForIn
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    <3>1. SUFFICES ASSUME NEW p1 \in Participant, NEW b1 \in AllBallot,
                    state[p1][p1].maxBal > b1
                 PROVE state'[p1][p1].maxBal > b1
        OBVIOUS
    <3>2. PICK mm \in msgs: OnMessage(pp)!(mm)
      BY <1>3 DEFS OnMessage
    <3>3. CASE p1 = pp
      <4>3. state[pp][pp].maxBal \in AllBallot
        BY DEFS Inv
      <4>1. state'[pp][pp].maxBal \in AllBallot
        BY <1>3
      <4>2. state'[pp][pp].maxBal >= state[pp][pp].maxBal
        BY <1>3, OnMessageBiggerProperty DEFS Inv
      <4> QED
        BY <3>1, <3>3, <4>1, <4>2, <4>3 DEFS Inv
    <3>4. CASE p1 # pp
      BY <1>3, <3>1, <3>2, <3>4 DEFS UpdateState, Max, OnMessage
    <3> QED
        BY <3>1, <3>2, <3>3, <3>4
  <2>3. ASSUME NEW p1 \in Participant, NEW b1 \in AllBallot, NEW v1 \in Value,
               WontVoteIn(p1, b1), VotedForIn(p1, b1, v1)'
        PROVE FALSE
    <3>1. PICK mm \in msgs':/\ mm.from = p1
                            /\ mm.state[p1].maxBal = b1
                            /\ mm.state[p1].maxVBal = b1
                            /\ mm.state[p1].maxVVal =v1
      BY <2>3 DEFS VotedForIn
    <3>2. mm \notin msgs
      BY <2>3, <3>1 DEFS WontVoteIn, VotedForIn, Inv
    <3>3. CASE p1 = pp
      <4>1. state'[pp][pp].maxBal = b1
        BY <1>3, <2>3, <3>1, <3>2, <3>3 DEFS OnMessage
      <4>2. state[pp][pp].maxBal > b1
        BY <2>3, <3>1, <3>2, <3>3 DEFS VotedForIn, WontVoteIn
      <4>3. state'[pp][pp].maxBal >= state[pp][pp].maxBal
        BY <1>3, OnMessageBiggerProperty DEFS Inv
      <4>5. state[pp][pp].maxBal \in AllBallot
        BY DEFS Inv
      <4>6. state'[pp][pp].maxBal \in AllBallot
        BY <1>3
      <4>4. state'[pp][pp].maxBal > b1
        BY <4>2, <4>3, <4>5, <4>6
      <4> QED
        BY <4>1, <4>4
    <3>4. CASE p1 # pp
      BY <1>3, <3>1, <3>2, <3>4 DEFS OnMessage
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4 DEFS OnMessage, WontVoteIn, VotedForIn, Inv
  <2>4. \A p1 \in Participant, b1 \in Ballot:
            WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <1>3, <2>2, <2>3 DEFS OnMessage, WontVoteIn
  <2> QED
    BY <1>3, <2>1, <2>4, QuorumAssumption DEFS OnMessage, SafeAt
<1> QED
  BY <1>1, <1>2, <1>3 DEF Next, Inv

LEMMA PrepareMsgInv == ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv, TypeOK'
                        PROVE MsgInv'
<1> USE DEF TypeOK, Ballot, AllBallot, Inv, MsgInv, State, Send, Message
<1> SUFFICES ASSUME NEW m \in msgs'
              PROVE MsgInv!(m)'
    OBVIOUS
<1> DEFINE mm == [from |-> p, to |-> Participant \ {p}, state |-> state'[p]]
<1>a. mm \in msgs' /\ mm.from = p
  BY DEFS Prepare
<1>aa. /\ state'[p][p].maxBal \in AllBallot
       /\ state[p][p].maxBal \in AllBallot
       /\ state[p][p].maxVBal \in AllBallot
  OBVIOUS
<1>b. /\ mm.state[p].maxBal # mm.state[p].maxVBal
      /\ mm.state[p].maxBal >= mm.state[p].maxVBal
  <2>1. state'[p][p].maxBal > state[p][p].maxBal
    BY DEFS Prepare
  <2>2. state[p][p].maxBal >= state[p][p].maxVBal
    BY DEFS AccInv
  <2>3. state'[p][p].maxVBal = state[p][p].maxVBal
    BY DEFS Prepare
  <2> QED
    BY <1>aa, <2>1, <2>2, <2>3
<1>c. m.from \notin m.to
  BY DEFS Prepare
<1>d. mm.state[p].maxBal >= mm.state[p].maxVBal
  BY <1>b
<1>1. CASE m = mm
  <2>1. m.state[m.from].maxBal # m.state[m.from].maxVBal
    BY <1>b, <1>1
  <2>2. m.state[m.from].maxBal =< state'[m.from][m.from].maxBal
    BY <1>a, <1>b, <1>1 DEFS Prepare
  <2>a. m.state[m.from].maxBal >= m.state[m.from].maxVBal
    BY <1>d, <1>1
  <2>3.  \/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Nat
            /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
    BY <1>1 DEFS Prepare, AccInv, VotedForIn
  <2>4. /\ \A c \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E v \in Value : VotedForIn(m.from, c, v))'
    <3>1. \A c \in (m.state[m.from].maxVBal+1)..(m.state[m.from].maxBal-1):
                ~(\E v \in Value : VotedForIn(m.from, c, v))
      <4> SUFFICES ASSUME NEW c \in (m.state[m.from].maxVBal+1)..(m.state[m.from].maxBal-1)
                    PROVE ~(\E v \in Value : VotedForIn(m.from, c, v))
        OBVIOUS
      <4>1a. state[p][p].maxVBal = (m.state)[m.from].maxVBal
        BY <1>a, <1>1 DEFS Prepare
      <4>1b. b = m.state[m.from].maxBal
        BY <1>a, <1>1 DEFS Prepare
      <4>1c. m.from = p
        BY <1>a, <1>1 DEFS Prepare
      <4>1d. c \in Ballot /\ c > state[p][p].maxVBal
        BY <4>1b, <4>1a, <4>1c
      <4>1. ~(\E v \in Value : VotedForIn(p, c, v))
        BY <4>1d DEFS AccInv
      <4> QED
        BY <4>1a, <4>1b, <4>1c, <4>1 DEFS AccInv, VotedForIn
    <3> QED
      BY <1>1, <3>1 DEFS Prepare, VotedForIn
  <2>5. m.state[m.from].maxBal \in Ballot
    BY <1>a, <1>b DEFS Prepare
  <2>6. \A q \in Participant: /\ m.state[q].maxVBal =< state'[q][q].maxVBal
                              /\ m.state[q].maxBal =< state'[q][q].maxBal
    BY <1>1, <2>a DEFS Prepare, AccInv
  <2> QED
    BY <1>c, <2>1, <2>a, <2>2, <2>3, <2>4, <2>5, <2>6 DEFS VotedForIn
<1>2. CASE m # mm
  <2>a. m \in msgs
    BY <1>2 DEFS Prepare
  <2>b. m.state[m.from].maxBal \in Ballot
    BY <2>a
  <2>c. m.state[m.from].maxBal >= m.state[m.from].maxVBal
    BY <2>a
  <2>d. \A q \in Participant: /\ m.state[q].maxVBal =< state'[q][q].maxVBal
                              /\ m.state[q].maxBal =< state'[q][q].maxBal
    <3> SUFFICES ASSUME NEW q \in Participant
                  PROVE /\ m.state[q].maxVBal =< state'[q][q].maxVBal
                        /\ m.state[q].maxBal =< state'[q][q].maxBal
      OBVIOUS
    <3>a. /\ m.state[q].maxBal \in AllBallot
          /\ state[q][q].maxBal \in AllBallot
          /\ state'[q][q].maxBal \in AllBallot
      BY DEFS MsgInv
    <3>1. state[q][q].maxBal =< state'[q][q].maxBal
      BY SMTT(100), IsaT(100) DEFS Prepare
    <3>2. m.state[q].maxBal =< state'[q][q].maxBal
      BY <2>a, <3>1, <3>a DEFS AccInv
    <3> QED
      BY <1>2, <2>a, <3>1, <3>2 DEFS Prepare, AccInv
  <2>1. CASE (m.state)[m.from].maxBal # (m.state)[m.from].maxVBal
      <3>1. m.state[m.from].maxBal =< state'[m.from][m.from].maxBal
        <4>a. m.state[m.from].maxBal =< state[m.from][m.from].maxBal
          BY <2>a, <2>1
        <4>1. CASE m.from = p
          <5>1. m.state[m.from].maxBal \in AllBallot /\ state[m.from][m.from].maxBal \in AllBallot
                /\ state'[m.from][m.from].maxBal \in AllBallot
            BY <2>1, <4>1
          <5> QED
            BY <4>a, <4>1,<5>1 DEFS Prepare
        <4>2. CASE m.from # p
          BY <4>a, <4>2 DEF Prepare
        <4> QED
          BY <4>1, <4>2
      <3>2.  \/ /\ (m.state)[m.from].maxVVal \in Value
                /\ (m.state)[m.from].maxVBal \in Nat
                /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
             \/ /\ (m.state)[m.from].maxVVal = None
                /\ (m.state)[m.from].maxVBal = -1
        BY <1>2, <2>1 DEFS Prepare, AccInv, VotedForIn
      <3>3. /\ \A c \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                    ~(\E v \in Value : VotedForIn(m.from, c, v))'
        <4>1. /\ \A c \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                    ~(\E v \in Value : VotedForIn(m.from, c, v))
          BY <1>2, <2>1 DEFS VotedForIn, Prepare
        <4> QED
          BY <1>b, <1>2, <2>1, <4>1, AllProvers DEF VotedForIn, Prepare
      <3> QED
        BY <1>c, <2>b, <2>c, <2>d, <2>1, <3>1, <3>2, <3>3
  <2>2. CASE (m.state)[m.from].maxBal = (m.state)[m.from].maxVBal
      <3>1.  \/ /\ (m.state)[m.from].maxVVal \in Value
                /\ (m.state)[m.from].maxVBal \in Nat
                /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
             \/ /\ (m.state)[m.from].maxVVal = None
                /\ (m.state)[m.from].maxVBal = -1
        BY <1>2, <2>2 DEFS Prepare, AccInv, VotedForIn
      <3>2. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)'
        <4>a. m.state[m.from].maxVBal \in Ballot /\ m.state[m.from].maxVVal \in Value
          BY <2>a, <2>b, <2>2, <3>1
        <4>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
          BY <2>a, <2>2
        <4> QED
          BY <4>a, <4>1, SafeAtStable DEFS Next
      <3>3. \A ma \in msgs': (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
        <4>1. \A ma \in msgs: (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
          BY <2>a, <2>2
        <4> QED
          BY <4>1, <1>b DEFS Prepare
      <3> QED
        BY <1>c, <2>b, <2>c, <2>d, <2>2, <3>1, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2

LEMMA UpdateStateViewValue == 
         ASSUME NEW q \in Participant, NEW p \in Participant, NEW m \in msgs, p = m.from, q \in m.to,
                    UpdateState(q, p, m.state[m.from]), Inv, TypeOK'
         PROVE /\ state'[q][p].maxBal >= state'[q][p].maxVBal
               /\ \/ /\ state'[q][p].maxBal = state[q][p].maxBal
                     /\ state'[q][p].maxVBal = state[q][p].maxVBal
                     /\ state'[q][p].maxVVal = state[q][p].maxVVal
                  \/ /\ state'[q][p].maxBal = m.state[m.from].maxBal
                     /\ state'[q][p].maxVBal = m.state[m.from].maxVBal
                     /\ state'[q][p].maxVVal = m.state[m.from].maxVVal
<1> USE DEFS AllBallot, Ballot
<1>a. /\ state[q][p].maxBal \in AllBallot
      /\ state[q][p].maxVBal \in AllBallot
      /\ m.state[m.from].maxVBal \in AllBallot
      /\ m.state[m.from].maxBal \in AllBallot
  BY DEFS Inv, TypeOK, State, MsgInv, Message
<1>b. /\ state'[q][p].maxBal = Max(state[q][p].maxBal, m.state[m.from].maxBal)
      /\ state'[q][p].maxVBal = Max(state[q][p].maxVBal, m.state[m.from].maxVBal)
      /\ state'[q][p].maxVVal = IF (state[q][p].maxVBal =< m.state[m.from].maxVBal)
                                        THEN m.state[m.from].maxVVal
                                        ELSE state[q][p].maxVVal
  BY DEFS UpdateState, State, Ballot, Inv, TypeOK
<1>c. /\ state[q][p].maxVBal =< state[q][p].maxBal
      /\ m.state[m.from].maxBal >= m.state[m.from].maxVBal
  BY DEFS Inv, AccInv, MsgInv
<1>d. /\ state[q][p].maxVBal =< state'[q][p].maxBal
      /\ m.state[m.from].maxVBal =< state'[q][p].maxBal
  BY <1>a, <1>b, <1>c DEFS Max
<1>e. p # q
  BY DEFS Inv, MsgInv
<1>1. state'[q][p].maxVBal =< state'[q][p].maxBal
  BY <1>a, <1>b, <1>d DEFS Max
<1>2. CASE state[q][p].maxBal = -1
  <2>1. state[q][p].maxVBal = -1
    BY <1>a, <1>2 DEFS Inv, AccInv
  <2>2. /\ state'[q][p].maxBal = m.state[m.from].maxBal
        /\ state'[q][p].maxVBal = m.state[m.from].maxVBal
        /\ state'[q][p].maxVVal = m.state[m.from].maxVVal
    BY <1>a, <1>b, <1>2, <2>1 DEFS Max
  <2> QED
    BY <1>1, <2>2
<1>3. CASE state[q][p].maxBal \in Ballot
  <2>a. PICK mm \in msgs:
          /\ mm.from = p 
          /\ mm.state[p].maxBal = state[q][p].maxBal
          /\ mm.state[p].maxVBal = state[q][p].maxVBal
          /\ mm.state[p].maxVVal = state[q][p].maxVVal
    BY <1>e, <1>3 DEFS Inv, AccInv
  <2>1. CASE state[q][p].maxBal < m.state[m.from].maxBal
    <3>1. state[q][p].maxVBal =< m.state[m.from].maxVBal
      <4> SUFFICES ASSUME state[q][p].maxVBal > m.state[m.from].maxVBal
                      PROVE FALSE
        BY <1>a, <2>1
      <4>1. /\ m.state[m.from].maxBal > m.state[m.from].maxVBal
            /\ state[q][p].maxVBal < m.state[m.from].maxBal
        BY <1>a, <2>1 DEFS Inv, AccInv
      <4>2. \A c \in (m.state[m.from].maxVBal+1)..(m.state[m.from].maxBal-1):
                ~ \E v \in Value: VotedForIn(m.from, c, v)
        BY <4>1 DEFS Inv, MsgInv
      <4>3. state[q][p].maxVBal \in Ballot /\ state[q][p].maxVVal \in Value
        BY <1>a, <2>a DEFS Inv, MsgInv
      <4>4. VotedForIn(p, state[q][p].maxVBal, state[q][p].maxVVal)
        BY <2>a, <4>3 DEFS Inv, MsgInv
      <4>5. state[q][p].maxVBal \in (m.state[m.from].maxVBal+1)..(m.state[m.from].maxBal-1)
        BY <1>a, <2>1, <4>1
      <4> QED
        BY <1>a, <2>a, <2>1, <4>2, <4>3, <4>4, <4>5 DEFS VotedForIn
    <3>2. /\ state'[q][p].maxBal = m.state[m.from].maxBal
          /\ state'[q][p].maxVBal = m.state[m.from].maxVBal
          /\ state'[q][p].maxVVal = m.state[m.from].maxVVal
      BY <1>a, <1>b, <2>1, <3>1 DEFS Max
    <3> QED
      BY <1>1, <3>2
  <2>2. CASE state[q][p].maxBal > m.state[m.from].maxBal
    <3>1. state[q][p].maxVBal >= m.state[m.from].maxVBal
      <4> SUFFICES ASSUME state[q][p].maxVBal < m.state[m.from].maxVBal
                    PROVE FALSE
        BY <1>a, <2>2
      <4>1. /\ state[q][p].maxBal > state[q][p].maxVBal
            /\ m.state[m.from].maxVBal < state[q][p].maxBal
        BY <1>a, <2>2 DEFS Inv, MsgInv
      <4>2. \A c \in (state[q][p].maxVBal+1)..(state[q][p].maxBal-1):
                ~ \E v \in Value: VotedForIn(p, c, v)
        BY <2>a, <4>1 DEFS Inv, MsgInv
      <4>3. m.state[m.from].maxVBal \in Ballot /\ m.state[m.from].maxVVal \in Value
        BY <1>a DEFS Inv, MsgInv
      <4>4. VotedForIn(p, m.state[m.from].maxVBal, m.state[m.from].maxVVal)
        BY <4>3 DEFS Inv, MsgInv
      <4>5. m.state[m.from].maxVBal \in (state[q][p].maxVBal+1)..(state[q][p].maxBal-1)
        BY <1>a, <2>2, <4>1
      <4> QED
        BY <4>2, <4>3, <4>4, <4>5
    <3>2. /\ state'[q][p].maxBal = state[q][p].maxBal
          /\ state'[q][p].maxVBal = state[q][p].maxVBal
          /\ state'[q][p].maxVVal = state[q][p].maxVVal
      <4>1. CASE state[q][p].maxVBal = m.state[m.from].maxVBal
        <5>1. CASE state[q][p].maxVBal = -1
          <6>1. /\ state[q][p].maxVVal = None
                /\ m.state[m.from].maxVVal = None
            BY <2>a, <4>1, <5>1 DEFS Inv, MsgInv
          <6> QED
            BY <1>b, <2>2, <4>1, <5>1, <6>1 DEFS Max
        <5>2. CASE state[q][p].maxVBal # -1
          <6>1. /\ VotedForIn(p, state[q][p].maxVBal, state[q][p].maxVVal)
                /\ VotedForIn(m.from, m.state[m.from].maxVBal, m.state[m.from].maxVVal)
            BY <2>a, <4>1, <5>2 DEFS Inv, MsgInv
          <6>2. state[q][p].maxVVal = m.state[m.from].maxVVal
            BY <4>1, <6>1 DEFS VotedForIn, MsgInv, Inv
          <6> QED
            BY <1>b, <2>2, <4>1, <5>2, <6>2 DEFS Max
        <5> QED
          BY <5>1, <5>2
      <4>2. CASE state[q][p].maxVBal > m.state[m.from].maxVBal
        BY <1>a, <1>b, <2>a, <2>2, <4>2 DEFS Max
      <4> QED
        BY <1>a, <3>1, <4>1, <4>2
    <3> QED
      BY <1>1, <3>2
  <2>3. CASE state[q][p].maxBal = m.state[m.from].maxBal
    BY <1>a, <1>b, <1>1, <2>3 DEFS Max
  <2> QED
    BY <1>a, <2>1, <2>2, <2>3
<1> QED
  BY <1>a, <1>2, <1>3

LEMMA UpdateStateValue == 
          ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State, pp.maxBal >= pp.maxVBal,
                     UpdateState(q, p, pp), Inv
            PROVE \/ /\ state'[q][q].maxVBal = state[q][q].maxVBal
                     /\ state'[q][q].maxVVal = state[q][q].maxVVal
                  \/ /\ state'[q][q].maxVBal = pp.maxVBal
                     /\ pp.maxVBal = pp.maxBal
                     /\ state'[q][q].maxVVal = pp.maxVVal
                     /\ state'[q][q].maxBal = pp.maxVBal
               /\ state'[q][q].maxBal >= state'[q][q].maxVBal 
               /\ state'[q][q].maxVBal >= state[q][q].maxVBal
<1> USE DEFS TypeOK, State, AllBallot, Ballot, Message, Inv
<1>a. state'[q][q].maxVBal = IF (Max(state[q][q].maxBal, pp.maxBal) <= pp.maxVBal)
                                THEN pp.maxVBal
                                ELSE state[q][q].maxVBal
  BY DEFS UpdateState
<1>b. state'[q][q].maxVVal = IF (Max(state[q][q].maxBal, pp.maxBal) <= pp.maxVBal)
                                THEN pp.maxVVal
                                ELSE state[q][q].maxVVal
  BY DEFS UpdateState
<1>c. state'[q][q].maxBal = Max(state[q][q].maxBal, pp.maxBal)
  BY DEFS UpdateState
<1>d. pp.maxVBal <= Max(state[q][q].maxBal, pp.maxBal)
  BY DEFS Max
<1>f. state[q][q].maxBal >= state[q][q].maxVBal
  BY DEFS AccInv
<1>e. state[q][q].maxVBal <= Max(state[q][q].maxBal, pp.maxBal)
  <2>1. state[q][q].maxBal <= Max(state[q][q].maxBal, pp.maxBal)
    BY DEFS Max
  <2>2. state[q][q].maxBal \in AllBallot /\ Max(state[q][q].maxBal, pp.maxBal) \in AllBallot
    BY DEFS Max
  <2> QED
    BY <1>f, <2>1, <2>2
<1>1. CASE (Max(state[q][q].maxBal, pp.maxBal) <= pp.maxVBal)
  <2>1. state'[q][q].maxVBal = pp.maxVBal
    BY <1>1 DEFS UpdateState
  <2>2. state'[q][q].maxVVal = pp.maxVVal
    BY <1>1 DEFS UpdateState
  <2>3. state'[q][q].maxVBal >= state[q][q].maxVBal
    <3>1. pp.maxVBal >= state[q][q].maxBal
      BY <1>1 DEFS Max
    <3>2. pp.maxVBal >= state[q][q].maxVBal
      BY <3>1, <1>f DEFS MsgInv
    <3> QED
      BY <2>1, <3>2
  <2> QED
    BY <1>1, <2>1, <2>2, <2>3, <1>c, <1>d, <1>e DEFS Max
<1>2. CASE ~(Max(state[q][q].maxBal, pp.maxBal) <= pp.maxVBal)
  <2>1. state'[q][q].maxVBal = state[q][q].maxVBal
    BY <1>2 DEFS UpdateState
  <2>2. state'[q][q].maxVVal = state[q][q].maxVVal
    BY <1>2 DEFS UpdateState
  <2>3. state'[q][q].maxVBal >= state[q][q].maxVBal
    BY <2>1 DEFS AccInv
  <2> QED
    BY <1>2, <2>1, <2>2, <2>3, <1>c, <1>e DEFS Max
<1> QED
  BY <1>1, <1>2

LEMMA AcceptMsgInv == ASSUME NEW p \in Participant, NEW b \in Ballot, NEW v \in Value, Accept(p, b, v), Inv, TypeOK'
                       PROVE MsgInv'
<1> USE DEF TypeOK, Ballot, AllBallot, Inv, MsgInv, State, Send, Message
<1> SUFFICES ASSUME NEW m \in msgs'
              PROVE MsgInv!(m)'
    OBVIOUS
<1> DEFINE mm == [from |-> p, to |-> Participant \ {p}, state |-> state'[p]]
<1>a. mm \in msgs' /\ mm.state[p].maxVBal \in Ballot /\ mm.state[p].maxVVal \in Value
  BY DEFS Accept
<1>b. mm.state[p].maxBal = mm.state[p].maxVBal /\ mm.state[p].maxBal = b
  BY <1>a DEFS Accept
<1>c. m.from \notin m.to
  BY DEFS Accept
<1>d. mm.state[p].maxBal >= mm.state[p].maxVBal
  BY SMT DEFS AccInv, Accept
<1>e. /\ state[p][p].maxVBal =< state'[p][p].maxVBal
      /\ state[p][p].maxBal =< state'[p][p].maxBal
  BY <1>a DEFS Accept, AccInv
<1>1. CASE mm = m
  <2>2. /\ m.state[m.from].maxBal = m.state[m.from].maxVBal
        /\ m.from = p
        /\ m.state[p].maxBal = b
    BY <1>1, <1>b DEFS Accept
  <2>1.  \/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Nat
            /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)' 
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
    BY <1>1, <2>2 DEFS Accept, VotedForIn 
  <2>a. m.state[m.from].maxBal >= m.state[m.from].maxVBal
    BY <1>d, <1>1
  <2>b. \A q \in Participant: /\ m.state[q].maxVBal =< state'[q][q].maxVBal
                              /\ m.state[q].maxBal =< state'[q][q].maxBal
    BY <1>1, <2>2 DEFS AccInv, Accept
  <2>3. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)'
    <3>a. m.state[m.from].maxVBal \in Ballot /\ m.state[m.from].maxVVal \in Value
      BY <1>a, <1>1 DEFS Accept
    <3>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
      <4>1. PICK Q \in Quorum:
                   /\ \A q \in Q : state[p][q].maxBal = b
                   /\ \/ \A q \in Q : state[p][q].maxVBal = -1
                      \/ \E c \in 0..(b-1):
                          /\ \A r \in Q: state[p][r].maxVBal =< c
                          /\ \E r \in Q: /\ state[p][r].maxVBal = c
                                         /\ state[p][r].maxVVal = v
        BY DEFS Accept
      <4>2. CASE \A q \in Q: state[p][q].maxVBal = -1
        <5>1. \A qq \in Q: 
                        \E qm \in msgs:
                                /\ qm.from = qq
                                /\ qm.state[qq].maxBal = state[p][qq].maxBal
                                /\ qm.state[qq].maxVBal = state[p][qq].maxVBal
                                /\ qm.state[qq].maxVVal = state[p][qq].maxVVal
          <6>1. \A qq \in Q: state[p][qq].maxBal \in Ballot
            BY <4>1
          <6> QED
            BY <4>1, <6>1, QuorumAssumption DEFS AccInv
        <5>2. \A c \in 0..(b-1): \A qq \in Q: WontVoteIn(qq, c)
          <6>1. \A qq \in Q: \A cc \in 0..(b-1): \A vv \in Value: ~ VotedForIn(qq, cc, vv)
            <7> SUFFICES ASSUME NEW qq \in Q
                          PROVE \A cc \in 0..(b-1):
                                    ~ \E vv \in Value: VotedForIn(qq, cc, vv)
              OBVIOUS
            <7>1a. PICK qm \in msgs:
                            /\ qm.from = qq
                            /\ qm.state[qq].maxBal = state[p][qq].maxBal
                            /\ qm.state[qq].maxVBal = state[p][qq].maxVBal
                            /\ qm.state[qq].maxVVal = state[p][qq].maxVVal
              BY <5>1
            <7>2. \A cc \in (qm.state[qq].maxVBal+1)..(qm.state[qq].maxBal-1):
                            ~ \E vv \in Value: VotedForIn(qq, cc, vv)
                <8>1. qm.state[qq].maxBal # qm.state[qq].maxVBal
                  BY <4>2, <4>1, <7>1a
                <8> QED
                  BY <7>1a, <8>1 DEFS MsgInv
            <7>3. state[p][qq].maxBal = b /\ state[p][qq].maxVBal = -1
              BY <4>1, <4>2
            <7> QED
              BY <7>1a, <7>2, <7>3
          <6>2. \A qq \in Q: \A cc \in 0..(b-1): state[qq][qq].maxBal > cc
            <7> SUFFICES ASSUME NEW qq \in Q, NEW cc \in 0..(b-1)
                          PROVE state[qq][qq].maxBal > cc
              OBVIOUS
            <7>1. state[qq][qq].maxBal >= b
              BY QuorumAssumption, <4>1 DEFS AccInv
            <7>2. cc \in AllBallot /\ cc < b /\ b \in AllBallot /\ state[qq][qq].maxBal \in AllBallot
              BY QuorumAssumption DEFS AllBallot
            <7> QED
              BY <7>1, QuorumAssumption, <7>2
          <6> QED
            BY <6>1, <6>2 DEFS WontVoteIn
        <5> QED
          BY <1>1, <2>2, <4>1, <5>2, QuorumAssumption DEFS SafeAt, Accept
      <4>3. CASE \E c \in 0..(b-1):
                      /\ \A r \in Q: state[p][r].maxVBal =< c
                      /\ \E r \in Q: /\ state[p][r].maxVBal = c
                                     /\ state[p][r].maxVVal = v
        <5>1a. m.state[m.from].maxVBal = b
          BY <2>2
        <5>1b. state'[p][p].maxVVal = v
          BY DEFS Accept
        <5>1c. m.state[m.from].maxVVal = v
          BY <1>a, <1>b, <1>1, <5>1b DEFS Accept
        <5>0. SUFFICES ASSUME NEW  cc \in 0..(b-1), \A qq \in Q: state[p][qq].maxVBal <= cc,
                            NEW qq \in Q, state[p][qq].maxVBal = cc, state[p][qq].maxVVal = v,
                            NEW d \in 0..(b-1)
                      PROVE \E QQ \in Quorum: \A a \in QQ: VotedForIn(a, d, v) \/ WontVoteIn(a, d) 
          BY <5>1a, <5>1c, <4>1, <4>3 DEFS SafeAt
        <5>1d. state[p][qq].maxBal = b
          BY <4>1
        <5>1e. VotedForIn(qq, cc, v)
          <6>1. PICK qqm \in msgs:   
                      /\ qqm.from = qq 
                      /\ qqm.state[qq].maxVBal = cc
                      /\ qqm.state[qq].maxVVal = v
            <7>1. state[p][qq].maxBal \in Ballot
              BY <4>1
            <7> QED
              BY <4>1, <7>1, <5>0, QuorumAssumption DEFS AccInv
          <6>2. /\ v \in Value
                /\ cc \in Ballot
            BY <6>1, QuorumAssumption
          <6> QED
            BY <6>1, <6>2, QuorumAssumption, IsaT(200)
        <5>1. CASE d \in 0..(cc-1)
          BY <5>1e, <5>1, VotedInv, QuorumAssumption DEFS SafeAt
        <5>2. CASE d = cc
          <6>1. \A qq1 \in Q, v1 \in Value: VotedForIn(qq1, cc, v1) => v1 = v
            BY <5>1e, VotedOnce, QuorumAssumption
          <6>2. \A qq1 \in Q: state[qq1][qq1].maxBal > cc
            <7> SUFFICES ASSUME NEW qq1 \in Q
                          PROVE state[qq1][qq1].maxBal > cc
                OBVIOUS
            <7>1. state[qq1][qq1].maxBal >= b
              BY QuorumAssumption, <4>1 DEFS AccInv
            <7>2. cc \in AllBallot /\ cc < b /\ b \in AllBallot /\ state[qq1][qq1].maxBal \in AllBallot
               BY QuorumAssumption DEFS AllBallot
            <7> QED
              BY <7>1, QuorumAssumption, <7>2
          <6> QED
            BY <5>2, <6>1, <6>2 DEFS WontVoteIn
        <5>3. CASE d \in (cc+1)..(b-1)
          <6>1. \A qq1 \in Q: \A v1 \in Value: ~ VotedForIn(qq1, d, v1)
            <7> SUFFICES ASSUME NEW qq1 \in Q, NEW v1 \in Value
                          PROVE ~ VotedForIn(qq1, d, v1)
              OBVIOUS
            <7>1. PICK qqm \in msgs:
                      /\ qqm.from = qq1
                      /\ qqm.state[qq1].maxBal = state[p][qq1].maxBal
                      /\ qqm.state[qq1].maxVBal = state[p][qq1].maxVBal
                      /\ qqm.state[qq1].maxVVal = state[p][qq1].maxVVal
              <8>1. state[p][qq1].maxBal \in Ballot
                BY <4>1
              <8> QED
                BY <4>1, <4>3, <8>1, QuorumAssumption DEFS AccInv
            <7>2. state[p][qq1].maxBal = b /\ state[p][qq1].maxVBal <= cc
              BY <4>1, <4>3, <5>0
            <7>4. qqm.state[qq1].maxBal # qqm.state[qq1].maxVBal
              BY <4>1, <4>3, <5>0, <7>1, <7>2
            <7>3. \A cc1 \in (qqm.state[qq1].maxVBal+1)..(qqm.state[qq1].maxBal-1): ~\E v2 \in Value: VotedForIn(qq1, cc1, v2)
              BY <7>1, <7>4, QuorumAssumption
            <7>5. d \in (qqm.state[qq1].maxVBal+1)..(qqm.state[qq1].maxBal-1)
              <8>1. cc \in AllBallot /\ state[p][qq1].maxVBal \in AllBallot
                BY QuorumAssumption
              <8> QED
                BY <5>3, <7>1, <7>2, <8>1
            <7> QED
              BY <5>3, <7>5, <7>3
          <6>2. \A qq1 \in Q: state[qq1][qq1].maxBal > d
            <7> SUFFICES ASSUME NEW qq1 \in Q
                          PROVE state[qq1][qq1].maxBal > d
                OBVIOUS
            <7>1. state[qq1][qq1].maxBal >= b
              BY QuorumAssumption, <4>1 DEFS AccInv
            <7>2. d \in AllBallot /\ d < b /\ b \in AllBallot /\ state[qq1][qq1].maxBal \in AllBallot
               BY QuorumAssumption DEFS AllBallot
            <7> QED
              BY <7>1, QuorumAssumption, <7>2
          <6> QED
            BY <5>3, <6>1, <6>2 DEFS WontVoteIn
        <5> QED
          BY <5>1a, <5>1c, <5>1, <5>2, <5>3
      <4> QED
        BY <4>1, <4>2, <4>3 DEFS Accept
    <3> QED
      BY <3>a, <3>1, SafeAtStable DEFS Next
  <2>4. \A ma \in msgs': (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
    BY <1>1, <1>a, <1>b, <2>2 DEFS Accept
  <2>5. m.state[m.from].maxBal \in Ballot
    BY <1>1, <1>a, <1>b DEF Accept
  <2> QED
    BY <1>d, <1>1, <2>1, <2>a, <2>b, <2>2, <2>3, <2>4, <2>5
<1>2. CASE mm # m
  <2>a. m \in msgs
    BY <1>2 DEFS Accept
  <2>b. \A q \in Participant: /\ m.state[q].maxVBal =< state'[q][q].maxVBal
                              /\ m.state[q].maxBal =< state'[q][q].maxBal
    <3> SUFFICES ASSUME NEW q \in Participant
                  PROVE /\ m.state[q].maxVBal =< state'[q][q].maxVBal
                        /\ m.state[q].maxBal =< state'[q][q].maxBal
      OBVIOUS
    <3>1. /\ m.state[q].maxVBal =< state[q][q].maxVBal
          /\ m.state[q].maxBal =< state[q][q].maxBal
      BY <2>a
    <3>2. /\ state[q][q].maxVBal =< state'[q][q].maxVBal
          /\ state[q][q].maxBal =< state'[q][q].maxBal
      BY <1>e DEFS Accept, AccInv
    <3>3. /\ state[q][q].maxVBal \in AllBallot /\ m.state[q].maxVBal \in AllBallot
          /\ state[q][q]'.maxVBal \in AllBallot
          /\ state[q][q].maxBal \in AllBallot /\ m.state[q].maxBal \in AllBallot
          /\ state[q][q]'.maxBal \in AllBallot
      OBVIOUS
    <3> QED
      BY <2>a, <3>1, <3>2, <3>3
  <2>c. m.state[m.from].maxBal >= m.state[m.from].maxVBal
    BY <2>a
  <2>1. m.state[m.from].maxBal \in Ballot
    BY <2>a
  <2>2.  \/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Nat
            /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
    BY <1>2, <2>1 DEFS Accept, VotedForIn
  <2>3. CASE (m.state)[m.from].maxBal # (m.state)[m.from].maxVBal
    <3>1. (m.state)[m.from].maxBal <= state'[m.from][m.from].maxBal
      <4>1 (m.state)[m.from].maxBal <= state[m.from][m.from].maxBal
        BY <1>2, <2>a, <2>3
      <4> QED
        BY <4>1 DEFS Accept
    <3>2. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))'
      <4>1. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))
        BY <1>2, <2>a, <2>3 DEFS VotedForIn, Accept
      <4>2. CASE m.from = p
        <5>. SUFFICES ASSUME NEW cc \in (m.state[m.from].maxVBal) + 1..(m.state[m.from].maxBal - 1),
                            NEW vv \in Value, VotedForIn(p, cc, vv)'
                      PROVE FALSE
          BY <4>1, <4>2
        <5>a. PICK pm \in msgs': 
                    /\ pm.from = p
                    /\ pm.state[p].maxBal = cc
                    /\ pm.state[p].maxVBal = cc
                    /\ pm.state[p].maxVVal = vv
          BY DEFS VotedForIn
        <5>b. pm \notin msgs
          BY <4>1, <4>2, <5>a DEFS VotedForIn
        <5>1. b = cc
          <6>1. pm = mm
            BY <1>a, <1>b, <5>a, <5>b DEFS Accept, VotedForIn
          <6> QED
            BY <5>a, <6>1 DEFS Accept
        <5>2. m.state[m.from].maxBal > b
          <6>1. m.state[m.from].maxBal - 1 >= cc /\ (m.state)[m.from].maxVBal \in AllBallot
            OBVIOUS
          <6>2. cc \in AllBallot /\ m.state[m.from].maxBal \in AllBallot
            BY <2>1, <6>1
          <6> QED
            BY <5>1, <6>1, <6>2
        <5>3. m.state[m.from].maxBal <= b
          BY <3>1, <4>2 DEFS Accept
        <5> QED
          BY <1>2, <2>3, <4>2, <5>2, <5>3 DEFS VotedForIn, Accept
      <4>3. CASE m.from # p
        BY <4>1, <4>3 DEFS Accept, VotedForIn
      <4> QED
        BY <4>2, <4>3
    <3> QED
      BY <1>c, <2>1, <2>b, <2>c, <2>2, <2>3, <3>1, <3>2
  <2>4. CASE (m.state)[m.from].maxBal = (m.state)[m.from].maxVBal
    <3>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)'
      <4>a. m.state[m.from].maxVBal \in Ballot /\ m.state[m.from].maxVVal \in Value
        BY <2>1, <2>2, <2>4
      <4>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
        BY <2>a, <2>4
      <4>2. QED
        BY <4>a, <4>1, SafeAtStable DEFS Next
    <3>2. \A ma \in msgs': (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
      <4>1. \A ma \in msgs: (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
        BY <2>a, <2>4
      <4>2. m.state[m.from].maxBal # mm.state[mm.from].maxBal
        BY <1>a, <1>b, <2>a, <2>4 DEFS Accept
      <4> QED
        BY <1>a, <1>b, <1>2, <4>1, <4>2 DEFS Accept 
    <3> QED
      BY <1>c, <2>1, <2>b, <2>c, <2>2, <2>4, <3>1, <3>2 
  <2> QED
    BY <1>c, <2>1, <2>c, <2>2, <2>3, <2>4
<1> QED
  BY <1>1, <1>2

LEMMA UpdateStateMsgInv ==
    ASSUME NEW q \in Participant, NEW p \in Participant, NEW mm \in msgs, mm.from = p, Inv, q \in mm.to, Next,
           UpdateState(q, p, mm.state[p]), TypeOK', Send([from |-> q, to |-> {mm.from}, state |-> state'[q]])
     PROVE MsgInv'
<1> USE DEFS TypeOK, Ballot, AllBallot, MsgInv, State, Send, Message
<1> DEFINE nm == [from |-> q, to |-> {mm.from}, state |-> state'[q]]
<1>a. nm \in msgs'
  OBVIOUS
<1>aa. state'[q][q].maxBal = Max(state[q][q].maxBal, mm.state[p].maxBal)
  BY DEFS UpdateState
<1>aaa. state'[q][q].maxBal >= state[q][q].maxBal
  <2>1. mm.state[p].maxBal \in Ballot /\ state[q][q].maxBal \in AllBallot
    BY DEFS Inv
  <2> QED
    BY <1>aa, <2>1 DEFS Max
<1>. SUFFICES ASSUME NEW m \in msgs'
              PROVE MsgInv!(m)'
  OBVIOUS
<1>bb./\ \/ /\ state'[q][q].maxVBal = state[q][q].maxVBal
            /\ state'[q][q].maxVVal = state[q][q].maxVVal
         \/ /\ state'[q][q].maxVBal = mm.state[p].maxVBal
            /\ mm.state[p].maxVBal = mm.state[p].maxBal
            /\ state'[q][q].maxVVal = mm.state[p].maxVVal
            /\ state'[q][q].maxBal = mm.state[p].maxVBal
       /\ state'[q][q].maxBal >= state'[q][q].maxVBal 
       /\ state'[q][q].maxVBal >= state[q][q].maxVBal  
  <2>1. mm.state[p] \in State
    OBVIOUS
  <2>2. mm.state[p].maxBal >= mm.state[p].maxVBal
    BY DEFS Inv
  <2> QED
    BY <2>1, <2>2, UpdateStateValue DEFS Next
<1>b./\\/ /\ nm.state[q].maxVBal = state[q][q].maxVBal
          /\ nm.state[q].maxVVal = state[q][q].maxVVal
          /\ nm.state[q].maxBal = Max(state[q][q].maxBal, mm.state[p].maxBal)
       \/ /\ nm.state[q].maxBal = mm.state[p].maxVBal
          /\ mm.state[p].maxVBal = mm.state[p].maxBal
          /\ nm.state[q].maxVBal = mm.state[p].maxVBal
          /\ nm.state[q].maxVVal = mm.state[p].maxVVal
          /\ nm.state[q].maxBal = Max(state[q][q].maxBal, mm.state[p].maxBal)
     /\ nm.state[q].maxVBal >= state[q][q].maxVBal
  <2>3. nm.state[q].maxVBal >= state[q][q].maxVBal
    BY <1>bb
  <2> QED
    BY <1>bb, <1>aa, <2>3, <1>a
<1>c. nm.state[q].maxBal >= nm.state[q].maxVBal
  BY <1>bb
<1>d. m.from \notin m.to
  BY DEFS Inv
<1>e. nm.state[nm.from].maxBal = state'[q][q].maxBal
  BY DEFS Inv
<1>1. CASE nm = m
  <2>a. m.state[m.from].maxBal \in Ballot
    <3>1. mm.state[p].maxBal \in Ballot /\ state[q][q].maxBal \in AllBallot
      BY DEFS Inv
    <3> QED
      BY<1>1, <1>b, <3>1 DEFS Max
  <2>b. m.state[m.from].maxBal >= m.state[m.from].maxVBal
    BY <1>c, <1>1
  <2>c.  \/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Ballot
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
    BY <1>b, <1>1, <2>a DEFS Inv, AccInv
  <2>d. m.state[m.from].maxBal = state'[m.from][m.from].maxBal
    BY <1>1
  <2>e. \A a \in Participant: /\ m.state[a].maxVBal =< state'[a][a].maxVBal
                              /\ m.state[a].maxBal =< state'[a][a].maxBal
    <3> SUFFICES ASSUME NEW a \in Participant
                  PROVE /\ m.state[a].maxVBal =< state'[a][a].maxVBal
                        /\ m.state[a].maxBal =< state'[a][a].maxBal
      OBVIOUS
    <3>1. /\ state'[q][p].maxVBal = Max(state[q][p].maxVBal, mm.state[mm.from].maxVBal)
          /\ state'[q][p].maxBal = Max(state[q][p].maxBal, mm.state[mm.from].maxBal)
      BY DEFS UpdateState
    <3>2. /\ state[q][p].maxVBal =< state[p][p].maxVBal /\ mm.state[mm.from].maxVBal =< state[p][p].maxVBal
          /\ state[q][p].maxBal =< state[p][p].maxBal /\ mm.state[mm.from].maxBal =< state[p][p].maxBal
      BY DEFS MsgInv, AccInv, Inv
    <3>3. /\ state'[q][p].maxVBal =< state[p][p].maxVBal
          /\ state'[q][p].maxBal =< state[p][p].maxBal
      BY <3>1, <3>2 DEFS Max
    <3>4. /\ state'[p][p].maxVBal = state[p][p].maxVBal
          /\ state'[p][p].maxBal = state[p][p].maxBal
      <4>1. p # q
        BY DEFS Inv
      <4> QED
        BY <4>1 DEFS UpdateState
    <3>5. CASE a = p
      BY <1>1, <3>3, <3>4, <3>5
    <3>6. CASE a = q
      <4>1. /\ m.state[a].maxVBal = state'[q][q].maxVBal
            /\ m.state[a].maxBal = state'[q][q].maxBal
        BY <1>1, <3>6
      <4>2. /\ m.state[a].maxVBal \in AllBallot /\ state'[q][q].maxVBal \in AllBallot
            /\ m.state[a].maxBal \in AllBallot /\ state'[q][q].maxBal \in AllBallot
        BY DEFS Inv
      <4> QED
        BY <3>6, <4>1, <4>2
    <3>7. CASE a # p /\ a # q
      <4>1. /\ state'[a][a].maxVBal = state[a][a].maxVBal
            /\ state'[a][a].maxBal = state[a][a].maxBal
        BY <3>7 DEFS UpdateState
      <4>2. /\ state[q][a].maxVBal =< state[a][a].maxVBal
            /\ state[q][a].maxBal =< state[a][a].maxBal 
        BY DEFS Inv, AccInv
      <4>3. /\ state'[q][a].maxVBal =< state[a][a].maxVBal
            /\ state'[q][a].maxBal =< state[a][a].maxBal
        BY <3>7, <4>2 DEFS UpdateState 
      <4> QED
        BY <1>1, <3>7, <4>1, <4>3
    <3> QED
      BY <1>1, <3>5, <3>6, <3>7
  <2>1. CASE m.state[q].maxBal = m.state[q].maxVBal
    <3>a. /\ (m.state)[m.from].maxVVal \in Value
          /\ (m.state)[m.from].maxVBal \in Ballot
        BY <1>1, <2>c, <2>1, <2>a
    <3>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)'
      <4>1. CASE (/\ m.state[m.from].maxVBal = state[q][q].maxVBal
                  /\ m.state[m.from].maxVVal = state[q][q].maxVVal)
        <5>a. state[q][q].maxVBal \in Ballot /\ state[q][q].maxVVal \in Value
          BY <3>a, <4>1
        <5>b. VotedForIn(q, state[q][q].maxVBal, state[q][q].maxVVal)
          BY <5>a DEFS Inv, AccInv
        <5>1. SafeAt(state[q][q].maxVBal, state[q][q].maxVVal)
          BY <5>a, <5>b, VotedInv DEFS Inv
        <5>2. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
          BY <5>1, <4>1
        <5> QED
          BY <3>a, <5>2, SafeAtStable
      <4>2. CASE (/\ m.state[m.from].maxBal = mm.state[p].maxVBal
                  /\ m.state[m.from].maxVBal = mm.state[p].maxVBal
                  /\ m.state[m.from].maxVVal = mm.state[p].maxVVal)
        <5>a. mm.state[p].maxBal = mm.state[p].maxVBal
          BY <1>1, <1>b, <2>1, <4>2 DEFS Max, Inv
        <5>1. SafeAt(mm.state[p].maxVBal, mm.state[p].maxVVal)
          BY <5>a DEFS Inv
        <5>2. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
          BY <5>1, <4>2
        <5> QED
          BY <3>a, <5>2, SafeAtStable
      <4> QED
        BY <1>1, <1>b, <4>1, <4>2
    <3>2. \A ma \in msgs': (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
     <4>1. \A ma \in msgs: (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
       <5>1.CASE (/\ m.state[m.from].maxBal = mm.state[p].maxVBal
                  /\ m.state[m.from].maxVBal = mm.state[p].maxVBal
                  /\ m.state[m.from].maxVVal = mm.state[p].maxVVal)
         <6>a. mm.state[p].maxBal = mm.state[p].maxVBal
           BY <1>1, <1>b, <2>1, <5>1 DEFS Max, Inv
         <6>1. \A ma \in msgs: (ma.state[ma.from].maxBal = mm.state[p].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = mm.state[p].maxVVal
           BY <6>a DEFS Inv
         <6> QED
           BY <1>1, <2>1, <5>1, <6>1, <6>a
       <5>2. CASE (/\ m.state[m.from].maxVBal = state[q][q].maxVBal
                   /\ m.state[m.from].maxVVal = state[q][q].maxVVal)
        <6>a. VotedForIn(q, state[q][q].maxVBal, state[q][q].maxVVal)
          BY <3>a, <5>2 DEFS AccInv, Inv
        <6>b. PICK qqm \in msgs: 
                /\ qqm.from = q
                /\ qqm.state[q].maxBal = state[q][q].maxVBal
                /\ qqm.state[q].maxVBal = state[q][q].maxVBal
                /\ qqm.state[q].maxVVal = state[q][q].maxVVal
          BY <6>a DEFS VotedForIn
        <6>c. qqm.state[q].maxBal = m.state[m.from].maxBal /\ qqm.state[q].maxBal = m.state[m.from].maxVBal
          BY <1>1, <2>1, <5>2, <6>b
        <6>1. \A ma \in msgs: (ma.state[ma.from].maxBal = qqm.state[q].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = qqm.state[q].maxVVal
          BY <6>b DEFS Inv
        <6> QED
          BY <1>1, <2>1, <5>2, <6>b, <6>c, <6>1
       <5> QED
         BY <1>1, <1>b, <5>1, <5>2
     <4> QED
       BY <4>1, <1>1
    <3>3. VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
      <4>a. /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Ballot
        BY <1>1, <2>c, <2>1, <2>a
      <4> QED
        BY <1>1, <2>1, <4>a DEFS VotedForIn
    <3> QED
      BY <1>1, <1>d, <2>a, <2>b, <2>c, <2>e, <2>1, <3>1, <3>2, <3>3
  <2>2. CASE m.state[q].maxBal # m.state[q].maxVBal
    <3>2. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))'
      <4>1. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))
        <5> SUFFICES ASSUME NEW cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1
                      PROVE ~(\E vv \in Value : VotedForIn(m.from, cc, vv))
          OBVIOUS
        <5>a. cc > (m.state)[q].maxVBal
          <6>1. cc >= (m.state)[m.from].maxVBal + 1
            OBVIOUS
          <6>2. (m.state)[m.from].maxVBal \in AllBallot
            BY <1>1, <1>b
          <6> QED
            BY <1>1, <6>1, <6>2
        <5>b. cc \in Ballot
          <6>1. (m.state)[m.from].maxVBal \in AllBallot
            BY <1>1, <1>b
          <6>2. (m.state)[m.from].maxVBal+1 \in Ballot
            BY <6>1
          <6> QED
            BY <6>2
        <5>1. \A c \in Ballot: c > state[q][q].maxVBal => 
                    ~ \E v \in Value: VotedForIn(q, c, v)
          BY DEFS AccInv, Inv
        <5>2. (m.state)[m.from].maxVBal >= state[q][q].maxVBal
          BY <1>1, <1>b
        <5>3. cc > state[q][q].maxVBal
            BY <1>1, <1>b, <5>2, <5>a DEFS Inv
        <5>4. ~ \E vv \in Value: VotedForIn(q, cc, vv)
          BY <5>1, <5>3, <5>b
        <5> QED
          BY <1>1, <5>4 DEF Inv
      <4> QED
        BY <1>1, <2>2, <4>1 DEFS VotedForIn
    <3>3.\/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Nat
            /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)' 
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
      <4>1. /\ m.state[m.from].maxVBal = state[q][q].maxVBal
            /\ m.state[m.from].maxVVal = state[q][q].maxVVal
        BY <1>b, <1>1, <2>2
      <4> QED
        BY <1>b, <1>1, <2>a, <4>1 DEFS  AccInv, VotedForIn, Inv
    <3> QED
      BY <1>1, <1>d, <2>a, <2>b, <2>c, <2>e, <2>2, <2>d, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1>2. CASE nm # m
  <2>a. m \in msgs
    BY <1>2
  <2>b. m.from \notin m.to
    BY <2>a DEFS Inv
  <2>c. m.state[m.from].maxBal >= m.state[m.from].maxVBal
    BY <2>a DEFS Inv
  <2>d. \A a \in Participant: /\ m.state[a].maxVBal =< state'[a][a].maxVBal
                              /\ m.state[a].maxBal =< state'[a][a].maxBal
    <3> SUFFICES ASSUME NEW a \in Participant
                  PROVE /\ m.state[a].maxVBal =< state'[a][a].maxVBal
                        /\ m.state[a].maxBal =< state'[a][a].maxBal
        OBVIOUS
    <3>1. /\ m.state[a].maxVBal =< state[a][a].maxVBal
          /\ m.state[a].maxBal =< state[a][a].maxBal 
      BY <2>a DEFS Inv, AccInv
    <3>2. /\ state[a][a].maxVBal =< state'[a][a].maxVBal
          /\ state[a][a].maxBal =< state'[a][a].maxBal
      <4>1. CASE a = q
        BY <1>bb, <1>aaa, <4>1
      <4>2. CASE a # q
        <5>1. /\ state[a][a].maxVBal = state'[a][a].maxVBal
              /\ state[a][a].maxBal = state'[a][a].maxBal
          BY <4>2 DEFS UpdateState
        <5>2. /\ state[a][a].maxVBal \in AllBallot /\ state'[a][a].maxVBal \in AllBallot
              /\ state[a][a].maxBal \in AllBallot /\ state'[a][a].maxBal \in AllBallot
          BY DEFS Inv
        <5> QED
          BY <5>1, <5>2
      <4> QED
        BY <4>1, <4>2
    <3>3. /\ state[a][a].maxVBal \in AllBallot 
          /\ m.state[a].maxVBal \in AllBallot
          /\ state'[a][a].maxVBal \in AllBallot
          /\ state[a][a].maxBal \in AllBallot 
          /\ m.state[a].maxBal \in AllBallot
          /\ state'[a][a].maxBal \in AllBallot
      BY DEFS Inv
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>1. m.state[m.from].maxBal \in Ballot
    BY <1>2, <2>a DEFS Inv
  <2>2.  \/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Nat
            /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
    BY <1>2, <2>a DEFS VotedForIn, Inv
  <2>3. CASE (m.state)[m.from].maxBal # (m.state)[m.from].maxVBal
    <3>1. (m.state)[m.from].maxBal <= state'[m.from][m.from].maxBal
      <4>a. (m.state)[m.from].maxBal <= state[m.from][m.from].maxBal
        BY <1>2, <2>a, <2>3 DEFS Inv
      <4>1. CASE m.from = q
        <5>1. state'[m.from][m.from].maxBal >= state[m.from][m.from].maxBal
          BY <1>aaa, <4>1
        <5>2. state[m.from][m.from].maxBal \in AllBallot /\ state'[m.from][m.from].maxBal \in AllBallot
          BY DEFS Inv
        <5> QED
          BY <4>a, <5>1, <5>2 DEFS Inv
      <4>2. CASE m.from # q
        <5>1. UNCHANGED state[m.from][m.from]
          BY <4>2 DEFS UpdateState
        <5> QED
          BY <4>a, <5>1
      <4> QED
        BY <4>1, <4>2
    <3>2. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))'
      <4>1. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))
        BY <2>a, <2>3 DEFS Inv
      <4>2. CASE m.from = q
        BY <3>1, <4>1, <4>2 DEFS VotedForIn, Inv
      <4>3. CASE m.from # q
        BY <4>1, <4>3 DEFS VotedForIn
      <4> QED
        BY <4>2, <4>3
    <3> QED
      BY <2>b, <2>c, <2>d, <2>1, <2>2, <2>3, <3>1, <3>2
  <2>4. CASE (m.state)[m.from].maxBal = (m.state)[m.from].maxVBal
    <3>a. m.state[m.from].maxVBal \in Ballot /\ m.state[m.from].maxVVal \in Value 
      BY <2>a, <2>4 DEFS Inv
    <3>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)'
      <4>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
        BY <2>a, <2>4 DEFS Inv
      <4> QED
        BY <4>1, <3>a, SafeAtStable
    <3>2. \A ma \in msgs': (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
      <4>1. \A ma \in msgs: (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
        BY <2>a, <2>4 DEFS Inv
      <4>2. CASE  /\ nm.state[q].maxVBal = state[q][q].maxVBal
                  /\ nm.state[q].maxVVal = state[q][q].maxVVal
                  /\ nm.state[q].maxBal = Max(state[q][q].maxBal, mm.state[p].maxBal)
        <5>1. CASE nm.state[q].maxBal # nm.state[q].maxVBal
          BY <4>1, <4>2, <5>1
        <5>2. CASE nm.state[q].maxBal = nm.state[q].maxVBal
          <6>a. nm.state[q].maxBal \in Ballot
            <7>a. state[q][q].maxBal \in AllBallot /\ mm.state[p].maxBal \in Ballot
              BY DEFS Inv
            <7> QED 
              BY <4>2, <5>2, <7>a DEFS Max
          <6>1. VotedForIn(q, state[q][q].maxVBal, state[q][q].maxVVal)
            BY <4>2, <5>2, <6>a DEFS AccInv, Inv
          <6> QED
            BY <6>1, <4>1, <4>2 DEFS VotedForIn, Inv
        <5> QED
          BY <5>1, <5>2
      <4>3. CASE  /\ nm.state[q].maxBal = mm.state[p].maxVBal
                  /\ mm.state[p].maxVBal = mm.state[p].maxBal
                  /\ nm.state[q].maxVBal = mm.state[p].maxVBal
                  /\ nm.state[q].maxVVal = mm.state[p].maxVVal
        BY <4>1, <4>3 DEFS Inv
      <4> QED
        BY <1>b, <4>2, <4>3
    <3> QED
      BY <2>b, <2>c, <2>d, <2>1, <2>2, <2>4, <3>1, <3>2
  <2> QED
    BY <2>3, <2>4
<1> QED
  BY <1>1, <1>2

LEMMA OnMessageMsgInv == ASSUME NEW q \in Participant, OnMessage(q), Inv, TypeOK'
                          PROVE MsgInv'
<1> USE DEF TypeOK, Ballot, AllBallot, Inv, MsgInv, State, Send, Message
<1> SUFFICES ASSUME NEW m \in msgs', NEW mm \in msgs, OnMessage(q)!(mm)
              PROVE MsgInv!(m)'
  BY DEFS OnMessage
<1>a. state'[q][q].maxBal >= state[q][q].maxBal
  <2>1. state[q][q].maxBal \in AllBallot
    OBVIOUS
  <2>2. mm.state[mm.from].maxBal \in AllBallot
    OBVIOUS
  <2>3. state'[q][q].maxBal = Max(state[q][q].maxBal, mm.state[mm.from].maxBal)
    BY ZenonT(100), IsaT(100), Z3T(100) DEFS OnMessage, UpdateState
  <2>4. Max(state[q][q].maxBal, mm.state[mm.from].maxBal) >= state[q][q].maxBal
    BY <2>1, <2>2 DEFS Max
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4, ZenonT(100), IsaT(100), Z3T(100)
<1>b. \/ /\ state'[q][q].maxVBal = state[q][q].maxVBal
         /\ state'[q][q].maxVVal = state[q][q].maxVVal
      \/ /\ state'[q][q].maxVBal = mm.state[mm.from].maxVBal
         /\ state'[q][q].maxVVal = mm.state[mm.from].maxVVal
  <2>1. mm.state[mm.from] \in State
    OBVIOUS
  <2> QED
    BY <2>1, UpdateStateValue DEF OnMessage
<1>c. m.from \notin m.to
  BY DEFS OnMessage
<1>d. state'[q][q].maxVBal >= state[q][q].maxVBal
  BY UpdateStateValue DEFS OnMessage
<1>1. CASE \/ (mm.state)[q].maxBal < (state')[q][q].maxBal
           \/ (mm.state)[q].maxVBal < (state')[q][q].maxVBal
  <2>1a. DEFINE nm == [from |-> q, to |-> {mm.from}, state |-> state'[q]]
  <2>1b. nm \in msgs'
    BY <1>1, <1>a DEFS OnMessage
  <2> QED
    BY  UpdateStateMsgInv, <1>1 DEFS Next
<1>2. CASE ~ (\/ (mm.state)[q].maxBal < (state')[q][q].maxBal
              \/ (mm.state)[q].maxVBal < (state')[q][q].maxVBal)
  <2>1a. m \in msgs
    BY <1>2 DEFS OnMessage
  <2>b. \A a \in Participant: /\ m.state[a].maxVBal =< state'[a][a].maxVBal
                              /\ m.state[a].maxBal =< state'[a][a].maxBal
    <3> SUFFICES ASSUME NEW a \in Participant
                  PROVE /\ m.state[a].maxVBal =< state'[a][a].maxVBal
                        /\ m.state[a].maxBal =< state'[a][a].maxBal
      OBVIOUS
    <3>1. /\ m.state[a].maxVBal =< state[a][a].maxVBal  
          /\ m.state[a].maxBal =< state[a][a].maxBal  
      BY <2>1a
    <3>2. /\ state[a][a].maxVBal <= state'[a][a].maxVBal
          /\ state[a][a].maxBal <= state'[a][a].maxBal
      BY <1>a, <1>d DEFS AccInv, UpdateState
    <3>3. state[a][a].maxVBal \in AllBallot /\ m.state[a].maxVBal \in AllBallot
          /\ state[a][a]'.maxVBal \in AllBallot /\ state[a][a].maxBal \in AllBallot
          /\ state'[a][a].maxBal \in AllBallot /\ m.state[a].maxBal \in AllBallot
      OBVIOUS
    <3> QED
      BY <2>1a, <3>1, <3>2, <3>3
  <2>1. m.state[m.from].maxBal \in Ballot
    BY <2>1a
  <2>2.  \/ /\ (m.state)[m.from].maxVVal \in Value
            /\ (m.state)[m.from].maxVBal \in Nat
            /\ VotedForIn(m.from, (m.state)[m.from].maxVBal, (m.state)[m.from].maxVVal)'
         \/ /\ (m.state)[m.from].maxVVal = None
            /\ (m.state)[m.from].maxVBal = -1
    BY <1>2, <2>1 DEFS OnMessage, VotedForIn
  <2>3. CASE (m.state)[m.from].maxBal # (m.state)[m.from].maxVBal
    <3>1. (m.state)[m.from].maxBal <= state'[m.from][m.from].maxBal
      <4>1 (m.state)[m.from].maxBal <= state[m.from][m.from].maxBal
        BY <1>2, <2>1a, <2>3
      <4>2. CASE m.from = q
        <5>1. state'[m.from][m.from].maxBal >= state[m.from][m.from].maxBal
          BY <1>a, <4>2
        <5>2. /\ state'[m.from][m.from].maxBal \in AllBallot 
              /\ state[m.from][m.from].maxBal \in AllBallot
              /\ (m.state)[m.from].maxBal \in AllBallot
          OBVIOUS
        <5> QED
          BY <5>1, <4>1, <5>2
      <4>3. CASE m.from # q
        <5>1. state'[m.from][m.from].maxBal = state[m.from][m.from].maxBal
           BY <2>1a, <4>3  DEFS UpdateState, Max, OnMessage
        <5> QED
          BY <4>1, <4>3 DEFS UpdateState, OnMessage, Max
      <4> QED
        BY <4>2, <4>3
    <3>2. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))'
      <4>1. \A cc \in (m.state)[m.from].maxVBal + 1..(m.state)[m.from].maxBal - 1 :
                ~(\E vv \in Value : VotedForIn(m.from, cc, vv))
        BY <1>2, <2>1a, <2>3 DEFS VotedForIn, OnMessage
      <4> QED
        BY <4>1, <1>2 DEFS OnMessage, VotedForIn
    <3> QED
      BY <1>2, <2>b, <2>1, <2>2, <2>3, <3>1, <3>2
  <2>4. CASE (m.state)[m.from].maxBal = (m.state)[m.from].maxVBal
    <3>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)'
      <4>a. m.state[m.from].maxVBal \in Ballot /\ m.state[m.from].maxVVal \in Value
        BY <2>1a, <2>2, <2>4
      <4>1. SafeAt(m.state[m.from].maxVBal, m.state[m.from].maxVVal)
        BY <2>1a, <2>4
      <4>2. QED
        BY <4>a, <4>1, SafeAtStable DEFS Next
    <3>2. \A ma \in msgs': (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
      <4>1. \A ma \in msgs: (ma.state[ma.from].maxBal = m.state[m.from].maxBal
                             /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                => ma.state[ma.from].maxVVal = m.state[m.from].maxVVal
        BY <2>1a, <2>4
      <4> QED
        BY <1>a, <1>2, <4>1 DEFS OnMessage
    <3> QED
      BY <1>c, <2>b, <2>1, <2>2, <2>4, <3>1, <3>2
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4
<1> QED
  BY <1>1, <1>2


LEMMA OnMessageAccInv == 
    ASSUME NEW qq \in Participant, OnMessage(qq), Inv, TypeOK'
     PROVE AccInv'
<1> USE DEFS Ballot, AllBallot, Send, Message, State, TypeOK
<1>. PICK mm \in msgs: OnMessage(qq)!(mm)
  BY DEFS OnMessage
<1>a. /\ state'[qq][qq].maxBal >= state'[qq][qq].maxVBal
      /\ state'[qq][qq].maxVBal >= state[qq][qq].maxVBal
  BY UpdateStateValue DEFS OnMessage, Inv, MsgInv
<1>b. \/ /\ state'[qq][qq].maxVBal = state[qq][qq].maxVBal
         /\ state'[qq][qq].maxVVal = state[qq][qq].maxVVal
      \/ /\ state'[qq][qq].maxVBal = mm.state[mm.from].maxVBal
         /\ mm.state[mm.from].maxVBal = mm.state[mm.from].maxBal
         /\ state'[qq][qq].maxVVal = mm.state[mm.from].maxVVal
         /\ state'[qq][qq].maxBal = mm.state[mm.from].maxVBal
  BY UpdateStateValue, ZenonT(100), SMTT(100), IsaT(100) DEFS OnMessage, Inv, MsgInv
<1>c. \A a \in Participant: a # qq => state'[a] = state[a]
  BY ZenonT(100), SMTT(100), IsaT(100) DEFS UpdateState
<1>d. DEFINE nm == [from |-> qq, to |-> {mm.from}, state |-> state'[qq]]
<1>e. /\ state'[qq][qq].maxVBal \in AllBallot
      /\ state[qq][qq].maxVBal \in AllBallot
      /\ state[qq][qq].maxBal \in AllBallot
      /\ mm.state[mm.from].maxBal \in AllBallot
      /\ mm.state[mm.from].maxVBal \in AllBallot
  BY DEFS Inv
<1>f. state'[qq][qq].maxBal >= state[qq][qq].maxBal 
  <2>1. state'[qq][qq].maxBal = Max(state[qq][qq].maxBal, mm.state[mm.from].maxBal)
    BY DEFS UpdateState
  <2> QED
    BY <1>e, <2>1 DEFS Max
<1>g. /\ state'[qq][mm.from].maxBal >= state'[qq][mm.from].maxVBal
      /\  \/ /\ state'[qq][mm.from].maxBal = state[qq][mm.from].maxBal
             /\ state'[qq][mm.from].maxVBal = state[qq][mm.from].maxVBal
             /\ state'[qq][mm.from].maxVVal = state[qq][mm.from].maxVVal
          \/ /\ state'[qq][mm.from].maxBal = mm.state[mm.from].maxBal
             /\ state'[qq][mm.from].maxVBal = mm.state[mm.from].maxVBal
             /\ state'[qq][mm.from].maxVVal = mm.state[mm.from].maxVVal
  BY UpdateStateViewValue, ZenonT(100) DEFS OnMessage, Inv, MsgInv
<1>1. \A a \in Participant: 
        /\ (state'[a][a].maxVBal = -1) <=> (state'[a][a].maxVVal = None)
  <2> SUFFICES ASSUME NEW a \in Participant
                PROVE (state'[a][a].maxVBal = -1) <=> (state'[a][a].maxVVal = None)
    OBVIOUS
  <2>1. (state[a][a].maxVBal = -1) <=> (state[a][a].maxVVal = None)
    BY DEFS Inv, AccInv
  <2>2. CASE a # qq
    BY <2>1, <2>2 DEFS UpdateState
  <2>3. CASE a = qq
    <3>1. ((mm.state)[mm.from].maxVBal = -1) <=> ((mm.state)[mm.from].maxVVal = None)
      BY NoneNotAValue, ZenonT(100), SMTT(100), IsaT(100) DEFS Inv, MsgInv
    <3> QED
      BY <1>b, <2>3, <3>1 DEFS Inv, MsgInv, AccInv
  <2> QED
    BY <2>2, <2>3
<1>2. \A a \in Participant:
        \A q \in Participant: state'[a][q].maxVBal =< state'[a][q].maxBal
  <2> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant
                PROVE state'[a][q].maxVBal =< state'[a][q].maxBal
    OBVIOUS
  <2>1. CASE a # qq
    BY <2>1 DEFS UpdateState, Inv, AccInv
  <2>2. CASE a = qq
    <3>1. CASE q = mm.from
      BY <1>g, <2>2, <3>1
    <3>2. CASE q = qq
      BY <1>a, <2>2, <3>2
    <3>3. CASE q # mm.from /\ q # qq
      <4>1. /\ state'[a][q].maxVBal = state[a][q].maxVBal
            /\ state'[a][q].maxBal = state[a][q].maxBal
        BY <2>2, <3>3 DEFS UpdateState
      <4> QED
        BY <2>2, <3>3, <4>1 DEFS AccInv, Inv
    <3> QED
      BY <2>2, <3>1, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2
<1>3. \A a \in Participant:
                state'[a][a].maxVBal >= 0
                      => VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)'
  <4> SUFFICES ASSUME NEW a \in Participant, state'[a][a].maxVBal >= 0
                PROVE VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)'
    OBVIOUS
  <4>1. CASE a = qq
    <5>1. CASE /\ state'[qq][qq].maxVBal = state[qq][qq].maxVBal
               /\ state'[qq][qq].maxVVal = state[qq][qq].maxVVal
      <6>1. VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)
        BY <4>1, <5>1 DEFS AccInv, Inv
      <6> QED
        BY <4>1, <5>1, <6>1 DEFS VotedForIn, UpdateState
    <5>2. CASE   /\ state'[qq][qq].maxVBal = mm.state[mm.from].maxVBal
                 /\ mm.state[mm.from].maxVBal = mm.state[mm.from].maxBal
                 /\ state'[qq][qq].maxVVal = mm.state[mm.from].maxVVal
                 /\ state'[qq][qq].maxBal = mm.state[mm.from].maxVBal
      <6>1. CASE state[qq][qq].maxVBal = mm.state[mm.from].maxVBal
        <7>a. state[qq][qq].maxVBal >= 0 /\ state[qq][qq].maxVBal \in Ballot
          BY <4>1, <5>2, <6>1
        <7>b. VotedForIn(mm.from, mm.state[mm.from].maxVBal, mm.state[mm.from].maxVVal)
          BY <6>1, <7>a DEFS MsgInv, Inv
        <7>c. VotedForIn(qq, state[qq][qq].maxVBal, state[qq][qq].maxVVal)
          BY <7>a DEFS Inv, AccInv
        <7>d. state[qq][qq].maxVVal \in Value /\ mm.state[mm.from].maxVVal \in Value
          BY <6>1, <7>a DEFS Inv, AccInv, MsgInv
        <7>1. state[qq][qq].maxVVal = mm.state[mm.from].maxVVal
          BY <4>1, <6>1, <7>a, <7>b, <7>c, <7>d, VotedOnce DEFS Inv
        <7>2. VotedForIn(qq, state'[qq][qq].maxVBal, state'[qq][qq].maxVVal)
          BY <5>2, <6>1, <7>c, <7>1
        <7> QED
          BY <4>1, <7>2 DEFS VotedForIn, OnMessage
      <6>2. CASE mm.state[mm.from].maxVBal # state[qq][qq].maxVBal
        <7>a. /\ mm.state[qq].maxVBal \in AllBallot
              /\ state[qq][qq].maxVBal \in AllBallot
              /\ mm.state[mm.from].maxVBal \in AllBallot
              /\ state'[qq][qq].maxVBal \in AllBallot
          BY DEFS Inv
        <7>b. mm.state[mm.from].maxVBal >= state[qq][qq].maxVBal
          BY <1>a, <5>2
        <7>c. mm.state[mm.from].maxVBal > state[qq][qq].maxVBal
          BY <6>2, <7>a, <7>b
        <7>d. mm.state[qq].maxVBal <= state[qq][qq].maxVBal
          BY DEFS Inv, MsgInv  
        <7>e. mm.state[qq].maxVBal < state'[qq][qq].maxVBal
          BY <5>2, <7>a, <7>c, <7>d
        <7>1. nm \in msgs'
          BY <7>e DEFS OnMessage
        <7> QED
          BY <4>1, <5>2, <6>2, <7>1 DEFS VotedForIn
      <6> QED
        BY <6>1, <6>2
    <5> QED
      BY <1>b, <5>1, <5>2 
  <4>2. CASE a # qq
    <5>2. VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)
      BY <4>2 DEFS UpdateState, Inv, AccInv
    <5> QED
      BY <4>2, <5>2 DEFS VotedForIn, UpdateState
  <4> QED
    BY <4>1, <4>2
<1>4. \A a \in Participant: 
                 /\ \A c \in Ballot: c > state'[a][a].maxVBal 
                    => ~ \E v \in Value: VotedForIn(a, c, v)'
  <2> SUFFICES ASSUME NEW a \in Participant, NEW c \in Ballot, c > state'[a][a].maxVBal
                  PROVE ~ \E v \in Value: VotedForIn(a, c, v)'
    OBVIOUS
  <2>1. c > state[a][a].maxVBal
    <3>1. CASE a = qq
      BY <1>a, <1>e, <3>1
    <3>2. CASE a # qq
      BY <3>2 DEFS UpdateState
    <3> QED
      BY <3>1, <3>2
  <2>2. ~ \E v \in Value: VotedForIn(a, c, v)
    BY <2>1 DEFS AccInv, Inv
  <2>3. CASE a = qq
    BY <1>b, <2>2 DEFS OnMessage, VotedForIn
  <2>4. CASE a # qq
    BY <2>2 DEFS OnMessage, VotedForIn
  <2> QED
    BY <2>3, <2>4
<1>5. \A a \in Participant:
                \A q \in Participant:
                    /\ state'[a][a].maxBal >= state'[q][a].maxBal
                    /\ state'[a][a].maxVBal >= state'[q][a].maxVBal
  <2> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant
                PROVE /\ state'[a][a].maxBal >= state'[q][a].maxBal
                      /\ state'[a][a].maxVBal >= state'[q][a].maxVBal
    OBVIOUS
  <2>a. /\ state'[a][a].maxBal \in AllBallot
        /\ state'[q][a].maxBal \in AllBallot
        /\ state'[a][a].maxVBal \in AllBallot
        /\ state'[q][a].maxBal \in AllBallot
        /\ state[a][a].maxBal \in AllBallot
        /\ state[a][a].maxVBal \in AllBallot
        /\ state[q][a].maxBal \in AllBallot
        /\ state[q][a].maxVBal \in AllBallot
    BY DEFS Inv
  <2>b. /\ state[a][a].maxBal >= state[q][a].maxBal
        /\ state[a][a].maxVBal >= state[q][a].maxVBal
    BY DEFS Inv, AccInv
  <2>1. CASE q = a /\ a = qq
    BY <2>1, <2>a
  <2>2. CASE q # a /\ a = qq
    <3>1. /\ state'[q][a].maxBal = state[q][a].maxBal
          /\ state'[q][a].maxVBal = state[q][a].maxVBal
      BY <2>2 DEFS UpdateState
    <3>2. /\ state'[a][a].maxBal >= state[a][a].maxBal
          /\ state'[a][a].maxVBal >= state[a][a].maxVBal
      BY <2>2, <1>a, <1>f
    <3> QED
      BY <2>a, <2>b, <2>2, <3>1, <3>2
  <2>3. CASE q = a /\ a # qq
    BY <2>3 DEFS UpdateState, Inv, AccInv
  <2>4. CASE q # a /\ a # qq 
    <3>1. /\ state'[a][a].maxBal = state[a][a].maxBal
          /\ state'[a][a].maxVBal = state[a][a].maxVBal
      BY <2>4 DEFS UpdateState
    <3>2. CASE q = qq /\ a = mm.from
      <4>1. /\ mm.state[mm.from].maxVBal <= state[a][a].maxVBal
        BY <3>2 DEFS Inv, MsgInv
      <4>2. /\ mm.state[mm.from].maxBal <= state[a][a].maxBal
        <5>1. CASE mm.state[mm.from].maxBal # mm.state[mm.from].maxVBal
          BY <3>2, <5>1 DEFS Inv, MsgInv
        <5>2. CASE mm.state[mm.from].maxBal = mm.state[mm.from].maxVBal
          <6>1. mm.state[mm.from].maxBal <= state[a][a].maxVBal
            BY <3>2, <5>2 DEFS Inv, MsgInv
          <6> QED
            BY <1>e, <2>a, <6>1 DEFS Inv, AccInv
        <5> QED
          BY <5>1, <5>2
      <4>3. /\ state'[q][a].maxVBal = Max(state[qq][a].maxVBal, mm.state[mm.from].maxVBal)
            /\ state'[q][a].maxBal = Max(state[qq][a].maxBal, mm.state[mm.from].maxBal)
        BY <3>2 DEFS UpdateState
      <4>4. Max(state[qq][a].maxBal, mm.state[mm.from].maxBal) <= state[a][a].maxBal
        BY <1>e, <2>a, <2>b, <4>2, <3>2 DEFS Max
      <4>5. Max(state[qq][a].maxVBal, mm.state[mm.from].maxVBal) <= state[a][a].maxVBal
        BY <1>e, <2>a, <2>b, <4>1, <3>2 DEFS Max
      <4> QED
        BY <3>1, <3>2, <4>3, <4>4, <4>5
    <3>3. CASE ~(q = qq /\ a = mm.from)
      <4>1. /\ state'[q][a].maxBal = state[q][a].maxBal
            /\ state'[q][a].maxVBal = state[q][a].maxVBal
        BY <2>4, <3>3 DEFS UpdateState
      <4> QED
        BY <2>a, <2>b, <3>1, <4>1
    <3> QED
      BY <2>4, <3>2, <3>3
  <2> QED
    BY <2>1, <2>2, <2>3, <2>4
<1>6. \A a \in Participant:
                 \A q \in Participant: 
                    state'[a][q].maxBal \in Ballot
                        => \E m \in msgs': 
                              /\ m.from = q 
                              /\ m.state[q].maxBal = state'[a][q].maxBal
                              /\ m.state[q].maxVBal = state'[a][q].maxVBal
                              /\ m.state[q].maxVVal = state'[a][q].maxVVal
  <2> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant, state'[a][q].maxBal \in Ballot
                  PROVE \E m \in msgs':
                          /\ m.from = q 
                          /\ m.state[q].maxBal = state'[a][q].maxBal
                          /\ m.state[q].maxVBal = state'[a][q].maxVBal
                          /\ m.state[q].maxVVal = state'[a][q].maxVVal
    OBVIOUS
  <2>a. /\ state'[a][q].maxBal \in AllBallot
        /\ state[a][q].maxBal \in AllBallot
        /\ state'[a][q].maxVBal \in AllBallot
        /\ state[a][q].maxVBal \in AllBallot
    BY DEFS Inv, MsgInv
  <2>2. CASE a = qq
    <3>1. CASE mm.from = q
      BY <1>g, <2>2, <3>1, SMTT(100) DEFS AccInv, Inv, OnMessage
    <3>2. CASE a = q
      <4>a. state'[qq][qq].maxBal = Max(state[qq][qq].maxBal, mm.state[mm.from].maxBal)
        BY DEFS UpdateState
      <4>1. CASE 
             /\ state'[qq][qq].maxVBal = mm.state[mm.from].maxVBal
             /\ mm.state[mm.from].maxVBal = mm.state[mm.from].maxBal
             /\ state'[qq][qq].maxVVal = mm.state[mm.from].maxVVal
             /\ state'[qq][qq].maxBal = mm.state[mm.from].maxVBal
        <5>1. VotedForIn(qq, mm.state[mm.from].maxVBal, mm.state[mm.from].maxVVal)'
          BY <1>3, <4>1 DEFS Inv, MsgInv
        <5> QED
          BY <2>2, <3>2, <4>1, <5>1 DEFS VotedForIn
      <4>2. CASE 
             /\ state'[qq][qq].maxVBal = state[qq][qq].maxVBal
             /\ state'[qq][qq].maxVVal = state[qq][qq].maxVVal
        <5>1. CASE state'[qq][qq].maxBal = state[qq][qq].maxBal
          <6>1. state[a][q].maxBal \in Ballot
            BY <2>2, <3>2, <4>2, <5>1
          <6>2. \E m \in msgs:
                  /\ m.from = q
                  /\ m.state[q].maxBal = state[a][q].maxBal
                  /\ m.state[q].maxVBal = state[a][q].maxVBal
                  /\ m.state[q].maxVVal = state[a][q].maxVVal
            BY <6>1 DEFS Inv, AccInv
          <6> QED
            BY <2>2, <3>2, <4>2, <5>1, <6>2 DEFS Inv, AccInv, OnMessage
        <5>2. CASE state'[qq][qq].maxBal > state[qq][qq].maxBal
          <6>a. /\ state'[qq][qq].maxBal \in AllBallot
                /\ state[qq][qq].maxBal \in AllBallot
                /\ mm.state[qq].maxBal \in AllBallot
            BY DEFS Inv
          <6>1. mm.state[qq].maxBal =< state[qq][qq].maxBal
            BY <2>2, <3>2, <4>2, <5>2 DEFS Inv, MsgInv
          <6>2. mm.state[qq].maxBal < state'[qq][qq].maxBal
            BY <5>2, <6>1, <6>a
          <6>3. nm \in msgs'
            BY <6>2
          <6> QED
            BY <2>2, <3>2, <5>2, <6>3
        <5> QED
          BY <1>e, <1>f, <5>1, <5>2
      <4> QED
        BY <1>b, <4>1, <4>2
    <3>3. CASE a # q /\ q # mm.from
      <4>1. /\ state'[a][q].maxBal = state[a][q].maxBal
            /\ state'[a][q].maxVBal = state[a][q].maxVBal
            /\ state'[a][q].maxVVal = state[a][q].maxVVal
        BY <2>2, <3>3, ZenonT(100), IsaT(100), SMTT(100) DEFS UpdateState
      <4>2. \E m \in msgs:
              /\ m.from = q 
              /\ m.state[q].maxBal = state[a][q].maxBal
              /\ m.state[q].maxVBal = state[a][q].maxVBal
              /\ m.state[q].maxVVal = state[a][q].maxVVal
        BY <4>1 DEFS Inv, AccInv
      <4> QED
        BY <4>1, <4>2 DEFS OnMessage
    <3> QED
      BY <3>1, <3>2, <3>3
  <2>3. CASE a # qq
    <3>1. /\ state'[a][q].maxBal = state[a][q].maxBal
          /\ state'[a][q].maxVBal = state[a][q].maxVBal
          /\ state'[a][q].maxVVal = state[a][q].maxVVal
      BY <2>3 DEFS UpdateState
    <3>2. \E m \in msgs:
              /\ m.from = q 
              /\ m.state[q].maxBal = state[a][q].maxBal
              /\ m.state[q].maxVBal = state[a][q].maxVBal
              /\ m.state[q].maxVVal = state[a][q].maxVVal
      BY <3>1 DEFS Inv, AccInv
    <3> QED
      BY <3>1, <3>2 DEFS OnMessage
  <2> QED
    BY <2>2, <2>3
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEFS AccInv
--------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
<1> USE DEFS Send, Ballot, TypeOK, State, AllBallot, InitState, 
             AllValue, Message, vars
<1>1. Init => Inv
  BY DEFS Init, AccInv, InitState, VotedForIn, MsgInv, TypeOK, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
                PROVE Inv'
      OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE Next
    <3>1. TypeOK'
      <4>1. ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv
             PROVE TypeOK'
        <5>1. state'[p][p].maxBal \in AllBallot
          BY <4>1 DEFS Prepare
        <5>2. state'[p][p].maxVBal \in AllBallot
          BY <4>1 DEFS Prepare
        <5>3. state'[p][p].maxVVal \in AllValue
          BY <4>1 DEFS Prepare
        <5>4. state'[p][p] \in [maxBal: AllBallot, maxVBal: Ballot \cup {-1}, maxVVal:Value \cup {None}]
          BY <4>1, <5>1, <5>2, <5>3 DEFS Prepare 
        <5>5. state' \in [Participant -> [Participant -> State]]
          BY <4>1, <5>4 DEFS Prepare
        <5>6. [from |-> p, to |-> Participant \ {p},
                      state |-> (state')[p]] \in Message
          BY <5>5
        <5>7. msgs' \subseteq Message
          BY <4>1, <5>6 DEFS Prepare
        <5> QED
          BY <5>5, <5>7 DEFS Prepare
      <4>2. ASSUME NEW p \in Participant, NEW b \in Ballot, NEW v \in Value, Accept(p, b, v), Inv
             PROVE TypeOK'
        <5>1. state[p][p].maxBal >= b
          BY <4>2, QuorumAssumption DEFS AccInv, Accept
        <5>2. state[p][p].maxBal <= b
          BY <4>2, <5>1 DEFS Accept
        <5>3. state'[p][p].maxBal = b /\ state'[p][p].maxVBal = b /\ state'[p][p].maxVVal = v
          BY <4>2, <5>1, <5>2 DEFS Accept
        <5>5. state' \in [Participant -> [Participant -> State]]
          BY <4>2, <5>3, ZenonT(100) DEFS Accept
        <5>6. [from |-> p, to |-> Participant \ {p},
                      state |-> (state')[p]] \in Message
          BY <5>5
        <5>7. msgs' \subseteq Message
          BY <4>2, <5>6 DEFS Accept
        <5> QED
        BY <4>2, <5>6, <5>7 DEFS Accept
      <4>3. ASSUME NEW p \in Participant, OnMessage(p), Inv
             PROVE TypeOK'
        <5>1. PICK mm \in msgs: OnMessage(p)!(mm)
          BY <4>3 DEFS OnMessage
        <5>2. state' \in [Participant -> [Participant -> State]]
          BY <4>3, UpdateStateTypeOKProperty DEFS OnMessage
        <5>3. [from |-> p, to |-> {mm.from}, state |-> (state')[p]] \in Message
          BY <4>3, <5>2 DEFS OnMessage, UpdateState
        <5>5. msgs' \subseteq Message
          <6>1. CASE \/ (mm.state)[p].maxBal < (state')[p][p].maxBal
                     \/ (mm.state)[p].maxVBal < (state')[p][p].maxVBal
            BY <4>3, <5>3 DEFS OnMessage
          <6>2. CASE ~ (\/ (mm.state)[p].maxBal < (state')[p][p].maxBal
                        \/ (mm.state)[p].maxVBal < (state')[p][p].maxVBal)
            BY <4>3, <5>3 DEFS OnMessage
          <6> QED
            BY <4>3, <6>1, <6>2 DEF OnMessage
        <5> QED
          BY <4>3, <5>2, <5>5 DEFS OnMessage
      <4> QED
        BY <2>1, <4>1, <4>2, <4>3 DEFS Next
    <3>2. MsgInv'
      <4> USE DEF MsgInv
      <4>1. ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv
             PROVE MsgInv'
        BY <3>1, <4>1, PrepareMsgInv
      <4>2. ASSUME NEW p \in Participant, NEW b \in Ballot, NEW v \in Value, Accept(p, b, v), Inv
             PROVE MsgInv'
        BY <3>1, <4>2, AcceptMsgInv
      <4>3.  ASSUME NEW p \in Participant, OnMessage(p), Inv
             PROVE MsgInv'
        BY <3>1, <4>3, OnMessageMsgInv
      <4> QED
        BY <2>1, <4>1, <4>2, <4>3 DEFS Next
    <3>3. AccInv'
      <4>1. ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv
             PROVE AccInv'
        <5> DEFINE nm == [from |-> p, to |-> Participant \ {p},
                            state |-> (state')[p]]
        <5>a. \A a \in Participant: 
                state[a][a].maxVBal = state'[a][a].maxVBal
          BY <4>1 DEFS Prepare
        <5>b. nm.state[p].maxBal # nm.state[p].maxVBal
          BY <4>1 DEFS Prepare, AccInv
        <5>1. \A a \in Participant: 
                /\ state'[a][a].maxVBal = -1 <=> state'[a][a].maxVVal = None
                /\ \A q \in Participant: state'[a][q].maxVBal =< state'[a][q].maxBal
          BY <4>1 DEFS Prepare, AccInv
        <5>3. \A a \in Participant: 
                state'[a][a].maxVBal >= 0
                      => VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)'
          BY <5>a, <4>1 DEFS VotedForIn, Prepare, AccInv
        <5>4. \A a \in Participant: 
                 /\ \A c \in Ballot: c > state'[a][a].maxVBal 
                    => ~ \E v \in Value: VotedForIn(a, c, v)'
          <6> SUFFICES ASSUME NEW a \in Participant, NEW c \in Ballot, c > state'[a][a].maxVBal
                        PROVE ~ \E v \in Value: VotedForIn(a, c, v)'
            OBVIOUS
          <6>1. ~ \E v \in Value: VotedForIn(a, c, v)
            BY <5>a DEFS AccInv
          <6> QED
            BY <4>1, <5>a, <5>b, <6>1 DEFS VotedForIn, Prepare
        <5>5. \A a \in Participant:
                \A q \in Participant:
                    /\ state'[a][a].maxBal >= state'[q][a].maxBal
                    /\ state'[a][a].maxVBal >= state'[q][a].maxVBal
          <6> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant
                        PROVE /\ state'[a][a].maxBal >= state'[q][a].maxBal
                              /\ state'[a][a].maxVBal >= state'[q][a].maxVBal
            OBVIOUS
          <6>1. CASE a # p
            BY <4>1, <6>1 DEFS Prepare, AccInv, VotedForIn
          <6>2. CASE a = p
            BY <4>1, <5>a, <6>2 DEFS Prepare, AccInv, VotedForIn
          <6> QED
            BY <6>1, <6>2
        <5>6. \A a \in Participant:
                 \A q \in Participant: 
                    state'[a][q].maxBal \in Ballot
                        => \E m \in msgs': 
                              /\ m.from = q 
                              /\ m.state[q].maxBal = state'[a][q].maxBal
                              /\ m.state[q].maxVBal = state'[a][q].maxVBal
                              /\ m.state[q].maxVVal = state'[a][q].maxVVal
          <6> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant, state'[a][q].maxBal \in Ballot
                        PROVE \E m \in msgs': 
                                  /\ m.from = q 
                                  /\ m.state[q].maxBal = state'[a][q].maxBal
                                  /\ m.state[q].maxVBal = state'[a][q].maxVBal
                                  /\ m.state[q].maxVVal = state'[a][q].maxVVal
            OBVIOUS
          <6>1. CASE (a = q /\ a = p)
            BY <4>1, <6>1, IsaT(100) DEFS Prepare
          <6>2. CASE ~(a = q /\ a = p)
            <7>1. /\ state'[a][q].maxBal = state[a][q].maxBal
                  /\ state'[a][q].maxVBal = state[a][q].maxVBal
                  /\ state'[a][q].maxVVal = state[a][q].maxVVal
              BY <4>1, <6>2 DEFS Prepare
            <7> QED
              BY <4>1, <6>2, <7>1 DEFS AccInv, Prepare
          <6> QED
          BY <6>1, <6>2
        <5> QED
          BY <5>1, <5>3, <5>4, <5>5, <5>6 DEFS AccInv
      <4>2. ASSUME NEW p \in Participant, NEW b \in Ballot, NEW v \in Value, Accept(p, b, v), Inv
             PROVE AccInv'
        <5> DEFINE nm == [from |-> p, to |-> Participant \ {p}, state |-> state'[p]]
        <5>a. nm.state[p].maxBal = nm.state[p].maxVBal
          BY <4>2 DEFS Accept
        <5>b. state'[p][p].maxVBal >= state[p][p].maxVBal
          BY <4>2 DEFS Accept, AccInv
        <5>1. state'[p][p].maxBal = state'[p][p].maxVBal /\ state'[p][p].maxBal = state[p][p].maxBal
          BY <4>2 DEFS Accept
        <5>2. state'[p][p].maxVBal \in Ballot /\ state'[p][p].maxVVal \in Value
          BY <4>2 DEFS Accept
        <5>3. VotedForIn(p, state[p][p].maxVBal, state[p][p].maxVVal)'
          BY <4>2, <5>1, <5>2, IsaT(100) DEFS Accept, VotedForIn
        <5>4. \A a \in Participant: 
                /\ state'[a][a].maxVBal = -1 <=> state'[a][a].maxVVal = None
                /\ \A q \in Participant: state'[a][q].maxVBal =< state'[a][q].maxBal
          BY <4>2, <5>2, NoneNotAValue DEFS AccInv, Accept
        <5>5. \A a \in Participant: 
                state'[a][a].maxVBal >= 0
                      => VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)'
          <6> SUFFICES ASSUME NEW a \in Participant, state'[a][a].maxVBal >= 0
                        PROVE VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)'  
            OBVIOUS
          <6>1. CASE a # p
            BY <4>2, <6>1 DEFS Accept, AccInv, VotedForIn
          <6>2. CASE a = p
            BY <4>2, <5>3, <6>2, IsaT(100) DEFS Accept, AccInv, VotedForIn
          <6> QED
            BY <6>1, <6>2
        <5>6. \A a \in Participant: 
                 /\ \A c \in Ballot: c > state'[a][a].maxVBal 
                    => ~ \E vv \in Value: VotedForIn(a, c, vv)'
          <6> SUFFICES ASSUME NEW a \in Participant, NEW c \in Ballot, c > state'[a][a].maxVBal
                        PROVE ~ \E vv \in Value: VotedForIn(a, c, vv)'
            OBVIOUS
          <6>1. c > state[a][a].maxVBal
            <7> QED
              BY <4>2, <5>b DEFS Accept
          <6>2. ~ \E vv \in Value: VotedForIn(a, c, vv)
            BY <6>1 DEFS AccInv
          <6> QED
            BY <4>2, <5>3, <6>2 DEFS Accept, VotedForIn
        <5>7. \A a \in Participant:
                \A q \in Participant:
                    /\ state'[a][a].maxBal >= state'[q][a].maxBal
                    /\ state'[a][a].maxVBal >= state'[q][a].maxVBal
          <6> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant
                        PROVE  /\ state'[a][a].maxBal >= state'[q][a].maxBal
                               /\ state'[a][a].maxVBal >= state'[q][a].maxVBal
            OBVIOUS
          <6>1. CASE ~ (q # a /\ a = p)
            BY <4>2, <6>1 DEFS Accept, AccInv
          <6>2. CASE q # a /\ a = p
            <7>1. /\ state'[q][a].maxBal = state[q][a].maxBal
                  /\ state'[q][a].maxVBal = state[q][a].maxVBal
                  /\ state'[a][a].maxBal = state[a][a].maxBal
                  /\ state'[a][a].maxVBal >= state[a][a].maxVBal
              BY <4>2, <5>b, <6>2 DEFS Accept
            <7>2. /\ state'[a][a].maxVBal \in AllBallot /\ state[q][a].maxVBal \in AllBallot
                  /\ state'[a][a].maxBal \in AllBallot /\ state[q][a].maxBal \in AllBallot
              BY <3>1
            <7> QED
              BY <4>2, <6>2, <7>1, <7>2 DEFS Accept, AccInv
          <6> QED
            BY <6>1, <6>2
        <5>8. \A a \in Participant:
                 \A q \in Participant: 
                    state'[a][q].maxBal \in Ballot
                        => \E m \in msgs': 
                              /\ m.from = q 
                              /\ m.state[q].maxBal = state'[a][q].maxBal
                              /\ m.state[q].maxVBal = state'[a][q].maxVBal
                              /\ m.state[q].maxVVal = state'[a][q].maxVVal
          <6> SUFFICES ASSUME NEW a \in Participant, NEW q \in Participant, state'[a][q].maxBal \in Ballot
                        PROVE \E m \in msgs': 
                                  /\ m.from = q 
                                  /\ m.state[q].maxBal = state'[a][q].maxBal
                                  /\ m.state[q].maxVBal = state'[a][q].maxVBal
                                  /\ m.state[q].maxVVal = state'[a][q].maxVVal
            OBVIOUS
          <6>1. CASE (a = q /\ a = p)
            BY <4>2, <6>1, IsaT(100) DEFS Accept
          <6>2. CASE ~(a = q /\ a = p)
            <7>1. /\ state'[a][q].maxBal = state[a][q].maxBal
                  /\ state'[a][q].maxVBal = state[a][q].maxVBal
                  /\ state'[a][q].maxVVal = state[a][q].maxVVal
              BY <4>2, <6>2 DEFS Accept
            <7> QED
              BY <4>2, <6>2, <7>1 DEFS AccInv, Accept
          <6> QED
            BY <6>1, <6>2
        <5> QED
          BY <5>4, <5>5, <5>6, <5>7, <5>8 DEFS AccInv
      <4>3.  ASSUME NEW p \in Participant, OnMessage(p), Inv
             PROVE AccInv'
        BY <4>3, <3>1, OnMessageAccInv
      <4> QED
        BY <2>1, <4>1, <4>2, <4>3 DEFS Next
    <3> QED
      BY <3>1, <3>2, <3>3 DEFS Inv
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEFS AccInv, MsgInv, TypeOK, VotedForIn, Next,
            SafeAt, WontVoteIn, VotedForIn
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, PTL DEFS Spec

--------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballot
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv, 
                      NEW b1 \in Ballot, NEW b2 \in Ballot,
                      NEW v1 \in Value, NEW v2 \in Value,
                      ChosenIn(b1, v1), ChosenIn(b2, v2),
                      b1 <= b2
               PROVE v1 = v2
      BY DEFS Chosen, Consistency
  <2>1. CASE b1 = b2
    BY <2>1, VotedOnce, QuorumAssumption DEFS Inv, ChosenIn
  <2>2. CASE b1 < b2
    <3>1. SafeAt(b2, v2)
      BY VotedInv, QuorumAssumption DEFS ChosenIn, Inv
    <3>2. PICK Q2 \in Quorum:
        \A a \in Q2: VotedForIn(a, b1, v2) \/ WontVoteIn(a, b1)
      BY <2>2, <3>1 DEFS SafeAt
    <3>3. PICK Q1 \in Quorum:
        \A a \in Q1: VotedForIn(a, b1, v1)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>3, <3>2, QuorumAssumption, VotedOnce DEFS WontVoteIn, Inv
  <2> QED 
    BY <2>1, <2>2
<1>2. QED
  BY Invariant, PTL, <1>1
---------------------------------------------------------------------------
(*
For checking Liveness
WF(A): if A ever becomes enabled, then an A step will eventually occur-even 
if A remains enabled for only a fraction of a nanosecond and is never again
enabled. 
Liveness in TPaxos: like paxos, there should be a single-leader to prapre
and accept.
*)

LConstrain == /\ \E p \in Participant:
                /\ MaxBallot \in Bals(p)
                /\ WF_vars(Prepare(p, MaxBallot))
                /\ \A v \in Value: WF_vars(Accept(p, MaxBallot, v))
                /\ \E Q \in Quorum:
                    /\ p \in Q
                    /\ \A q \in Q: WF_vars(OnMessage(q))

LSpec == Spec /\ LConstrain

Liveness == <>(chosen # {})
=============================================================================
\* Modification History
\* Last modified Thu Oct 29 15:28:07 CST 2020 by stary
\* Last modified Wed Oct 14 16:39:25 CST 2020 by pure_
\* Last modified Fri Oct 09 14:33:01 CST 2020 by admin
\* Created Thu Jun 25 14:23:28 CST 2020 by admin