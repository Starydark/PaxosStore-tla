------------------------ MODULE PaxosStoreRefVoting ------------------------
EXTENDS UniversalPaxosStoreQuorum

VARIABLE voted
varsR == <<vars, voted>>

InitR == /\ Init 
         /\ voted = [q \in Participant |-> {}]
            
PrepareR(p, b) == /\ Prepare(p, b)
                  /\ voted' = voted
           
AcceptR(p, b, v) == /\ Accept(p, b, v)
                    /\ voted' = [voted EXCEPT ![p] = @ \cup {<<b, v>>}]
                    
OnMessageR(q) == /\ OnMessage(q)
                 /\ IF state'[q][q].maxVBal # -1
                      THEN voted' = [voted EXCEPT ![q] = @ \cup {<<state'[q][q].maxVBal, state'[q][q].maxVVal>>}]
                      ELSE UNCHANGED voted
                        
NextR == \E p \in Participant : \/ OnMessageR(p)
                                \/ \E b \in Ballot : \/ PrepareR(p, b)
                                                     \/ \E v \in Value : AcceptR(p, b, v)
SpecR == InitR /\ [][NextR]_varsR

(***************************************************************************
  To verify Spec => Voting, we should define votes and maxBal
          votes,   \* votes[a] is the set of votes cast by Participant a
          maxBal   \* maxBal[a] is a ballot number.  Participant a will cast
                   \* further votes only in ballots numbered \geq maxBal[a]
 ***************************************************************************)

V == INSTANCE EagerVoting WITH Acceptor <- Participant,
                               votes    <- voted,
                               maxBal   <- [p \in Participant |-> state[p][p].maxBal]

THEOREM SpecR => V!Spec

=============================================================================
\* Modification History
\* Last modified Thu Aug 15 21:25:10 CST 2019 by pure_
\* Created Tue Aug 06 20:46:18 CST 2019 by pure_
