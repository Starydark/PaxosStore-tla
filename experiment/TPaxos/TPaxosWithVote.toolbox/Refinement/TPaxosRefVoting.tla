------------------------ MODULE TPaxosRefVoting ------------------------
EXTENDS TPaxos

VARIABLE votes
varsR == <<vars, votes>>

InitR == 
    /\ Init 
    /\ votes = [q \in Participant |-> {}]
            
PrepareR(p, b) == 
    /\ Prepare(p, b)
    /\ votes' = votes
           
AcceptR(p, b, v) == 
    /\ Accept(p, b, v)
    /\ votes' = [votes EXCEPT ![p] = @ \cup {<<b, v>>}]
                    
OnMessageR(q) == 
    /\ OnMessage(q)
    /\ IF state'[q][q].maxVBal # -1
         THEN votes' = [votes EXCEPT ![q] = @ \cup 
                                {<<state'[q][q].maxVBal, state'[q][q].maxVVal>>}]
         ELSE UNCHANGED votes
                        
NextR == \E p \in Participant : 
                \/ OnMessageR(p)
                \/ \E b \in Ballot : \/ PrepareR(p, b)
                                     \/ \E v \in Value : AcceptR(p, b, v)
SpecR == InitR /\ [][NextR]_varsR

(***************************************************************************
  To verify Spec => Voting, we should define votes and maxBal
          votes,   \* votes[a] is the set of votes cast by Participant a
          maxBal   \* maxBal[a] is a ballot number.  Participant a will cast
                   \* further votes only in ballots numbered \geq maxBal[a]
 ***************************************************************************)
maxBal == [p \in Participant |-> state[p][p].maxBal]

V == INSTANCE EagerVoting WITH Acceptor <- Participant 
                               (*votes <- votes, maxBal <- maxBal*)

THEOREM SpecR => V!Spec

=============================================================================
\* Modification History
\* Last modified Wed Aug 28 10:43:19 CST 2019 by pure_
\* Created Tue Aug 06 20:46:18 CST 2019 by pure_
