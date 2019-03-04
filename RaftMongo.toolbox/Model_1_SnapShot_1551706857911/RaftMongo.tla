--------------------------------- MODULE RaftMongo ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT NODES \* sequence of nodes in a replset.
CONSTANT NUM_NODES

CONSTANT VALUE

CONSTANT TERMS

CONSTANTS FOLLOWER, LEADER, CANDIDATE

Last(s) == s[Len(s)]

(*
--algorithm mongoRaft {
variable
    globalCurrentTerm = 0,
    rVals = [rVal \in NODES |-> {0}],
    logs = [log \in NODES |-> <<[term |-> globalCurrentTerm, value |-> VALUE]>>],
    states = [state \in NODES |-> {FOLLOWER, CANDIDATE, LEADER}];


\* term of the last entry in a log.
macro GetTerm(xlog, index, term) {
    if (index = 0) {
        term := 0;
    } else {
        term := xlog[index].term;
    };
}

macro LastTerm(xlog, term) {
    GetTerm(xlog, Len(xlog), term);
}

\*procedure appendOplog(i, j) {
\*    if (Len(log[i]) < Len(log[j])) {
\*      if (LastTerm(log[i]) = LogTerm) {
\*      
\*      }
\*    };
\*}

macro canElectMe(myLogs, theirLogs, numElectMe) {
    with (myTerm = Last(myLogs).term, theirTerm = Last(theirLogs).term) {
        if (myTerm > theirTerm \/ (theirTerm = myTerm /\ Len(logs[self]) >= Len(logs[curNode]))) {
            numElectMe := numElectMe + 1;
        }
    }
}

procedure instantElection() 
variables numElectMe = 0, curNode = 1;
{
el0: while (curNode <= NUM_NODES) {
        canElectMe(logs[self], logs[curNode], numElectMe);
        curNode := curNode + 1;
     };
     print<<"numElectMe: ", self, numElectMe>>;
     
     if (numElectMe * 2 > NUM_NODES) {
        globalCurrentTerm := globalCurrentTerm + 1;
     }
     
     
     
}

\*electable := Tail(log).term > Tail(logs[self]).term \/
\*                  (Tail(log).term = Tail(logs[self]).term /\ Len(logs[self]) > Len(log));
\*     if (TRUE) {
\*         print <<"electable", electable>>;
\*     };



process (Node \in NODES)
{
pr0: print <<"starting process: ", self, logs[self]>>;

pr1: call instantElection();
}



}
*)
\* BEGIN TRANSLATION
VARIABLES globalCurrentTerm, rVals, logs, states, pc, stack, numElectMe, 
          curNode

vars == << globalCurrentTerm, rVals, logs, states, pc, stack, numElectMe, 
           curNode >>

ProcSet == (NODES)

Init == (* Global variables *)
        /\ globalCurrentTerm = 0
        /\ rVals = [rVal \in NODES |-> {0}]
        /\ logs = [log \in NODES |-> <<[term |-> globalCurrentTerm, value |-> VALUE]>>]
        /\ states = [state \in NODES |-> {FOLLOWER, CANDIDATE, LEADER}]
        (* Procedure instantElection *)
        /\ numElectMe = [ self \in ProcSet |-> 0]
        /\ curNode = [ self \in ProcSet |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "pr0"]

el0(self) == /\ pc[self] = "el0"
             /\ IF curNode[self] <= NUM_NODES
                   THEN /\ LET myTerm == Last((logs[self])).term IN
                             LET theirTerm == Last((logs[curNode[self]])).term IN
                               IF myTerm > theirTerm \/ (theirTerm = myTerm /\ Len(logs[self]) >= Len(logs[curNode[self]]))
                                  THEN /\ numElectMe' = [numElectMe EXCEPT ![self] = numElectMe[self] + 1]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED numElectMe
                        /\ curNode' = [curNode EXCEPT ![self] = curNode[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "el0"]
                        /\ UNCHANGED globalCurrentTerm
                   ELSE /\ PrintT(<<"numElectMe: ", self, numElectMe[self]>>)
                        /\ IF numElectMe[self] * 2 > NUM_NODES
                              THEN /\ globalCurrentTerm' = globalCurrentTerm + 1
                              ELSE /\ TRUE
                                   /\ UNCHANGED globalCurrentTerm
                        /\ pc' = [pc EXCEPT ![self] = "Error"]
                        /\ UNCHANGED << numElectMe, curNode >>
             /\ UNCHANGED << rVals, logs, states, stack >>

instantElection(self) == el0(self)

pr0(self) == /\ pc[self] = "pr0"
             /\ PrintT(<<"starting process: ", self, logs[self]>>)
             /\ pc' = [pc EXCEPT ![self] = "pr1"]
             /\ UNCHANGED << globalCurrentTerm, rVals, logs, states, stack, 
                             numElectMe, curNode >>

pr1(self) == /\ pc[self] = "pr1"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "instantElection",
                                                      pc        |->  "Done",
                                                      numElectMe |->  numElectMe[self],
                                                      curNode   |->  curNode[self] ] >>
                                                  \o stack[self]]
             /\ numElectMe' = [numElectMe EXCEPT ![self] = 0]
             /\ curNode' = [curNode EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "el0"]
             /\ UNCHANGED << globalCurrentTerm, rVals, logs, states >>

Node(self) == pr0(self) \/ pr1(self)

Next == (\E self \in ProcSet: instantElection(self))
           \/ (\E self \in NODES: Node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

==========================================================================================
\* This is the formal specification for the Raft consensus algorithm in MongoDB

\*EXTENDS Naturals, FiniteSets, Sequences, TLC
\*
\*\* The set of server IDs
\*CONSTANTS Server
\*
\*\* The set of requests that can go into the log
\*CONSTANTS Value
\*
\*\* Server states.
\*\* Candidate is not used, but this is fine.
\*CONSTANTS Follower, Candidate, Leader
\*
\*\* A reserved value.
\*CONSTANTS Nil
\*
\*----
\*\* Global variables
\*
\*\* The server's term number.
\*VARIABLE globalCurrentTerm
\*
\*----
\*\* The following variables are all per server (functions with domain Server).
\*
\*\* The server's state (Follower, Candidate, or Leader).
\*VARIABLE state
\*
\*\* The commit point learned by each server.
\*VARIABLE commitPoint
\*
\*electionVars == <<globalCurrentTerm, state>>
\*serverVars == <<electionVars, commitPoint>>
\*
\*\* A Sequence of log entries. The index into this sequence is the index of the
\*\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\*\* with index 1, so be careful not to use that!
\*VARIABLE log
\*logVars == <<log>>
\*
\*\* End of per server variables.
\*----
\*
\*\* All variables; used for stuttering (asserting state hasn't changed).
\*vars == <<serverVars, logVars>>
\*
\*(*
\*--algorithm MongoRaft {
\*    \* term of the last entry in a log.
\*    macro GetTerm(xlog, index, term) {
\*        if (index = 0) {
\*            term := 0;
\*        } else {
\*            term := xlog[index].term;
\*        };
\*    }
\*    
\*    macro LastTerm(xlog, term) {
\*        GetTerm(xlog, Len(xlog), term);
\*    }
\*}
\**)
