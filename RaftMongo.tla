--------------------------------- MODULE RaftMongo ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT NODES \* sequence of nodes in a replset.
CONSTANT NUM_NODES

CONSTANT VALUE

CONSTANT TERMS

CONSTANTS FOLLOWER, LEADER, CANDIDATE

Last(s) == s[Len(s)]

LastTerm(s) == Last(s).term

(*
--algorithm mongoRaft {
variable
    globalCurrentTerm = 0,
    \* Global return values;
    rVals = [rVal \in NODES |-> {0}],
    logs = [log \in NODES |-> <<[term |-> globalCurrentTerm, value |-> VALUE]>>],
    states = [state \in NODES |-> FOLLOWER]; \* Start all notes in FOLLOWER state.

macro canElectMe(myLogs, theirLogs, numElectMe) {
    with (myTerm = LastTerm(myLogs), theirTerm = LastTerm(theirLogs)) {    
        when (myTerm > theirTerm \/ (theirTerm = myTerm /\ Len(logs[self]) >= Len(logs[curNode])));
        numElectMe := numElectMe + 1;
    }
}

procedure appendOplog()
{
ao0:
    print <<self, "doing append oplog:">>;
    \* Randomly select a sync source.
    with (ssNode \in NODES, myLogs = logs[self]) {
       with (ssLogs = logs[ssNode],
             myLastTerm = LastTerm(myLogs),
             ssLastTerm = LastTerm(ssLogs)) {

           when Len(myLogs) < Len(ssLogs) /\ myLastTerm = ssLastTerm;
           logs[self] := Append(myLogs, Last(ssLogs));
           print <<self, "appended oplog:", Last(ssLogs)>>;
       };
    };
}

procedure clientWrite()
{
cw0:
    print <<self, "doing client write:", states[self]>>;
    when (states[self] = LEADER);
    with (logEntry = [term |-> globalCurrentTerm, value |-> VALUE]) {
        logs[self] := Append(logs[self], logEntry);
        print <<self, "appended log entry", logEntry>>;
    };
}

procedure instantElection() 
variables numElectMe = 0, curNode = 1;
{
el0:
    while (curNode <= NUM_NODES) {
       canElectMe(logs[self], logs[curNode], numElectMe);
       curNode := curNode + 1;
    };
\*     print<<"num elected me: ", numElectMe, "I am: ", self>>;
    print <<self, "doing instant election:">>;
     
    when (numElectMe * 2 > NUM_NODES);
    globalCurrentTerm := globalCurrentTerm + 1;
    states := [[state \in NODES |-> FOLLOWER] EXCEPT ![self] = LEADER];
\*    print <<self, "won election; states:", states>>;
}

process (Node \in NODES)
{
proc1:
    call instantElection();
proc2:    
    call appendOplog();
proc3:
    call clientWrite();
} \* end process
} \* end --algorithm mongoRaft
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
        /\ states = [state \in NODES |-> FOLLOWER]
        (* Procedure instantElection *)
        /\ numElectMe = [ self \in ProcSet |-> 0]
        /\ curNode = [ self \in ProcSet |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "proc1"]

ao0(self) == /\ pc[self] = "ao0"
             /\ PrintT(<<self, "doing append oplog:">>)
             /\ \E ssNode \in NODES:
                  LET myLogs == logs[self] IN
                    LET ssLogs == logs[ssNode] IN
                      LET myLastTerm == LastTerm(myLogs) IN
                        LET ssLastTerm == LastTerm(ssLogs) IN
                          /\ Len(myLogs) < Len(ssLogs) /\ myLastTerm = ssLastTerm
                          /\ logs' = [logs EXCEPT ![self] = Append(myLogs, Last(ssLogs))]
                          /\ PrintT(<<self, "appended oplog:", Last(ssLogs)>>)
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << globalCurrentTerm, rVals, states, stack, 
                             numElectMe, curNode >>

appendOplog(self) == ao0(self)

cw0(self) == /\ pc[self] = "cw0"
             /\ PrintT(<<self, "doing client write:", states[self]>>)
             /\ (states[self] = LEADER)
             /\ LET logEntry == [term |-> globalCurrentTerm, value |-> VALUE] IN
                  /\ logs' = [logs EXCEPT ![self] = Append(logs[self], logEntry)]
                  /\ PrintT(<<self, "appended log entry", logEntry>>)
             /\ pc' = [pc EXCEPT ![self] = "Error"]
             /\ UNCHANGED << globalCurrentTerm, rVals, states, stack, 
                             numElectMe, curNode >>

clientWrite(self) == cw0(self)

el0(self) == /\ pc[self] = "el0"
             /\ IF curNode[self] <= NUM_NODES
                   THEN /\ LET myTerm == LastTerm((logs[self])) IN
                             LET theirTerm == LastTerm((logs[curNode[self]])) IN
                               /\ (myTerm > theirTerm \/ (theirTerm = myTerm /\ Len(logs[self]) >= Len(logs[curNode[self]])))
                               /\ numElectMe' = [numElectMe EXCEPT ![self] = numElectMe[self] + 1]
                        /\ curNode' = [curNode EXCEPT ![self] = curNode[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "el0"]
                        /\ UNCHANGED << globalCurrentTerm, states >>
                   ELSE /\ PrintT(<<self, "doing instant election:">>)
                        /\ (numElectMe[self] * 2 > NUM_NODES)
                        /\ globalCurrentTerm' = globalCurrentTerm + 1
                        /\ states' = [[state \in NODES |-> FOLLOWER] EXCEPT ![self] = LEADER]
                        /\ pc' = [pc EXCEPT ![self] = "Error"]
                        /\ UNCHANGED << numElectMe, curNode >>
             /\ UNCHANGED << rVals, logs, stack >>

instantElection(self) == el0(self)

proc1(self) == /\ pc[self] = "proc1"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "instantElection",
                                                        pc        |->  "proc2",
                                                        numElectMe |->  numElectMe[self],
                                                        curNode   |->  curNode[self] ] >>
                                                    \o stack[self]]
               /\ numElectMe' = [numElectMe EXCEPT ![self] = 0]
               /\ curNode' = [curNode EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "el0"]
               /\ UNCHANGED << globalCurrentTerm, rVals, logs, states >>

proc2(self) == /\ pc[self] = "proc2"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "appendOplog",
                                                        pc        |->  "proc3" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "ao0"]
               /\ UNCHANGED << globalCurrentTerm, rVals, logs, states, 
                               numElectMe, curNode >>

proc3(self) == /\ pc[self] = "proc3"
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "clientWrite",
                                                        pc        |->  "Done" ] >>
                                                    \o stack[self]]
               /\ pc' = [pc EXCEPT ![self] = "cw0"]
               /\ UNCHANGED << globalCurrentTerm, rVals, logs, states, 
                               numElectMe, curNode >>

Node(self) == proc1(self) \/ proc2(self) \/ proc3(self)

Next == (\E self \in ProcSet:  \/ appendOplog(self) \/ clientWrite(self)
                               \/ instantElection(self))
           \/ (\E self \in NODES: Node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
==========================================================================================
