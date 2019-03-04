--------------------------------- MODULE RaftMongo ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* module parameters (aka constants):
CONSTANT NODES \* sequence of nodes in a replset.
CONSTANT NUM_NODES \* length of the NODES
CONSTANT VALUE \* arbitrary value to put in a log
CONSTANT FOLLOWER, LEADER, CANDIDATE \* keys for indicating the state of a node.

(*
--algorithm mongoRaft {
variable
    globalCurrentTerm = 0,
    \* Global return values;
    rVals = [rVal \in NODES |-> {0}],
    logs = [log \in NODES |-> <<[term |-> globalCurrentTerm, value |-> VALUE]>>],
    states = [state \in NODES |-> FOLLOWER]; \* Start all notes in FOLLOWER state.
define {
    Last(s) == s[Len(s)]
    LastTerm(s) == Last(s).term
}

macro canElectMe(myLogs, theirLogs, numElectMe) {
    with (myTerm = LastTerm(myLogs), theirTerm = LastTerm(theirLogs)) {    
        when (myTerm > theirTerm \/ (theirTerm = myTerm /\ Len(logs[self]) >= Len(logs[curNode])));
        numElectMe := numElectMe + 1;
    }
}

procedure appendOplog()
{
ao0:
    print <<self, "doing append oplog:", states>>;
    \* Randomly select a sync source.
    with (ssNode \in NODES,
          myLog = logs[self],
          ssLog = logs[ssNode],
          myLastTerm = LastTerm(myLog),
          ssLastTerm = LastTerm(ssLog)) {
        when Len(myLog) < Len(ssLog) /\ myLastTerm = ssLastTerm;
        logs[self] := Append(myLog, Last(ssLog));
        print <<self, "appended oplog:", Last(ssLog)>>;
    };
    return;
}

procedure clientWrite()
{
cw0:
    print <<self, "doing client write:", states>>;
    when (states[self] = LEADER);
    with (logEntry = [term |-> globalCurrentTerm, value |-> VALUE]) {
        logs[self] := Append(logs[self], logEntry);
        print <<self, "wrote log entry", logEntry>>;
    };
    return;
}

procedure instantElection() 
variables numElectMe = 0, curNode = 1;
{
el0:
    while (curNode <= NUM_NODES) {
       canElectMe(logs[self], logs[curNode], numElectMe);
       curNode := curNode + 1;
    };
    print <<self, "doing instant election:", numElectMe, states>>;

    when (numElectMe * 2 > NUM_NODES);
    globalCurrentTerm := globalCurrentTerm + 1;
    states := [node \in NODES |-> IF node = self THEN LEADER ELSE FOLLOWER];
    print <<self, "won election", globalCurrentTerm, states>>;
    return;
}

process (Node \in NODES)
{
proc:
    either {
        call appendOplog();
    } or {
        call instantElection();
    } or {
        call clientWrite();
    }
} \* end process
} \* end --algorithm mongoRaft
*)
\* BEGIN TRANSLATION
VARIABLES globalCurrentTerm, rVals, logs, states, pc, stack

(* define statement *)
Last(s) == s[Len(s)]
LastTerm(s) == Last(s).term

VARIABLES numElectMe, curNode

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
        /\ pc = [self \in ProcSet |-> "proc"]

ao0(self) == /\ pc[self] = "ao0"
             /\ PrintT(<<self, "doing append oplog:", states>>)
             /\ \E ssNode \in NODES:
                  LET myLog == logs[self] IN
                    LET ssLog == logs[ssNode] IN
                      LET myLastTerm == LastTerm(myLog) IN
                        LET ssLastTerm == LastTerm(ssLog) IN
                          /\ Len(myLog) < Len(ssLog) /\ myLastTerm = ssLastTerm
                          /\ logs' = [logs EXCEPT ![self] = Append(myLog, Last(ssLog))]
                          /\ PrintT(<<self, "appended oplog:", Last(ssLog)>>)
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << globalCurrentTerm, rVals, states, numElectMe, 
                             curNode >>

appendOplog(self) == ao0(self)

cw0(self) == /\ pc[self] = "cw0"
             /\ PrintT(<<self, "doing client write:", states>>)
             /\ (states[self] = LEADER)
             /\ LET logEntry == [term |-> globalCurrentTerm, value |-> VALUE] IN
                  /\ logs' = [logs EXCEPT ![self] = Append(logs[self], logEntry)]
                  /\ PrintT(<<self, "wrote log entry", logEntry>>)
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << globalCurrentTerm, rVals, states, numElectMe, 
                             curNode >>

clientWrite(self) == cw0(self)

el0(self) == /\ pc[self] = "el0"
             /\ IF curNode[self] <= NUM_NODES
                   THEN /\ LET myTerm == LastTerm((logs[self])) IN
                             LET theirTerm == LastTerm((logs[curNode[self]])) IN
                               /\ (myTerm > theirTerm \/ (theirTerm = myTerm /\ Len(logs[self]) >= Len(logs[curNode[self]])))
                               /\ numElectMe' = [numElectMe EXCEPT ![self] = numElectMe[self] + 1]
                        /\ curNode' = [curNode EXCEPT ![self] = curNode[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "el0"]
                        /\ UNCHANGED << globalCurrentTerm, states, stack >>
                   ELSE /\ PrintT(<<self, "doing instant election:", numElectMe[self], states>>)
                        /\ (numElectMe[self] * 2 > NUM_NODES)
                        /\ globalCurrentTerm' = globalCurrentTerm + 1
                        /\ states' = [node \in NODES |-> IF node = self THEN LEADER ELSE FOLLOWER]
                        /\ PrintT(<<self, "won election", globalCurrentTerm', states'>>)
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ numElectMe' = [numElectMe EXCEPT ![self] = Head(stack[self]).numElectMe]
                        /\ curNode' = [curNode EXCEPT ![self] = Head(stack[self]).curNode]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << rVals, logs >>

instantElection(self) == el0(self)

proc(self) == /\ pc[self] = "proc"
              /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "appendOplog",
                                                             pc        |->  "Done" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "ao0"]
                    /\ UNCHANGED <<numElectMe, curNode>>
                 \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "instantElection",
                                                             pc        |->  "Done",
                                                             numElectMe |->  numElectMe[self],
                                                             curNode   |->  curNode[self] ] >>
                                                         \o stack[self]]
                    /\ numElectMe' = [numElectMe EXCEPT ![self] = 0]
                    /\ curNode' = [curNode EXCEPT ![self] = 1]
                    /\ pc' = [pc EXCEPT ![self] = "el0"]
                 \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "clientWrite",
                                                             pc        |->  "Done" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "cw0"]
                    /\ UNCHANGED <<numElectMe, curNode>>
              /\ UNCHANGED << globalCurrentTerm, rVals, logs, states >>

Node(self) == proc(self)

Next == (\E self \in ProcSet:  \/ appendOplog(self) \/ clientWrite(self)
                               \/ instantElection(self))
           \/ (\E self \in NODES: Node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
==========================================================================================
