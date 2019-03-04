---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707967558319000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707967558320000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707967558321000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707967558322000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707967558323000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707967558324000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707967558325000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707967558326000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:59:27 EST 2019 by guo
