---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707817267303000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707817267304000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707817267305000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707817267306000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707817267307000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707817267308000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707817267309000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707817267310000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:56:57 EST 2019 by guo
