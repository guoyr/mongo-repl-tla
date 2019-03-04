---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707886372311000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707886372312000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707886372313000 == 
1..3
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707886372314000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707886372315000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707886372316000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707886372317000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707886372318000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:58:06 EST 2019 by guo
