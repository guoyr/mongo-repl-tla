---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707564450271000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707564450272000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707564450273000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707564450274000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707564450275000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707564450276000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707564451277000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707564451278000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:52:44 EST 2019 by guo
