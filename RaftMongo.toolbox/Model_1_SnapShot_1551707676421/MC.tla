---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707673407287000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707673407288000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707673407289000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707673407290000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707673407291000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707673407292000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707673407293000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707673407294000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:54:33 EST 2019 by guo
