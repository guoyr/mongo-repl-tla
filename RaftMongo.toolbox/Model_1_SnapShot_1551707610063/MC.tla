---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707607047279000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707607047280000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707607047281000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707607047282000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707607047283000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707607047284000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707607047285000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707607047286000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:53:27 EST 2019 by guo
