---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551706854900255000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551706854900256000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551706854900257000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551706854900258000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551706854900259000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551706854900260000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551706854900261000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551706854900262000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:40:54 EST 2019 by guo
