---- MODULE MC ----
EXTENDS RaftMongo, TLC

\* CONSTANT definitions @modelParameterConstants:0VALUE
const_1551707464340263000 == 
42
----

\* CONSTANT definitions @modelParameterConstants:1TERMS
const_1551707464340264000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2NODES
const_1551707464340265000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:3NUM_NODES
const_1551707464340266000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:4FOLLOWER
const_1551707464340267000 == 
"follower"
----

\* CONSTANT definitions @modelParameterConstants:5LEADER
const_1551707464340268000 == 
"leader"
----

\* CONSTANT definitions @modelParameterConstants:6CANDIDATE
const_1551707464340269000 == 
"candidate"
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1551707464340270000 ==
Spec
----
=============================================================================
\* Modification History
\* Created Mon Mar 04 08:51:04 EST 2019 by guo
