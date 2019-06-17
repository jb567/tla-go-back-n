-------------------------------- MODULE tcp --------------------------------
VARIABLES senderState, receiverState
vars == <<senderState, receiverState>>

SYN == /\ senderState = "WAITING"
       /\ receiverState = "WAITING"
       /\ senderState' = "OPENING"

SYNACK == /\ senderState = "OPENING"
          /\ receiverState = "WAITING"
          /\ receiverState' = "OPEN"

ACK == /\ senderState = "OPENING"
       /\ receiverState = "OPEN"
       /\ senderState' = "OPEN"

Next == \/ SYN /\ UNCHANGED <<receiverState>>
        \/ SYNACK /\ UNCHANGED <<senderState>>
        \/ ACK /\ UNCHANGED <<receiverState>>

Init == /\ senderState = "WAITING"
        /\ receiverState = "WAITING"

Spec == /\ Init
        /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Jun 17 02:06:33 NZST 2019 by jb567
\* Created Mon Jun 17 02:01:08 NZST 2019 by jb567
