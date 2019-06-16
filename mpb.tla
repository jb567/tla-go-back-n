-------------------------------- MODULE mpb --------------------------------
EXTENDS Sequences, Naturals

CONSTANT MESSAGE, WINDOW_SIZE

VARIABLES index, output, buffer, n
vars == <<index, output, buffer, n>>
\* MULTIPLACE BUFFER

SendN == /\ buffer = <<>>
         /\ n = 0
         /\ LET q == CHOOSE q \in 1..WINDOW_SIZE : index + q <= Len(MESSAGE)
            IN /\ buffer' = SubSeq(MESSAGE,index,q)
               /\ n' = q

ReceiveN == /\ buffer # <<>>
            /\ output' = output \o buffer
            /\ buffer = <<>>

MovePlace == /\ buffer = <<>>
             /\ n # 0
             /\ index' = index + n
             /\ n = 0



Init == /\ index = 1
        /\ output = <<>>
        /\ buffer = <<>>
        /\ n = 0

Next == \/ SendN /\ UNCHANGED <<output, index>>
        \/ ReceiveN /\ UNCHANGED <<n, index>>
        \/ MovePlace /\ UNCHANGED <<output>>
        
Spec == /\ Init
        /\ [][Next]_vars
        /\ <>[](
=============================================================================
\* Modification History
\* Last modified Mon Jun 03 12:24:24 NZST 2019 by jb567
\* Created Mon Jun 03 12:09:13 NZST 2019 by jb567
