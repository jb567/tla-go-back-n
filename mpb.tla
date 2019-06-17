-------------------------------- MODULE mpb --------------------------------
EXTENDS Sequences, Naturals

Min(x,y) == IF x < y THEN x ELSE y


CONSTANT MESSAGE, WINDOW_SIZE

VARIABLES index, output, buffer, n
vars == <<index, output, buffer, n>>
\* MULTIPLACE BUFFER

SendN == /\ buffer = <<>>
         /\ n = 0
         /\ n' \in index..Min(index+WINDOW_SIZE,Len(MESSAGE))
         /\ buffer' = SubSeq(MESSAGE,index,n'-index)

ReceiveN == /\ buffer # <<>>
            /\ output' = output \o buffer
            /\ buffer = <<>>

MovePlace == /\ buffer = <<>>
             /\ n # 0
             /\ index' = n
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

=============================================================================
\* Modification History
\* Last modified Mon Jun 17 21:59:01 NZST 2019 by jb567
\* Created Mon Jun 03 12:09:13 NZST 2019 by jb567
