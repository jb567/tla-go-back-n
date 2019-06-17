------------------------------ MODULE dataWire ------------------------------
EXTENDS Sequences, TLC, Naturals

CONSTANTS CORRUPT_DATA

(* --algorithm DataWire
variables
    input = <<>>,
    output = <<>>;

define

DropRandom(input1) == LET n == CHOOSE n \in 1..Len(input1) : TRUE
                     IN SubSeq(input1, 1, n) \o SubSeq(input1, n+2, Len(input1))
CorruptRandom(input2) == LET n == CHOOSE n \in 1..Len(input2) : TRUE
                        IN SubSeq(input2, 1, n) \o <<CORRUPT_DATA>> \o SubSeq(input2, n+2, Len(input2))



RECURSIVE CorruptLen2(_)
CorruptLen2(i) == IF i = 0 THEN <<>>
                  ELSE <<CORRUPT_DATA>> \o CorruptLen2(i-1)
CorruptLen(input3) == CorruptLen2(Len(input3))

end define;

fair+ process sendNormally = "Send"
begin A:
while TRUE do
    await input # <<>> /\ output = <<>>;
    output := input;
    input := <<>>;
end while;
end process;

process dropRandomPacket = "Drop Rand"
begin A:
while TRUE do
    await input # <<>> /\ output = <<>>;
    output := DropRandom(input);
    input := <<>>;
end while;
end process;

process dropAllPackets = "Drop All"
begin A:
while TRUE do
    await input # <<>> /\ output = <<>>;
    input := <<>>;
end while;
end process;

process corruptRandom = "corruptRandom"
begin A:
while TRUE do
    await input # <<>> /\ output = <<>>;
    output := CorruptRandom(input);
    input := <<>>;
end while;
end process;

process corruptAllPackets = "corruptAll"
begin A:
while TRUE do
    await input # <<>> /\ output = <<>>;
    output := CorruptLen(input);
    input := <<>>;
end while;
end process;

\* Shuffle was not attempted due to complexity, and corruption / dropping solves a similar problem 
end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process sendNormally at line 29 col 1 changed to A_
\* Label A of process dropRandomPacket at line 38 col 1 changed to A_d
\* Label A of process dropAllPackets at line 47 col 1 changed to A_dr
\* Label A of process corruptRandom at line 55 col 1 changed to A_c
VARIABLES input, output

(* define statement *)
DropRandom(input1) == LET n == CHOOSE n \in 1..Len(input1) : TRUE
                     IN SubSeq(input1, 1, n) \o SubSeq(input1, n+2, Len(input1))
CorruptRandom(input2) == LET n == CHOOSE n \in 1..Len(input2) : TRUE
                        IN SubSeq(input2, 1, n) \o <<CORRUPT_DATA>> \o SubSeq(input2, n+2, Len(input2))



RECURSIVE CorruptLen2(_)
CorruptLen2(i) == IF i = 0 THEN <<>>
                  ELSE <<CORRUPT_DATA>> \o CorruptLen2(i-1)
CorruptLen(input3) == CorruptLen2(Len(input3))


vars == << input, output >>

ProcSet == {"Send"} \cup {"Drop Rand"} \cup {"Drop All"} \cup {"corruptRandom"} \cup {"corruptAll"}

Init == (* Global variables *)
        /\ input = <<>>
        /\ output = <<>>

sendNormally == /\ input # <<>> /\ output = <<>>
                /\ output' = input
                /\ input' = <<>>

dropRandomPacket == /\ input # <<>> /\ output = <<>>
                    /\ output' = DropRandom(input)
                    /\ input' = <<>>

dropAllPackets == /\ input # <<>> /\ output = <<>>
                  /\ input' = <<>>
                  /\ UNCHANGED output

corruptRandom == /\ input # <<>> /\ output = <<>>
                 /\ output' = CorruptRandom(input)
                 /\ input' = <<>>

corruptAllPackets == /\ input # <<>> /\ output = <<>>
                     /\ output' = CorruptLen(input)
                     /\ input' = <<>>

Next == sendNormally \/ dropRandomPacket \/ dropAllPackets \/ corruptRandom
           \/ corruptAllPackets

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(sendNormally)

\* END TRANSLATION
Fairness == /\ SF_vars(sendNormally)
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 00:59:40 NZST 2019 by jb567
\* Created Sat Jun 01 15:52:42 NZST 2019 by jb567
