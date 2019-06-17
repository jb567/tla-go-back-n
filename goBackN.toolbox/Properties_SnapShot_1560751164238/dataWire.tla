------------------------------ MODULE dataWire ------------------------------
EXTENDS Sequences, TLC, Naturals

CONSTANTS CORRUPT_DATA, WINDOW_SIZE

(* --algorithm DataWire
variables
    input = <<>>,
    output = <<>>;

fair+ process send = "Send"
begin A:
while TRUE do
    await input # <<>> /\ Len(output) < WINDOW_SIZE;
    output := output \o <<Head(input)>>;
    input := Tail(input);
end while;
end process;

process drop = "Drop"
begin A:
while TRUE do
    await input # <<>> /\ Len(output) < WINDOW_SIZE;
    input := Tail(input);
end while;
end process;

process corrupt = "Corrupt"
begin A:
while TRUE do
    await input # <<>> /\ Len(output) < WINDOW_SIZE;
    output := output \o <<CORRUPT_DATA>>;
    input := Tail(input);
end while;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION
\* Label A of process send at line 13 col 1 changed to A_
\* Label A of process drop at line 22 col 1 changed to A_d
VARIABLES input, output

vars == << input, output >>

ProcSet == {"Send"} \cup {"Drop"} \cup {"Corrupt"}

Init == (* Global variables *)
        /\ input = <<>>
        /\ output = <<>>

send == /\ input # <<>> /\ Len(output) < WINDOW_SIZE
        /\ output' = output \o <<Head(input)>>
        /\ input' = Tail(input)

drop == /\ input # <<>> /\ Len(output) < WINDOW_SIZE
        /\ input' = Tail(input)
        /\ UNCHANGED output

corrupt == /\ input # <<>> /\ Len(output) < WINDOW_SIZE
           /\ output' = output \o <<CORRUPT_DATA>>
           /\ input' = Tail(input)

Next == send \/ drop \/ corrupt

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(send)

\* END TRANSLATION
Fairness == /\ SF_vars(send)
            /\ SF_vars(/\ send
                       /\ output' # CORRUPT_DATA
                       /\ output'[1] = input[1])
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 17:59:07 NZST 2019 by jb567
\* Created Sat Jun 01 15:52:42 NZST 2019 by jb567
