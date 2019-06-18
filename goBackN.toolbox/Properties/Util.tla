-------------------------------- MODULE Util --------------------------------
EXTENDS Naturals, Sequences, TLC
CONSTANTS WINDOW_SIZE

Limit == WINDOW_SIZE*2

(* - Packets are sent with a "window" numbering system rather than a continuous system
   - The length should be at least WINDOW_SIZE * 2 in order to prevent collisions
   - It starts at an arbitrary number in order to support the SYN/SYNACK choosing numbers
   - Packet-to-index formulae are in this module in order to keep it accessible to both server
     and client*)

\* Get Packet Number in window number
GetNextPacketNumber(start, i) == IF i+1 > start + Limit THEN start ELSE i+1

\* Convert 0 indexed to packet indexing
ConvertIdx(start, idx) == (idx % Limit) + start


RECURSIVE getPackets2(_,_,_,_)
\*This converts the input at index into packets
getPackets(input,start, idx) == getPackets2(input, idx, start, WINDOW_SIZE)


getPackets2(input, idx, start, size) == IF idx > Len(input) \/ size = 0
                                        THEN <<>>
                                        ELSE << <<ConvertIdx(start,idx), input[idx]>> >> 
                                             \o getPackets2(input, idx+1, start, size-1)

(*
    Was the window provided good enough?
    trueIdxStart = where the equivalent start of the window is
    systemStart = start of the numbering system (i.e. where is 0 in the numbering system)
    idxChecked = the ackNumber we are comparing (to see if it is within the currently sending window)
    
    @returns whether the index is equivalent to one we sent
*)
InWindow(trueIdxStart, systemStart, idxChecked) == idxChecked \in {x \in trueIdxStart..(trueIdxStart+WINDOW_SIZE): ConvertIdx(systemStart,x)}

WindowPos(startIdx, idx) == IF startIdx < idx THEN idx
                            ELSE (Limit - startIdx) + idx
=============================================================================
\* Modification History
\* Last modified Tue Jun 18 21:49:55 NZST 2019 by jb567
\* Created Mon Jun 17 22:15:17 NZST 2019 by jb567
