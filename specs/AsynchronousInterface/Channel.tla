-------------------------- MODULE Channel -------------------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE channel
TypeInvariant == channel \in [ val: Data, rdy: {0,1}, ack: {0,1} ]
-------------------------------------------------------------------------------
Init == /\ TypeInvariant
        /\ channel.ack = channel.rdy
Send(d) == /\ channel.rdy = channel.ack
           /\ channel' = [channel EXCEPT !.val = d, !.rdy = 1 - @]
Rcv == /\ channel.rdy /= channel.ack
       /\ channel' = [channel EXCEPT !.ack = 1 - @]
Next == ( \exists d \in Data : Send(d)) \/ Rcv
Spec == Init /\ [][Next]_channel
-------------------------------------------------------------------------------
THEOREM  Spec => []TypeInvariant
===============================================================================