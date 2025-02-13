
(* Simplified memory model inteface for CN *)

Module Type Memory.
    Parameter integer_value : Type.
    Parameter floating_value : Type.
    Parameter pointer_value : Type.
    Parameter mem_value : Type.
End Memory.
