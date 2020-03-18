open Symbolic

val pp_symbolic: ('a -> PPrint.document) -> ('b -> PPrint.document) -> ('a, 'b) symbolic -> PPrint.document
