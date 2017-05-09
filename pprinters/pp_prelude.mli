module P = PPrint

val (!^): string -> P.document
val (^^): P.document -> P.document -> P.document
val (^/^): P.document -> P.document -> P.document

val (^^^): P.document -> P.document -> P.document
val comma_list: ('a -> P.document) -> 'a list -> P.document
val semi_list: ('a -> P.document) -> 'a list -> P.document
