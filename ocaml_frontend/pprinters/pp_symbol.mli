open Cerb_symbol

val pp_identifier: ?clever:bool -> Identifier.t -> PPrint.document

val to_string: Sym.t -> string
val to_string_pretty: ?is_human:bool -> Sym.t -> string

(** print_nums is false by default *)
val to_string_pretty_cn: ?print_nums:bool -> Sym.t -> string

val pp_prefix: prefix -> PPrint.document
