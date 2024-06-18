open Symbol


val to_string: sym -> string
val to_string_pretty: ?is_human:bool -> sym -> string

val to_string_cn: sym -> string
val to_string_pretty_cn: sym -> string


val pp_prefix: prefix -> PPrint.document



val pp_identifier: ?clever:bool -> Symbol.identifier -> PPrint.document


val pp_cn_sym_nums: bool ref

