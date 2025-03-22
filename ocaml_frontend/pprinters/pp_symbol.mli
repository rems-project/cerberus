open Symbol


val to_string: sym -> string
val to_string_pretty: ?is_human:bool -> sym -> string

(** print_nums is false by default *)
val to_string_pretty_cn: ?print_nums:bool -> sym -> string


val pp_prefix: prefix -> PPrint.document



val pp_identifier: ?clever:bool -> Symbol.identifier -> PPrint.document

