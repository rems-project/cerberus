open Symbol


val to_string: ?compact:bool -> sym -> string
val to_string_pretty: ?compact:bool -> sym -> string


val pp_prefix: prefix -> PPrint.document



val pp_identifier: Symbol.identifier -> PPrint.document
