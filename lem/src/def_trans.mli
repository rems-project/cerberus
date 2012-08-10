open Typed_ast
type def_macro = Name.t list -> env -> def -> (env * def list) option

val list_to_mac : def_macro list -> def_macro

val process_defs : Name.t list -> def_macro -> Name.t -> env -> def list -> (env * def list)

val remove_vals : def_macro
val remove_indrelns : def_macro
val remove_opens : def_macro
val remove_classes : def_macro
val instance_to_module : def_macro
val type_annotate_definitions : def_macro

val prune_target_bindings : Ast.target -> def list -> def list

(*
val flatten_modules : def_macro
*)
