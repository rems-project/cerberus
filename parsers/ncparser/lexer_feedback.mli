(* Created by Victor Gomes 2017-10-04 *)

(* Based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
   "A simple, possibly correct LR parser for C11" *)

type context
val save_context: unit -> context
val restore_context: context -> unit

val declare_typedefname: string -> unit
val declare_varname: string -> unit
val is_typedefname: string -> bool

type declarator

val identifier: declarator -> string
val cabs_of_declarator: declarator -> Cabs.declarator

val pointer_decl: Cabs.pointer_declarator -> declarator -> declarator
val identifier_decl: Location_ocaml.t -> string -> declarator
val declarator_decl: declarator -> declarator
val array_decl: Cabs.array_declarator -> declarator -> declarator
val fun_decl: Cabs.parameter_type_list -> context -> declarator -> declarator

val reinstall_function_context: declarator -> unit
