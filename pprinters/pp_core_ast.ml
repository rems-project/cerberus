open Core

open Pp_prelude
open Pp_ast
open Colour

module P = PPrint

let isatty = ref false

let pp_symbol sym =
  !^ (ansi_format [Blue] (Pp_symbol.to_string_pretty sym))


let rec dtree_of_cabs_expression (CabsExpression (loc, expr)) =


(*
let rec dtree_of_core_object_type = function
 | OTy_integer ->
     Dleaf (pp_ctor "OTy_integer")
 | OTy_floating ->
     Dleaf (pp_ctor "OTy_floating")
 | OTy_pointer ->
     Dleaf (pp_ctor "OTy_pointr")
(*
 | OTy_cfunction of maybe core_object_type * list core_object_type
     (* the return type is Nothing for void functions *)
     (* NOTE: the types are core object type (instead of ctypes), because in the elaborated Core we have forgotten
        about the latter since the signature of procedure have core types. *)
*)
 | OTy_cfunction of maybe core_object_type (* return type *) * nat (* number of params *) * bool (* isVariadic *)
 | OTy_array oTy ->
     Dnode
 | OTy_struct sym ->
     Dleaf (pp_ctor "OTy_struct" ^^ Pp.pp_symbol sym)
 | OTy_union sym ->
     Dleaf (pp_ctor "OTy_union" ^^ Pp.pp_symbol sym)
*)


let rec dtree_ofgeneric_object_value = function
 | OVinteger ival ->
     Dleaf (pp_ctor "OVinteger" ^^^ !^ "TODO(ival)")
 | OVfloating fval ->
     Dleaf (pp_ctor "OVfloating" ^^^ !^ "TODO(fval)")
 | OVpointer ptrval ->
     Dleaf (pp_ctor "OVpointer" ^^^ !^ "TODO(ptrval)")
 | OVcfunction nm ->
     Dleaf (pp_ctor "OVcfunction" ^^^ !^ "TODO(nm)")
(*
 | OVarray of list (generic_loaded_value 'sym) (* C array value *)
 | OVstruct of Symbol.sym * list (Cabs.cabs_identifier * Mem.mem_value) (* C struct value *)
 | OVunion of Symbol.sym * Cabs.cabs_identifier * Mem.mem_value (* C union value *)
*)

and dtree_of_generic_loaded_value = function
 | LVspecified oval ->
     failwith "LVspecified"
 | LVunspecified ty ->
     failwith "LVunspecified"
