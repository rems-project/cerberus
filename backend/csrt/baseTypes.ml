open List
open PPrint
open Pp_tools
module Loc=Locations


type field_access = {loc : Loc.t; struct_type: Sym.t; field: Id.t}
let field_accesses_subst sym with_it = 
  List.map (fun a -> {a with struct_type = Sym.subst sym with_it a.struct_type})
let pp_field_accesses accesses =
  separate_map dot (fun a -> Id.pp a.field) accesses

type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | Struct of Sym.t
  (* | OpenStruct of Sym.t * (Sym.t * Sym.t) list *)
  | StructField of Sym.t * field_access list

let is_unit = function Unit -> true | _ -> false
let is_bool = function Bool -> true | _ -> false
let is_int = function Int -> true | _ -> false
let is_loc = function Loc -> true | _ -> false
let is_array = function Array -> true | _ -> false
let is_struct = function Struct s -> Some s | _ -> None
(* let is_openstruct = function OpenStruct (s,f) -> Some (s,f) | _ -> None *)
let is_structfield = function 
  | StructField (p,access) -> Some (p,access) 
  | _ -> None


let rec pp = function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "int"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> parens ((!^ "list") ^^^ pp bt)
  | Tuple nbts -> parens (!^ "tuple" ^^^ flow_map (break 1) pp (nbts))
  | Struct sym -> parens (!^ "struct" ^^^ Sym.pp sym)
  (* | OpenStruct (sym,fields) ->
   *    let pp_field (s1,s2) = parens (Sym.pp s1 ^^^ Sym.pp s2) in
   *    (!^ "open-struct" ^^^ Sym.pp sym ^^^ 
   *       brackets (flow_map (break 1) pp_field fields)) *)
  | StructField (p,a) -> 
     Sym.pp p ^^ dot ^^ pp_field_accesses a


let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst sym with_sym = function
  | Struct s -> Struct (Sym.subst sym with_sym s)
  (* | OpenStruct (s, flds) -> 
   *    let flds = List.map (fun (id,s) -> (id, Sym.subst sym with_sym s)) flds in
   *    OpenStruct (Sym.subst sym with_sym s, flds) *)
  | StructField (p,accesses) ->
     StructField (Sym.subst sym with_sym p,
                  field_accesses_subst sym with_sym accesses)
  | bt -> bt


