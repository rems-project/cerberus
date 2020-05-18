open List
open PPrint
open Pp_tools
module Loc=Locations


type field_access = {loc : Loc.t; struct_type: Sym.t; field: Id.t}
let field_accesses_subst sym with_it = 
  List.map (fun a -> {a with struct_type = Sym.subst sym with_it a.struct_type})
let pp_field_accesses accesses =
  separate_map dot (fun a -> Id.pp a.field) accesses

type field = Sym.t * (Cerb_frontend.Ctype.ctype * (Sym.t option))
type open_struct = {typ : Sym.t; fields : field list}

type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | Struct of Sym.t
  | StructField of Sym.t * field_access list
  | FunctionPointer of Sym.t
  | StoredStruct of open_struct

let is_loc = function Loc -> true | _ -> false



let rec pp = function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "int"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> parens ((!^ "list") ^^^ pp bt)
  | Tuple nbts -> parens (!^ "tuple" ^^^ flow_map (break 1) pp (nbts))
  | Struct sym -> parens (!^ "struct" ^^^ Sym.pp sym)
  | StructField (p,a) -> 
     parens (!^"structfield" ^^^ Sym.pp p ^^ dot ^^ pp_field_accesses a)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)
  | StoredStruct s ->
     let pp_field_names =
       flow_map (comma ^^ break 1) 
         (fun (f,(_,mfvar)) -> 
           match mfvar with
           | Some fvar -> parens (Sym.pp f ^^^ arrow ^^^ Sym.pp fvar) 
           | None -> parens (Sym.pp f ^^^ arrow ^^^ !^"uninitialised") 
         )
         s.fields
     in
     Colour.pp_ansi_format [Red;Bold] 
       (parens (!^"opened struct" ^^^ Sym.pp s.typ  ^^^ parens pp_field_names))


let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)




let subst_fields sym with_it fields = 
  List.map (fun (f,(ct,fvar)) -> 
      let f = Sym.subst sym with_it f in
      let fvar = match fvar with
        | None -> None
        | Some fvar -> Some (Sym.subst sym with_it fvar)
      in
      (f, (ct, fvar))
    ) fields

let subst sym with_sym = function
  | Struct s -> Struct (Sym.subst sym with_sym s)
  | StructField (p,accesses) ->
     StructField (Sym.subst sym with_sym p,
                  field_accesses_subst sym with_sym accesses)
  | FunctionPointer p ->
     FunctionPointer (Sym.subst sym with_sym p)
  | StoredStruct s ->
     StoredStruct {typ = Sym.subst sym with_sym s.typ;
                   fields = subst_fields sym with_sym s.fields}
  | bt -> bt


