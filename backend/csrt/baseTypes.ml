open List
open PPrint
open Pp_tools
module Loc=Locations

module SymSet = Set.Make(Sym)

type struct_type = S_Id of Sym.t
type var = Sym.t

type field_access = {loc : Loc.t; struct_type: struct_type; field: string}

type field = string * (Cerb_frontend.Ctype.ctype * (var option))

type openstruct = {typ : struct_type; fields : field list}

type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | Struct of struct_type
  | StructField of var * field_access list
  | FunctionPointer of var
  | OpenStruct of openstruct

let is_loc = function Loc -> true | _ -> false


let pp_field_access access =
  separate_map dot (fun a -> !^(a.field)) access


let rec pp = function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "int"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> parens ((!^ "list") ^^^ pp bt)
  | Tuple nbts -> parens (!^ "tuple" ^^^ flow_map (break 1) pp (nbts))
  | Struct (S_Id sym) -> parens (!^ "struct" ^^^ Sym.pp sym)
  | StructField (p,a) -> 
     parens (!^"structfield" ^^^ Sym.pp p ^^ dot ^^ pp_field_access a)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)
  | OpenStruct s ->
     let (S_Id typ) = s.typ in
     let pp_field_names =
       flow_map (comma ^^ break 1) 
         (fun (f,(_,mfvar)) -> 
           match mfvar with
           | Some fvar -> parens (!^f ^^^ equals ^^^ Sym.pp fvar) 
           | None -> parens (!^f ^^^ equals ^^^ !^"uninitialised") 
         )
         s.fields
     in
     Colour.pp_ansi_format [Red;Bold] 
       (parens (!^"opened struct" ^^^ Sym.pp typ  ^^^ parens pp_field_names))


let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)





let subst_var sym with_sym bt = 

  let subst_fields sym with_it fields = 
    List.map (fun (f,(ct,fvar)) -> 
        let fvar = match fvar with
          | None -> None
          | Some fvar -> Some (Sym.subst sym with_it fvar)
        in
        (f, (ct, fvar))
      ) fields
  in

  match bt with
  | FunctionPointer p -> FunctionPointer (Sym.subst sym with_sym p)
  | OpenStruct s ->
     OpenStruct {s with fields = subst_fields sym with_sym s.fields}
  | StructField (p,a) -> StructField (Sym.subst sym with_sym p, a)
  | bt -> bt


let vars_in bt = 
  match bt with
  | FunctionPointer p -> SymSet.singleton p
  | OpenStruct s -> SymSet.of_list (filter_map (fun (_,(_,f)) -> f) s.fields)
  | StructField (p,a) -> SymSet.singleton p
  | _ -> SymSet.empty
