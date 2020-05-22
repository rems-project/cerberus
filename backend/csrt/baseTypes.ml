open List
open PPrint
open Pp_tools
open Cerb_frontend
module Loc=Locations

module SymSet = Set.Make(Sym)

type struct_type = S_Id of Sym.t
type var = Sym.t

type field_access = {loc : Loc.t; struct_type: struct_type; field: string}


type offset = Num.t


type field = string * (offset * Ctype.ctype * Sym.t option)

type openstruct = 
  {typ : struct_type; 
   size : Num.t;
   fields : field list;
  }


let rec pp_openstruct o = 
  pp_field_names o.fields

and pp_field_names fields =
  braces (
    flow_map (semi ^^ break 1) 
      (fun (f,(_,_,mfvar)) -> 
        match mfvar with
        | Some fvar -> dot ^^ !^f ^^^ arrow ^^^ Sym.pp fvar
        | None -> dot ^^ !^f ^^^ !^"uninit"
      )
      fields
    )

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


let rec pp atomic = 
  let mparens pped = if atomic then parens pped else pped in
  function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "int"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> mparens ((!^ "list") ^^^ pp true bt)
  | Tuple nbts -> mparens (!^ "tuple" ^^^ flow_map (comma ^^ break 1) (pp false) (nbts))
  | Struct (S_Id sym) -> parens (!^ "struct" ^^^ Sym.pp sym)
  | StructField (p,a) -> 
     mparens (!^"structfield" ^^^ Sym.pp p ^^ dot ^^ pp_field_access a)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)
  | OpenStruct s -> pp_openstruct s



let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)




let rec subst_openstruct sym with_it o = 
  { o with fields = subst_fields sym with_it o.fields }

and subst_fields sym with_it fields = 
  List.map (fun (f,(offset,ct,fvar)) -> 
      let fvar = match fvar with
        | None -> None
        | Some fvar -> Some (Sym.subst sym with_it fvar)
      in
      (f,(offset,ct,fvar))
    ) fields

let subst_var sym with_sym bt = 
  match bt with
  | FunctionPointer p -> FunctionPointer (Sym.subst sym with_sym p)
  | StructField (p,a) -> StructField (Sym.subst sym with_sym p, a)
  | OpenStruct s ->
     OpenStruct (subst_openstruct sym with_sym s)
  | bt -> bt

let vars_in = function
  | FunctionPointer p -> SymSet.singleton p
  | StructField (p,a) -> SymSet.singleton p
  | OpenStruct s -> SymSet.of_list (filter_map (fun (_,(_,_,f)) -> f) s.fields)
  | bt -> SymSet.empty




