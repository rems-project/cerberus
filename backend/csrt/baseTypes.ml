open Subst
open List
open Pp
module Loc=Locations
module SymSet = Set.Make(Sym)


type tag = Tag of Sym.t
type member = Member of string





type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | ClosedStruct of tag
  | OpenStruct of tag * (member * Sym.t) list
  | StoredStruct of tag * (member * Sym.t) list
  | FunctionPointer of Sym.t






(* TODO *)
let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)


let subst_fieldmap subst fields = 
  List.map (fun (f,fvar) -> (f,Sym.subst subst fvar)) fields

let subst_var subst bt = 
  match bt with
  | FunctionPointer p -> 
     FunctionPointer (Sym.subst subst p)
  | OpenStruct (tag,fieldmap) ->
     OpenStruct (tag,subst_fieldmap subst fieldmap)
  | StoredStruct (tag,fieldmap) ->
     StoredStruct (tag,subst_fieldmap subst fieldmap)
  | bt -> bt

let subst_vars = make_substs subst_var


let vars_in = function
  | FunctionPointer p -> SymSet.singleton p
  | OpenStruct (tag,fieldmap) -> SymSet.of_list (map snd fieldmap)
  | StoredStruct (tag,fieldmap) -> SymSet.of_list (map snd fieldmap)
  | bt -> SymSet.empty



let pp_addrmap stored fields =
  flow_map (semi ^^ break 1) 
    (fun (Member f,fvar) -> ampersand ^^ !^f ^^ equals ^^ Sym.pp fvar)
    fields

let pp_valmap stored fields =
  flow_map (semi ^^ break 1) 
    (fun (Member f,fvar) -> !^f ^^ equals ^^ Sym.pp fvar)
    fields


let rec pp atomic = 
  let mparens pped = if atomic then parens pped else pped in
  function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "integer"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  | List bt -> mparens ((!^ "list") ^^^ pp true bt)
  | Tuple nbts -> mparens (!^ "tuple" ^^^ flow_map (comma ^^ break 1) (pp false) (nbts))
  | ClosedStruct (Tag sym) -> 
     mparens (!^ "closed" ^^^ !^"struct" ^^^ Sym.pp sym)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)
  | OpenStruct (Tag tag,fieldmap) -> 
     mparens (!^"open" ^^^ !^"struct" ^^^ Sym.pp tag ^^^ pp_valmap false fieldmap)
  | StoredStruct (Tag tag,fieldmap) -> 
     mparens (!^"stored" ^^^ !^"struct" ^^^ Sym.pp tag ^^^ pp_addrmap true fieldmap)
