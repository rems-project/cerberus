open Tools
open List
open Pp
module Loc=Locations
module SymSet = Set.Make(Sym)


type tag = Tag of Sym.t
type member = Member of string

type access = { loc: Loc.t; tag: tag; member: member }
type path = access list

type fieldmap = (member * Sym.t) list



type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | ClosedStruct of tag
  | OpenStruct of tag * fieldmap
  | StoredStruct of tag * fieldmap
  | Path of Sym.t * path
  | FunctionPointer of Sym.t



let pp_field_access access =
  separate_map dot (fun { member = Member member; _} -> !^member) access


let pp_fieldmap stored fields =
  braces (
    flow_map (semi ^^ break 1) 
      (fun (Member f,fvar) -> 
        (if stored then ampersand else empty) ^^ 
          !^f ^^ equals ^^ Sym.pp fvar)
      fields
    )

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
  | ClosedStruct (Tag sym) -> 
     mparens (!^ "closed" ^^^ !^"struct" ^^^ Sym.pp sym)
  | Path (p,a) -> 
     mparens (!^"path" ^^^ Sym.pp p ^^ dot ^^ pp_field_access a)
  | FunctionPointer p ->
     parens (!^"function" ^^^ Sym.pp p)
  | OpenStruct (Tag tag,fieldmap) -> 
     mparens (!^"open" ^^^ !^"struct" ^^^ Sym.pp tag ^^^ pp_fieldmap false fieldmap)
  | StoredStruct (Tag tag,fieldmap) -> 
     mparens (!^"stored" ^^^ !^"struct" ^^^ Sym.pp tag ^^^ pp_fieldmap true fieldmap)



let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)




let subst_fieldmap subst fields = 
  List.map (fun (f,fvar) -> (f,Sym.subst subst fvar)) fields

let subst_var subst bt = 
  match bt with
  | FunctionPointer p -> FunctionPointer (Sym.subst subst p)
  | Path (p,a) -> Path (Sym.subst subst p, a)
  | OpenStruct (tag,fieldmap) ->
     OpenStruct (tag,subst_fieldmap subst fieldmap)
  | StoredStruct (tag,fieldmap) ->
     StoredStruct (tag,subst_fieldmap subst fieldmap)
  | bt -> bt

let subst_vars = make_substs subst_var


let vars_in = function
  | FunctionPointer p -> SymSet.singleton p
  | Path (p,a) -> SymSet.singleton p
  | OpenStruct (tag,fieldmap) -> SymSet.of_list (map snd fieldmap)
  | StoredStruct (tag,fieldmap) -> SymSet.of_list (map snd fieldmap)
  | bt -> SymSet.empty




