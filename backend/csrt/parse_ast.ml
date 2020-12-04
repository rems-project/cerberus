(* some from https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param *)

open Pp

module type ParserArg = sig
  val default_label : string
end


type 'label parse_object =
  | Id of 'label * string
  | PredicateArg of 'label parse_object * string
  | Pointee of 'label parse_object


module Object = struct 

  type t = string parse_object

  type obj = t


  let rec pp = function
    | Id (label,s) -> !^s ^^ Pp.at ^^ !^label
    | PredicateArg (o, s) -> pp o ^^ dot ^^ dot ^^ !^s
    (* | StructMember (o, s) -> pp o ^^ dot ^^ !^s *)
    | Pointee o -> star ^^ pp o


  let compare o1 o2 =
    let rec aux o1 o2 = 
    match o1, o2 with
    | Id (l1,v1), Id (l2,v2) ->
       let compared = String.compare v1 v2 in
       if compared = 0 then String.compare v1 v2 else compared
    | Id _, _ -> -1
    | _, Id _ -> 1

    | PredicateArg (o1,a1), PredicateArg (o2,a2) ->
       let compared = aux o1 o2 in
       if compared = 0 then String.compare a1 a2 else compared
    | PredicateArg _, _ -> -1
    | _, PredicateArg _ -> 1

    (* | StructMember (o1,a1), StructMember (o2,a2) ->
     *    let compared = aux o1 o2 in
     *    if compared = 0 then String.compare a1 a2 else compared
     * | StructMember _, _ -> -1
     * | _, StructMember _ -> 1 *)

    | Pointee o1, Pointee o2 -> aux o1 o2
    in
    aux o1 o2

end

module Path = struct

  type accessor = 
    | Pointee
    | PredicateArg of string

  let accessor_equal a1 a2 =
    match a1, a2 with
    | Pointee, Pointee -> true
    | PredicateArg pa1, PredicateArg pa2 -> String.equal pa1 pa2
    | Pointee, _ -> false
    | PredicateArg _, _ -> false

  type t = {label : string; name : string; path : accessor list}

  let access {label; name; path} a = 
    {label; name; path = path @ [a]}

  let pp_access = function
    | Pointee -> Pp.dot
    | PredicateArg s -> Pp.dot ^^ Pp.dot ^^ !^s

  let pp {label; name; path} = 
    !^name ^^ Pp.at ^^ !^label ^^ Pp.separate_map empty pp_access path

  let rec of_object = function
    | Id (label,name) -> {label; name; path = []}
    | PredicateArg (o, s) -> access (of_object o) (PredicateArg s)
    | Pointee o -> access (of_object o) Pointee

  type map = {path : t; res : Sym.t}
  type mapping = map list

  let pointee p = access p Pointee

  let equal p1 p2 =
    String.equal p1.label p2.label &&
    String.equal p1.name p2.name &&
    List.equal accessor_equal p1.path p2.path

  let pp_map {path; res} = 
    Pp.parens (pp path ^^ comma ^^^ Sym.pp res)

  let pp_mapping = 
    Pp.list pp_map 


end


module IndexTerms = struct

  type t_ = 
    | Object of Object.t
    | Bool of bool
    | Num of Z.t
    | EQ of t * t
    | NE of t * t
    | LT of t * t
    | GT of t * t
    | LE of t * t
    | GE of t * t
    | Add of t * t
    | Sub of t * t
    | Mul of t * t
    | Div of t * t
    | Min of t * t
    | Max of t * t

    (* maybe remove *)
    | MIN_U32
    | MIN_U64
    | MAX_U32
    | MAX_U64
    | MIN_I32
    | MIN_I64
    | MAX_I32
    | MAX_I64

  and t = 
    | IndexTerm of Locations.t * t_

  type index_term = t

end






module Loc = Locations


type ownership = 
  | OUnowned 
  | OBlock

type parsed_condition = 
  | Constraint of IndexTerms.t
  | Ownership of Object.t * ownership

type logical_constraint = 
  {loc : Loc.t; lc : IndexTerms.t }

type ownership_constraint = 
  {loc : Loc.t; path : Path.t; ownership : ownership}








(* copying subset of Ctype.ctype *)

module ECT = struct

  type typ = 
    Typ of Loc.t * typ_

  and typ_ =
    | Void
    | Integer of CF.Ctype.integerType
    | Pointer of CF.Ctype.qualifiers * pointer
    | Struct of Sym.t

  and pointer =
    | Owned of typ
    | Unowned of Loc.t * typ
    | Block of Loc.t * typ

  let rec to_sct (Typ (loc, typ_)) =
    let annots = [CF.Annot.Aloc (Loc.unpack loc)] in
    match typ_ with
    | Void -> Sctypes.Sctype (annots, Sctypes.Void)
    | Integer it -> Sctypes.Sctype (annots, Sctypes.Integer it)
    | Pointer (qualifiers, Owned t)
    | Pointer (qualifiers, Unowned (_, t))
    | Pointer (qualifiers, Block (_, t)) ->
       Sctypes.Sctype (annots, Sctypes.Pointer (qualifiers, (to_sct t)))
    | Struct tag ->
       Sctypes.Sctype (annots, Sctypes.Struct tag)


end

open ECT


type varg = { name: string; vsym: Sym.t; typ : typ }
type aarg = { name: string; asym: Sym.t; typ : typ }

type vargs = varg list
type aargs = aarg list

type function_post = 
  | Post of logical_constraint list

type function_return = 
  | Ret of varg * aargs * function_post

type function_pre =
  | Pre of logical_constraint list * function_return

type function_arguments = 
  | Args of aargs * function_pre

type function_type = 
  | FunctionType of function_arguments




type label_inv =
  | LInv of logical_constraint list

type label_arguments = 
  | LArgs of {function_arguments : aargs; 
              label_arguments : vargs; inv : label_inv}

type label_type = 
  | LabelType of label_arguments


