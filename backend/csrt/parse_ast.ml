(* some from https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param *)

module CF = Cerb_frontend

open Pp

module type ParserArg = sig
  val default_label : string
end


module BaseName = struct

  type t = 
    {label : string; v : string}

  let equal b1 b2 = 
    String.equal b1.label b2.label && String.equal b1.v b2.v

  let pp {v; label} = 
    !^v ^^ at ^^ !^label

end



module Pred = struct

  type t = 
    | OUnowned 
    | OBlock
    | OPred of Id.t

  let equal p1 p2 =
    match p1, p2 with
    | OUnowned, OUnowned -> true
    | OBlock, OBlock -> true
    | OPred s1, OPred s2 -> Id.equal s1 s2
    | OUnowned, _ -> false
    | OBlock, _ -> false
    | OPred _, _ -> false

  let pp = function
    | OUnowned -> !^"Unowned"
    | OBlock -> !^"Block"
    | OPred s -> Id.pp s

end



module Ownership = struct

  type pointee = Pointee

  type access = {name : BaseName.t; derefs : pointee list}
  
  let pp_access {name; derefs} = 
    repeat (List.length derefs) star ^^ BaseName.pp name


  type t = 
    { access : access; 
      pred : Pred.t }

  let pointee_access {name; derefs} = 
    {name; derefs = Pointee :: derefs }

end


module Object = struct

  module Path = struct

    type t = 
      | Var of BaseName.t
      | Pointee of t

    let rec equal p1 p2 =
      match p1, p2 with
      | Var b1, Var b2 -> 
         BaseName.equal b1 b2
      | Pointee p1, Pointee p2 ->
         equal p1 p2
      | Var _, _ ->
         false
      | Pointee _, _ ->
         false

    let rec pp = function
      | Var b -> BaseName.pp b
      | Pointee p -> star ^^ (pp p)

  end
    
  type addr_or_path =
    | Addr of BaseName.t
    | Path of Path.t

  let pointee = function
    | Addr bn -> Path (Var bn)
    | Path p -> Path (Pointee p)

  type t =
    | AddrOrPath of addr_or_path
    | PredArg of {pred: Pred.t; path : Path.t; arg: string}

  let equal o1 o2 =
    match o1, o2 with
    | AddrOrPath (Addr b1), AddrOrPath (Addr b2) ->
       BaseName.equal b1 b2
    | AddrOrPath (Path p1), AddrOrPath (Path p2) ->
       Path.equal p1 p2
    | PredArg pa1, PredArg pa2 ->
       Pred.equal pa1.pred pa2.pred &&
         Path.equal pa1.path pa2.path &&
           String.equal pa1.arg pa2.arg
    | AddrOrPath _, _ ->
       false
    | PredArg _, _ ->
       false

  let pp = function
    | AddrOrPath (Addr b) ->
       ampersand ^^ BaseName.pp b
    | AddrOrPath (Path p) ->
       Path.pp p
    | PredArg pa ->
       Pred.pp pa.pred ^^ parens (Path.pp pa.path) ^^ dot ^^ !^(pa.arg)
       


  
  module Mapping = struct

    type item = {obj : t; res : BaseTypes.t * Sym.t}
    type t = item list
    
    let pp_item {obj; res} = 
      Pp.parens (pp obj ^^ comma ^^^ Sym.pp (snd res))
    
    let pp = Pp.list pp_item

    let empty = []

  end

  type mapping = Mapping.t


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
    | MinInteger of CF.Ctype.integerType
    | MaxInteger of CF.Ctype.integerType


  and t = 
    | IndexTerm of Locations.t * t_

  type index_term = t
       
 
 end



module Loc = Locations




type parsed_spec = 
  | Constraint of IndexTerms.t
  | Ownership of Ownership.t

type logical_spec = 
  Loc.t * IndexTerms.t

type resource_spec = 
  Loc.t * Ownership.t








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
    (* | Uninit of Loc.t * typ *)
    | Block of Loc.t * typ
    | Pred of Loc.t * Id.t * typ

  let rec to_sct (Typ (loc, typ_)) =
    let annots = [CF.Annot.Aloc (Loc.unpack loc)] in
    match typ_ with
    | Void -> Sctypes.Sctype (annots, Sctypes.Void)
    | Integer it -> Sctypes.Sctype (annots, Sctypes.Integer it)
    | Pointer (qualifiers, Owned t)
    | Pointer (qualifiers, Unowned (_, t))
    | Pointer (qualifiers, Block (_, t))
    | Pointer (qualifiers, Pred (_, _, t))
    (* | Pointer (qualifiers, Uninit (_, t))  *)
      ->
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
  | Post of logical_spec list

type function_return = 
  | Ret of varg * aargs * function_post

type function_pre =
  | Pre of logical_spec list * function_return

type function_arguments = 
  | Args of aargs * function_pre

type function_type = 
  | FunctionType of function_arguments




type label_inv =
  | LInv of logical_spec list

type label_arguments = 
  | LArgs of {function_arguments : aargs; 
              label_arguments : vargs; inv : label_inv}

type label_type = 
  | LabelType of label_arguments


