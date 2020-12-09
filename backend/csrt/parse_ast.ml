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
    | Owned
    | Unowned 
    | Block
    | Pred of Id.t

  let equal p1 p2 =
    match p1, p2 with
    | Owned, Owned -> true
    | Unowned, Unowned -> true
    | Block, Block -> true
    | Pred s1, Pred s2 -> Id.equal s1 s2
    | Owned, _ -> false
    | Unowned, _ -> false
    | Block, _ -> false
    | Pred _, _ -> false

  let pp = function
    | Owned -> !^"Owned"
    | Unowned -> !^"Unowned"
    | Block -> !^"Block"
    | Pred s -> Id.pp s

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


  let pp {access; pred} = 
    Pred.pp pred ^^ parens (pp_access access)

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
    
  module AddrOrPath = struct

    type t =
      | Addr of BaseName.t
      | Path of Path.t

    let equal aop1 aop2 =
      match aop1, aop2 with
      | Addr bn1, Addr bn2 -> BaseName.equal bn1 bn2
      | Path p1, Path p2 -> Path.equal p1 p2
      | Addr _, _ -> false
      | Path _, _ -> false

    let pointee = function
      | Addr bn -> Path (Var bn)
      | Path p -> Path (Pointee p)

    let pp = function
      | Addr bn -> ampersand ^^ BaseName.pp bn
      | Path p -> Path.pp p

  end

  type pred_arg = {pred : Pred.t; arg : string}

  let equal_pred_arg pa1 pa2 =
    Pred.equal pa1.pred pa2.pred && 
      String.equal pa1.arg pa2.arg

  type t =
    | Obj of AddrOrPath.t * pred_arg option


  let equal (Obj (aop1,pa1)) (Obj (aop2,pa2)) =
    AddrOrPath.equal aop1 aop2 &&
      Option.equal equal_pred_arg pa1 pa2

  let pp = function
    | Obj (aop, None) -> 
       AddrOrPath.pp aop       
    | Obj (aop, Some pa) -> 
       parens (Pred.pp pa.pred ^^ parens (AddrOrPath.pp aop)) ^^ dot ^^ !^(pa.arg)
       


  
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
    | IntegerToPointerCast of t
    | PointerToIntegerCast of t


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





let default_pointer_ownership = Pred.Unowned




(* copying subset of Ctype.ctype *)

module ECT = struct

  type typ = 
    Typ of Loc.t * typ_

  and typ_ =
    | Void
    | Integer of CF.Ctype.integerType
    | Pointer of CF.Ctype.qualifiers * Loc.t * Pred.t * typ
    | Struct of Sym.t

  let rec to_sct (Typ (loc, typ_)) =
    let annots = [CF.Annot.Aloc (Loc.unpack loc)] in
    match typ_ with
    | Void -> 
       Sctypes.Sctype (annots, Sctypes.Void)
    | Integer it -> 
       Sctypes.Sctype (annots, Sctypes.Integer it)
    | Pointer (qualifiers, _, _, t) ->
       Sctypes.Sctype (annots, Sctypes.Pointer (qualifiers, (to_sct t)))
    | Struct tag ->
       Sctypes.Sctype (annots, Sctypes.Struct tag)

  let rec of_ct loc ((Sctypes.Sctype (annots,raw_ctype)) : Sctypes.t) =
    let loc = Loc.update loc (CF.Annot.get_loc_ annots) in
    match raw_ctype with
    | Sctypes.Void -> 
       Typ (loc, Void)
    | Sctypes.Integer it -> 
       Typ (loc, Integer it)
    | Pointer (qualifiers, ct) ->
       let t = of_ct loc ct in
       Typ (loc, Pointer (qualifiers, loc, default_pointer_ownership, t))
    | Struct tag ->
       Typ (loc, Struct tag)


end

open ECT


type varg = { name: string; vsym: Sym.t; typ : typ }
type aarg = { name: string; asym: Sym.t; typ : typ }

type vargs = varg list
type aargs = aarg list

type function_post = 
  | FPost of logical_spec list

type function_return_type = 
  | FRT of {ret : varg; glob_rets: aargs; arg_rets: aargs}

type function_return =
  | FRet of function_return_type * function_post

type function_pre =
  | FPre of logical_spec list * function_return

type function_args = 
  | FA of {globs : aargs; args : aargs} 

type function_type = 
  | FT of function_args * function_pre





type label_inv =
  | LInv of logical_spec list

type label_args = 
  | LA of {globs : aargs; fargs : aargs; largs : vargs} 

type label_type = 
  | LT of label_args * label_inv
