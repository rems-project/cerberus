module BT = BaseTypes
module Loc = Locations
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



(* copying subset of Ctype.ctype *)

module Pred = struct

  type t = 
    | Owned
    | Region of Z.t
    | Block
    | Pred of Id.t

  let equal p1 p2 =
    match p1, p2 with
    | Owned, Owned -> true
    | Region z1, Region z2 -> Z.equal z2 z2
    | Block, Block -> true
    | Pred s1, Pred s2 -> Id.equal s1 s2
    | Owned, _ -> false
    | Region _, _ -> false
    | Block, _ -> false
    | Pred _, _ -> false

  let pp = function
    | Owned -> !^"Owned"
    | Region z -> !^"Region" ^^^ Z.pp z
    | Block -> !^"Block"
    | Pred s -> Id.pp s

end







module Path = struct

  type t = 
    | Addr of BaseName.t
    | Var of BaseName.t
    | Pointee of t
    | PredArg of Pred.t * t list * string

  let rec equal p1 p2 =
    match p1, p2 with
    | Addr b1, Addr b2 ->
       BaseName.equal b1 b2
      | Var b1, Var b2 -> 
       BaseName.equal b1 b2
    | Pointee p1, Pointee p2 ->
       equal p1 p2
    | PredArg (p1, t1, a1), PredArg (p2, t2, a2) ->
       Pred.equal p1 p2 && List.equal equal t1 t2 && String.equal a1 a2
    | Addr _, _ -> 
       false
    | Var _, _ ->
       false
    | Pointee _, _ ->
       false
    | PredArg _, _ ->
       false


  let rec pp = function
    | Addr b -> ampersand ^^ BaseName.pp b
    | Var b -> BaseName.pp b
    | Pointee p -> star ^^ (pp p)
    | PredArg (p,t,a) -> Pred.pp p ^^ parens (separate_map comma pp t) ^^ dot ^^ !^a

  let addr bn = 
    Addr bn

  let var bn = 
    Var bn


  let pointee = function
    | Addr bn -> Var bn
    | Var bn -> Pointee (Var bn)
    | Pointee p -> Pointee p
    | PredArg (pr,p,a) -> Pointee (PredArg (pr,p,a))

  let predarg pr p a =
    PredArg (pr,p,a)

  let rec deref_path = function
    | Var bn -> 
       Some (bn, 0)
    | Pointee p -> 
       Option.bind (deref_path p) 
         (fun (bn, pp) -> Some (bn, pp+1))
    | Addr _ -> 
       None
    | PredArg _ -> 
       None


end
    



module Mapping = struct

  type item = {path : Path.t; sym : Sym.t; bt : BaseTypes.t}
  type t = item list

  let pp_item {path; sym; bt} = 
    Pp.parens (Path.pp path ^^ comma ^^ Sym.pp sym ^^ comma ^^ BT.pp false bt)

  let pp = Pp.list pp_item

  let empty = []

end

type mapping = Mapping.t





module IndexTerms = struct

  type t_ =
    | Path of Path.t
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





type parsed_spec = 
  | R of (Pred.t * Path.t list)
  | C of IndexTerms.t

type logical_spec = Loc.t * IndexTerms.t
type resource_spec = 
  Loc.t * (Pred.t * Path.t list)





(* let default_pointer_ownership = Pred.Unowned *)





type varg = { name: string; vsym: Sym.t; typ : Sctypes.t }
type aarg = { name: string; asym: Sym.t; typ : Sctypes.t }
type garg = { name: string; lsym: Sym.t; typ : Sctypes.t; accessed : bool }

type arg = 
  | Aarg of aarg
  | Varg of varg
  | Garg of garg

type vargs = varg list
type aargs = aarg list
type gargs = garg list

type function_post = 
  | FPost of resource_spec list * logical_spec list

type function_return =
  | FRet of varg

type function_pre =
  | FPre of resource_spec list * logical_spec list

type function_args = 
  | FA of {globs : gargs; fargs : aargs} 

type function_type = 
  | FT of function_args * function_pre * function_return * function_post





type label_inv =
  | LInv of resource_spec list * logical_spec list

type label_args = 
  | LA of {globs : gargs; fargs : aargs; largs : vargs} 

type label_type = 
  | LT of label_args * label_inv
