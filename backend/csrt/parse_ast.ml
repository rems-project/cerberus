module BT = BaseTypes
module Loc = Locations
module CF = Cerb_frontend
open Pp
(* some from https://gitlab.inria.fr/fpottier/menhir/-/tree/master/demos/calc-param *)


module type ParserArg = sig
  val default_label : string
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
    | Exp of t * t
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
  | R of (string * Path.predarg list)
  | C of IndexTerms.t

type logical_spec = Loc.t * IndexTerms.t
type resource_spec = Loc.t * (string * Path.predarg list)





(* let default_pointer_ownership = Pred.Unowned *)





type varg = { name: string; vsym: Sym.t; typ : Sctypes.t }
type aarg = { name: string; asym: Sym.t; typ : Sctypes.t }
type garg = { name: string; lsym: Sym.t; typ : Sctypes.t; accessed : Loc.t option }

(* type larg =
 *   | Varg of varg
 *   | Aarg of aarg *)


type vargs = varg list
type aargs = aarg list
type gargs = garg list
(* type largs = larg list *)

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
  | LA of {globs : gargs; fargs : aargs; largs : aargs} 

type label_type = 
  | LT of label_args * label_inv
