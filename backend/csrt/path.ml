module type BN_Sig = sig
  type t
  val equal : t -> t -> bool
  val pp : t -> Pp.document
end

open Pp

module Make (BN: BN_Sig) = struct


type path = 
  | Addr of BN.t
  | Var of BN.t
  | Pointee of path
  | PredArg of string * predarg list * string

and predarg = 
  | PathArg of path
  | NumArg of Z.t

type t = path


let rec equal p1 p2 =
  match p1, p2 with
  | Addr b1, Addr b2 ->
     BN.equal b1 b2
  | Var b1, Var b2 -> 
     BN.equal b1 b2
  | Pointee p1, Pointee p2 ->
     equal p1 p2
  | PredArg (p1, t1, a1), PredArg (p2, t2, a2) ->
     String.equal p1 p2 && List.equal predarg_equal t1 t2 && String.equal a1 a2
  | Addr _, _ -> 
     false
  | Var _, _ ->
     false
  | Pointee _, _ ->
     false
  | PredArg _, _ ->
     false

and predarg_equal pa1 pa2 = 
  match pa1, pa2 with
  | PathArg p1, PathArg p2 -> equal p1 p2
  | NumArg z1, NumArg z2 -> Z.equal z1 z2
  | PathArg _, _ -> false
  | NumArg _, _ -> false


let rec pp = function
  | Addr b -> ampersand ^^ BN.pp b
  | Var b -> BN.pp b
  | Pointee p -> star ^^ (pp p)
  | PredArg (p,t,a) -> !^p ^^ parens (separate_map comma pp_predarg t) ^^ dot ^^ !^a

and pp_predarg = function
  | PathArg t -> pp t
  | NumArg z -> Z.pp z

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
