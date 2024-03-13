module IT = IndexTerms
module BT = BaseTypes
module SymSet = Set.Make(Sym)
open Pp


type logical_constraint =
  | T of IT.t
  | Forall of (Sym.t * BT.t) * IT.t
[@@deriving eq, ord]

type t = logical_constraint

let equal = equal_logical_constraint
let compare = compare_logical_constraint



let pp = function
  | T it ->
     IT.pp it
  | Forall ((s, bt), it) ->
     Pp.c_app !^"forall" [Sym.pp s; BT.pp bt] ^^ dot ^^^ IT.pp it

let json c : Yojson.Safe.t =
  `String (Pp.plain (pp c))



let subst su c =
  match c with
  | T it ->
     T (IT.subst su it)
  | Forall ((s, bt), body) ->
     let s, body = IT.suitably_alpha_rename su.relevant (s, bt) body in
     Forall ((s, bt), IT.subst su body)

let subst_ su c =
  subst (IT.make_subst su) c


let free_vars = function
  | T c ->
     IT.free_vars c
  | Forall ((s,_), body) ->
     SymSet.remove s (IT.free_vars body)


let alpha_equivalent lc lc' = match lc, lc' with
  | T c, T c' -> IT.equal c c'
  | Forall ((s, bt), c), Forall ((s', bt'), c') ->
    BT.equal bt bt' && if Sym.equal s s'
    then IT.equal c c'
    else begin
      let new_s = Sym.fresh_same s in
      let loc = Cerb_location.other __FUNCTION__ in
      let c = IT.subst (IT.make_subst [(s, IT.sym_ (new_s, bt, loc))]) c in
      let c' = IT.subst (IT.make_subst [(s', IT.sym_ (new_s, bt, loc))]) c' in
      IT.equal c c'
    end
  | _ -> false




let t_ it = T it
let forall_ (s,bt) it = Forall ((s, bt), it)



let is_sym_lhs_equality = function
  | T t ->
      begin match IT.is_eq t with
      | Some (lhs, rhs) ->
          begin match IT.is_sym lhs with
          | Some (s, _) -> Some (s, rhs)
          | _ -> None
          end
      | _ -> None
      end
  | _ -> None

let is_sym_equality t = match is_sym_lhs_equality t with
  | Some (s, rhs) -> begin match IT.is_sym rhs with
      | Some (s', _) -> Some (s, s')
      | _ -> None
      end
  | _ -> None



let is_equality = function
  | T it ->
     begin match it with
     | IT (Binop (EQ,a, b), _, _) -> Some ((a, b), true)
     | IT (Unop (Not, IT (Binop (EQ,a, b), _, _)), _, _) -> Some ((a, b), false)
     | _ -> None
     end
  | _ ->
     None

let equates_to it2 = function
  | T it ->
     begin match it with
     | IT (Binop (EQ,a, b), _, _) when IT.equal a it2 -> Some b
     | IT (Binop (EQ,a, b), _, _) when IT.equal b it2 -> Some a
     | _ -> None
     end
  | _ ->
     None



let dtree =
  let open Cerb_frontend.Pp_ast in
  function
  | T it -> Dnode (pp_ctor "T", [IT.dtree it])
  | Forall ((s, bt), t) -> Dnode (pp_ctor "Forall", [Dleaf (Sym.pp s); IT.dtree t])
