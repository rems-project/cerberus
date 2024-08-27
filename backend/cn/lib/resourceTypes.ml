open Pp
module CF = Cerb_frontend
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)
module IT = IndexTerms
open IT
module LC = LogicalConstraints
module LCSet = Set.Make (LC)

type init =
  | Init
  | Uninit
[@@deriving eq, ord]

type predicate_name =
  | Owned of Sctypes.t * init
  | PName of Sym.t
[@@deriving eq, ord]

let pp_init = function Init -> !^"Init" | Uninit -> !^"Uninit"

let pp_predicate_name = function
  | Owned (ct, Init) -> !^"Owned" ^^ angles (Sctypes.pp ct)
  | Owned (ct, Uninit) -> !^"Block" ^^ angles (Sctypes.pp ct)
  | PName pn -> Sym.pp pn


type predicate_type =
  { name : predicate_name;
    pointer : IT.t; (* I *)
    iargs : IT.t list (* I *)
  }
[@@deriving eq, ord]

type qpredicate_type =
  { name : predicate_name;
    pointer : IT.t; (* I *)
    q : Sym.t * BT.t;
    q_loc : loc; [@equal fun _ _ -> true] [@compare fun _ _ -> 0]
    step : IT.t;
    permission : IT.t; (* I, function of q *)
    iargs : IT.t list (* I, function of q *)
  }
[@@deriving eq, ord]

let subsumed p1 p2 =
  (* p1 subsumed by p2 *)
  equal_predicate_name p1 p2
  ||
  match (p1, p2) with
  | Owned (ct, Uninit), Owned (ct', Init) when Sctypes.equal ct ct' -> true
  | _ -> false


type resource_type =
  | P of predicate_type
  | Q of qpredicate_type
[@@deriving eq, ord]

type t = resource_type

let predicate_name = function P p -> p.name | Q p -> p.name

let pp_maybe_oargs = function None -> Pp.empty | Some oargs -> parens (IT.pp oargs)

let pp_predicate_type_aux (p : predicate_type) oargs =
  let args = List.map IT.pp (p.pointer :: p.iargs) in
  c_app (pp_predicate_name p.name) args ^^ pp_maybe_oargs oargs


let pp_qpredicate_type_aux (p : qpredicate_type) oargs =
  (* XXX: this is `p + i * step` but that's "wrong" in a couple of ways:
     - we are not using the correct precedences for `p` and `step`
     - in C pointer arithmetic takes account of the types, but here
       we seem to be doing it at the byte level.  Would `step` ever
       differ from the size of elements that `p` points to?
     - perhaps print as `&p[i]` or `&p[j + i]`
  *)
  let pointer = IT.pp p.pointer ^^^ plus ^^^ Sym.pp (fst p.q) ^^^ star ^^^ IT.pp p.step in
  let args = pointer :: List.map IT.pp p.iargs in
  !^"each"
  ^^ parens (BT.pp (snd p.q) ^^^ Sym.pp (fst p.q) ^^ semi ^^^ IT.pp p.permission)
  ^/^ braces (c_app (pp_predicate_name p.name) args)
  ^^ pp_maybe_oargs oargs


let pp_predicate_type p = pp_predicate_type_aux p None

let pp_qpredicate_type p = pp_qpredicate_type_aux p None

let pp_aux r o =
  match r with P p -> pp_predicate_type_aux p o | Q qp -> pp_qpredicate_type_aux qp o


let pp r = pp_aux r None

let equal = equal_resource_type

let compare = compare_resource_type

let json re : Yojson.Safe.t = `String (Pp.plain (pp re))

let alpha_rename_qpredicate_type_ (q' : Sym.t) (qp : qpredicate_type) =
  let subst = make_rename ~from:(fst qp.q) ~to_:q' in
  { name = qp.name;
    pointer = qp.pointer;
    q = (q', snd qp.q);
    q_loc = qp.q_loc;
    step = qp.step;
    permission = IT.subst subst qp.permission;
    iargs = List.map (IT.subst subst) qp.iargs
  }


let alpha_rename_qpredicate_type qp =
  alpha_rename_qpredicate_type_ (Sym.fresh_same (fst qp.q)) qp


let subst_predicate_type substitution (p : predicate_type) =
  { name = p.name;
    pointer = IT.subst substitution p.pointer;
    iargs = List.map (IT.subst substitution) p.iargs
  }


let subst_qpredicate_type substitution (qp : qpredicate_type) =
  let qp =
    if SymSet.mem (fst qp.q) substitution.Subst.relevant then
      alpha_rename_qpredicate_type qp
    else
      qp
  in
  { name = qp.name;
    pointer = IT.subst substitution qp.pointer;
    q = qp.q;
    q_loc = qp.q_loc;
    step = IT.subst substitution qp.step;
    permission = IT.subst substitution qp.permission;
    iargs = List.map (IT.subst substitution) qp.iargs
  }


let subst (substitution : _ Subst.t) = function
  | P p -> P (subst_predicate_type substitution p)
  | Q qp -> Q (subst_qpredicate_type substitution qp)


let free_vars = function
  | P p -> IT.free_vars_list (p.pointer :: p.iargs)
  | Q p ->
    SymSet.union
      (SymSet.union (IT.free_vars p.pointer) (IT.free_vars p.step))
      (SymSet.remove (fst p.q) (IT.free_vars_list (p.permission :: p.iargs)))


(* resources of the same type as a request, such that the resource coult potentially be
   used to fulfil the request *)
let same_predicate_name r1 r2 =
  equal_predicate_name (predicate_name r1) (predicate_name r2)


let alpha_equivalent r1 r2 =
  match (r1, r2) with
  | P _, P _ -> equal_resource_type r1 r2
  | Q x, Q y ->
    let y2 = alpha_rename_qpredicate_type_ (fst x.q) y in
    equal_resource_type (Q x) (Q y2)
  | _ -> false


let steps_constant = function Q qp -> Option.is_some (IT.is_const qp.step) | _ -> true

let pointer = function P pred -> pred.pointer | Q pred -> pred.pointer

open Cerb_frontend.Pp_ast
open Pp

let dtree_of_predicate_name = function
  | Owned (ty, init) ->
    Dleaf (!^"Owned" ^^ angles (Sctypes.pp ty ^^ comma ^^ pp_init init))
  | PName s -> Dleaf (Sym.pp s)


let dtree_of_predicate_type (pred : predicate_type) =
  Dnode
    ( pp_ctor "pred",
      dtree_of_predicate_name pred.name
      :: IT.dtree pred.pointer
      :: List.map IT.dtree pred.iargs )


let dtree_of_qpredicate_type (pred : qpredicate_type) =
  Dnode
    ( pp_ctor "qpred",
      Dleaf (Pp.parens (Pp.typ (Sym.pp (fst pred.q)) (BT.pp (snd pred.q))))
      :: IT.dtree pred.step
      :: IT.dtree pred.permission
      :: dtree_of_predicate_name pred.name
      :: IT.dtree pred.pointer
      :: List.map IT.dtree pred.iargs )


let dtree = function
  | P pred -> dtree_of_predicate_type pred
  | Q pred -> dtree_of_qpredicate_type pred
