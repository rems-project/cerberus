open Pp.Infix
module IT = IndexTerms

let pp_maybe_oargs = function None -> Pp.empty | Some oargs -> Pp.parens (IT.pp oargs)

type init =
  | Init
  | Uninit
[@@deriving eq, ord]

let pp_init = function Init -> !^"Init" | Uninit -> !^"Uninit"

type name =
  | Owned of Sctypes.t * init
  | PName of Sym.t
[@@deriving eq, ord]

let pp_name = function
  | Owned (ct, Init) -> !^"RW" ^^ Pp.angles (Sctypes.pp ct)
  | Owned (ct, Uninit) -> !^"W" ^^ Pp.angles (Sctypes.pp ct)
  | PName pn -> Sym.pp pn


let dtree_of_name =
  let open Cerb_frontend.Pp_ast in
  function
  | Owned (ty, init) ->
    Dleaf (!^"Owned" ^^ Pp.angles (Sctypes.pp ty ^^ Pp.comma ^^ pp_init init))
  | PName s -> Dleaf (Sym.pp s)


let subsumed p1 p2 =
  (* p1 subsumed by p2 *)
  equal_name p1 p2
  ||
  match (p1, p2) with
  | Owned (ct, Uninit), Owned (ct', Init) when Sctypes.equal ct ct' -> true
  | _ -> false


module Predicate = struct
  let alloc = PName Alloc.Predicate.sym

  type t =
    { name : name;
      pointer : IT.t; (* I *)
      iargs : IT.t list (* I *)
    }
  [@@deriving eq, ord]

  let pp_aux (p : t) oargs =
    let args = List.map IT.pp (p.pointer :: p.iargs) in
    Pp.c_app (pp_name p.name) args ^^ pp_maybe_oargs oargs


  let subst substitution (p : t) =
    { name = p.name;
      pointer = IT.subst substitution p.pointer;
      iargs = List.map (IT.subst substitution) p.iargs
    }


  let dtree (pred : t) =
    let open Cerb_frontend.Pp_ast in
    Dnode
      ( pp_ctor "pred",
        dtree_of_name pred.name :: IT.dtree pred.pointer :: List.map IT.dtree pred.iargs
      )
end

let make_alloc pointer = Predicate.{ name = alloc; pointer; iargs = [] }

module QPredicate = struct
  type t =
    { name : name;
      pointer : IT.t; (* I *)
      q : Sym.t * BaseTypes.t;
      q_loc : Locations.t; [@equal fun _ _ -> true] [@compare fun _ _ -> 0]
      step : IT.t;
      permission : IT.t; (* I, function of q *)
      iargs : IT.t list (* I, function of q *)
    }
  [@@deriving eq, ord]

  let pp_aux (p : t) oargs =
    let open Pp in
    (* ISD: this is `p + i * step` but that's "wrong" in a couple of ways:
       - we are not using the correct precedences for `p` and `step`
       - in C pointer arithmetic takes account of the types, but here
         we seem to be doing it at the byte level.  Would `step` ever
         differ from the size of elements that `p` points to?
       - perhaps print as `&p[i]` or `&p[j + i]`
    *)
    let pointer =
      IT.pp p.pointer ^^^ plus ^^^ Sym.pp (fst p.q) ^^^ star ^^^ IT.pp p.step
    in
    let args = pointer :: List.map IT.pp p.iargs in
    !^"each"
    ^^ parens (BaseTypes.pp (snd p.q) ^^^ Sym.pp (fst p.q) ^^ semi ^^^ IT.pp p.permission)
    ^/^ braces (c_app (pp_name p.name) args)
    ^^ pp_maybe_oargs oargs


  let alpha_rename_ (q' : Sym.t) (qp : t) =
    let subst = IT.make_rename ~from:(fst qp.q) ~to_:q' in
    { name = qp.name;
      pointer = qp.pointer;
      q = (q', snd qp.q);
      q_loc = qp.q_loc;
      step = qp.step;
      permission = IT.subst subst qp.permission;
      iargs = List.map (IT.subst subst) qp.iargs
    }


  let alpha_rename qp = alpha_rename_ (Sym.fresh_same (fst qp.q)) qp

  let subst substitution (qp : t) =
    let qp =
      if Sym.Set.mem (fst qp.q) substitution.Subst.relevant then
        alpha_rename qp
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


  let dtree (qpred : t) =
    let open Cerb_frontend.Pp_ast in
    Dnode
      ( pp_ctor "qpred",
        Dleaf (Pp.parens (Pp.typ (Sym.pp (fst qpred.q)) (BaseTypes.pp (snd qpred.q))))
        :: IT.dtree qpred.step
        :: IT.dtree qpred.permission
        :: dtree_of_name qpred.name
        :: IT.dtree qpred.pointer
        :: List.map IT.dtree qpred.iargs )


  let get_lower_bound (qpred : t) : IT.t =
    IndexTerms.Bounds.get_lower_bound qpred.q qpred.permission


  let get_upper_bound (qpred : t) : IT.t =
    IndexTerms.Bounds.get_upper_bound qpred.q qpred.permission


  let get_bounds (qpred : t) : IT.t * IT.t = (get_lower_bound qpred, get_upper_bound qpred)
end

type t =
  | P of Predicate.t
  | Q of QPredicate.t
[@@deriving eq, ord]

let get_name = function P p -> p.name | Q p -> p.name

(* resources of the same type as a request, such that the resource coult potentially be
   used to fulfil the request *)
let same_name r1 r2 = equal_name (get_name r1) (get_name r2)

let pp_aux r o =
  match r with P p -> Predicate.pp_aux p o | Q qp -> QPredicate.pp_aux qp o


let pp r = pp_aux r None

let json re : Yojson.Safe.t = `String (Pp.plain (pp re))

let subst (substitution : _ Subst.t) = function
  | P p -> P (Predicate.subst substitution p)
  | Q qp -> Q (QPredicate.subst substitution qp)


let free_vars_bts = function
  | P p -> IT.free_vars_bts_list (p.pointer :: p.iargs)
  | Q p ->
    Sym.Map.union
      (fun _ bt1 bt2 ->
        assert (BaseTypes.equal bt1 bt2);
        Some bt1)
      (IT.free_vars_bts_list [ p.pointer; p.step ])
      (Sym.Map.remove (fst p.q) (IT.free_vars_bts_list (p.permission :: p.iargs)))


let free_vars = function
  | P p -> IT.free_vars_list (p.pointer :: p.iargs)
  | Q p ->
    Sym.Set.union
      (Sym.Set.union (IT.free_vars p.pointer) (IT.free_vars p.step))
      (Sym.Set.remove (fst p.q) (IT.free_vars_list (p.permission :: p.iargs)))


let alpha_equivalent r1 r2 =
  match (r1, r2) with
  | P _, P _ -> equal r1 r2
  | Q x, Q y ->
    let y2 = QPredicate.alpha_rename_ (fst x.q) y in
    equal (Q x) (Q y2)
  | _ -> false


let steps_constant = function Q qp -> Option.is_some (IT.is_const qp.step) | _ -> true

let dtree = function P pred -> Predicate.dtree pred | Q qpred -> QPredicate.dtree qpred
