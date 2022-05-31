open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT
module LC = LogicalConstraints
module LCSet = Set.Make(LC)



type predicate_name = 
  | Block of Sctypes.t
  | Owned of Sctypes.t
  | PName of Sym.t
[@@deriving eq, ord]

let pp_predicate_name = function
  | Block ct -> !^"Block" ^^ angles (Sctypes.pp ct)
  | Owned ct -> !^"Owned" ^^ angles (Sctypes.pp ct)
  | PName pn -> Sym.pp pn




type predicate_type = {
    name : predicate_name; 
    pointer: IT.t;            (* I *)
    permission: IT.t;         (* I *)
    iargs: IT.t list;         (* I *)
  }
[@@deriving eq, ord]


type qpredicate_type = {
    name : predicate_name; 
    pointer: IT.t;            (* I *)
    q: Sym.t;
    step: int;
    permission: IT.t;         (* I, function of q *)
    iargs: IT.t list;         (* I, function of q *)
  }
[@@deriving eq, ord]




type resource_type =
  | P of predicate_type
  | Q of qpredicate_type
[@@deriving eq, ord]


type t = resource_type



let predicate_name = function
  | P p -> p.name
  | Q p -> p.name



let pp_predicate_type (p : predicate_type) =
  let args = 
    [IT.pp p.pointer;
     IT.pp p.permission] @
    List.map IT.pp (p.iargs)
  in
  c_app (pp_predicate_name p.name) args

let pp_qpredicate_type (p : qpredicate_type) =
  let args = 
    [IT.pp p.pointer ^^^ plus ^^^ parens (Sym.pp p.q ^^^ star ^^^ !^(string_of_int p.step));
     IT.pp p.permission] @
    List.map IT.pp (p.iargs)
  in
  !^"each" ^^^ Sym.pp p.q ^^ dot ^^^
  c_app (pp_predicate_name p.name) args


let pp = function
  | P p -> pp_predicate_type p
  | Q qp -> pp_qpredicate_type qp



let equal = equal_resource_type
let compare = compare_resource_type


let json re : Yojson.Safe.t = 
  `String (Pp.plain (pp re))




let alpha_rename_qpredicate_type (q' : Sym.t) (qp : qpredicate_type) = 
  let subst = make_subst [(qp.q, sym_ (q', BT.Integer))] in
  { name = qp.name;
    pointer = qp.pointer;
    q = q';
    step = qp.step;
    permission = IT.subst subst qp.permission;
    iargs = List.map (IT.subst subst) qp.iargs;
  }


let subst_predicate_type substitution (p : predicate_type) = 
  {
    name = p.name;
    pointer = IT.subst substitution p.pointer;
    permission = IT.subst substitution p.permission;
    iargs = List.map (IT.subst substitution) p.iargs;
  }

let subst_qpredicate_type substitution (qp : qpredicate_type) =
  let qp = 
    if SymSet.mem qp.q substitution.Subst.relevant
    then alpha_rename_qpredicate_type (Sym.fresh_same qp.q) qp 
    else qp
  in
  {
    name = qp.name;
    pointer = IT.subst substitution qp.pointer;
    q = qp.q;
    step = qp.step;
    permission = IT.subst substitution qp.permission;
    iargs = List.map (IT.subst substitution) qp.iargs;
  }


let subst (substitution : IT.t Subst.t) = function
  | P p -> P (subst_predicate_type substitution p)
  | Q qp -> Q (subst_qpredicate_type substitution qp)




let free_vars = function
  | P p -> 
     IT.free_vars_list (p.pointer :: p.permission :: p.iargs)
  | Q p -> 
     SymSet.union
       (IT.free_vars p.pointer)
       (SymSet.remove p.q (IT.free_vars_list (p.permission :: p.iargs)))



open Simplify


let simp_predicate_type structs values equalities lcs (p : predicate_type) = {
    name = p.name; 
    pointer = simp structs values equalities lcs p.pointer; 
    permission = simp structs values equalities lcs p.permission;
    iargs = List.map (simp structs values equalities lcs) p.iargs; 
  }

let simp_qpredicate_type structs values equalities lcs (qp : qpredicate_type) = 
  let qp = alpha_rename_qpredicate_type (Sym.fresh_same qp.q) qp in
  let permission = Simplify.simp_flatten structs values equalities lcs qp.permission in
  let permission_lcs = LCSet.of_list (List.map LC.t_ permission) in
  let simp_lcs = LCSet.union permission_lcs lcs in
  {
    name = qp.name;
    pointer = simp structs values equalities lcs qp.pointer;
    q = qp.q;
    step = qp.step;
    permission = and_ permission;
    iargs = List.map (simp structs values equalities simp_lcs) qp.iargs;
  }



let simp structs values equalities lcs = function
  | P p -> P (simp_predicate_type structs values equalities lcs p)
  | Q qp -> Q (simp_qpredicate_type structs values equalities lcs qp)



let simp_or_empty structs values equalities lcs resource = 
  match simp structs values equalities lcs resource with
  | P p when IT.is_false p.permission -> None
  | Q p when IT.is_false p.permission -> None
  | re -> Some re



(* resources of the same type as a request, such that the resource
   can be used to fulfil the request *)
let same_predicate_name r1 r2 =
  equal_predicate_name (predicate_name r1) (predicate_name r2)
