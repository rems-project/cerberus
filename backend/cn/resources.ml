open Pp
open Subst
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT
module LC = LogicalConstraints
module LCSet = Set.Make(LC)




module type Output = sig
  type t
  val pp : t -> document
  val subst : IT.t Subst.t -> t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val free_vars : t -> SymSet.t
  val free_vars_list : t list -> SymSet.t
  val simp : Memory.struct_decls ->
             IT.t SymMap.t -> 
             bool Simplify.ITPairMap.t ->
             LCSet.t ->
             t ->
             t
end






type predicate_name = 
  | Owned of Sctypes.t
  | PName of string
[@@deriving eq, ord]


let value_sym = Sym.fresh_named "value"
let init_sym = Sym.fresh_named "init"

let owned_iargs _ct = []
let owned_oargs ct = 
  [(value_sym, BT.of_sct ct);
   (init_sym, BT.Bool)]
let q_owned_oargs ct = 
  [(value_sym, BT.Map (Integer, BT.of_sct ct));
   (init_sym, BT.Map (Integer, BT.Bool))]



module Make (O : Output) = struct

  type predicate = {
      name : predicate_name; 
      pointer: IT.t;            (* I *)
      permission: IT.t;         (* I *)
      iargs: IT.t list;         (* I *)
      oargs: O.t list;          (* O *)
    }
  [@@deriving eq, ord]

  type qpredicate = {
      name : predicate_name; 
      pointer: IT.t;            (* I *)
      q: Sym.t;
      step: int;
      permission: IT.t;         (* I, function of q *)
      iargs: IT.t list;         (* I, function of q *)
      oargs: O.t list;          (* O, function of q *)
    }
  [@@deriving eq, ord]

  type resource = 
    | P of predicate
    | Q of qpredicate
  [@@deriving eq, ord]

  type t = resource


  let pp_predicate_name = function
    | Owned ct -> !^"Owned" ^^ angles (Sctypes.pp ct)
    | PName pn -> !^pn

  let pp_predicate (p : predicate) =
    let args = 
      [IT.pp p.pointer;
       IT.pp p.permission] @
      List.map IT.pp (p.iargs) @ 
      List.map O.pp p.oargs 
    in
    c_app (pp_predicate_name p.name) args

  let pp_qpredicate (p : qpredicate) =
    let args = 
      [IT.pp p.pointer ^^^ plus ^^^ parens (Sym.pp p.q ^^^ star ^^^ !^(string_of_int p.step));
       IT.pp p.permission] @
      List.map IT.pp (p.iargs) @ 
      List.map O.pp p.oargs 
    in
    !^"each" ^^^ Sym.pp p.q ^^ dot ^^^
    c_app (pp_predicate_name p.name) args


  let pp = function
    | P p -> pp_predicate p
    | Q qp -> pp_qpredicate qp


  let json re : Yojson.Safe.t = 
    `String (Pp.plain (pp re))



  let alpha_rename_qpredicate (q' : Sym.t) (qp : qpredicate) : qpredicate = 
    let subst = make_subst [(qp.q, sym_ (q', BT.Integer))] in
    { name = qp.name;
      pointer = qp.pointer;
      q = q';
      step = qp.step;
      permission = IT.subst subst qp.permission;
      iargs = List.map (IT.subst subst) qp.iargs;
      oargs = List.map (O.subst subst) qp.oargs;
    }


  let subst_predicate substitution (p : predicate) = 
    {
      name = p.name;
      pointer = IT.subst substitution p.pointer;
      permission = IT.subst substitution p.permission;
      iargs = List.map (IT.subst substitution) p.iargs;
      oargs = List.map (O.subst substitution) p.oargs;
    }

  let subst_qpredicate substitution (qp : qpredicate) : qpredicate =
    let qp = 
      if SymSet.mem qp.q substitution.relevant
      then alpha_rename_qpredicate (Sym.fresh_same qp.q) qp 
      else qp
    in
    {
      name = qp.name;
      pointer = IT.subst substitution qp.pointer;
      q = qp.q;
      step = qp.step;
      permission = IT.subst substitution qp.permission;
      iargs = List.map (IT.subst substitution) qp.iargs;
      oargs = List.map (O.subst substitution) qp.oargs;
    }


let subst (substitution : IT.t Subst.t) = function
  | P p -> P (subst_predicate substitution p)
  | Q qp -> Q (subst_qpredicate substitution qp)




  let equal = equal_resource
  let compare = compare_resource


  let free_vars = function
    | P p -> 
       SymSet.union
         (IT.free_vars_list (p.pointer :: p.permission :: p.iargs))
         (O.free_vars_list p.oargs)
    | Q p -> 
       SymSet.union
         (IT.free_vars p.pointer)
         (SymSet.remove p.q
            (SymSet.union
               (IT.free_vars_list (p.permission :: p.iargs))
               (O.free_vars_list p.oargs)
         ))

  let free_vars_list l = 
    List.fold_left (fun acc sym -> 
        SymSet.union acc (free_vars sym)
      ) SymSet.empty l


  let free_input_vars = function
    | P p -> 
       IT.free_vars_list (p.pointer :: p.permission :: p.iargs)
    | Q p -> 
       SymSet.union 
         (IT.free_vars p.pointer)
         (SymSet.remove p.q (IT.free_vars_list (p.permission :: p.iargs)))

  let free_output_vars = function
    | P p -> O.free_vars_list p.oargs
    | Q p -> SymSet.remove p.q (O.free_vars_list p.oargs)

  let outputs = function
    | P p -> p.oargs
    | Q p -> p.oargs

  let quantifier = function
    | P p -> None
    | Q p -> Some (p.q, BT.Integer)

  let bound resource = match quantifier resource with
    | Some (s, _) -> SymSet.singleton s
    | None -> SymSet.empty



  open Simplify

  let simp_predicate structs values equalities lcs (p : predicate) = {
      name = p.name; 
      pointer = simp structs values equalities lcs p.pointer; 
      permission = simp structs values equalities lcs p.permission;
      iargs = List.map (simp structs values equalities lcs) p.iargs; 
      oargs = List.map (O.simp structs values equalities lcs) p.oargs; 
    }

  let simp_qpredicate structs values equalities lcs (qp : qpredicate) = 
    let old_q = qp.q in
    let qp = alpha_rename_qpredicate (Sym.fresh_same old_q) qp in
    let permission = Simplify.simp_flatten structs values equalities lcs qp.permission in
    let permission_lcs = LCSet.of_list (List.map LC.t_ permission) in
    let qp = {
        name = qp.name;
        pointer = simp structs values equalities lcs qp.pointer;
        q = qp.q;
        step = qp.step;
        permission = and_ permission;
        iargs = List.map (simp structs values equalities (LCSet.union permission_lcs lcs)) qp.iargs;
        oargs = List.map (O.simp structs values equalities (LCSet.union permission_lcs lcs)) qp.oargs;
      }
    in 
    alpha_rename_qpredicate old_q qp


  let simp structs values equalities lcs = function
    | P p -> P (simp_predicate structs values equalities lcs p)
    | Q qp -> Q (simp_qpredicate structs values equalities lcs qp)


    




  let simp_or_empty structs values equalities lcs resource = 
    match simp structs values equalities lcs resource with
    | P p when IT.is_false p.permission -> None
    | Q p when IT.is_false p.permission -> None
    | re -> Some re






end



module Requests = 
  Make (struct
      type t = BT.t
      let pp _ = underscore
      let subst _ o = o
      let equal = BT.equal
      let compare = BT.compare
      let free_vars _ = SymSet.empty
      let free_vars_list _ = SymSet.empty
      let simp _ _ _ _ bt = bt
    end)






module RE = struct 
  include 
    Make(struct 
        include IT 
        let simp = Simplify.simp        
      end)



  




  (* assumption: the resource is owned *)
  let derived_lc1 = function
    (* | Point p -> *)
    (*    [impl_ (and_ [p.permission; p.init],  *)
    (*            good_ (p.ct, p.value))] *)
    (* impl_ (p.permission,  *)
    (*        ne_ (p.pointer, null_)) *)
    | _ -> []
  
  
  (* assumption: both resources are owned at the same *)
  (* todo, depending on how much we need *)
  let derived_lc2 resource resource' =
    match resource, resource' with
    (* | Point p, Point p' ->  *)
    (*    [impl_ ( *)
    (*         and_ [p.permission; p'.permission], *)
    (*         ne_ (p.pointer, p'.pointer) *)
    (*       ) *)
    (*    ] *)
    (* | Point p, QPoint qp *)
    (* | QPoint qp, Point p -> *)
    (*    [] *)
    (* | QPoint qp, QPoint qp' -> *)
    (*    (\* todo: this requires all-quantified constraints *\) *)
    (*    [] *)
    | (P _ | Q _), _ ->
    (* | _, (P _ | QPredicate _) -> *)
       (* we don't know anything until we unpack: the resource could
          be "ownership-empty" *)
       []


  let pointer_facts =
    let rec aux acc = function
      | [] -> acc
      | r :: rs ->
         let acc = derived_lc1 r @ (List.concat_map (derived_lc2 r) rs) @ acc in 
         aux acc rs
    in
    fun resources -> aux [] resources








  let request_predicate (p : predicate) : Requests.predicate = {
      name = p.name;
      pointer = p.pointer;
      permission = p.permission;
      iargs = p.iargs;
      oargs = List.map IT.bt p.oargs;
    }

  let request_qpredicate (p : qpredicate) : Requests.qpredicate = {
      name = p.name;
      pointer = p.pointer;
      q = p.q;
      step = p.step;
      permission = p.permission;
      iargs = p.iargs;
      oargs = List.map IT.bt p.oargs;
    }


  let request = function
    | P p -> Requests.P (request_predicate p)
    | Q p -> Requests.Q (request_qpredicate p)

end

(* resources of the same type as a request, such that the resource
   can be used to fulfil the request *)
let same_type_resource req res = 
  match req, res with
  | Requests.P p1, RE.P p2 -> equal_predicate_name p1.name p2.name
  | Requests.Q p1, RE.P p2 -> equal_predicate_name p1.name p2.name
  | Requests.P p1, RE.Q p2 -> equal_predicate_name p1.name p2.name
  | Requests.Q p1, RE.Q p2 -> equal_predicate_name p1.name p2.name




