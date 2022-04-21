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




module Make (O : Output) = struct

  (* ownership + "init --> good(value)" *)
  type point = {
      ct: Sctypes.t; 
      pointer: IT.t;            (* I *)
      permission: IT.t;         (* I *)
      value: O.t;               (* O *)
      init: O.t;                (* O *)
    }
  [@@deriving eq, ord]

  (* ownership + "init --> good(value)" *)
  type qpoint = {
      ct: Sctypes.t; 
      pointer: IT.t;            (* I *)
      q: Sym.t;
      permission: IT.t;         (* I, function of q *)
      value: O.t;               (* O, function of q *)
      init: O.t;                (* O, function of q *)
    }
  [@@deriving eq, ord]


  type predicate = {
      name : string; 
      pointer: IT.t;            (* I *)
      permission: IT.t;         (* I *)
      iargs: IT.t list;         (* I *)
      oargs: O.t list;          (* O *)
    }
  [@@deriving eq, ord]

  type qpredicate = {
      name : string; 
      pointer: IT.t;            (* I *)
      q: Sym.t;
      step: int;
      permission: IT.t;         (* I, function of q *)
      iargs: IT.t list;         (* I, function of q *)
      oargs: O.t list;          (* O, function of q *)
    }
  [@@deriving eq, ord]

  type resource = 
    | Point of point
    | QPoint of qpoint
    | Predicate of predicate
    | QPredicate of qpredicate
  [@@deriving eq, ord]

  type t = resource


  let pp_point (p : point) =
    let args = 
      [Sctypes.pp p.ct; 
       IT.pp p.pointer; 
       IT.pp p.permission;
       O.pp p.value; 
       O.pp p.init;
      ]
    in
    c_app !^"Points" args

  let pp_qpoint (p : qpoint) = 
    let args = 
      [Sctypes.pp p.ct; 
       IT.pp p.pointer ^^^ plus ^^^ parens (Sym.pp p.q ^^^ star ^^^ !^(string_of_int (Memory.size_of_ctype p.ct)));
       IT.pp p.permission;
       O.pp p.value; 
       O.pp p.init;
      ] 
    in
    flow (break 1)
      [!^"each" ^^^ Sym.pp p.q ^^ dot; c_app !^"Points" args]


  let pp_predicate (p : predicate) =
    let args = 
      [IT.pp p.pointer;
       IT.pp p.permission] @
      List.map IT.pp (p.iargs) @ 
      List.map O.pp p.oargs 
    in
    c_app (string p.name) args

  let pp_qpredicate (p : qpredicate) =
    let args = 
      [IT.pp p.pointer ^^^ plus ^^^ parens (Sym.pp p.q ^^^ star ^^^ !^(string_of_int p.step));
       IT.pp p.permission] @
      List.map IT.pp (p.iargs) @ 
      List.map O.pp p.oargs 
    in
    !^"each" ^^^ Sym.pp p.q ^^ dot ^^^
    c_app (string p.name) args


  let pp = function
    | Point p -> pp_point p
    | QPoint qp -> pp_qpoint qp
    | Predicate p -> pp_predicate p
    | QPredicate qp -> pp_qpredicate qp


  let json re : Yojson.Safe.t = 
    `String (Pp.plain (pp re))



  let alpha_rename_qpoint (q' : Sym.t) (qp : qpoint) : qpoint = 
    let subst = make_subst [(qp.q, sym_ (q', BT.Integer))] in
    { ct = qp.ct;
      pointer = qp.pointer;
      q = q';
      permission = IT.subst subst qp.permission;
      value = O.subst subst qp.value;
      init = O.subst subst qp.init;
    }


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


  let subst_point substitution (p : point) = 
    {
      ct = p.ct;
      pointer = IT.subst substitution p.pointer;
      permission = IT.subst substitution p.permission;
      value = O.subst substitution p.value;
      init = O.subst substitution p.init;
    }

  let subst_qpoint substitution (qp : qpoint) : qpoint = 
    let qp = 
      if SymSet.mem qp.q substitution.relevant 
      then alpha_rename_qpoint (Sym.fresh_same qp.q) qp 
      else qp
    in
    {
      ct = qp.ct;
      pointer = IT.subst substitution qp.pointer;
      q = qp.q;
      permission = IT.subst substitution qp.permission;
      value = O.subst substitution qp.value;
      init = O.subst substitution qp.init;
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


let subst (substitution : IT.t Subst.t) resource =
  match resource with
  | Point p -> Point (subst_point substitution p)
  | QPoint qp -> QPoint (subst_qpoint substitution qp)
  | Predicate p -> Predicate (subst_predicate substitution p)
  | QPredicate qp -> QPredicate (subst_qpredicate substitution qp)




  let equal = equal_resource
  let compare = compare_resource


  let free_vars = function
    | Point b -> 
       SymSet.union
         (IT.free_vars_list [b.pointer; b.permission])
         (O.free_vars_list [b.value; b.init])
    | QPoint b -> 
       SymSet.union
         (IT.free_vars b.pointer)
         (SymSet.remove b.q (
              SymSet.union (IT.free_vars b.permission)
                (O.free_vars_list [b.value; b.init])
         ))
    | Predicate p -> 
       SymSet.union
         (IT.free_vars_list (p.pointer :: p.permission :: p.iargs))
         (O.free_vars_list p.oargs)
    | QPredicate p -> 
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
    | Point p -> 
       IT.free_vars_list [p.pointer; p.permission]
    | QPoint p -> 
       SymSet.union 
         (IT.free_vars p.pointer)
         (SymSet.remove p.q (IT.free_vars p.permission))
    | Predicate p -> 
       IT.free_vars_list (p.pointer :: p.permission :: p.iargs)
    | QPredicate p -> 
       SymSet.union 
         (IT.free_vars p.pointer)
         (SymSet.remove p.q (IT.free_vars_list (p.permission :: p.iargs)))

  let free_output_vars = function
    | Point b -> 
       O.free_vars_list [b.value; b.init]
    | QPoint b -> 
       SymSet.remove b.q (O.free_vars_list [b.value; b.init])
    | Predicate p -> 
       O.free_vars_list p.oargs
    | QPredicate p -> 
       SymSet.remove p.q (O.free_vars_list p.oargs)

  let outputs = function
    | Point b -> [b.value; b.init]
    | QPoint b -> [b.value; b.init]
    | Predicate p -> p.oargs
    | QPredicate p -> p.oargs

  let quantifier = function
    | Point p -> None
    | QPoint p -> Some (p.q, BT.Integer)
    | Predicate p -> None
    | QPredicate p -> Some (p.q, BT.Integer)

  let bound resource = match quantifier resource with
    | Some (s, _) -> SymSet.singleton s
    | None -> SymSet.empty


  


  open Simplify

  let simp_point structs values equalities lcs (p : point) ={
      ct = p.ct;
      pointer = simp structs values equalities lcs p.pointer; 
      permission = simp structs values equalities lcs p.permission;
      value = O.simp structs values equalities lcs p.value;
      init = O.simp structs values equalities lcs p.init; 
    }

  let simp_qpoint structs values equalities lcs (qp : qpoint) = 
    let old_q = qp.q in
    let qp = alpha_rename_qpoint (Sym.fresh_same old_q) qp in
    let permission = Simplify.simp_flatten structs values equalities lcs qp.permission in
    let permission_lcs = LCSet.of_list (List.map LC.t_ permission) in
    let qp = { 
        ct = qp.ct;
        pointer = simp structs values equalities lcs qp.pointer;
        q = qp.q;
        permission = and_ permission;
        value = O.simp structs values equalities (LCSet.union permission_lcs lcs) qp.value;
        init = O.simp structs values equalities (LCSet.union permission_lcs lcs) qp.init;
      }
    in
    alpha_rename_qpoint old_q qp

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
    | Point p -> Point (simp_point structs values equalities lcs p)
    | QPoint qp -> QPoint (simp_qpoint structs values equalities lcs qp)
    | Predicate p -> Predicate (simp_predicate structs values equalities lcs p)
    | QPredicate qp -> QPredicate (simp_qpredicate structs values equalities lcs qp)


    




  let simp_or_empty structs values equalities lcs resource = 
    match simp structs values equalities lcs resource with
    | Point p when IT.is_false p.permission -> None
    | QPoint p when IT.is_false p.permission -> None
    | Predicate p when IT.is_false p.permission -> None
    | QPredicate p when IT.is_false p.permission -> None
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
    | Point p, Point p' -> 
       [impl_ (
            and_ [p.permission; p'.permission],
            ne_ (p.pointer, p'.pointer)
          )
       ]
    | Point p, QPoint qp
    | QPoint qp, Point p ->
       []
    | QPoint qp, QPoint qp' ->
       (* todo: this requires all-quantified constraints *)
       []
    | (Predicate _ | QPredicate _), _
    | _, (Predicate _ | QPredicate _) ->
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








  let request_point (p : point) : Requests.point = { 
      ct = p.ct;
      pointer = p.pointer;
      permission = p.permission;
      value = IT.bt p.value;
      init = IT.bt p.init;
    }
  
  let request_qpoint (p : qpoint) : Requests.qpoint = { 
      ct = p.ct;
      pointer = p.pointer;
      q = p.q;
      permission = p.permission;
      value = IT.bt p.value;
      init = IT.bt p.init;
    }

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
    | Point p -> Requests.Point (request_point p)
    | QPoint p -> Requests.QPoint (request_qpoint p)
    | Predicate p -> Requests.Predicate (request_predicate p)
    | QPredicate p -> Requests.QPredicate (request_qpredicate p)

end

(* resources of the same type as a request, such that the resource
   can be used to fulfil the request *)
let same_type_resource req res = begin match (req, res) with
  | (Requests.Point p, RE.Point p2) -> Sctypes.equal p.ct p2.ct
  | (Requests.QPoint qp, RE.Point p2) -> Sctypes.equal qp.ct p2.ct
  | (Requests.Point p, RE.QPoint qp2) -> Sctypes.equal p.ct qp2.ct
  | (Requests.QPoint qp, RE.QPoint qp2) -> Sctypes.equal qp.ct qp2.ct
  | (Requests.Predicate p, RE.Predicate p2) -> String.equal p.name p2.name
  | (Requests.QPredicate qp, RE.Predicate p2) -> String.equal qp.name p2.name
  | (Requests.Predicate p, RE.QPredicate qp2) -> String.equal p.name qp2.name
  | (Requests.QPredicate qp, RE.QPredicate qp2) -> String.equal qp.name qp2.name
  | _ -> false
  end


