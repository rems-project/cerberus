open Pp
open Subst
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT
module LC = LogicalConstraints




module type Output = sig
  type t
  val pp : t -> document
  val subst : IT.t Subst.t -> t -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val free_vars : t -> SymSet.t
  val free_vars_list : t list -> SymSet.t
  val simp : ?some_known_facts:IT.t list ->
             Memory.struct_decls ->
             LC.t list ->
             t ->
             t
end




module Make (O : Output) = struct


  type point = {
      ct: Sctypes.t; 
      pointer: IT.t;            (* I *)
      permission: IT.t;         (* I *)
      value: O.t;               (* O *)
      init: O.t;                (* O *)
    }
  [@@deriving eq, ord]

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


  


  let simp_it struct_decls lcs extra_facts it = 
    Simplify.simp struct_decls lcs 
      ~some_known_facts:extra_facts it 
      
  let simp_o struct_decls lcs extra_facts = 
    O.simp ~some_known_facts:extra_facts
      struct_decls lcs
  
  let simp_point ?(only_outputs=false) struct_decls lcs (p : point) =
    let simp_it = simp_it struct_decls lcs in
    let simp_o = simp_o struct_decls lcs in
    {
      ct = p.ct;
      pointer = if only_outputs then p.pointer else simp_it [] p.pointer; 
      permission = if only_outputs then p.permission else simp_it [] p.permission;
      value = simp_o [] p.value;
      init = simp_o [] p.init; 
    }

  let simp_qpoint ?(only_outputs=false) struct_decls lcs (qp : qpoint) = 
    let simp_it = simp_it struct_decls lcs in
    let simp_o = simp_o struct_decls lcs in
    let old_q = qp.q in
    let qp = alpha_rename_qpoint (Sym.fresh_same old_q) qp in
    let permission = Simplify.simp_flatten struct_decls lcs qp.permission in
    let qp = { 
        ct = qp.ct;
        pointer = if only_outputs then qp.pointer else simp_it [] qp.pointer;
        q = qp.q;
        permission = if only_outputs then qp.permission else and_ permission;
        value = simp_o permission qp.value;
        init = simp_o permission qp.init;
      }
    in
    alpha_rename_qpoint old_q qp

  let simp_predicate ?(only_outputs=false) struct_decls lcs (p : predicate) = 
    let simp_it = simp_it struct_decls lcs in
    let simp_o = simp_o struct_decls lcs in
    {
      name = p.name; 
      pointer = if only_outputs then p.pointer else simp_it [] p.pointer; 
      permission = if only_outputs then p.permission else simp_it [] p.permission;
      iargs = if only_outputs then p.iargs else List.map (simp_it []) p.iargs; 
      oargs = List.map (simp_o []) p.oargs; 
    }

  let simp_qpredicate ?(only_outputs=false) struct_decls lcs (qp : qpredicate) = 
    let simp_it = simp_it struct_decls lcs in
    let simp_o = simp_o struct_decls lcs in
    let old_q = qp.q in
    let qp = alpha_rename_qpredicate (Sym.fresh_same old_q) qp in
    let permission = Simplify.simp_flatten struct_decls lcs qp.permission in
    let qp = {
        name = qp.name;
        pointer = if only_outputs then qp.pointer else simp_it [] qp.pointer;
        q = qp.q;
        step = qp.step;
        permission = if only_outputs then qp.permission else and_ permission;
        iargs = if only_outputs then qp.iargs else List.map (simp_it permission) qp.iargs;
        oargs = List.map (simp_o permission) qp.oargs;
      }
    in 
    alpha_rename_qpredicate old_q qp


  let simp struct_decls lcs resource =
    match resource with
    | Point p -> Point (simp_point struct_decls lcs p)
    | QPoint qp -> QPoint (simp_qpoint struct_decls lcs qp)
    | Predicate p -> Predicate (simp_predicate struct_decls lcs p)
    | QPredicate qp -> QPredicate (simp_qpredicate struct_decls lcs qp)


    




  let simp_or_empty struct_decls lcs resource = 
    match simp struct_decls lcs resource with
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
      let simp ?(some_known_facts:_) _ _ bt = bt
    end)






module RE = struct 
  include 
    Make(struct 
        include IT 
        let simp = Simplify.simp        
      end)



  




  (* assumption: resource is owned *)
  let derived_constraint resource = 
    let lc = match resource with
      | Point p -> 
         bool_ true
         (* impl_ (p.permission,  *)
         (*        ne_ (p.pointer, null_)) *)
      | _ ->
         bool_ true
    in
    LC.t_ lc
  
  
  (* assumption: resource owned at the same time as resources' *)
  (* todo, depending on how much we need *)
  let derived_constraints resource resource' =
    (* let open IT in *)
    match resource, resource' with
    | Point p, Point p' -> 
       LC.T (impl_ (
            and_ [p.permission; p'.permission],
            ne_ (p.pointer, p'.pointer)
          )
         )
    | Point p, QPoint qp
    | QPoint qp, Point p ->
       LC.T (bool_ true)
       (* (\* copying and adapting code from point_request logic *\) *)
       (* let base = qp.pointer in *)
       (* let item_size = int_ (Memory.size_of_ctype qp.ct) in *)
       (* let offset = array_offset_of_pointer ~base ~pointer:p.pointer in *)
       (* let index = array_pointer_to_index ~base ~item_size ~pointer:p.pointer in *)
       (* let impossible_match =  *)
       (*   and_ [lePointer_ (base, p.pointer); *)
       (*         eq_ (rem_ (offset, item_size), int_ 0); *)
       (*         IT.subst (IT.make_subst [(qp.q, index)]) qp.permission;  *)
       (*         p.permission]  *)
       (* in *)
       (* LC.T (not_ impossible_match) *)
    | QPoint qp, QPoint qp' ->
       (* todo: this requires all-quantified constraints *)
       LC.T (bool_ true)
    | (Predicate _ | QPredicate _), _
    | _, (Predicate _ | QPredicate _) ->
       (* we don't know anything until we unpack: the resource could
          be "ownership-empty" *)
       LC.T (bool_ true)











  let request = function
    | Point p -> 
       Requests.Point { 
           ct = p.ct;
           pointer = p.pointer;
           permission = p.permission;
           value = IT.bt p.value;
           init = IT.bt p.init;
         }
    | QPoint p -> 
       Requests.QPoint { 
           ct = p.ct;
           pointer = p.pointer;
           q = p.q;
           permission = p.permission;
           value = IT.bt p.value;
           init = IT.bt p.init;
         }
    | Predicate p -> 
       Requests.Predicate {
           name = p.name;
           pointer = p.pointer;
           permission = p.permission;
           iargs = p.iargs;
           oargs = List.map IT.bt p.oargs;
         }
    | QPredicate p ->
       Requests.QPredicate {
           name = p.name;
           pointer = p.pointer;
           q = p.q;
           step = p.step;
           permission = p.permission;
           iargs = p.iargs;
           oargs = List.map IT.bt p.oargs;
         }


end

