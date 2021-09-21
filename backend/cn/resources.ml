open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT
module LC = LogicalConstraints







type predicate_name = string
let pp_predicate_name = Pp.string
let predicate_name_equal = String.equal





module type Output = sig

  type t
  val pp : t -> document
  val subst : IT.t Subst.t -> t -> t
  val equal : t -> t -> bool
  val free_vars : t -> SymSet.t
  val free_vars_list : t list -> SymSet.t

end




module Make (O : Output) = struct


  type point = {
      ct: Sctypes.t; 
      pointer: IT.t; 
      permission: IT.t;
      value: O.t; 
      init: O.t;
    }

  type qpoint = {
      ct: Sctypes.t; 
      qpointer: Sym.t;
      permission: IT.t;
      value: O.t; 
      init: O.t;
    }


  type predicate = {
      name : predicate_name; 
      pointer: IT.t;
      permission: IT.t;
      iargs: IT.t list;
      oargs: O.t list;
    }

  type qpredicate = {
      name : predicate_name; 
      qpointer: Sym.t;
      permission: IT.t;         (* function of qpointer *)
      iargs: IT.t list;         (* function of qpointer *)
      oargs: O.t list;          (* function of qpointer *)
    }


  type t = 
    | Point of point
    | QPoint of qpoint
    | Predicate of predicate
    | QPredicate of qpredicate

  type resource = t



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
       Sym.pp p.qpointer; 
       IT.pp p.permission;
       O.pp p.value; 
       O.pp p.init;
      ] 
    in
    flow (break 1)
      [!^"each" ^^^ Sym.pp p.qpointer ^^ dot; c_app !^"Points" args]


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
      [Sym.pp p.qpointer;
       IT.pp p.permission] @
      List.map IT.pp (p.iargs) @ 
      List.map O.pp p.oargs 
    in
    !^"for" ^^^ Sym.pp p.qpointer ^^ dot ^^^
    c_app (pp_predicate_name p.name) args


  let pp = function
    | Point p -> pp_point p
    | QPoint p -> pp_qpoint p
    | Predicate p -> pp_predicate p
    | QPredicate p -> pp_qpredicate p



  let json re : Yojson.Safe.t = 
    `String (Pp.plain (pp re))



  let alpha_rename_qpoint qpointer' (qp : qpoint) = 
    let subst = [(qp.qpointer, sym_ (qpointer', BT.Loc))] in
    { ct = qp.ct;
      qpointer = qpointer';
      permission = IT.subst subst qp.permission;
      value = O.subst subst qp.value;
      init = O.subst subst qp.init;
    }


  let alpha_rename_qpredicate qpointer' (qp : qpredicate) = 
    let subst = [(qp.qpointer, sym_ (qpointer', BT.Loc))] in
    { name = qp.name;
      qpointer = qpointer';
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

  let subst_qpoint substitution (qp : qpoint) = 
    let qp = alpha_rename_qpoint 
               (Sym.fresh_same qp.qpointer) qp in
    {
      ct = qp.ct;
      qpointer = qp.qpointer;
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

  let subst_qpredicate substitution (qp : qpredicate) =
    let qp = alpha_rename_qpredicate 
               (Sym.fresh_same qp.qpointer) qp in
    {
      name = qp.name;
      qpointer = qp.qpointer;
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




  (* literal equality, no alpha renaming of IteratedStar quantifier *)
  let equal t1 t2 = 
    match t1, t2 with
    | Point b1, Point b2 ->
       Sctypes.equal b1.ct b2.ct &&
       IT.equal b1.pointer b2.pointer &&
       IT.equal b1.permission b2.permission &&
       O.equal b1.value b2.value &&
       O.equal b1.init b2.init
    | QPoint b1, QPoint b2 ->
       Sctypes.equal b1.ct b2.ct &&
       Sym.equal b1.qpointer b2.qpointer &&
       IT.equal b1.permission b2.permission &&
       O.equal b1.value b2.value &&
       O.equal b1.init b2.init
    | Predicate p1, Predicate p2 ->
       predicate_name_equal p1.name p2.name && 
       IT.equal p1.pointer p2.pointer && 
       IT.equal p1.permission p2.permission &&
       List.equal IT.equal p1.iargs p2.iargs && 
       List.equal O.equal p1.oargs p2.oargs
    | QPredicate p1, QPredicate p2 ->
       predicate_name_equal p1.name p2.name && 
       Sym.equal p1.qpointer p2.qpointer && 
       IT.equal p1.permission p2.permission &&
       List.equal IT.equal p1.iargs p2.iargs && 
       List.equal O.equal p1.oargs p2.oargs
    | Point _, _ -> false
    | QPoint _, _ -> false
    | Predicate _, _ -> false
    | QPredicate _, _ -> false




  let free_vars = function
    | Point b -> 
       SymSet.union
         (IT.free_vars_list [b.pointer; b.permission])
         (O.free_vars_list [b.value; b.init])
    | QPoint b -> 
       SymSet.remove b.qpointer 
         (SymSet.union
            (IT.free_vars b.permission) 
            (O.free_vars_list [b.value; b.init]))
    | Predicate p -> 
       SymSet.union
         (IT.free_vars_list (p.pointer :: p.permission :: p.iargs))
         (O.free_vars_list p.oargs)
    | QPredicate p -> 
       SymSet.remove p.qpointer 
         (SymSet.union 
            (IT.free_vars_list (p.permission :: p.iargs))
            (O.free_vars_list p.oargs))

  let free_vars_list l = 
    List.fold_left (fun acc sym -> 
        SymSet.union acc (free_vars sym)
      ) SymSet.empty l



end



module Requests = 
  Make (struct
      type t = BT.t
      let pp _ = underscore
      let subst _ o = o
      let equal = BT.equal
      let free_vars _ = SymSet.empty
      let free_vars_list _ = SymSet.empty
    end)






module RE = struct 
  include Make(IT)

  (* auxiliary functions *)

  (* derived information *)


  (* let pointer = function
   *   | Point p -> Some p.pointer
   *   | QPoint p -> None
   *   | Predicate p -> Some p.pointer
   *   | QPredicate p -> Some None *)

  let inputs = function
    | Point p -> [p.pointer; p.permission]
    | QPoint p -> [p.permission]
    | Predicate p -> p.pointer :: p.permission :: p.iargs
    | QPredicate p -> p.permission :: p.iargs

  let outputs = function
    | Point b -> [b.value; b.init]
    | QPoint b -> [b.value; b.init]
    | Predicate p -> p.oargs
    | QPredicate p -> p.oargs

  let quantifier = function
    | Point p -> None
    | QPoint p -> Some (p.qpointer, BT.Loc)
    | Predicate p -> None
    | QPredicate p -> Some (p.qpointer, BT.Loc)

  let bound resource = match quantifier resource with
    | Some (s, _) -> SymSet.singleton s
    | None -> SymSet.empty






  (* assumption: resource is owned *)
  let derived_constraint resource = 
    let open IT in
    let lc = match resource with
      | Point p -> 
         impl_ (gt_ (p.permission, q_ (0, 1)), 
                not_ (eq_ (null_, p.pointer)))
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
            gt_ (add_ (p.permission, p'.permission), q_ (1, 1)),
            ne_ (p.pointer, p'.pointer)
          )
         )
    | Predicate _, _
    | _, Predicate _ -> 
       LC.T (bool_ true)
    | _ ->
       (* todo *)
       LC.T (bool_ true)



  (* construction *)


  let array_offset_of_index ~item_ct ~index = 
    mul_ (index, int_ (Memory.size_of_ctype item_ct))

  let array_index_to_pointer ~base ~item_ct ~index =
    addPointer_ (base, array_offset_of_index ~item_ct ~index)
  
  let array_offset_of_pointer ~base ~pointer = 
    sub_ (pointerToIntegerCast_ pointer, 
          pointerToIntegerCast_ base)

  let array_pointer_to_index ~base ~item_ct ~pointer =
    div_ (array_offset_of_pointer ~base ~pointer, 
          int_ (Memory.size_of_ctype item_ct))
  
  (* check this *)
  let array_permission ~base ~item_ct ~length ~qpointer ~permission =
    let offset = array_offset_of_pointer ~base ~pointer:qpointer in
    let index = array_pointer_to_index ~base ~item_ct ~pointer:qpointer in
    let condition = 
      and_ [lePointer_ (base, qpointer);
            eq_ (rem_ (offset, int_ (Memory.size_of_ctype item_ct)), int_ 0);
            le_ (int_ 0, index); lt_ (index, length)]
    in
    ite_ (condition, permission, q_ (0,1))




  let simp lcs resource =
    let simp_it = Simplify.simp lcs in
    match resource with
    | Point p ->
       Point {
           ct = p.ct;
           pointer = simp_it p.pointer; 
           permission = simp_it p.permission;
           value = simp_it p.value;
           init = simp_it p.init; 
         }
    | QPoint qp ->
       let qp = alpha_rename_qpoint 
                  (Sym.fresh_same qp.qpointer) qp in
       QPoint 
         { ct = qp.ct;
           qpointer = qp.qpointer;
           permission = simp_it qp.permission;
           value = simp_it qp.value;
           init = simp_it qp.init;
         }
    | Predicate p -> 
       Predicate {
           name = p.name; 
           pointer = simp_it p.pointer; 
           permission = simp_it p.permission;
           iargs = List.map simp_it p.iargs; 
           oargs = List.map simp_it p.oargs; 
         }
    | QPredicate qp -> 
       let qp = alpha_rename_qpredicate 
                  (Sym.fresh_same qp.qpointer) qp in
       QPredicate {
           name = qp.name;
           qpointer = qp.qpointer;
           permission = simp_it qp.permission;
           iargs = List.map simp_it qp.iargs;
           oargs = List.map simp_it qp.oargs;
         }




  let simp_or_empty lcs resource = 
    match simp lcs resource with
    | Point p when IT.zero_frac p.permission -> None
    | QPoint p when IT.zero_frac p.permission -> None
    | Predicate p when IT.is_false p.permission -> None
    | QPredicate p when IT.is_false p.permission -> None
    | re -> Some re





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
           qpointer = p.qpointer;
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
           qpointer = p.qpointer;
           name = p.name;
           permission = p.permission;
           iargs = p.iargs;
           oargs = List.map IT.bt p.oargs;
         }

end

