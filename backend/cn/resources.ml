open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT
open Subst







type predicate_name = 
  | Ctype of Sctypes.t
  | Id of String.t

let pp_predicate_name = function
  | Id id -> !^id
  | Ctype ct -> parens (Sctypes.pp ct)

let predicate_name_equal pn1 pn2 =
  match pn1, pn2 with
  | Ctype t1, Ctype t2 -> Sctypes.equal t1 t2
  | Id id1, Id id2 -> String.equal id1 id2
  | Ctype _, _ -> false
  | Id _, _ -> false





module type Output = sig

  type t
  val pp : t -> document
  val subst_var : (Sym.t, Sym.t) Subst.t -> t -> t
  val subst_it : (Sym.t, IT.t) Subst.t -> t -> t
  val equal : t -> t -> bool
  val free_vars : t -> SymSet.t
  val free_vars_list : t list -> SymSet.t

end




module Make (O : Output) = struct


  type point = {
      pointer: IT.t; 
      size: Z.t; 
      permission: IT.t;
      value: O.t; 
      init: O.t;
    }

  type qpoint = {
      qpointer: Sym.t;
      size: Z.t; 
      permission: IT.t;
      value: O.t; 
      init: O.t;
    }


  type predicate = {
      name : predicate_name; 
      pointer: IT.t;
      iargs: IT.t list;
      oargs: O.t list;
      unused: bool;
    }

  type qpredicate = {
      pointer: IT.t;
      element_size: IT.t;
      length: IT.t;
      moved: IT.t list;
      unused: bool;
      name : predicate_name; 
      i: Sym.t;                   (* assumed of integer type *)
      iargs: IT.t list;           (* function of i *)
      oargs: O.t list;         (* function of i *)
    }


  type t = 
    | Point of point
    | QPoint of qpoint
    | Predicate of predicate
    | QPredicate of qpredicate

  type resource = t



  let pp_predicate (p : predicate) =
    if p.unused then 
      let args = List.map IT.pp (p.pointer :: p.iargs) @ List.map O.pp p.oargs in
      c_app (pp_predicate_name p.name) args
    else
      parens (Pp.string "used predicate")

  let pp_qpredicate (qp: qpredicate) =
    if not qp.unused then
      parens (Pp.string "used iterated predicate")
    else
      !^"for" ^^
      parens (separate (semi ^^ space) 
                ([Sym.pp qp.i ^^^ equals ^^^ !^"0";
                  Sym.pp qp.i ^^^ langle ^^^ IT.pp qp.length;
                  Sym.pp qp.i ^^^ plus ^^^ !^"1"])) ^^^
        let args = 
          let pointer_arg = addPointer_ (qp.pointer, sym_ (qp.i, BT.Integer)) in
          List.map IT.pp (pointer_arg :: qp.iargs) @
            List.map O.pp qp.oargs in
        braces (c_app (pp_predicate_name qp.name) args) ^^^
        c_comment (!^"moved" ^^ colon ^^ 
                     brackets (separate_map comma IT.pp qp.moved) )

  let pp_point (p : point) =
    let args = 
      [IT.pp p.pointer; O.pp p.value; O.pp p.init;
       Z.pp p.size; IT.pp p.permission]
    in
    c_app !^"Points" args

  let pp_qpoint p = 
    let args = 
      [Sym.pp p.qpointer; O.pp p.value; O.pp p.init;
       Z.pp p.size; IT.pp p.permission] 
    in
    flow (break 1)
      [!^"forall" ^^^ Sym.pp p.qpointer ^^ dot; c_app !^"Points" args]

  let pp = function
    | Point p -> pp_point p
    | QPoint p -> pp_qpoint p
    | Predicate p -> pp_predicate p
    | QPredicate p -> pp_qpredicate p



  let json re : Yojson.Safe.t = 
    `String (Pp.plain (pp re))



  let alpha_rename_qpoint qp = 
    let qpointer' = Sym.fresh_same qp.qpointer in
    let subst = {before=qp.qpointer;after=qpointer'} in
    { qpointer = qpointer';
      size = qp.size;
      value = O.subst_var subst qp.value;
      init = O.subst_var subst qp.init;
      permission = IT.subst_var subst qp.permission }


  let alpha_rename_qpredicate qp = 
    let i' = Sym.fresh_same qp.i in
    let subst = {before=qp.i;after=i'} in
    { pointer = qp.pointer;
      element_size = qp.element_size;
      length = qp.length;
      moved = qp.moved;
      unused = qp.unused;
      name = qp.name;
      i = i';
      iargs = List.map (IT.subst_var subst) qp.iargs;
      oargs = List.map (O.subst_var subst) qp.oargs }



  let subst_var (subst: (Sym.t,Sym.t) Subst.t) resource = 
    match resource with
    | Point {pointer; size; value; init; permission} ->
       let pointer = IT.subst_var subst pointer in
       let value = O.subst_var subst value in
       let init = O.subst_var subst init in
       let permission = IT.subst_var subst permission in
       Point {pointer; size; value; init; permission}
    | QPoint {qpointer; size; value; init; permission} ->
       if Sym.equal subst.before qpointer then 
         QPoint {qpointer; size; value; init; permission}
       else if Sym.equal qpointer subst.after then
         let qpointer' = Sym.fresh_same qpointer in
         let subst' = {before=qpointer;after=qpointer'} in
         let value = O.subst_var subst' value in
         let init = O.subst_var subst' init in
         let permission = IT.subst_var subst' permission in
         let value = O.subst_var subst value in
         let init = O.subst_var subst init in
         let permission = IT.subst_var subst permission in
         QPoint {qpointer = qpointer'; size; value; init; permission}
       else
         let value = O.subst_var subst value in
         let init = O.subst_var subst init in
         let permission = IT.subst_var subst permission in
         QPoint {qpointer; size; value; init; permission}
    | Predicate {name; pointer; iargs; oargs; unused} -> 
       let pointer = IT.subst_var subst pointer in
       let iargs = List.map (IT.subst_var subst) iargs in
       let oargs = List.map (O.subst_var subst) oargs in
       (* let unused = IT.subst_var subst unused in *)
       Predicate {name; pointer; iargs; oargs; unused}
    | QPredicate {pointer; element_size; length; moved; unused; name; i; iargs; oargs} ->
       let pointer = IT.subst_var subst pointer in
       let element_size = IT.subst_var subst element_size in
       let length = IT.subst_var subst length in
       let moved = List.map (IT.subst_var subst) moved in
       if Sym.equal i subst.before then
         QPredicate {pointer; element_size; length; moved; unused; i; name; iargs; oargs}
       else if Sym.equal i subst.after then
         let i' = Sym.fresh_same i in
         let iargs = List.map (IT.subst_var {before=i;after=i'}) iargs in
         let oargs = List.map (O.subst_var {before=i;after=i'}) oargs in
         let iargs = List.map (IT.subst_var subst) iargs in
         let oargs = List.map (O.subst_var subst) oargs in
         QPredicate {pointer; element_size; length; moved; unused; name; i = i'; iargs; oargs}
       else
         let iargs = List.map (IT.subst_var subst) iargs in
         let oargs = List.map (O.subst_var subst) oargs in
         QPredicate {pointer; element_size; length; moved; unused; name; i; iargs; oargs}


  let subst_it (subst: (Sym.t,IT.t) Subst.t) resource =
    match resource with
    | Point {pointer; size; value; init; permission} ->
       let pointer = IT.subst_it subst pointer in
       let value = O.subst_it subst value in
       let init = O.subst_it subst init in
       let permission = IT.subst_it subst permission in
       Point {pointer; size; value; init; permission}
    | QPoint {qpointer; size; value; init; permission} ->
       if Sym.equal subst.before qpointer then 
         QPoint {qpointer; size; value; init; permission}
       else if SymSet.mem qpointer (IT.free_vars subst.after) then
         let qpointer' = Sym.fresh_same qpointer in
         let subst' = {before=qpointer;after=qpointer'} in
         let value = O.subst_var subst' value in
         let init = O.subst_var subst' init in
         let permission = IT.subst_var subst' permission in
         let value = O.subst_it subst value in
         let init = O.subst_it subst init in
         let permission = IT.subst_it subst permission in
         QPoint {qpointer = qpointer'; size; value; init; permission}
       else
         let value = O.subst_it subst value in
         let init = O.subst_it subst init in
         let permission = IT.subst_it subst permission in
         QPoint {qpointer; size; value; init; permission}
    | Predicate {name; pointer; iargs; oargs; unused} -> 
       let pointer = IT.subst_it subst pointer in 
       let iargs = List.map (IT.subst_it subst) iargs in
       let oargs = List.map (O.subst_it subst) oargs in
       (* let unused = IT.subst_it subst unused in *)
       Predicate {name; pointer; iargs; oargs; unused}
    | QPredicate {pointer; element_size; length; moved; unused; name; i; iargs; oargs} ->
       let pointer = IT.subst_it subst pointer in
       let element_size = IT.subst_it subst element_size in
       let length = IT.subst_it subst length in
       let moved = List.map (IT.subst_it subst) moved in
       if Sym.equal i subst.before then
         QPredicate {pointer; element_size; length; moved; unused; name; i; iargs; oargs}
       else if SymSet.mem i (IT.free_vars subst.after) then
         let i' = Sym.fresh_same i in
         let iargs = List.map (IT.subst_var {before=i;after=i'}) iargs in
         let oargs = List.map (O.subst_var {before=i;after=i'}) oargs in
         let iargs = List.map (IT.subst_it subst) iargs in
         let oargs = List.map (O.subst_it subst) oargs in
         QPredicate {pointer; element_size; length; moved; unused; name; i = i'; iargs; oargs}
       else
         let iargs = List.map (IT.subst_it subst) iargs in
         let oargs = List.map (O.subst_it subst) oargs in
         QPredicate {pointer; element_size; length; moved; unused; name; i; iargs; oargs}



  let subst_vars = Subst.make_substs subst_var



  (* literal equality, no alpha renaming of IteratedStar quantifier *)
  let equal t1 t2 = 
    match t1, t2 with
    | Point b1, Point b2 ->
       IT.equal b1.pointer b2.pointer &&
       Z.equal b1.size b2.size &&
       O.equal b1.value b2.value &&
       O.equal b1.init b2.init &&
       IT.equal b1.permission b2.permission
    | QPoint b1, QPoint b2 ->
       Sym.equal b1.qpointer b2.qpointer &&
       Z.equal b1.size b2.size &&
       O.equal b1.value b2.value &&
       O.equal b1.init b2.init &&
       IT.equal b1.permission b2.permission
    | Predicate p1, Predicate p2 ->
       predicate_name_equal p1.name p2.name && 
       IT.equal p1.pointer p2.pointer && 
       List.equal IT.equal p1.iargs p2.iargs && 
       List.equal O.equal p1.oargs p2.oargs &&
       (* IT.equal *) p1.unused = p2.unused
    | QPredicate p1, QPredicate p2 ->
       IT.equal p1.pointer p2.pointer &&
       IT.equal p1.element_size p2.element_size &&
       IT.equal p1.length p2.length &&
       List.equal IT.equal p1.moved p2.moved &&
       p1.unused = p2.unused && 
       predicate_name_equal p1.name p2.name && 
       Sym.equal p1.i p2.i &&
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
         (IT.free_vars_list ((* p.unused :: *) p.iargs))
         (O.free_vars_list p.oargs)
    | QPredicate p -> 
       SymSet.union 
         (IT.free_vars_list ([p.pointer; p.element_size; p.length] @ p.moved) )
         (SymSet.remove p.i (
              SymSet.union 
                (IT.free_vars_list p.iargs)
                (O.free_vars_list p.oargs)))

  let free_vars_list l = 
    List.fold_left (fun acc sym -> 
        SymSet.union acc (free_vars sym)
      ) SymSet.empty l




  let qpredicate_index_to_pointer qp i = 
    addPointer_ (qp.pointer, mul_ (qp.element_size, i))

  let qpredicate_offset_of_pointer qp pointer = 
    sub_ (pointerToIntegerCast_ pointer, 
          pointerToIntegerCast_ qp.pointer)

  let qpredicate_pointer_to_index qp pointer = 
    div_ (qpredicate_offset_of_pointer qp pointer, qp.element_size)

  let is_pointer_within_qpredicate_range qp pointer = 
    let offset = qpredicate_offset_of_pointer qp pointer in
    let index = div_ (offset, qp.element_size) in
    and_ [le_ (int_ 0, index);
          lt_ (index, qp.length);
          eq_ (rem_f_ (offset, qp.element_size), int_ 0)]


  let is_qpredicate_instance_pointer qp pointer = 
    and_ (is_pointer_within_qpredicate_range qp pointer ::
          List.map (ne__ pointer) qp.moved)

  let is_qpredicate_instance_index qp index = 
    let pointer = qpredicate_index_to_pointer qp index in
    and_ (le_ (int_ 0, index) ::
          lt_ (index, qp.length) ::
          List.map (ne__ pointer) qp.moved)


end



module Requests = 
  Make (struct
      type t = BT.t
      let pp _ = underscore
      let subst_var _ o = o
      let subst_it _ o = o
      let equal = BT.equal
      let free_vars _ = SymSet.empty
      let free_vars_list _ = SymSet.empty
    end)


module RE = struct 
  include Make(IT)

  (* auxiliary functions *)

  (* derived information *)
  let inputs = function
    | Point p -> [p.pointer; p.permission]
    (* the quantifier in IteratedStar is neither input nor output *)
    | QPoint p -> [p.permission]
    | Predicate p -> p.iargs
    | QPredicate p -> p.pointer :: p.element_size :: p.length :: p.iargs

  let outputs = function
    | Point b -> [b.value; b.init]
    | QPoint b -> [b.value; b.init]
    | Predicate p -> p.oargs
    | QPredicate p -> p.oargs @ p.moved


  let quantified = function
    | Point p -> []
    | QPoint p -> [(p.qpointer, BT.Loc)]
    | Predicate p -> []
    | QPredicate p -> [(p.i, BT.Integer)]

  (* assumption: resource is owned *)
  let derived_constraint resource = 
    let open IT in
    match resource with
    | Point p -> 
       impl_ (gt_ (p.permission, q_ (0, 1)), not_ (eq_ (null_, p.pointer)))
    | QPoint p ->
       (* todo *)
       bool_ true
    | Predicate _ ->
       bool_ true
    | QPredicate _ ->
       bool_ true


  (* assumption: resource owned at the same time as resources' *)
  (* todo, depending on how much we need *)
  let derived_constraints resource resource' =
    let open IT in
    match resource, resource' with
    | Point p, Point p' -> 
        (* for now *)
        [impl_ (
            gt_ (add_ (p.permission, p'.permission), q_ (1, 1)),
            ne_ (p.pointer, p'.pointer)
          )
       ]
    | Predicate _, _
    | _, Predicate _ -> 
       []
    | _ ->
       (* todo *)
       []



  (* construction *)

  let point (pointer, size) permission value init =
    Point {pointer; size; value; init; permission}


  let predicateP predicate_name pointer iargs oargs =
    {name = predicate_name; pointer; iargs; oargs; unused = true}

  let predicate predicate_name pointer iargs oargs =
    Predicate (predicateP predicate_name pointer iargs oargs)



  let array_index_to_pointer base element_size index =
    addPointer_ (base, mul_ (element_size, index))

  let array_pointer_to_index base element_size pointer =
    div_ (sub_ (pointerToIntegerCast_ pointer, 
                pointerToIntegerCast_ base), element_size)

  let array_is_at_valid_index base element_size pointer =
    eq_ (rem_f_ (sub_ (pointerToIntegerCast_ pointer, 
                       pointerToIntegerCast_ base), element_size),
         int_ 0)





  (* check this *)
  let array q start length element_size value init permission =
    let open IT in
    let qt = sym_ (q, BT.Loc) in
    let qt_int = pointerToIntegerCast_ qt in
    let start_int = pointerToIntegerCast_ start in
    let it = div_ (sub_ (qt_int, start_int), z_ element_size) in
    let condition = 
      and_ [
          le_ (int_ 0, it);
          lt_ (it, length);
          eq_ (rem_f_ (sub_ (qt_int, start_int), z_ element_size), int_ 0);
        ]
    in
    let point = {
        qpointer = q;
        size = element_size;
        value = value;
        init = init;
        permission = ite_ (condition, permission, q_ (0,1))
      }
    in
    QPoint point






  let simp lcs resource =
    let open Simplify in
    match resource with
    | Point {pointer; size; value; init; permission} ->
       let pointer = simp lcs pointer in
       let value = simp lcs value in
       let init = simp lcs init in
       let permission = simp lcs permission in
       Point {pointer; size; value; init; permission}
    | QPoint {qpointer; size; value; init; permission} ->
       let qpointer' = Sym.fresh_same qpointer in
       let subst = {before=qpointer;after=qpointer'} in
       let value = simp lcs (IT.subst_var subst value) in
       let init = simp lcs (IT.subst_var subst init) in
       let permission = simp lcs (IT.subst_var subst permission) in
       QPoint {qpointer = qpointer'; size; value; init; permission}
    | Predicate {name; pointer; iargs; oargs; unused} -> 
       let pointer = simp lcs pointer in
       let iargs = List.map (simp lcs) iargs in
       let oargs = List.map (simp lcs) oargs in
       (* let unused = IT.subst_var subst unused in *)
       Predicate {name; pointer; iargs; oargs; unused}
    | QPredicate {pointer; element_size; length; name; iargs; oargs; i; unused; moved} -> 
       let i' = Sym.fresh_same i in
       let iargs = List.map (IT.subst_var {before=i;after=i'}) iargs in
       let oargs = List.map (IT.subst_var {before=i;after=i'}) oargs in
       let pointer = simp lcs pointer in
       let element_size = simp lcs element_size in
       let length = simp lcs length in
       let iargs = List.map (simp lcs) iargs in
       let oargs = List.map (simp lcs) oargs in
       let moved = List.map (simp lcs) moved in
       QPredicate {pointer; element_size; length; name; iargs; oargs; i = i'; unused; moved}



  let simp_or_empty lcs resource = 
    match simp lcs resource with
    | Point p when IT.zero_frac p.permission -> None
    | QPoint p when IT.zero_frac p.permission -> None
    | Predicate p when not p.unused -> None
    | QPredicate p when not p.unused -> None
    | re -> Some re



  let request = function
    | Point p -> 
       Requests.Point { 
           pointer = p.pointer;
           size = p.size;
           value = IT.bt p.value;
           init = IT.bt p.init;
           permission = p.permission;
         }
    | QPoint p -> 
       Requests.QPoint { 
           qpointer = p.qpointer;
           size = p.size;
           value = IT.bt p.value;
           init = IT.bt p.init;
           permission = p.permission;
         }
    | Predicate p -> 
       Requests.Predicate {
           name = p.name;
           pointer = p.pointer;
           iargs = p.iargs;
           oargs = List.map IT.bt p.oargs;
           unused = p.unused;
         }
    | QPredicate p ->
       Requests.QPredicate {
           pointer = p.pointer;
           element_size = p.element_size;
           length = p.length;
           moved = p.moved;
           unused = p.unused;
           name = p.name;
           i = p.i;
           iargs = p.iargs;
           oargs = List.map IT.bt p.oargs;
         }

end




