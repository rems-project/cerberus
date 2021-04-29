open Pp
open Simplify
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


type point = {
    pointer: IT.t; 
    size: Z.t; 
    permission: IT.t;
    value: IT.t; 
    init: IT.t;
  }

type qpoint = {
    qpointer: Sym.t;
    size: Z.t; 
    permission: IT.t;
    value: IT.t; 
    init: IT.t;
  }


type predicate = {
    name : predicate_name; 
    pointer: IT.t;
    iargs: IT.t list;
    oargs: IT.t list;
    unused: bool;
  }

type qpredicate = {
    start: IT.t;
    step: IT.t;
    stop: IT.t;
    moved: IT.t list;
    unused: bool;
    name : predicate_name; 
    i: Sym.t;                   (* assumed of integer type *)
    iargs: IT.t list;           (* function of i *)
    oargs: IT.t list;           (* function of i *)
  }




type t = 
  | Point of point
  | QPoint of qpoint
  | Predicate of predicate
  | QPredicate of qpredicate

type resource = t



let pp_predicate (p : predicate) =
  if p.unused then 
    let args = List.map IT.pp (p.pointer :: p.iargs @ p.oargs) in
    c_app (pp_predicate_name p.name) args
  else
    parens (Pp.string "used predicate")

let pp_qpredicate (qp : qpredicate) =
  if qp.unused then
    let args = List.map IT.pp (qp.iargs @ qp.oargs) in
    parens (separate (semi ^^ space) 
              ([Sym.pp qp.i ^^^ equals ^^^ IT.pp qp.start;
                Sym.pp qp.i ^^^ !^"<=" ^^^ IT.pp qp.stop;
                Sym.pp qp.i ^^^ plus ^^^ IT.pp qp.step;
                brackets (separate comma (List.map IT.pp qp.moved))])) ^^^
      braces (c_app (pp_predicate_name qp.name) args)
  else
    parens (Pp.string "used iterated predicate")

let pp_point (p : point) =
  let args = 
    [IT.pp p.pointer; IT.pp p.value; IT.pp p.init;
     Z.pp p.size; IT.pp p.permission]
  in
  c_app !^"Points" args

let pp_qpoint p = 
  let args = 
    [Sym.pp p.qpointer; IT.pp p.value; IT.pp p.init;
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
  let qpointer' = Sym.fresh () in
  let subst = {before=qp.qpointer;after=qpointer'} in
  { qpointer = qpointer';
    size = qp.size;
    value = IT.subst_var subst qp.value;
    init = IT.subst_var subst qp.init;
    permission = IT.subst_var subst qp.permission }


let alpha_rename_qpredicate qp = 
  let i' = Sym.fresh () in
  let subst = {before=qp.i;after=i'} in
  { start = qp.start;
    step = qp.step;
    stop = qp.stop;
    moved = qp.moved;
    unused = qp.unused;
    name = qp.name;
    i = i';
    iargs = List.map (IT.subst_var subst) qp.iargs;
    oargs = List.map (IT.subst_var subst) qp.oargs }



let subst_var (subst: (Sym.t,Sym.t) Subst.t) resource = 
  match resource with
  | Point {pointer; size; value; init; permission} ->
     let pointer = IT.subst_var subst pointer in
     let value = IT.subst_var subst value in
     let init = IT.subst_var subst init in
     let permission = IT.subst_var subst permission in
     Point {pointer; size; value; init; permission}
  | QPoint {qpointer; size; value; init; permission} ->
     if Sym.equal subst.before qpointer then 
       QPoint {qpointer; size; value; init; permission}
     else if Sym.equal qpointer subst.after then
       let qpointer' = Sym.fresh () in
       let subst' = {before=qpointer;after=qpointer'} in
       let value = IT.subst_var subst' value in
       let init = IT.subst_var subst' init in
       let permission = IT.subst_var subst' permission in
       let value = IT.subst_var subst value in
       let init = IT.subst_var subst init in
       let permission = IT.subst_var subst permission in
       QPoint {qpointer = qpointer'; size; value; init; permission}
     else
       let value = IT.subst_var subst value in
       let init = IT.subst_var subst init in
       let permission = IT.subst_var subst permission in
       QPoint {qpointer; size; value; init; permission}
  | Predicate {name; pointer; iargs; oargs; unused} -> 
     let pointer = IT.subst_var subst pointer in
     let iargs = List.map (IT.subst_var subst) iargs in
     let oargs = List.map (IT.subst_var subst) oargs in
     (* let unused = IT.subst_var subst unused in *)
     Predicate {name; pointer; iargs; oargs; unused}
  | QPredicate {start; stop; step; moved; unused; name; i; iargs; oargs} ->
     let start = IT.subst_var subst start in
     let stop = IT.subst_var subst stop in
     let step = IT.subst_var subst step in
     let moved = List.map (IT.subst_var subst) moved in
     if Sym.equal i subst.before then
       QPredicate {start; stop; step; moved; unused; i; name; iargs; oargs}
     else if Sym.equal i subst.after then
       let i' = Sym.fresh () in
       let iargs = List.map (IT.subst_var {before=i;after=i'}) iargs in
       let oargs = List.map (IT.subst_var {before=i;after=i'}) oargs in
       let iargs = List.map (IT.subst_var subst) iargs in
       let oargs = List.map (IT.subst_var subst) oargs in
       QPredicate {start; stop; step; moved; unused; name; i = i'; iargs; oargs}
     else
       let iargs = List.map (IT.subst_var subst) iargs in
       let oargs = List.map (IT.subst_var subst) oargs in
       QPredicate {start; stop; step; moved; unused; name; i; iargs; oargs}


let subst_it (subst: (Sym.t,IT.t) Subst.t) resource =
  match resource with
  | Point {pointer; size; value; init; permission} ->
     let pointer = IT.subst_it subst pointer in
     let value = IT.subst_it subst value in
     let init = IT.subst_it subst init in
     let permission = IT.subst_it subst permission in
     Point {pointer; size; value; init; permission}
  | QPoint {qpointer; size; value; init; permission} ->
     if Sym.equal subst.before qpointer then 
       QPoint {qpointer; size; value; init; permission}
     else if SymSet.mem qpointer (IT.free_vars subst.after) then
       let qpointer' = Sym.fresh () in
       let subst' = {before=qpointer;after=qpointer'} in
       let value = IT.subst_var subst' value in
       let init = IT.subst_var subst' init in
       let permission = IT.subst_var subst' permission in
       let value = IT.subst_it subst value in
       let init = IT.subst_it subst init in
       let permission = IT.subst_it subst permission in
       QPoint {qpointer = qpointer'; size; value; init; permission}
     else
       let value = IT.subst_it subst value in
       let init = IT.subst_it subst init in
       let permission = IT.subst_it subst permission in
       QPoint {qpointer; size; value; init; permission}
  | Predicate {name; pointer; iargs; oargs; unused} -> 
     let pointer = IT.subst_it subst pointer in 
     let iargs = List.map (IT.subst_it subst) iargs in
     let oargs = List.map (IT.subst_it subst) oargs in
     (* let unused = IT.subst_it subst unused in *)
     Predicate {name; pointer; iargs; oargs; unused}
  | QPredicate {start; stop; step; moved; unused; name; i; iargs; oargs} ->
     let start = IT.subst_it subst start in
     let stop = IT.subst_it subst stop in
     let step = IT.subst_it subst step in
     let moved = List.map (IT.subst_it subst) moved in
     if Sym.equal i subst.before then
       QPredicate {start; stop; step; moved; unused; name; i; iargs; oargs}
     else if SymSet.mem i (IT.free_vars subst.after) then
       let i' = Sym.fresh () in
       let iargs = List.map (IT.subst_var {before=i;after=i'}) iargs in
       let oargs = List.map (IT.subst_var {before=i;after=i'}) oargs in
       let iargs = List.map (IT.subst_it subst) iargs in
       let oargs = List.map (IT.subst_it subst) oargs in
       QPredicate {start; stop; step; moved; unused; name; i = i'; iargs; oargs}
     else
       let iargs = List.map (IT.subst_it subst) iargs in
       let oargs = List.map (IT.subst_it subst) oargs in
       QPredicate {start; stop; step; moved; unused; name; i; iargs; oargs}



let subst_vars = Subst.make_substs subst_var



(* literal equality, no alpha renaming of IteratedStar quantifier *)
let equal t1 t2 = 
  match t1, t2 with
  | Point b1, Point b2 ->
     IT.equal b1.pointer b2.pointer &&
     Z.equal b1.size b2.size &&
     IT.equal b1.value b2.value &&
     IT.equal b1.init b2.init &&
     IT.equal b1.permission b2.permission
  | QPoint b1, QPoint b2 ->
     Sym.equal b1.qpointer b2.qpointer &&
     Z.equal b1.size b2.size &&
     IT.equal b1.value b2.value &&
     IT.equal b1.init b2.init &&
     IT.equal b1.permission b2.permission
  | Predicate p1, Predicate p2 ->
     predicate_name_equal p1.name p2.name && 
     IT.equal p1.pointer p2.pointer && 
     List.equal IT.equal p1.iargs p2.iargs && 
     List.equal IT.equal p1.oargs p2.oargs &&
     (* IT.equal *) p1.unused = p2.unused
  | QPredicate p1, QPredicate p2 ->
     IT.equal p1.start p2.start &&
     IT.equal p1.stop p2.stop &&
     IT.equal p1.step p2.step &&
     List.equal IT.equal p1.moved p2.moved &&
     p1.unused = p2.unused && 
     predicate_name_equal p1.name p2.name && 
     Sym.equal p1.i p2.i &&
     List.equal IT.equal p1.iargs p2.iargs && 
     List.equal IT.equal p1.oargs p2.oargs
  | Point _, _ -> false
  | QPoint _, _ -> false
  | Predicate _, _ -> false
  | QPredicate _, _ -> false








let free_vars = function
  | Point b -> 
     IT.free_vars_list [b.pointer; b.permission; b.value; b.init]
  | QPoint b -> 
     SymSet.remove b.qpointer 
       (IT.free_vars_list [b.permission; b.value; b.init])
  | Predicate p -> 
     IT.free_vars_list ((* p.unused :: *) (p.iargs @ p.oargs))
  | QPredicate p -> 
     SymSet.union 
       (IT.free_vars_list ([p.start; p.stop; p.step] @ p.moved) )
       (SymSet.remove p.i (IT.free_vars_list (p.iargs @ p.oargs)))

let free_vars_list l = 
  List.fold_left (fun acc sym -> 
      SymSet.union acc (free_vars sym)
    ) SymSet.empty l









(* auxiliary functions *)

(* derived information *)
let inputs = function
  | Point p -> [p.pointer; p.permission]
  (* the quantifier in IteratedStar is neither input nor output *)
  | QPoint p -> [p.permission]
  | Predicate p -> p.iargs
  | QPredicate p -> p.start :: p.stop :: p.step :: p.iargs

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



let is_qpredicate_instance qpredicate pointer = 
  and_ 
    ([lePointer_ (qpredicate.start, pointer);
      lePointer_ (pointer, qpredicate.stop);
      eq_ (rem_f_ (sub_ (pointerToIntegerCast_ pointer, 
                         pointerToIntegerCast_ qpredicate.start), 
                   qpredicate.step),
          int_ 0)
     ] 
     @
     List.map (ne__ pointer) qpredicate.moved
    )

let qpredicate_index_to_pointer qpredicate i = 
  addPointer_ (qpredicate.start, mul_ (qpredicate.step, i))

let qpredicate_pointer_to_index qpredicate pointer = 
  div_ (sub_ (pointerToIntegerCast_ pointer, 
              pointerToIntegerCast_ qpredicate.start), 
        qpredicate.step)














let simp lcs resource = 
  match resource with
  | Point {pointer; size; value; init; permission} ->
     let pointer = simp lcs pointer in
     let value = simp lcs value in
     let init = simp lcs init in
     let permission = simp lcs permission in
     if IT.zero_frac permission
     then None 
     else Some (Point {pointer; size; value; init; permission})
  | QPoint {qpointer; size; value; init; permission} ->
     let qpointer' = Sym.fresh () in
     let subst = {before=qpointer;after=qpointer'} in
     let value = simp lcs (IT.subst_var subst value) in
     let init = simp lcs (IT.subst_var subst init) in
     let permission = simp lcs (IT.subst_var subst permission) in
     if IT.zero_frac permission
     then None 
     else Some (QPoint {qpointer = qpointer'; size; value; init; permission})
  | Predicate {name; pointer; iargs; oargs; unused} -> 
     let pointer = simp lcs pointer in
     let iargs = List.map (simp lcs) iargs in
     let oargs = List.map (simp lcs) oargs in
     (* let unused = IT.subst_var subst unused in *)
     if not unused then None
     else Some (Predicate {name; pointer; iargs; oargs; unused})
  | QPredicate {start; stop; step; name; iargs; oargs; i; unused; moved} -> 
     let i' = Sym.fresh () in
     let iargs = List.map (IT.subst_var {before=i;after=i'}) iargs in
     let oargs = List.map (IT.subst_var {before=i;after=i'}) oargs in
     let start = simp lcs start in
     let stop = simp lcs stop in
     let step = simp lcs step in
     let iargs = List.map (simp lcs) iargs in
     let oargs = List.map (simp lcs) oargs in
     let moved = List.map (simp lcs) moved in
     if not unused then None
     else Some (QPredicate {start; stop; step; name; iargs; oargs; i = i'; unused; moved})



