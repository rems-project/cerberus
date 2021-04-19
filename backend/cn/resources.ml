open Pp
open Simplify
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms
open IT



type predicate_name = 
  | Tag of BaseTypes.tag
  | Id of String.t

let predicate_name_pp = function
  | Tag tag -> Sym.pp tag
  | Id id -> !^id

let predicate_name_equal pn1 pn2 =
  match pn1, pn2 with
  | Tag t1, Tag t2 -> Sym.equal t1 t2
  | Id id1, Id id2 -> String.equal id1 id2
  | Tag _, _ -> false
  | Id _, _ -> false


type predicate = {
    name : predicate_name; 
    iargs: IT.t list;
    oargs: IT.t list;
    unused: bool;
  }



type point = {
    pointer: IT.t; 
    size: Z.t; 
    content: IT.t; 
    permission: IT.t;
  }

type qpoint = {
    qpointer: Sym.t; 
    size: Z.t; 
    content: IT.t; 
    permission: IT.t
  }


type t = 
  | Point of point
  | IteratedStar of qpoint
  | Predicate of predicate




type resource = t

let pp_predicate_name = function
  | Id id -> !^id
  | Tag tag -> !^"StoredStruct" ^^ parens (Sym.pp tag)

let pp_predicate {name; iargs; oargs; unused} =
  let args = List.map IT.pp (iargs @ oargs) @ [IT.pp (IT.bool_ unused)] in
  c_app (pp_predicate_name name) args

let pp = function
  | Point {pointer; size; content; permission} ->
     group (c_app !^"Points" [IT.pp pointer; IT.pp content; Z.pp size; IT.pp permission])
  | IteratedStar {qpointer; size; content; permission} ->
     group 
       (flow (break 1)
          [!^"forall" ^^^ Sym.pp qpointer ^^ dot;
           c_app !^"Points" [Sym.pp qpointer; IT.pp content; Z.pp size; IT.pp permission]])
  | Predicate p ->
     pp_predicate p
          
        



let json re : Yojson.Safe.t = 
  `String (Pp.plain (pp re))


let subst_var (subst: (Sym.t,Sym.t) Subst.t) = function
  | Point {pointer; size; content; permission} ->
     let pointer = IT.subst_var subst pointer in
     let content = IT.subst_var subst content in
     let permission = IT.subst_var subst permission in
     Point {pointer; size; content; permission}
  | IteratedStar {qpointer; size; content; permission} ->
     if Sym.equal subst.before qpointer then 
       IteratedStar {qpointer; size; content; permission}
     else if Sym.equal qpointer subst.after then
       let qpointer' = Sym.fresh () in
       let content = IT.subst_var {before=qpointer;after=qpointer'} content in
       let permission = IT.subst_var {before=qpointer;after=qpointer'} permission in
       let content = IT.subst_var subst content in
       let permission = IT.subst_var subst permission in
       IteratedStar {qpointer = qpointer'; size; content; permission}       
     else
       let content = IT.subst_var subst content in
       let permission = IT.subst_var subst permission in
       IteratedStar {qpointer; size; content; permission}
  | Predicate {name; iargs; oargs; unused} -> 
     let iargs = List.map (IT.subst_var subst) iargs in
     let oargs = List.map (IT.subst_var subst) oargs in
     (* let unused = IT.subst_var subst unused in *)
     Predicate {name; iargs; oargs; unused}



let subst_it (subst: (Sym.t,IT.t) Subst.t) resource =
  match resource with
  | Point {pointer; size; content; permission} ->
     let pointer = IT.subst_it subst pointer in
     let content = IT.subst_it subst content in
     let permission = IT.subst_it subst permission in
     Point {pointer; size; content; permission}
  | IteratedStar {qpointer; size; content; permission} ->
     if Sym.equal subst.before qpointer then 
       IteratedStar {qpointer; size; content; permission}
     else if SymSet.mem qpointer (IT.free_vars subst.after) then
       let qpointer' = Sym.fresh () in
       let content = IT.subst_var {before=qpointer;after=qpointer'} content in
       let permission = IT.subst_var {before=qpointer;after=qpointer'} permission in
       let content = IT.subst_it subst content in
       let permission = IT.subst_it subst permission in
       IteratedStar {qpointer = qpointer'; size; content; permission}
     else
       let content = IT.subst_it subst content in
       let permission = IT.subst_it subst permission in
       IteratedStar {qpointer; size; content; permission}
  | Predicate {name; iargs; oargs; unused} -> 
     let iargs = List.map (IT.subst_it subst) iargs in
     let oargs = List.map (IT.subst_it subst) oargs in
     (* let unused = IT.subst_it subst unused in *)
     Predicate {name; iargs; oargs; unused}



let subst_vars = Subst.make_substs subst_var



(* at the moment literal equality, no alpha renaming of IteratedStar
   quantifier *)
let equal t1 t2 = 
  match t1, t2 with
  | Point b1, Point b2 ->
     IT.equal b1.pointer b2.pointer &&
     Z.equal b1.size b2.size &&
     IT.equal b1.content b2.content &&
     IT.equal b1.permission b2.permission
  | IteratedStar b1, IteratedStar b2 ->
     Sym.equal b1.qpointer b2.qpointer &&
     Z.equal b1.size b2.size &&
     IT.equal b1.content b2.content &&
     IT.equal b1.permission b2.permission
  | Predicate p1, Predicate p2 ->
     predicate_name_equal p1.name p2.name && 
     List.equal IT.equal p1.iargs p2.iargs && 
     List.equal IT.equal p1.oargs p2.oargs &&
     (* IT.equal *) p1.unused = p2.unused
  | Point _, _ -> false
  | IteratedStar _, _ -> false
  | Predicate _, _ -> false








let free_vars = function
  | Point b -> 
     IT.free_vars_list [b.pointer; b.permission; b.content]
  | IteratedStar b -> 
     SymSet.remove b.qpointer 
       (IT.free_vars_list [b.permission; b.content])
  | Predicate p -> 
     IT.free_vars_list ((* p.unused :: *) (p.iargs @ p.oargs))

let free_vars_list l = 
  List.fold_left (fun acc sym -> 
      SymSet.union acc (free_vars sym)
    ) SymSet.empty l









(* auxiliary functions *)

(* derived information *)
let inputs = function
  | Point p -> [p.pointer; p.permission]
  (* the quantifier in IteratedStar is neither input nor output *)
  | IteratedStar p -> [p.permission]
  | Predicate p -> p.iargs

let outputs = function
  | Point b -> [b.content]
  | IteratedStar b -> [b.content]
  | Predicate p -> p.oargs


let permission = function
  | Point p -> p.permission
  | IteratedStar s -> s.permission
  | Predicate p when p.unused -> IT.q_ (1, 1)
  | Predicate p -> IT.q_ (0, 1)

let quantified = function
  | Point p -> []
  | IteratedStar p -> [(p.qpointer, BaseTypes.Loc)]
  | Predicate p -> []

(* assumption: resource is owned *)
let derived_constraint resource = 
  let open IT in
  match resource with
  | Point p -> 
     impl_ (gt_ (p.permission, q_ (0, 1)), not_ (eq_ (null_, p.pointer)))
  | IteratedStar p ->
     (* todo *)
     bool_ true
  | Predicate _ ->
     bool_ true


(* assumption: resource owned at the same time as resources' *)
(* todo, depending on how much we need *)
let derived_constraints resource resource' =
  let open IT in
  match resource, resource' with
  | Point p, Point p' -> 
     (* [impl_ (
      *      gt_ (add_ (p.permission, p'.permission), q_ (1, 1)),
      *      disjoint_ ((p.pointer, z_ p.size), (p'.pointer, z_ p'.size))
      * ); *)
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

let point (pointer, size) permission value =
  Point {pointer; size; content = value; permission}

let predicate predicate_name iargs oargs =
  Predicate {name = predicate_name; iargs; oargs; unused = true}


let char_region pointer size permission =
  let open IT in
  let q = Sym.fresh () in
  let qt = sym_ (q, BT.Loc) in
  let condition = 
    and_ [
        lePointer_ (pointer, qt);
        ltPointer_ (qt, addPointer_ (pointer, size));
      ]
  in
  let point = {
      qpointer = q;
      size = Z.of_int 1;
      content = nothing_ BT.Integer;
      permission = ite_ (condition, permission, q_ (0,1))
    }
  in
  IteratedStar point


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
let array pointer length element_size content permission =
  let open IT in
  let q = Sym.fresh () in
  let qt = sym_ (q, BT.Loc) in
  let qt_int = pointerToIntegerCast_ qt in
  let pointer_int = pointerToIntegerCast_ pointer in
  let it = div_ (sub_ (qt_int, pointer_int), z_ element_size) in
  let condition = 
    and_ [
        le_ (int_ 0, it);
        lt_ (it, length);
        eq_ (rem_f_ (sub_ (qt_int, pointer_int), z_ element_size), int_ 0);
      ]
  in
  let point = {
      qpointer = q;
      size = element_size;
      content = something_ (content it);
      permission = ite_ (condition, permission, q_ (0,1))
    }
  in
  IteratedStar point






let if_non_zero_frac resource = 
  if not (IT.zero_frac (permission resource))
  then Some resource else None

let simp lcs resource = 
  match resource with
  | Point {pointer; size; content; permission} ->
     let pointer = simp lcs pointer in
     let content = simp lcs content in
     let permission = simp lcs permission in
     if_non_zero_frac (Point {pointer; size; content; permission})
  | IteratedStar {qpointer; size; content; permission} ->
     let qpointer' = Sym.fresh () in
     let subst = Subst.{before=qpointer;after=qpointer'} in
     let content = simp lcs (IT.subst_var subst content) in
     let permission = simp lcs (IT.subst_var subst permission) in
     if_non_zero_frac (IteratedStar {qpointer = qpointer'; size; content; permission})
  | Predicate {name; iargs; oargs; unused} -> 
     let iargs = List.map (simp lcs) iargs in
     let oargs = List.map (simp lcs) oargs in
     (* let unused = IT.subst_var subst unused in *)
     if unused 
     then Some (Predicate {name; iargs; oargs; unused})
     else None






module External = struct

  open Memory
  open IT

  type t = 
    | E_Point of {
        pointer : IT.t;
        size: Z.t;
        content: IT.t;
        permission: IT.t;
      }
    | E_Iterated of {
        pointer: IT.t;               (* not a function of 'index' *)
        index: Sym.t;
        element_size: Z.t;
        length: IT.t;                (* not a function of 'index' *)
        content: IT.t;               (* function of 'index' *)
        permission: IT.t             (* function of 'index' *)
      }
    (* | E_Predicate of predicate *)

  let subst_it subst resource = 
    match resource with
    | E_Point {pointer; size; content; permission} ->
       let pointer = IT.subst_it subst pointer in
       let content = IT.subst_it subst content in
       let permission = IT.subst_it subst permission in
       E_Point {pointer; size; content; permission}
    | E_Iterated {pointer; index; length; element_size; content; permission} ->
       if Sym.equal subst.before index then 
         E_Iterated {pointer; index; length; element_size; content; permission}
       else if SymSet.mem index (IT.free_vars subst.after) then
         let index' = Sym.fresh () in
         let first_subst = Subst.{before=index;after=IT.sym_ (index', BT.Integer)} in
         let pointer = 
           IT.subst_it subst (IT.subst_it first_subst pointer) 
         in
         let content = IT.subst_it subst (IT.subst_it first_subst content) in
         let permission = IT.subst_it subst (IT.subst_it first_subst permission) in
         let length = IT.subst_it subst (IT.subst_it first_subst length) in
         E_Iterated {index = index'; pointer; length; element_size; content; permission}
       else
         let pointer = IT.subst_it subst pointer in
         let content = IT.subst_it subst content in
         let permission = IT.subst_it subst permission in
         let length = IT.subst_it subst length in
         E_Iterated {index; pointer; length; element_size; content; permission}
    (* | E_Predicate {name; iargs; oargs; unused} -> 
     *    let iargs = List.map (IT.subst_it subst) iargs in
     *    let oargs = List.map (IT.subst_it subst) oargs in
     *    (\* let unused = IT.subst_it subst unused in *\)
     *    E_Predicate {name; iargs; oargs; unused} *)

  let subst_its subst resource = Subst.make_substs subst_it subst resource



  let to_internal = 
    let open Subst in
    function
    | E_Point {pointer; size; content; permission} ->
       Point {pointer; size; content; permission}
    | E_Iterated {pointer; index; length; element_size; content; permission} ->
       let qpointer = Sym.fresh () in 
       let qpointer_t = sym_ (qpointer, BT.Loc) in
       let subst = {before = index; 
                    after = array_pointer_to_index pointer (z_ element_size) qpointer_t} in
       let permission = 
         ite_ (
             and_ [
                 le_ (int_ 0, array_pointer_to_index pointer (z_ element_size) qpointer_t);
                 lt_ (array_pointer_to_index pointer (z_ element_size) qpointer_t, length);
                 array_is_at_valid_index pointer (z_ element_size) qpointer_t
               ],
             IT.subst_it subst permission,
             q_ (0, 1)
           )
       in
       let content = IT.subst_it subst content in
       IteratedStar {qpointer; size = element_size; content; permission}



  let represents (layouts : Sym.t -> Memory.struct_layout) typ pointer ((ovalue : IT.t option), bt) permission =
    let rec aux (Sctypes.Sctype (_, t_)) pointer (ovalue, bt) =
      match t_ with
      | Void -> 
         Debug_ocaml.error "representation: Void"
      | Integer it ->
         [E_Point {
              pointer;
              size = Memory.size_of_integer_type it; 
              content = 
                begin match ovalue with
                | Some value -> something_ value
                | None -> nothing_ bt
                end; 
              permission
            }]
      | Pointer (_qualifiers, _t) ->
         [E_Point {
              pointer;
              size = Memory.size_of_pointer; 
              content =
                begin match ovalue with
                | Some value -> something_ value
                | None -> nothing_ bt
                end; 
              permission
            }]
      | Array (t, None) ->
         Debug_ocaml.error "representation: array of unknown length"
      | Array (t, Some n) ->
         let index = Sym.fresh () in 
         let index_t = sym_ (index, BT.Integer) in
         let representation' = 
           aux t pointer 
             (Option.map (fun value ->
                  app_ value [index_t])
                ovalue, 
              BT.of_sct t)
         in
         let length = int_ n in
         List.map (function
             | E_Point {pointer; size; content; permission} -> 
                E_Iterated {pointer; index; length; element_size = size; 
                            content; permission}
             | E_Iterated arr ->
                let substs = 
                  let open Subst in
                  [{before = arr.index; after = rem_f_ (index_t, arr.length)};
                   {before = index; after = rem_f_ (index_t, length)}]
                in
                let content = IT.subst_its substs arr.content in
                let length = mul_ (int_ n, arr.length) in
                let element_size = arr.element_size in
                let permission = IT.subst_its substs arr.permission in
                E_Iterated {pointer = arr.pointer; index; length; element_size; content; permission}
           ) representation'
      | Struct tag -> 
         List.concat_map (fun {offset;size;member_or_padding}  ->
             let member_pointer = addPointer_ (pointer, z_ offset) in
             begin match member_or_padding with
             | None -> 
                [E_Point {pointer = member_pointer; size; permission; content = nothing_ BT.Integer}]
             | Some (member, ct) ->
                aux ct member_pointer 
                  (Option.map (fun value ->
                       (structMember_ ~member_bt:(BT.of_sct ct) 
                          (tag, value, member))
                     ) ovalue,
                  BT.of_sct ct)
             end
           ) (layouts tag)
      | Function _ ->
         Debug_ocaml.error "representation: Function"
    in
    aux typ pointer (ovalue, bt)

end




let represent layouts typ pointer ovalue permission =
  List.map External.to_internal
    (External.represents layouts typ pointer ovalue permission)
