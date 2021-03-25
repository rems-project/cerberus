open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module IT = IndexTerms

type size = Z.t


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

(* for error reporting only *)
type block_type = 
  | Nothing
  | Uninit
  | Padding

type point_content = 
  | Block of block_type
  | Value of IT.t

type point = {
    pointer: IT.t; 
    size: Z.t; 
    content: point_content; 
    permission: IT.t
  }

type qpoint = {
    qpointer: Sym.t; 
    size: Z.t; 
    content: point_content; 
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
     begin match content with
     | Block block_type ->
        let rname = match block_type with
          | Nothing -> !^"Block"
          | Uninit -> !^"Uninit"
          | Padding -> !^"Padding"
        in
        group (c_app rname [IT.pp pointer; Z.pp size; IT.pp permission])
     | Value v ->
        group (c_app !^"Points" [IT.pp pointer; IT.pp v; Z.pp size; IT.pp permission])
     end
  | IteratedStar {qpointer; size; content; permission} ->
     begin match content with
     | Block block_type ->
        let rname = match block_type with
          | Nothing -> !^"Block"
          | Uninit -> !^"Uninit"
          | Padding -> !^"Padding"
        in
        group 
          (flow (break 1) 
             [!^"forall" ^^^ Sym.pp qpointer ^^ dot;
              c_app rname [Sym.pp qpointer; Z.pp size; IT.pp permission]])
     | Value v ->
        group 
          (flow (break 1)
             [!^"forall" ^^^ Sym.pp qpointer ^^ dot;
              c_app !^"Points" [Sym.pp qpointer; IT.pp v; Z.pp size; IT.pp permission]])
     end
  | Predicate p ->
     pp_predicate p
          
        



let json re : Yojson.Safe.t = 
  `String (Pp.plain (pp re))

let subst_var_content subst content =
  match content with
  | Block block_type -> Block block_type
  | Value v -> Value (IT.subst_var subst v)

let subst_var (subst: (Sym.t,Sym.t) Subst.t) = function
  | Point {pointer; size; content; permission} ->
     let pointer = IT.subst_var subst pointer in
     let content = subst_var_content subst content in
     let permission = IT.subst_var subst permission in
     Point {pointer; size; content; permission}
  | IteratedStar {qpointer; size; content; permission} ->
     if Sym.equal subst.before qpointer then 
       IteratedStar {qpointer; size; content; permission}
     else
       let content = subst_var_content subst content in
       let permission = IT.subst_var subst permission in
       IteratedStar {qpointer; size; content; permission}
  | Predicate {name; iargs; oargs; unused} -> 
     let iargs = List.map (IT.subst_var subst) iargs in
     let oargs = List.map (IT.subst_var subst) oargs in
     (* let unused = IT.subst_var subst unused in *)
     Predicate {name; iargs; oargs; unused}


let subst_it_content subst content =
  match content with
  | Block block_type -> Block block_type
  | Value v -> Value (IT.subst_it subst v)

let subst_it (subst: (Sym.t,IT.t) Subst.t) resource =
  match resource with
  | Point {pointer; size; content; permission} ->
     let pointer = IT.subst_it subst pointer in
     let content = subst_it_content subst content in
     let permission = IT.subst_it subst permission in
     Point {pointer; size; content; permission}
  | IteratedStar {qpointer; size; content; permission} ->
     if Sym.equal subst.before qpointer then 
       IteratedStar {qpointer; size; content; permission}
     else
       let content = subst_it_content subst content in
       let permission = IT.subst_it subst permission in
       IteratedStar {qpointer; size; content; permission}
  | Predicate {name; iargs; oargs; unused} -> 
     let iargs = List.map (IT.subst_it subst) iargs in
     let oargs = List.map (IT.subst_it subst) oargs in
     (* let unused = IT.subst_it subst unused in *)
     Predicate {name; iargs; oargs; unused}



let subst_vars = Subst.make_substs subst_var

let block_type_equal b1 b2 = 
  match b1, b2 with
  | Nothing, Nothing -> true
  | Uninit, Uninit -> true
  | Padding, Padding -> true
  | Nothing, _ -> false
  | Uninit, _ -> false
  | Padding, _ -> false

(* at the moment literal equality, no alpha renaming of IteratedStar
   quantifier *)
let equal t1 t2 = 
  match t1, t2 with
  | Point b1, Point b2 ->
     IT.equal b1.pointer b2.pointer &&
     Z.equal b1.size b2.size &&
     begin match b1.content, b2. content with
     | Block bt1, Block bt2 -> block_type_equal bt1 bt2 
     | Value v1, Value v2 -> IT.equal v1 v2
     | _, _ -> false
     end &&
     IT.equal b1.permission b2.permission
  | IteratedStar b1, IteratedStar b2 ->
     Sym.equal b1.qpointer b2.qpointer &&
     Z.equal b1.size b2.size &&
     begin match b1.content, b2. content with
     | Block bt1, Block bt2 -> block_type_equal bt1 bt2 
     | Value v1, Value v2 -> IT.equal v1 v2
     | _, _ -> false
     end &&
     IT.equal b1.permission b2.permission
  | Predicate p1, Predicate p2 ->
     predicate_name_equal p1.name p2.name && 
     List.equal IT.equal p1.iargs p2.iargs && 
     List.equal IT.equal p1.oargs p2.oargs &&
     (* IT.equal *) p1.unused = p2.unused
  | Point _, _ -> false
  | IteratedStar _, _ -> false
  | Predicate _, _ -> false



(* Block unifies with Blocks of other block type *)
let unify_content c c' res = 
  let open Option in
  match c, c' with
  | Block _, Block _ -> return res
  | Value v, Value v' -> IT.unify v v' res
  | _, _ -> fail


(* requires equality on inputs, unifies outputs *)
let unify r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Point b, Point b' 
       when IT.equal b.pointer b'.pointer &&
            Z.equal b.size b'.size &&
            IT.equal b.permission b'.permission ->
     (* Block unifies with Blocks of other block type *)
     unify_content b.content b'.content res
  | IteratedStar b, IteratedStar b' when
         Z.equal b.size b'.size ->
     let b = 
       let subst = Subst.{before = b.qpointer; after = b'.qpointer} in
       let content = subst_var_content subst b.content in
       let permission = IT.subst_var subst b.permission in
       {b with qpointer = b'.qpointer; content; permission}
     in
     if IT.equal b.permission b'.permission 
     then unify_content b.content b'.content res
     else fail
  | Predicate p, Predicate p' 
       when predicate_name_equal p.name p'.name &&
            List.equal IT.equal p.iargs p'.iargs &&
            List.length p.oargs = List.length p'.oargs &&
            (* IT.equal *) p.unused = p'.unused ->
     List.fold_left (fun ores (sym1,sym2) ->
         let@ res = ores in
         IT.unify sym1 sym2 res
       ) (Some res) (List.combine p.oargs p'.oargs)
  | _ -> 
     fail


let free_vars = function
  | Point b -> 
     let itlist = match b.content with
       | Block _ -> [b.pointer; b.permission]
       | Value v -> [b.pointer; b.permission; v]
     in
     IT.free_vars_list itlist
  | IteratedStar b -> 
     let itlist = match b.content with
       | Block _ -> [b.permission]
       | Value v -> [b.permission; v]
     in
     SymSet.remove b.qpointer (IT.free_vars_list itlist)
  | Predicate p -> 
     IT.free_vars_list ((* p.unused :: *) (p.iargs @ p.oargs))

let free_vars_list l = 
  List.fold_left (fun acc sym -> 
      SymSet.union acc (free_vars sym)
    ) SymSet.empty l


let quantified = function
  | Point p -> []
  | IteratedStar p -> [(p.qpointer, BaseTypes.Loc)]
  | Predicate p -> []


(* the quantifier in IteratedStar is neither input nor output *)
let inputs = function
  | Point p -> [p.pointer; p.permission]
  | IteratedStar p -> [p.permission]
  | Predicate p -> p.iargs

let outputs = function
  | Point {content = Block _; _} -> []
  | Point {content = Value v; _} -> [v]
  | IteratedStar {content = Block _; _} -> []
  | IteratedStar {content = Value v; _} -> [v]
  | Predicate p -> p.oargs


let permission = function
  | Point p -> p.permission
  | IteratedStar s -> s.permission
  | Predicate p when p.unused -> IT.q_ (1, 1)
  | Predicate p -> IT.q_ (0, 1)



(* assumption: resource is owned *)
let derived_constraint resource = 
  let open IT in
  simplify []
    begin match resource with
    | Point p -> 
       impl_ (gt_ (p.permission, q_ (0, 1)), not_ (eq_ (null_, p.pointer)))
    | IteratedStar p ->
       (* todo *)
       bool_ true
    | Predicate _ ->
       bool_ true
    end


(* assumption: resource owned at the same time as resources' *)
(* todo, depending on how much we need *)
let derived_constraints resource resource' =
  let open IT in
  simplify [] 
    begin match resource, resource' with
    | Point p, Point p' -> 
       and_ [impl_ (
                 gt_ (add_ (p.permission, p'.permission), q_ (1, 1)),
                 disjoint_ ((p.pointer, z_ p.size), (p'.pointer, z_ p'.size))
         )]
    | Predicate _, _
      | _, Predicate _ -> 
       bool_ true
    | _ ->
       (* todo *)
       bool_ true
    end







let region pointer size permission =
  let open IT in
  let q = Sym.fresh () in
  let qt = sym_ (BT.Loc, q) in
  let condition = 
    and_ [
        lePointer_ (pointer, qt);
        ltPointer_ (qt, addPointer_ (pointer, size));
      ]
  in
  let point = {
      qpointer = q;
      size = Z.of_int 1;
      content = Block Nothing;
      permission = ite_ BT.Real (condition, permission, q_ (0,1))
    }
  in
  IteratedStar point


(* check this *)
let array pointer length element_size content permission =
  let open IT in
  let q = Sym.fresh () in
  let qt = sym_ (BT.Loc, q) in
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
      content = Value (content it);
      permission = ite_ BT.Real (condition, permission, q_ (0,1))
    }
  in
  IteratedStar point
