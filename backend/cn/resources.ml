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
    oargs: Sym.t list
  }

(* for error reporting only *)
type block_type = 
  | Nothing
  | Uninit
  | Padding

type point_content = 
  | Block of block_type
  | Value of Sym.t


type t = 
  | Point of {pointer: IT.t; size: Z.t; content: point_content}
  | Region of {pointer: IT.t; size: IT.t}
  | Array of {pointer: IT.t; element_size: Z.t; length: IT.t; content: Sym.t }
  | Predicate of predicate

type resource = t

let pp_predicate_name = function
  | Id id -> !^id
  | Tag tag -> !^"StoredStruct" ^^ parens (Sym.pp tag)

let pp_predicate {name; iargs; oargs} =
  let args = List.map IT.pp iargs @ List.map Sym.pp oargs in
  c_app (pp_predicate_name name) args

let pp = function
  | Point {pointer; size; content} ->
     begin match content with
     | Block block_type ->
        let rname = match block_type with
          | Nothing -> !^"Block"
          | Uninit -> !^"Uninit"
          | Padding -> !^"Padding"
        in
        c_app rname [IT.pp pointer; Z.pp size]
     | Value v ->
        c_app !^"Points" [IT.pp pointer; Sym.pp v; Z.pp size]
     end
  | Region {pointer; size} ->
     c_app !^"Region" [IT.pp pointer; IT.pp size]
  | Array a ->
     c_app !^"Array" [IT.pp a.pointer; Sym.pp a.content; IT.pp a.length]
  | Predicate p ->
     pp_predicate p
          
        



let json re : Yojson.Safe.t = 
  `String (Pp.plain (pp re))

let subst_var (subst: (Sym.t,Sym.t) Subst.t) = function
  | Point {pointer; size; content} ->
     let pointer = IT.subst_var subst pointer in
     let content = match content with
       | Block block_type -> Block block_type
       | Value v -> Value (Sym.subst subst v)
     in
     Point {pointer; size; content}
  | Region {pointer; size} ->
     let pointer = IT.subst_var subst pointer in
     let size = IT.subst_var subst size in
     Region {pointer; size}
  | Array {pointer; element_size; length; content} ->
     let pointer = IT.subst_var subst pointer in
     let length = IT.subst_var subst length in
     let content = Sym.subst subst content in
     Array {pointer; element_size; length; content}
  | Predicate {name; iargs; oargs} -> 
     let iargs = List.map (IT.subst_var subst) iargs in
     let oargs = List.map (Sym.subst subst) oargs in
     Predicate {name; iargs; oargs}


let subst_it (subst: (Sym.t,IT.t) Subst.t) resource =
  let open Option in
  let subst_sym s = if Sym.equal s subst.before then None else Some s in
  match resource with
  | Point {pointer; size; content} ->
     let pointer = IT.subst_it subst pointer in
     let@ block_type = match content with
       | Block block_type -> 
          return (Block block_type)
       | Value v ->
          let@ v = subst_sym v in
          return (Value v)
     in
     return (Point {pointer; size; content})
  | Region {pointer; size} ->
     let pointer = IT.subst_it subst pointer in
     let size = IT.subst_it subst size in
     return (Region {pointer; size})
  | Array {pointer; element_size; length; content} ->
     let pointer = IT.subst_it subst pointer in
     let length = IT.subst_it subst length in
     let@ content = subst_sym content in
     return (Array {pointer; element_size; length; content})
  | Predicate {name; iargs; oargs} -> 
     let iargs = List.map (IT.subst_it subst) iargs in
     let@ oargs = Option.ListM.mapM subst_sym oargs in
     return (Predicate {name; iargs; oargs})


let subst_vars = Subst.make_substs subst_var


let block_type_equal b1 b2 = 
  match b1, b2 with
  | Nothing, Nothing -> true
  | Uninit, Uninit -> true
  | Padding, Padding -> true

  | Nothing, _
  | Uninit, _ 
  | Padding, _ -> 
     false

let equal t1 t2 = 
  match t1, t2 with
  | Point b1, Point b2 ->
     IT.equal b1.pointer b2.pointer &&
     Z.equal b1.size b2.size &&
     begin match b1.content, b2. content with
     | Block bt1, Block bt2 ->
        block_type_equal bt1 bt2 
     | Value v1, Value v2 -> 
        Sym.equal v1 v2
     | _, _ -> 
        false
     end
  | Region r1, Region r2 ->
     IT.equal r1.pointer r2.pointer &&
     IT.equal r1.size r2.size
  | Predicate p1, Predicate p2 ->
     predicate_name_equal p1.name p2.name && 
     List.equal IT.equal p1.iargs p2.iargs && 
     List.equal Sym.equal p1.oargs p2.oargs
  | Array a1, Array a2 ->
     IT.equal a1.pointer a2.pointer &&
     Z.equal a1.element_size a2.element_size &&
     IT.equal a1.length a2.length &&
     Sym.equal a1.content a2.content
  | Point _, _ -> false
  | Region _, _ -> false
  | Array _, _ -> false
  | Predicate _, _ -> false



let footprint = function
  | Point b -> Some (b.pointer, IT.num_ b.size)
  | Region r -> Some (r.pointer, r.size)
  | Array a -> Some (a.pointer, IT.mul_ (a.length, IT.num_ a.element_size))
  | Predicate p -> None

let pointer r = Option.map fst (footprint r)
let size r = Option.map snd (footprint r)

let vars_in = function
  | Point b -> 
     SymSet.union 
       (IT.vars_in b.pointer)
       (match b.content with
        | Block _ -> SymSet.empty
        | Value v -> SymSet.singleton v)
  | Region r -> 
     SymSet.union
       (IT.vars_in r.pointer) 
       (IT.vars_in r.size) 
  | Array a -> 
     SymSet.add a.content
       (SymSet.union 
          (IT.vars_in a.length)
          (IT.vars_in a.pointer))
  | Predicate p -> 
     SymSet.union 
       (IT.vars_in_list p.iargs)
       (SymSet.of_list p.oargs)


(* let set_pointer re pointer = 
 *   match re with
 *   | Block b -> Block { b with pointer }
 *   | Points p -> Points { p with pointer }
 *   | Predicate p -> Predicate { p with key } *)


(* requires equality on inputs, unifies outputs *)
let unify r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Point b, Point b' 
       when IT.equal b.pointer b'.pointer &&
              Z.equal b.size b'.size ->
     begin match b.content, b'.content with
     | Block _, Block _ -> (* Block unifies with Blocks of other block type *)
        return res
     | Value v, Value v' ->          
        Uni.unify_sym v v' res
     | _, _ -> 
        fail
     end
  | Region r, Region r' 
       when IT.equal r.pointer r'.pointer &&
              IT.equal r.size r'.size ->
     return res
  | Array a, Array a' 
       when IT.equal a.pointer a'.pointer && 
              Z.equal a.element_size a'.element_size &&
              IT.equal a.length a'.length ->
     Uni.unify_sym a.content a'.content res
  | Predicate p, Predicate p' 
       when predicate_name_equal p.name p'.name &&
              List.equal IT.equal p.iargs p'.iargs &&
              List.length p.oargs = List.length p'.oargs ->
     List.fold_left (fun ores (sym1,sym2) ->
         let@ res = ores in
         Uni.unify_sym sym1 sym2 res
       ) (Some res) (List.combine p.oargs p'.oargs)
  | _ -> 
     fail


(* let subst_non_pointer subst = function
 *   | Block p -> Block p
 *   | Points p -> Points {p with pointee = Sym.subst subst p.pointee}
 *   | Predicate p -> Predicate {p with args = List.map (Sym.subst subst) p.args} *)





let input = function
  | Point p -> IT.vars_in_list [p.pointer]
  | Region r -> IT.vars_in_list [r.pointer; r.size]
  | Array a -> SymSet.union (IT.vars_in a.pointer) (IT.vars_in a.length)
  | Predicate p -> IT.vars_in_list p.iargs

let output = function
  | Point {content = Block _; _} -> SymSet.empty
  | Point {content = Value v; _} -> SymSet.singleton v
  | Region r -> SymSet.empty
  | Array a -> SymSet.singleton a.content
  | Predicate p -> SymSet.of_list p.oargs




