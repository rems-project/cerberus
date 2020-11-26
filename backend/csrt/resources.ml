open Pp
module CF = Cerb_frontend
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

type size = Z.t


type predicate_name = 
  | Tag of BaseTypes.tag
  | Id of Id.t

let pp_predicate_name = function
  | Tag tag -> Sym.pp tag
  | Id id -> Id.pp id

let equal_predicate_name pn1 pn2 =
  match pn1, pn2 with
  | Tag t1, Tag t2 -> Sym.equal t1 t2
  | Id id1, Id id2 -> Id.equal id1 id2
  | Tag _, _ -> false
  | Id _, _ -> false


type predicate = {pointer: IndexTerms.t; name : predicate_name; args: Sym.t list}

(* for error reporting only *)
type block_type = 
  | Nothing
  | Uninit
  | Padding


type t = 
  | Block of {pointer: IndexTerms.t; size: size; block_type: block_type}
  | Points of {pointer: IndexTerms.t; pointee: Sym.t; size: size}
  | Predicate of predicate

type resource = t

let pp = function
  | Block {pointer; size; block_type} ->
     begin match block_type with
     | Nothing -> 
        !^"Block" ^^ parens (IndexTerms.pp pointer ^^ comma ^^ Z.pp size)
     | Uninit -> 
        !^"Uninit" ^^ parens (IndexTerms.pp pointer ^^ comma ^^ Z.pp size)
     | Padding -> 
        !^"Padding" ^^ parens (IndexTerms.pp pointer ^^ comma ^^ Z.pp size)
     end
  | Points {pointer; pointee; size} ->
     !^"Points" ^^ 
       parens (IndexTerms.pp pointer ^^ comma ^^ Sym.pp pointee ^^ 
                 comma ^^ Z.pp size)
  | Predicate {pointer; name; args} ->
     match name with
     | Id id ->
        Id.pp id ^^ 
          parens (separate comma ((IndexTerms.pp pointer) :: List.map Sym.pp args))
     | Tag tag ->
        !^"StoredStruct" ^^ parens (Sym.pp tag) ^^ 
          parens (separate comma ((IndexTerms.pp pointer) :: List.map Sym.pp args))
        



let json re : Yojson.Safe.t = 
  `String (Pp.plain (pp re))

let subst_var (subst: (Sym.t,Sym.t) Subst.t) = function
  | Block {pointer; size; block_type} ->
     let pointer = IndexTerms.subst_var subst pointer in
     Block {pointer; size; block_type}
  | Points {pointer; pointee; size} -> 
     let pointer = IndexTerms.subst_var subst pointer in
     let pointee = Sym.subst subst pointee in
     Points {pointer; pointee; size}
  | Predicate {pointer; name; args} -> 
     let pointer = IndexTerms.subst_var subst pointer in
     let args = List.map (Sym.subst subst) args in
     Predicate {pointer; name; args}


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
  | Block u1, Block u2 ->
     
     IndexTerms.equal u1.pointer u2.pointer &&
     Z.equal u1.size u2.size
  | Points p1, Points p2 ->
     IndexTerms.equal p1.pointer p2.pointer &&
     Sym.equal p1.pointee p2.pointee &&
     Z.equal p1.size p2.size
  | Predicate p1, Predicate p2 ->
     IndexTerms.equal p1.pointer p2.pointer && 
     equal_predicate_name p1.name p2.name && 
     List.equal Sym.equal p1.args p2.args
  | _, _ -> false


let pointer = function
  | Block b -> b.pointer
  | Points p -> p.pointer
  | Predicate p -> p.pointer

let size = function
  | Block b -> Some b.size
  | Points p -> Some p.size
  | Predicate _p -> None

let fp resource = 
  match size resource with
  | None -> None
  | Some size -> Some (pointer resource, size)

let vars_in = function
  | Block b -> IndexTerms.vars_in b.pointer
  | Points p -> SymSet.add p.pointee (IndexTerms.vars_in p.pointer)
  | Predicate p -> SymSet.union (IndexTerms.vars_in p.pointer)
                     (SymSet.of_list p.args)


let set_pointer re pointer = 
  match re with
  | Block b -> Block { b with pointer }
  | Points p -> Points { p with pointer }
  | Predicate p -> Predicate { p with pointer }


(* requires equality on index terms (does not try to unify them) *)
let unify r1 r2 res = 
  let open Option in
  match r1, r2 with
  | Block b, Block b' (* Block unifies with Blocks of other block type *)
       when Z.equal b.size b'.size && IndexTerms.equal b.pointer b'.pointer ->
     return res
  | Points p, Points p' 
       when Z.equal p.size p'.size && IndexTerms.equal p.pointer p'.pointer ->
     Uni.unify_sym p.pointee p'.pointee res
  | Predicate p, Predicate p' 
       when equal_predicate_name p.name p'.name &&
              List.length p.args = List.length p'.args ->
     List.fold_left (fun ores (sym1,sym2) ->
         let* res = ores in
         Uni.unify_sym sym1 sym2 res
       ) (Some res) (List.combine p.args p'.args)
  | _ -> 
     fail


let subst_non_pointer subst = function
  | Block p -> Block p
  | Points p -> Points {p with pointee = Sym.subst subst p.pointee}
  | Predicate p -> Predicate {p with args = List.map (Sym.subst subst) p.args}





let input = function
  | Block b -> IndexTerms.vars_in b.pointer
  | Points p -> IndexTerms.vars_in p.pointer
  | Predicate p -> IndexTerms.vars_in p.pointer

let output = function
  | Block _ -> SymSet.empty
  | Points p -> SymSet.singleton p.pointee
  | Predicate p -> SymSet.of_list p.args



