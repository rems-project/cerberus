open Coqlib
open Datatypes
open Lattice
open List0
open ListSet
open Maps
open MetatheoryAtom
open Specif
open Analysis
open Infrastructure
open Syntax

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val reachablity_analysis_aux_func :
    (LLVMsyntax.l list, (LLVMsyntax.ls ATree.t, (LLVMsyntax.l, LLVMsyntax.l
    list) sigT) sigT) sigT -> LLVMsyntax.l list option **)

let rec reachablity_analysis_aux_func x =
  let nvisited = projT1 x in
  let succs = projT1 (projT2 x) in
  let curr = projT1 (projT2 (projT2 x)) in
  let acc = projT2 (projT2 (projT2 x)) in
  let reachablity_analysis_aux0 = fun nvisited0 succs0 curr0 acc0 ->
    let y = Coq_existT (nvisited0, (Coq_existT (succs0, (Coq_existT (curr0,
      acc0)))))
    in
    reachablity_analysis_aux_func y
  in
  let filtered_var = ATree.get curr succs in
  let branch_0 = fun _ -> None in
  let branch_1 = fun nexts ->
    fold_left (fun oacc' next ->
      let branch_1 = fun _ -> None in
      let branch_2 = fun acc' ->
        if in_dec AtomImpl.eq_atom_dec next nvisited
        then if in_dec AtomImpl.eq_atom_dec next acc
             then Some acc'
             else let filtered_var0 =
                    reachablity_analysis_aux0
                      (remove AtomImpl.eq_atom_dec next nvisited) succs next
                      (next::acc)
                  in
                  let branch_2 = fun _ -> None in
                  let branch_3 = fun acc'' -> Some
                    (set_union AtomImpl.eq_atom_dec acc' acc'')
                  in
                  (match filtered_var0 with
                     | Some acc'' -> branch_3 acc''
                     | None -> branch_2 __)
        else Some acc'
      in
      (match oacc' with
         | Some acc' -> branch_2 acc'
         | None -> branch_1 __)) nexts (Some acc)
  in
  (match filtered_var with
     | Some nexts -> branch_1 nexts
     | None -> branch_0 __)

(** val reachablity_analysis_aux :
    LLVMsyntax.l list -> LLVMsyntax.ls ATree.t -> LLVMsyntax.l ->
    LLVMsyntax.l list -> LLVMsyntax.l list option **)

let reachablity_analysis_aux nvisited succs curr acc =
  reachablity_analysis_aux_func (Coq_existT (nvisited, (Coq_existT (succs,
    (Coq_existT (curr, acc))))))

(** val get_reachable_labels :
    LLVMsyntax.l list -> bool AMap.t -> LLVMsyntax.l list -> LLVMsyntax.l
    list **)

let rec get_reachable_labels bd rd acc =
  match bd with
    | [] -> acc
    | l0::bd' ->
        if AMap.get l0 rd
        then get_reachable_labels bd' rd (l0::acc)
        else get_reachable_labels bd' rd acc

(** val reachablity_analysis :
    LLVMsyntax.fdef -> LLVMsyntax.l list option **)

let reachablity_analysis f =
  match LLVMinfra.getEntryBlock f with
    | Some b ->
        (match areachable_aux f with
           | Some rd -> Some (get_reachable_labels (bound_fdef f) rd [])
           | None -> None)
    | None -> None

type coq_DTree =
  | DT_node of LLVMsyntax.l * coq_DTrees
and coq_DTrees =
  | DT_nil
  | DT_cons of coq_DTree * coq_DTrees

(** val coq_DTree_rect :
    (LLVMsyntax.l -> coq_DTrees -> 'a1) -> coq_DTree -> 'a1 **)

let coq_DTree_rect f = function
  | DT_node (x, x0) -> f x x0

(** val coq_DTree_rec :
    (LLVMsyntax.l -> coq_DTrees -> 'a1) -> coq_DTree -> 'a1 **)

let coq_DTree_rec f = function
  | DT_node (x, x0) -> f x x0

(** val coq_DTrees_rect :
    'a1 -> (coq_DTree -> coq_DTrees -> 'a1 -> 'a1) -> coq_DTrees -> 'a1 **)

let rec coq_DTrees_rect f f0 = function
  | DT_nil -> f
  | DT_cons (d0, d1) -> f0 d0 d1 (coq_DTrees_rect f f0 d1)

(** val coq_DTrees_rec :
    'a1 -> (coq_DTree -> coq_DTrees -> 'a1 -> 'a1) -> coq_DTrees -> 'a1 **)

let rec coq_DTrees_rec f f0 = function
  | DT_nil -> f
  | DT_cons (d0, d1) -> f0 d0 d1 (coq_DTrees_rec f f0 d1)

(** val dtree_dom : coq_DTree -> AtomSetImpl.t **)

let rec dtree_dom = function
  | DT_node (l0, dts0) ->
      AtomSetImpl.union (AtomSetImpl.singleton l0) (dtrees_dom dts0)

(** val dtrees_dom : coq_DTrees -> AtomSetImpl.t **)

and dtrees_dom = function
  | DT_nil -> AtomSetImpl.empty
  | DT_cons (dt0, dts0) ->
      AtomSetImpl.union (dtree_dom dt0) (dtrees_dom dts0)

(** val get_dtree_root : coq_DTree -> LLVMsyntax.l **)

let get_dtree_root = function
  | DT_node (l0, d) -> l0

(** val gt_sdom :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
    -> bool **)

let gt_sdom bd res l1 l2 =
  proj_sumbool (in_dec LLVMinfra.l_dec l1 (AMap.get l2 res))

(** val find_min :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
    set -> LLVMsyntax.l **)

let rec find_min bd res acc = function
  | [] -> acc
  | l0::dts' ->
      if gt_sdom bd res acc l0
      then find_min bd res l0 dts'
      else find_min bd res acc dts'

(** val insert_sort_sdom_iter :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
    list -> LLVMsyntax.l list -> LLVMsyntax.l list **)

let rec insert_sort_sdom_iter bd res l0 prefix suffix = match suffix with
  | [] -> rev (l0::prefix)
  | l1::suffix' ->
      if gt_sdom bd res l0 l1
      then app (rev (l0::prefix)) suffix
      else insert_sort_sdom_iter bd res l0 (l1::prefix) suffix'

(** val insert_sort_sdom :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
    LLVMsyntax.l list -> LLVMsyntax.l list **)

let rec insert_sort_sdom bd res data acc =
  match data with
    | [] -> acc
    | l1::data' ->
        insert_sort_sdom bd res data'
          (insert_sort_sdom_iter bd res l1 [] acc)

(** val sort_sdom :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
    LLVMsyntax.l list **)

let sort_sdom bd res data =
  insert_sort_sdom bd res data []

(** val getEntryLabel : LLVMsyntax.fdef -> LLVMsyntax.l option **)

let getEntryLabel = function
  | LLVMsyntax.Coq_fdef_intro (f0, b) ->
      (match b with
         | [] -> None
         | b0::l0 ->
             let LLVMsyntax.Coq_block_intro (l1, p, c, t0) = b0 in Some l1)

(** val remove_redundant : LLVMsyntax.l list -> LLVMsyntax.l list **)

let rec remove_redundant input = match input with
  | [] -> input
  | a::input' ->
      (match input' with
         | [] -> input
         | b::l0 ->
             if LLVMinfra.l_dec a b
             then remove_redundant input'
             else a::(remove_redundant input'))

(** val compute_sdom_chains_aux :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
    (LLVMsyntax.l*LLVMsyntax.l list) list -> (LLVMsyntax.l*LLVMsyntax.l list)
    list **)

let rec compute_sdom_chains_aux bd0 res bd acc =
  match bd with
    | [] -> acc
    | l0::bd' ->
        compute_sdom_chains_aux bd0 res bd'
          ((l0,(remove_redundant (sort_sdom bd0 res (l0::(AMap.get l0 res)))))::acc)

(** val compute_sdom_chains :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
    (LLVMsyntax.l*LLVMsyntax.l list) list **)

let compute_sdom_chains bd res rd =
  compute_sdom_chains_aux bd res rd []

(** val in_children_roots : LLVMsyntax.l -> coq_DTrees -> bool **)

let rec in_children_roots child = function
  | DT_nil -> false
  | DT_cons (d, dts') ->
      let DT_node (l0, d0) = d in
      if LLVMinfra.l_dec l0 child then true else in_children_roots child dts'

(** val dtree_insert :
    coq_DTree -> LLVMsyntax.id -> LLVMsyntax.l -> coq_DTree **)

let rec dtree_insert dt parent child =
  let DT_node (l0, dts0) = dt in
  if LLVMinfra.id_dec parent l0
  then if in_children_roots child dts0
       then dt
       else DT_node (l0, (DT_cons ((DT_node (child, DT_nil)), dts0)))
  else DT_node (l0, (dtrees_insert dts0 parent child))

(** val dtrees_insert :
    coq_DTrees -> LLVMsyntax.id -> LLVMsyntax.l -> coq_DTrees **)

and dtrees_insert dts parent child =
  match dts with
    | DT_nil -> DT_nil
    | DT_cons (dt0, dts0) -> DT_cons ((dtree_insert dt0 parent child),
        (dtrees_insert dts0 parent child))

(** val is_dtree_edge :
    coq_DTree -> LLVMsyntax.id -> LLVMsyntax.l -> bool **)

let rec is_dtree_edge dt parent child =
  let DT_node (l0, dts0) = dt in
  if LLVMinfra.id_dec parent l0
  then if in_children_roots child dts0
       then true
       else is_dtrees_edge dts0 parent child
  else is_dtrees_edge dts0 parent child

(** val is_dtrees_edge :
    coq_DTrees -> LLVMsyntax.id -> LLVMsyntax.l -> bool **)

and is_dtrees_edge dts parent child =
  match dts with
    | DT_nil -> false
    | DT_cons (dt0, dts0) ->
        if is_dtree_edge dt0 parent child
        then true
        else is_dtrees_edge dts0 parent child

(** val dtrees_rec2 :
    (LLVMsyntax.l -> coq_DTrees -> 'a2 -> 'a1) -> 'a2 -> (coq_DTree -> 'a1 ->
    coq_DTrees -> 'a2 -> 'a2) -> coq_DTrees -> 'a2 **)

let dtrees_rec2 f f0 f1 =
  let rec f2 = function
    | DT_node (l0, d0) -> f l0 d0 (f3 d0)
  and f3 = function
    | DT_nil -> f0
    | DT_cons (d0, d1) -> f1 d0 (f2 d0) d1 (f3 d1)
  in f3

(** val dtree_rec2 :
    (LLVMsyntax.l -> coq_DTrees -> 'a2 -> 'a1) -> 'a2 -> (coq_DTree -> 'a1 ->
    coq_DTrees -> 'a2 -> 'a2) -> coq_DTree -> 'a1 **)

let dtree_rec2 f f0 f1 =
  let rec f2 = function
    | DT_node (l0, d0) -> f l0 d0 (f3 d0)
  and f3 = function
    | DT_nil -> f0
    | DT_cons (d0, d1) -> f1 d0 (f2 d0) d1 (f3 d1)
  in f2

(** val dtree_mutrec :
    (LLVMsyntax.l -> coq_DTrees -> 'a2 -> 'a1) -> 'a2 -> (coq_DTree -> 'a1 ->
    coq_DTrees -> 'a2 -> 'a2) -> (coq_DTree -> 'a1)*(coq_DTrees -> 'a2) **)

let dtree_mutrec h1 h2 h3 =
  (dtree_rec2 h1 h2 h3),(dtrees_rec2 h1 h2 h3)

(** val create_dtree_from_chain :
    coq_DTree -> LLVMsyntax.id list -> coq_DTree **)

let rec create_dtree_from_chain dt = function
  | [] -> dt
  | p::chain' ->
      (match chain' with
         | [] -> dt
         | ch::l0 -> create_dtree_from_chain (dtree_insert dt p ch) chain')

(** val create_dtree : LLVMsyntax.fdef -> coq_DTree option **)

let create_dtree f =
  match getEntryLabel f with
    | Some root ->
        (match reachablity_analysis f with
           | Some rd ->
               let dt = dom_analyze f in
               let b = bound_fdef f in
               let chains = compute_sdom_chains b dt rd in
               Some
               (fold_left (fun acc elt ->
                 let y,chain = elt in create_dtree_from_chain acc chain)
                 chains (DT_node (root, DT_nil)))
           | None -> None)
    | None -> None

(** val size_of_dtrees : coq_DTrees -> nat **)

let rec size_of_dtrees = function
  | DT_nil -> O
  | DT_cons (d, dts') -> S (size_of_dtrees dts')

(** val find_idom_aux :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
    set -> LLVMsyntax.l option **)

let rec find_idom_aux bd res acc = function
  | [] -> Some acc
  | l0::dts' ->
      if in_dec LLVMinfra.l_dec l0 (AMap.get acc res)
      then find_idom_aux bd res acc dts'
      else if in_dec LLVMinfra.l_dec acc (AMap.get l0 res)
           then find_idom_aux bd res l0 dts'
           else None

(** val find_idom :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l -> LLVMsyntax.l
    option **)

let find_idom bd res l0 =
  match AMap.get l0 res with
    | [] -> None
    | l1::dts0 -> find_idom_aux bd res l1 dts0

(** val compute_idoms :
    AtomImpl.atom set -> Dominators.t AMap.t -> LLVMsyntax.l list ->
    (LLVMsyntax.l*LLVMsyntax.l) list -> (LLVMsyntax.l*LLVMsyntax.l) list **)

let rec compute_idoms bd res rd acc =
  match rd with
    | [] -> acc
    | l0::rd' ->
        (match find_idom bd res l0 with
           | Some l1 -> compute_idoms bd res rd' ((l1,l0)::acc)
           | None -> compute_idoms bd res rd' acc)

