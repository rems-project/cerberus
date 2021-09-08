open Pp
open List

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources.RE
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module IT = IndexTerms
module SymMap = Map.Make(Sym)






type where = 
  | Loc of Loc.t
  | Label of string

let pp_where = function
  | Label l -> !^l
  | Loc loc -> !^(Loc.simple_location loc)

(* type old = { address : IT.t; value : IT.t; where : where }
 * 
 * let pp_old old = 
 *   parens (IT.pp old.address ^^^ !^"->" ^^^ IT.pp old.value) ^^ at ^^ 
 *     pp_where old.where *)

module type S = sig

  include Solver.S
  type t 
  val empty : unit -> t
  val pp : t -> Pp.document
  val all_computational : t -> (SymMap.key * (LS.t * SymMap.key)) list
  val all_logical : t -> (SymMap.key * LS.t) list
  val all_constraints : t -> LC.t list
  val all_resources : t -> RE.t list
  val bound : Sym.t -> Kind.t -> t -> bool
  val get_a : Sym.t -> t -> BT.t * SymMap.key
  val get_l : Sym.t -> t -> LS.t
  val add_a : Sym.t -> BT.t * Sym.t -> t -> t
  val add_l : Sym.t -> LS.t -> t -> t
  val add_c : LC.t -> t -> t
  val add_cs : LC.t list -> t -> t
  val add_r : where option -> RE.t -> t -> t
  val solver : t -> Z3.Solver.solver
  (* val old : t -> old list *)

  val map_and_fold_resources : 
    (RE.t -> 'acc -> RE.t * 'acc) -> 
    t -> 'acc -> t * 'acc
  val all_vars : t -> Sym.t list
  val json : t -> Yojson.Safe.t
  val bind : where option -> t -> Sym.t -> ReturnTypes.t -> t
  val bind_logical : where option -> t -> LogicalReturnTypes.t -> t
  val bind_logically : where option -> t -> ReturnTypes.t -> (BT.t * Sym.t) * t

  

end



module Make (S : Solver.S) : S = struct

  include S

  type t = {
      computational : (BT.t * Sym.t) SymMap.t;
      logical : LS.t SymMap.t;
      resources : RE.t list;
      constraints : LC.t list;
      solver : Z3.Solver.solver;
      (* old : old list; *)
    }


  let empty () = {
      computational = SymMap.empty;
      logical = SymMap.empty;
      resources = [];
      constraints = [];
      solver = Z3.Solver.mk_simple_solver Solver.context;
      (* old = []; *)
    }






  let pp (local : t) = 
    item "computational" 
      (Pp.list (fun (sym, (bt,lsym)) -> 
           typ (Sym.pp sym) (BT.pp bt ^^ tilde ^^ Sym.pp lsym)
         ) (SymMap.bindings local.computational)) ^/^
    item "logical" 
      (Pp.list (fun (sym, ls) -> 
           typ (Sym.pp sym) (LS.pp ls)
         ) (SymMap.bindings local.logical)) ^/^
    item "resources" 
      (Pp.list RE.pp local.resources) ^/^
    item "constraints" 
      (Pp.list LC.pp local.constraints) (* ^/^
     * item "old" 
     *   (Pp.list pp_old local.old) *)


  let all_computational (local : t) = SymMap.bindings local.computational
  let all_logical (local : t) = SymMap.bindings local.logical
  let all_resources (local : t) = local.resources
  let all_constraints (local : t) = local.constraints

  let solver local = local.solver

  (* let old local = local.old *)


  let bound sym kind local = 
    match kind with
    | Kind.KComputational -> SymMap.mem sym local.computational
    | Kind.KLogical -> SymMap.mem sym local.logical



  let get_a (name: Sym.t) (local:t)  = 
    SymMap.find name local.computational

  let get_l (name: Sym.t) (local:t) = 
    SymMap.find name local.logical

  let add_a aname (bt, lname) local = 
    {local with computational = SymMap.add aname (bt, lname) local.computational}

  let add_l lname ls (local : t) = 
    {local with logical = SymMap.add lname ls local.logical}

  let add_ls lvars local = 
    List.fold_left (fun local (s,ls) -> add_l s ls local) local lvars

  let add_c lc (local : t) = 
    let lcs = Simplify.simp_lc_flatten local.constraints lc in
    let scs = List.concat_map S.constr lcs in
    let () = 
      Z3.Solver.add local.solver 
        [Z3.Boolean.mk_and Solver.context scs] 
    in
    { local with constraints = lcs @ local.constraints;
                 solver = local.solver }

  let add_cs lcs (local : t) = 
    List.fold_left (fun local lc -> add_c lc local) local lcs


  let add_r owhere r (local : t) = 
    match RE.simp_or_empty local.constraints r with
    | Some r -> 
       let (r, lvars, lcs1) = RE.normalise r in
       let lcs2 = 
         RE.derived_constraint r ::
           List.map (fun r' -> RE.derived_constraints r r') 
             (all_resources local)
       in
       let local = add_ls lvars local in
       let local = {local with resources = r :: local.resources} in
       let local = add_cs (lcs1 @ lcs2) local in
       local
    | None ->
       local




  let map_and_fold_resources (f : RE.t -> 'acc -> RE.t * 'acc) 
        (local : t) (acc : 'acc) = 
    let (resources, lvars, lcs), acc =
      List.fold_right (fun re ((resources, lvars, lcs), acc) ->
          let (re, acc) = f re acc in
          match RE.simp_or_empty local.constraints re with
          | Some re -> 
             let (re, lvars', lcs') = RE.normalise re in
             ((re :: resources, lvars' @ lvars, lcs' @ lcs), acc)
          | None -> 
             ((resources, lvars, lcs), acc)
        ) local.resources (([],[],[]), acc)
    in
    let local = {local with resources} in
    let local = add_ls lvars local in
    let local = add_cs lcs local in
    (local, acc)





  let all_vars (local : t) = 
    List.map fst (SymMap.bindings local.computational) @
    List.map fst (SymMap.bindings local.logical)


  let json (local : t) : Yojson.Safe.t = 

    let computational  = 
      List.map (fun (sym, (bt, lname)) ->
          `Assoc [("name", Sym.json sym);
                  ("basetype", BT.json bt); 
                  ("logical", Sym.json lname)]        
        ) (SymMap.bindings local.computational)
    in
    let logical = 
      List.map (fun (sym, ls) ->
          `Assoc [("name", Sym.json sym);
                  ("sort", LS.json ls)]
        ) (SymMap.bindings local.logical)
    in
    let resources = List.map RE.json local.resources in
    let constraints = List.map LC.json local.constraints in
    let json_record = 
      `Assoc [("computational", `List computational);
              ("logical", `List logical);
              ("resources", `List resources);
              ("constraints", `List constraints)
        ]
    in
    `Variant ("Context", Some json_record)




  module LRT = LogicalReturnTypes
  module RT = ReturnTypes



  let rec bind_logical where (local : t) (lrt : LRT.t) : t = 
    match lrt with
    | Logical ((s, ls), _oinfo, rt) ->
       let s' = Sym.fresh () in
       let rt' = LRT.subst [(s, IT.sym_ (s', ls))] rt in
       bind_logical where (add_l s' ls local) rt'
    | Resource (re, _oinfo, rt) -> 
       bind_logical where (add_r where re local) rt
    | Constraint (lc, _oinfo, rt) -> 
       bind_logical where (add_c lc local) rt
    | I -> local

  let bind_computational where (local : t) (name : Sym.t) (rt : RT.t) : t =
    let Computational ((s, bt), _oinfo, rt) = rt in
    let s' = Sym.fresh () in
    let rt' = LRT.subst [(s, IT.sym_ (s', bt))] rt in
    bind_logical where (add_a name (bt, s') (add_l s' bt local)) rt'


  let bind where (local : t) (name : Sym.t) (rt : RT.t) : t =
    bind_computational where local name rt

  let bind_logically where (local : t) (rt : RT.t) : ((BT.t * Sym.t) * t) =
    let Computational ((s, bt), _oinfo, rt) = rt in
    let s' = Sym.fresh () in
    let rt' = LRT.subst [(s, IT.sym_ (s', bt))] rt in
    ((bt, s'), bind_logical where (add_l s' bt local) rt')


end
