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



type t = {
    computational : (BT.t * Sym.t) SymMap.t;
    logical : LS.t SymMap.t;
    resources : RE.t list;
    constraints : LC.t list;
    (* a subset of the logical symbols, just for error reporting, all
       pointer-typed *)
    global : SymSet.t;
  }


let empty = {
    computational = SymMap.empty;
    logical = SymMap.empty;
    resources = [];
    constraints = [];
    global = SymSet.empty;
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
    (Pp.list LC.pp local.constraints)


(* let filter (p : Sym.t * bound -> 'a option) (local : t) = 
 *   let aux sym b (acc : 'a list) =
 *     match p (sym, b) with
 *     | Some a -> a :: acc
 *     | None -> acc
 *   in
 *   SymMap.fold aux local [] *)

let all_computational (local : t) = SymMap.bindings local.computational
let all_logical (local : t) = SymMap.bindings local.logical
let all_resources (local : t) = local.resources
let all_constraints (local : t) = local.constraints



let map_and_fold_resources (f : RE.t -> 'acc -> RE.t * 'acc) 
      (local : t) (acc : 'acc) = 
  let resources, acc =
    List.fold_right (fun re (resources, acc) ->
        let (re, acc) = f re acc in
        match RE.simp_or_empty local.constraints re with
        | Some re -> (re :: resources, acc)
        | None -> (resources, acc)
      ) local.resources ([], acc)
  in
  ({local with resources}, acc)



(* let kind sym (local : t) = Option.map VB.kind (get_safe sym local)
 * let bound sym (local : t) = Option.is_some (kind sym local) *)

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

let add_c lc (local : t) = 
  let lcs = Simplify.simp_flatten local.constraints lc in
  {local with constraints = lcs @ local.constraints}

let add_cs lcs (local : t) = 
  List.fold_left (fun local lc -> add_c lc local) local lcs


let add_r r (local : t) = 
  match RE.simp_or_empty local.constraints r with
  | Some r -> 
     let resources = r :: local.resources in
     let lcs = 
       RE.derived_constraint r ::
         List.concat_map (fun r' -> RE.derived_constraints r r') 
           (all_resources local)
     in
     let local = {local with resources} in
     add_cs lcs local
  | None ->
     local


let remove_resource resource local = 
  let resources = 
    List.filter (fun r -> 
        not (RE.equal r resource)
      ) local.resources
  in
  { local with resources }






let concat (local' : t) (local : t) = 
  let local = SymMap.fold add_a local'.computational local in
  let local = SymMap.fold add_l local'.logical local in
  let local = List.fold_right add_r local'.resources local in
  let local = List.fold_right add_c local'.constraints local in
  local


let (++) = concat


let all_names (local : t) = 
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


