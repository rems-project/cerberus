open Pp
open List

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module LCSet = Set.Make(LC)
module Loc = Locations
module SymMap = Map.Make(Sym)



type l_info = (Locations.t * Pp.doc Lazy.t)


type t = {
    computational : (BaseTypes.t * l_info) SymMap.t;
    logical : (BaseTypes.t * l_info) SymMap.t;
    resources : (RE.t * int) list * int;
    constraints : LCSet.t;
    global : Global.t;
    location_trace : Locations.loc list;
    statement_locs : Locations.loc CStatements.LocMap.t;
  }


let empty = {
    computational = SymMap.empty;
    logical = SymMap.empty;
    resources = ([], 0);
    constraints = LCSet.empty;
    global = Global.empty;
    location_trace = [];
    statement_locs  = CStatements.LocMap.empty;
  }



let get_rs (ctxt : t) = List.map fst (fst ctxt.resources)

let pp (ctxt : t) = 
  item "computational" 
    (Pp.list (fun (sym, (bt, _)) -> 
         typ (Sym.pp sym) (BaseTypes.pp bt)
       ) (SymMap.bindings ctxt.computational)) ^/^
  item "logical"
    (Pp.list (fun (sym, (bt, _)) ->
         typ (Sym.pp sym) (BaseTypes.pp bt)
       ) (SymMap.bindings ctxt.logical)) ^/^
  item "resources" 
    (Pp.list RE.pp (get_rs ctxt)) ^/^
  item "constraints" 
    (Pp.list (fun lc -> 
         if (!print_level >= 11 || Option.is_none (LC.is_sym_lhs_equality lc))
         then LC.pp lc
         else parens !^"..."
       ) (LCSet.elements ctxt.constraints))


let bound_a s ctxt =
  SymMap.exists (fun s' _ -> Sym.equal s s') ctxt.computational
let bound_l s ctxt =
  SymMap.exists (fun s' _ -> Sym.equal s s') ctxt.logical

let bound s ctxt =
  bound_a s ctxt || bound_l s ctxt


let get_a s ctxt =
  fst (SymMap.find s ctxt.computational)

let get_l s ctxt =
  fst (SymMap.find s ctxt.logical)


let add_a s bt info ctxt =
  if (bound s ctxt) then failwith ("already bound: " ^ Sym.pp_string s);
  { ctxt with computational = SymMap.add s (bt, info) ctxt.computational }

let add_l s bt info ctxt =
  if (bound s ctxt) then failwith ("already bound: " ^ Sym.pp_string s);
  { ctxt with logical = SymMap.add s (bt, info) ctxt.logical }


(* Move s from computational to logical world so we can keep the
   constraints that may be attached to s: s will still be bound
   "logically", but out of scope as far as the Core program goes. *)
let remove_a s ctxt = 
  let (bt, info) = SymMap.find s ctxt.computational in
  add_l s bt info { ctxt with computational = SymMap.remove s ctxt.computational }


let add_c c (ctxt : t) =
  let s = ctxt.constraints in
  if LCSet.mem c s then ctxt
  else { ctxt with constraints = LCSet.add c s }

let add_r r (ctxt : t) =
  let (rs, ix) = ctxt.resources in
  {ctxt with resources = ((r, ix) :: rs, ix + 1)}




let json (ctxt : t) : Yojson.Safe.t = 

  let computational  = 
    List.map (fun (sym, (bt, _)) ->
        `Assoc [("name", Sym.json sym);
                ("type", BaseTypes.json bt)]
      ) (SymMap.bindings ctxt.computational)
  in
  let logical = 
    List.map (fun (sym, (bt, _)) ->
        `Assoc [("name", Sym.json sym);
                ("type", BaseTypes.json bt)]
      ) (SymMap.bindings ctxt.logical)
  in
  let resources = List.map RE.json (get_rs ctxt) in
  let constraints = List.map LC.json (LCSet.elements ctxt.constraints) in
  let json_record = 
    `Assoc [("computational", `List computational);
            ("logical", `List logical);
            ("resources", `List resources);
            ("constraints", `List constraints)
      ]
  in
  `Variant ("Context", Some json_record)

(* (\* Detects if the same variables and constraints are present *)
(*    (things visible to the solver), but ignores whether the *)
(*    resource states are the same. Assumes a related history *)
(*    (that is, one is an extension of the other). *\) *)
(* let constraints_not_extended ctxt1 ctxt2 = *)
(*     List.compare_lengths ctxt1.logical ctxt2.logical == 0 && *)
(*     List.compare_lengths ctxt1.computational ctxt2.computational == 0 && *)
(*     LCSet.cardinal ctxt1.constraints == LCSet.cardinal ctxt2.constraints *)

