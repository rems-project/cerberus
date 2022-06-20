open Pp
open List

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module LCSet = Set.Make(LC)
module Loc = Locations





type where = 
  | Loc of Loc.t
  | Label of string

let pp_where = function
  | Label l -> !^l
  | Loc loc -> !^(Loc.simple_location loc)


type t = {
    computational : (Sym.t * (BT.t * Sym.t)) list;
    logical : (Sym.t * LS.t) list;
    resources : (RE.t * int) list * int;
    constraints : LCSet.t * LC.t list;
    global : Global.t;
    location_trace : Locations.loc list;
    statement_locs : Locations.loc list;
  }


let empty = {
    computational = [];
    logical = [];
    resources = ([], 0);
    constraints = (LCSet.empty, []);
    global = Global.empty;
    location_trace = [];
    statement_locs  = [];
  }



let get_rs (ctxt : t) = List.map fst (fst ctxt.resources)

let pp (ctxt : t) = 
  item "computational" 
    (Pp.list (fun (sym, (bt,lsym)) -> 
         typ (Sym.pp sym) (BT.pp bt ^^ tilde ^^ Sym.pp lsym)
       ) ctxt.computational) ^/^
  item "logical" 
    (Pp.list (fun (sym, ls) -> 
         typ (Sym.pp sym) (LS.pp ls)
       ) ctxt.logical) ^/^
  item "resources" 
    (Pp.list RE.pp (get_rs ctxt)) ^/^
  item "constraints" 
    (Pp.list (fun lc -> 
         if (!print_level >= 11 || Option.is_none (LC.is_sym_lhs_equality lc))
         then LC.pp lc
         else parens !^"..."
       ) (LCSet.elements (fst ctxt.constraints)))


let bound_a sym ctxt = 
  Option.is_some (List.assoc_opt Sym.equal sym ctxt.computational)
let bound_l sym ctxt = 
  Option.is_some (List.assoc_opt Sym.equal sym ctxt.logical)



let get_a (name: Sym.t) (ctxt: t)  = 
  List.assoc Sym.equal name ctxt.computational

let get_l (name: Sym.t) (ctxt:t) = 
  List.assoc Sym.equal name ctxt.logical

let add_a aname (bt, lname) ctxt = 
  {ctxt with computational = (aname, (bt, lname)) :: ctxt.computational}

let remove_a aname ctxt = 
  {ctxt with computational = List.remove_assoc aname ctxt.computational}

let add_as avars ctxt = 
  List.fold_left (fun ctxt (s,(bt,l)) -> add_a s (bt,l) ctxt) ctxt avars

let remove_as avars ctxt = 
  List.fold_left (fun ctxt s -> remove_a s ctxt) ctxt avars


let add_l lname ls (ctxt : t) = 
  {ctxt with logical = (lname, ls) :: ctxt.logical}

let add_ls lvars ctxt = 
  List.fold_left (fun ctxt (s,ls) -> add_l s ls ctxt) ctxt lvars

let add_c c (ctxt : t) =
  let (s, cs) = ctxt.constraints in
  if LCSet.mem c s then ctxt
  else { ctxt with constraints = (LCSet.add c s, c :: cs) }

let add_r owhere r (ctxt : t) =
  let (rs, ix) = ctxt.resources in
  {ctxt with resources = ((r, ix) :: rs, ix + 1)}

let add_rs owhere r rs ctxt = List.fold_right (add_r owhere) rs ctxt


let add_stmt_locs stmts (ctxt : t) =
  {ctxt with statement_locs = stmts @ ctxt.statement_locs}

let json (ctxt : t) : Yojson.Safe.t = 

  let computational  = 
    List.map (fun (sym, (bt, lname)) ->
        `Assoc [("name", Sym.json sym);
                ("basetype", BT.json bt); 
                ("logical", Sym.json lname)]        
      ) ctxt.computational
  in
  let logical = 
    List.map (fun (sym, ls) ->
        `Assoc [("name", Sym.json sym);
                ("sort", LS.json ls)]
      ) ctxt.logical
  in
  let resources = List.map RE.json (get_rs ctxt) in
  let constraints = List.map LC.json (snd ctxt.constraints) in
  let json_record = 
    `Assoc [("computational", `List computational);
            ("logical", `List logical);
            ("resources", `List resources);
            ("constraints", `List constraints)
      ]
  in
  `Variant ("Context", Some json_record)

(* Detects if the same variables and constraints are present
   (things visible to the solver), but ignores whether the
   resource states are the same. Assumes a related history
   (that is, one is an extension of the other). *)
let constraints_not_extended ctxt1 ctxt2 =
    List.compare_lengths ctxt1.logical ctxt2.logical == 0 &&
    List.compare_lengths ctxt1.computational ctxt2.computational == 0 &&
    LCSet.cardinal (fst ctxt1.constraints) == LCSet.cardinal (fst ctxt2.constraints)

