open Pp
open List

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources.RE
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
    resources : RE.t list;
    constraints : LCSet.t;
    global : Global.t;
    location_trace : Locations.loc list;
  }


let empty = {
    computational = [];
    logical = [];
    resources = [];
    constraints = LCSet.empty;
    global = Global.empty;
    location_trace = [];
  }






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
    (Pp.list RE.pp ctxt.resources) ^/^
  item "constraints" 
    (Pp.list (fun lc -> 
         if (!print_level >= 11 || Option.is_none (LC.is_sym_lhs_equality lc))
         then LC.pp lc
         else parens !^"..."
       ) (LCSet.elements ctxt.constraints))


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

let add_l lname ls (ctxt : t) = 
  {ctxt with logical = (lname, ls) :: ctxt.logical}

let add_ls lvars ctxt = 
  List.fold_left (fun ctxt (s,ls) -> add_l s ls ctxt) ctxt lvars

let add_c c (ctxt : t) = 
  { ctxt with constraints = LCSet.add c ctxt.constraints }


let add_r owhere r (ctxt : t) = 
  {ctxt with resources = r :: ctxt.resources}


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
  let resources = List.map RE.json ctxt.resources in
  let constraints = List.map LC.json (LCSet.elements ctxt.constraints) in
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
    LCSet.cardinal ctxt1.constraints == LCSet.cardinal ctxt2.constraints

