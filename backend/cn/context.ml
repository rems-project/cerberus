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


type t = {
    computational : (Sym.t * (BT.t * Sym.t)) list;
    logical : (Sym.t * LS.t) list;
    resources : RE.t list;
    constraints : LC.t list;
    global : Global.t;
    location_trace : Locations.loc list;
  }


let empty global = {
    computational = [];
    logical = [];
    resources = [];
    constraints = [];
    global = global;
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
       ) ctxt.constraints)


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
  { ctxt with constraints = c :: ctxt.constraints }


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
  let constraints = List.map LC.json ctxt.constraints in
  let json_record = 
    `Assoc [("computational", `List computational);
            ("logical", `List logical);
            ("resources", `List resources);
            ("constraints", `List constraints)
      ]
  in
  `Variant ("Context", Some json_record)



