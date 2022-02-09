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


open Global



type where = 
  | Loc of Loc.t
  | Label of string

let pp_where = function
  | Label l -> !^l
  | Loc loc -> !^(Loc.simple_location loc)


type t = {
    computational : (BT.t * Sym.t) SymMap.t;
    logical : LS.t SymMap.t;
    resources : RE.t list;
    constraints : LC.t list;
    global : Global.t;
  }


let empty global = {
    computational = SymMap.empty;
    logical = SymMap.empty;
    resources = [];
    constraints = [];
    global = global;
  }






let pp (ctxt : t) = 
  item "computational" 
    (Pp.list (fun (sym, (bt,lsym)) -> 
         typ (Sym.pp sym) (BT.pp bt ^^ tilde ^^ Sym.pp lsym)
       ) (SymMap.bindings ctxt.computational)) ^/^
  item "logical" 
    (Pp.list (fun (sym, ls) -> 
         typ (Sym.pp sym) (LS.pp ls)
       ) (SymMap.bindings ctxt.logical)) ^/^
  item "resources" 
    (Pp.list RE.pp ctxt.resources) ^/^
  item "constraints" 
    (Pp.list LC.pp ctxt.constraints)


let bound_a sym ctxt = 
  SymMap.mem sym ctxt.computational
let bound_l sym ctxt = 
  SymMap.mem sym ctxt.logical



let get_a (name: Sym.t) (ctxt: t)  = 
  SymMap.find name ctxt.computational

let get_l (name: Sym.t) (ctxt:t) = 
  SymMap.find name ctxt.logical

let add_a aname (bt, lname) ctxt = 
  {ctxt with computational = SymMap.add aname (bt, lname) ctxt.computational}

let add_l lname ls (ctxt : t) = 
  {ctxt with logical = SymMap.add lname ls ctxt.logical}

let add_ls lvars ctxt = 
  List.fold_left (fun ctxt (s,ls) -> add_l s ls ctxt) ctxt lvars

let add_c c (ctxt : t) = 
  { ctxt with constraints = c :: ctxt.constraints }


let add_r owhere r (ctxt : t) = 
  match RE.simp_or_empty ctxt.global.struct_decls ctxt.constraints r with
  | None -> ctxt
  | Some re -> {ctxt with resources = r :: ctxt.resources}


let map_and_fold_resources (f : RE.t -> 'acc -> RE.t * 'acc) 
      (ctxt : t) (acc : 'acc) = 
  let resources, acc =
    List.fold_right (fun re (resources, acc) ->
        let (re, acc) = f re acc in
        match RE.simp_or_empty ctxt.global.struct_decls ctxt.constraints re with
        | Some re -> 
           (re :: resources, acc)
        | None -> 
           (resources, acc)
      ) ctxt.resources ([], acc)
  in
  let ctxt = {ctxt with resources} in
  (ctxt, acc)





let json (ctxt : t) : Yojson.Safe.t = 

  let computational  = 
    List.map (fun (sym, (bt, lname)) ->
        `Assoc [("name", Sym.json sym);
                ("basetype", BT.json bt); 
                ("logical", Sym.json lname)]        
      ) (SymMap.bindings ctxt.computational)
  in
  let logical = 
    List.map (fun (sym, ls) ->
        `Assoc [("name", Sym.json sym);
                ("sort", LS.json ls)]
      ) (SymMap.bindings ctxt.logical)
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



