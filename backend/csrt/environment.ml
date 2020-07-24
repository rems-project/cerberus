open Pp
open List
open Except
open TypeErrors

module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module FT = FunctionTypes



(* Auxiliaries *)

module ImplMap = 
  Map.Make
    (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
     end)


let lookup_sym_map (loc : Loc.t) (e: 'v SymMap.t) (name: Sym.t) =
  match SymMap.find_opt name e with
  | None -> fail loc (Unbound_name name)
  | Some v -> return v

let lookup_impl (loc : Loc.t) (e: 'v ImplMap.t) i =
  match ImplMap.find_opt i e with
  | None -> fail loc (Unbound_impl_const i)
  | Some v -> return v

let lookup_sym_list (loc : Loc.t) (local: (Sym.t * 'a) list) (sym: Sym.t) =
  match List.find_opt (fun (sym',_) -> Sym.equal sym' sym) local with
  | None -> fail loc (Unbound_name sym)
  | Some (n,t) -> return t


let rec remove_sym_list (loc : Loc.t) (local: (Sym.t * 'a) list) (sym: Sym.t) = 
  match local with
  | [] -> fail loc (Unbound_name sym)
  | (sym',t)::rest when Sym.equal sym sym' -> return rest
  | (sym',t)::rest ->
     let* rest' = remove_sym_list loc rest sym in
     return ((sym',t)::rest')


module Global = struct 

  type struct_sig = { sbinder: Sym.t; souter: RT.t }
                  
  type struct_decl = 
    { raw: (BT.member * BT.t) list;
      ctypes: (BaseTypes.member * CF.Ctype.ctype) list;
      open_type: struct_sig;
      closed_type: struct_sig; 
    }

  type t = 
    { struct_decls : struct_decl SymMap.t; 
      fun_decls : (Loc.t * FT.t) SymMap.t;
      impl_fun_decls : FT.t ImplMap.t;
      impl_constants : BT.t ImplMap.t;
    } 

  let empty = 
    { struct_decls = SymMap.empty; 
      fun_decls = SymMap.empty;
      impl_fun_decls = ImplMap.empty;
      impl_constants = ImplMap.empty;
    }

  let get_struct_decl loc global (BT.Tag s) = 
    match SymMap.find_opt s global.struct_decls with
    | Some decl -> return decl 
    | None -> 
       fail loc (Generic_error (!^"struct" ^^^ Sym.pp s ^^^ !^"not defined"))

  let get_fun_decl loc global sym = lookup_sym_map loc global.fun_decls sym
  let get_impl_fun_decl loc global i = lookup_impl loc global.impl_fun_decls i
  let get_impl_constant loc global i = lookup_impl loc global.impl_constants i

  let pp_struct_decl (sym,decl) = 
    let tag = BT.Tag sym in
    let open_typ = 
      RT.Computational (decl.open_type.sbinder, 
                        BT.Struct tag, 
                        decl.open_type.souter) 
    in
    let closed_typ = 
      RT.Computational (decl.closed_type.sbinder, 
                        BT.Struct tag, 
                        decl.closed_type.souter) 
    in
    item (plain (Sym.pp sym) ^ " (raw)") 
         (pp_list (fun (BT.Member m, bt) -> typ !^m (BT.pp true bt)) decl.raw) 
    ^/^
    item (plain (Sym.pp sym) ^ " (open)") (RT.pp open_typ) 
    ^/^
    item (plain (Sym.pp sym) ^ " (closed)") 
         (RT.pp closed_typ)
    
  let pp_struct_decls decls = pp_list pp_struct_decl (SymMap.bindings decls) 

  let pp_fun_decl (sym, (_, t)) = item (plain (Sym.pp sym)) (FT.pp t)
  let pp_fun_decls decls = flow_map hardline pp_fun_decl (SymMap.bindings decls)

  let pp_items global = 
    [ (1, h2 "Structs")
    ; (1, pp_struct_decls global.struct_decls)
    ; (1, h2 "Functions")
    ; (1, pp_fun_decls global.fun_decls)
    ]

  let pp global = separate (break 1) (map snd (pp_items global))

end


module Local = struct

  type binding =
    | Computational of Sym.t * BT.t
    | Logical of LS.t
    | Resource of RE.t
    | UsedResource of RE.t * Loc.t list
    | Constraint of LC.t

  type binder = Sym.t * binding

  type t = binder list

  let empty = []

  let (++) local' local = local' @ local

  let print_constraint_names = false

  let pp_binder print_used (sym,binding) =
    match binding with
    | Computational (lname,bt) -> 
       !^"A" ^^^ parens (typ (Sym.pp sym) (parens (BT.pp false bt ^^ bar ^^ Sym.pp lname)))
    | Logical ls -> 
       !^"L" ^^^ parens (typ (Sym.pp sym) (LS.pp false ls))
    | Resource re -> 
       !^"R" ^^^ parens (RE.pp false re )
    | UsedResource (re,_locs) -> 
       if print_used then parens (!^"R used" ^^^ RE.pp false re) 
       else underscore
    | Constraint lc -> 
       !^"C" ^^^ parens (LC.pp false lc )

  let pp local = 
    match local with
    | [] -> !^"(empty)"
    | _ -> flow_map (comma ^^ break 1) (pp_binder false) local



  let get = lookup_sym_list

  let wanted_but_found loc wanted found = 
    let err = match wanted with
    | `Computational -> 
       !^"wanted computational variable but found" ^^^ pp_binder true found
    | `Logical ->
       !^"wanted logical variable but found" ^^^ pp_binder true found
    | `Resource ->
       !^"wanted resource variable but found" ^^^ pp_binder true found
    | `Constraint ->
       !^"wanted resource variable but found" ^^^ pp_binder true found
    in
    fail loc (Unreachable err)
    
  let get_a (loc : Loc.t) local (name: Sym.t) = 
    let* b = get loc local name in
    match b with 
    | Computational (lname,bt) -> return (bt,lname)
    | _ -> wanted_but_found loc `Computational (name,b)

  let get_l (loc : Loc.t) (local:t) (name: Sym.t) = 
    let* b = get loc local name in
    match b with 
    | Logical ls -> return ls
    | _ -> wanted_but_found loc `Logical (name,b)

  let get_r (loc : Loc.t) local (name: Sym.t) = 
    let* b = get loc local name in
    match b with 
    | Resource re -> return re
    | _ -> wanted_but_found loc `Resource (name,b)

  let get_c (loc : Loc.t) local (name: Sym.t) = 
    let* b = get loc local name in
    match b with 
    | Constraint lc -> return lc
    | _ -> wanted_but_found loc `Resource (name,b)
      
  let remove loc local name = remove_sym_list loc local name
  let remove_list loc local names = fold_leftM (remove loc) local names

  let add local (name, b) = (name, b) :: local
  let add_a local (aname, (bt,lname)) = add local (aname, Computational (lname,bt))
  let add_l local (lname, ls)         = add local (lname, Logical ls)
  let add_r local (rname, re)         = add local (rname, Resource re)
  let add_c local (cname, lc)         = add local (cname, Constraint lc)
  let add_ur local re = add_r local (Sym.fresh (), re)
  let add_uc local lc = add_c local (Sym.fresh (), lc)

  let ensure_resource_used loc local sym = 
    let* b = get loc local sym in
    match b with
    | Resource re -> fail loc (Generic_error (!^"unused" ^^^ pp_binder true (sym,b)))
    | UsedResource (re,where) -> return ()
    | _ -> wanted_but_found loc `Resource (sym,b)

  let ensure_resources_used loc local syms = 
    fold_leftM (fun () sym -> ensure_resource_used loc local sym) () syms


  let use_resource loc local sym where = 
    let* b = get loc local sym in
    match b with
    | UsedResource (re,where) -> 
       fail loc (Unreachable (!^"resource already used" ^^^ pp_binder true (sym,b)))
    | Resource re -> 
       let* local = remove loc local sym in
       return (add local (sym, UsedResource (re,where)))
    | _ -> wanted_but_found loc `Resource (sym,b)


  let all_constraints local = 
    List.filter_map (fun (_,b) ->
        match b with
        | Constraint lc -> Some lc
        | _ -> None
      ) local


  let filter_a p (local : t) = 
    filter_mapM (fun (sym,b) -> 
        match b with
        | Computational (lname,bt) -> p sym lname bt
        | _ -> return None
      )
      local

  let filter_r p (local : t) = 
    filter_mapM (fun (sym,b) -> 
        match b with
        | Resource t -> p sym t
        | _ -> return None
      )
      local

  let is_bound sym local =
    match List.find_opt (fun (sym',_) -> Sym.equal sym' sym) local with
    | Some _ -> true
    | None -> false

end



type t = 
  { global : Global.t; 
    local : Local.t;  }




