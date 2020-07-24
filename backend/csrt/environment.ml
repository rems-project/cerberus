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

  type struct_sig = { sbinder: Sym.t; souter: RT.l }
                  
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

  type t = Bindings of binder list

  let empty = Bindings []

  let concat (Bindings local') (Bindings local) = 
    Bindings (local' @ local)



  let mA sym (bt,lname) = (sym, Computational (lname,bt))
  let mL sym ls = (sym, Logical ls)
  let mR sym re = (sym, Resource re)
  let mC sym lc = (sym, Constraint lc)
  let mUR re = mR (Sym.fresh ()) re
  let mUC lc = mC (Sym.fresh ()) lc


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

  let pp (Bindings local) = 
    match local with
    | [] -> !^"(empty)"
    | _ -> flow_map (comma ^^ break 1) (pp_binder false) local



  let get loc (Bindings e) sym = lookup_sym_list loc e sym

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
      
  let remove loc name (Bindings e) = 
    let* e = remove_sym_list loc e name in
    return (Bindings e)

  let add (name, b) (Bindings e) = Bindings ((name, b) :: e)

  let removeS loc names local = 
    fold_leftM (fun local name -> remove loc name local) local names

  let addA aname (bt,lname) = add (aname, Computational (lname,bt))
  let addL lname ls         = add (lname, Logical ls)
  let addR rname re         = add (rname, Resource re)
  let addC cname lc         = add (cname, Constraint lc)
  let addUR re = addR (Sym.fresh ()) re
  let addUC lc = addC (Sym.fresh ()) lc

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
       let* local = remove loc sym local in
       return (add (sym, UsedResource (re,where)) local)
    | _ -> wanted_but_found loc `Resource (sym,b)


  let all_constraints (Bindings e) = 
    List.filter_map (fun (_,b) ->
        match b with
        | Constraint lc -> Some lc
        | _ -> None
      ) e


  let filter p (Bindings e) = filter_map (fun (sym,b) -> p sym b) e
  let filterM p (Bindings e) = filter_mapM (fun (sym,b) -> p sym b) e


  let filter_a p (local : t) = 
    filter (fun sym b -> 
        match b with
        | Computational (lname,bt) -> p sym lname bt
        | _ -> None
      )
      local

  let filter_r p (local : t) = 
    filter (fun sym b -> 
        match b with
        | Resource t -> p sym t
        | _ -> None
      )
      local

  let filter_rM p (local : t) = 
    filterM (fun sym b -> 
        match b with
        | Resource t -> p sym t
        | _ -> return None
      )
      local


  let all_a = filter_a (fun s _ _ -> Some s) 
  let all_r = filter_r (fun s _ -> Some s) 


  let is_bound sym (Bindings local) =
    match List.find_opt (fun (sym',_) -> Sym.equal sym' sym) local with
    | Some _ -> true
    | None -> false

  let (++) = concat

end



type t = 
  { global : Global.t; 
    local : Local.t;  }




