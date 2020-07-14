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



module ImplMap = 
  Map.Make
    (struct 
      type t = CF.Implementation.implementation_constant
      let compare = CF.Implementation.implementation_constant_compare 
     end)


let lookup_sym_list (loc : Loc.t) (e: (Sym.t * 'a) list) (name: Sym.t) =
  match List.find_opt (fun (n,_) -> n = name) e with
  | None -> fail loc (Unbound_name name)
  | Some (n,t) -> return t

let rec remove_sym_list (loc : Loc.t) (e: (Sym.t * 'a) list) (name: Sym.t) = 
  match e with
  | (name',t)::rest when name = name' ->
     return rest
  | (name',t)::rest ->
     let* rest' = remove_sym_list loc rest name in
     return ((name',t)::rest')
  | [] -> 
     fail loc (Unreachable (!^"symbol to remove not in environment:" ^^^ Sym.pp name))
  
  

let lookup_sym_map (loc : Loc.t) (e: 'v SymMap.t) (name: Sym.t) =
  match SymMap.find_opt name e with
  | None -> fail loc (Unbound_name name)
  | Some v -> return v

let lookup_impl (loc : Loc.t) (e: 'v ImplMap.t) i =
  match ImplMap.find_opt i e with
  | None -> fail loc (Unbound_impl_const i)
  | Some v -> return v


type struct_sig = 
  { sbinder: Sym.t;
    souter: RT.t 
  }

type struct_decl = 
  { raw: (BT.member * BT.t) list;
    ctypes: (BaseTypes.member * CF.Ctype.ctype) list;
    open_type: struct_sig;
    closed_type: struct_sig; 
  }


module Global = struct 

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

  let get_struct_decl loc genv (BT.Tag s) = 
    match SymMap.find_opt s genv.struct_decls with
    | Some decl -> return decl 
    | None -> 
       let err = !^"struct" ^^^ Sym.pp s ^^^ !^"not defined" in
       fail loc (Generic_error err)

  let get_fun_decl loc genv sym = lookup_sym_map loc genv.fun_decls sym
  let get_impl_fun_decl loc genv i = lookup_impl loc genv.impl_fun_decls i
  let get_impl_constant loc genv i = lookup_impl loc genv.impl_constants i

  let pp_struct_decls decls = 
    pp_list
      (fun (sym, s) -> 
        let tag = BT.Tag sym in
        item (plain (Sym.pp sym) ^ " (raw)") 
          (pp_list (fun (BT.Member m, bt) -> typ !^m (BT.pp true bt)) s.raw) ^/^
        item (plain (Sym.pp sym) ^ " (open)") 
          (RT.pp (RT.Computational (s.open_type.sbinder, BT.Struct tag, s.open_type.souter))) ^/^
        item (plain (Sym.pp sym) ^ " (closed)") 
          (RT.pp (RT.Computational (s.closed_type.sbinder, BT.Struct tag, s.closed_type.souter)))
      )
      (SymMap.bindings decls) 
             

  let pp_fun_decls decls = 
    flow_map hardline
      (fun (sym, (_, t)) -> item (plain (Sym.pp sym)) (FT.pp t))
      (SymMap.bindings decls)

  let pp_items genv = 
    [ (1, h2 "Structs")
    ; (1, pp_struct_decls genv.struct_decls)
    ; (1, h2 "Functions")
    ; (1, pp_fun_decls genv.fun_decls)
    ]

  let pp genv = separate (break 1) (map snd (pp_items genv))

end

module Local = struct

  type used = 
    | Used of Loc.t
    | Unused

  type lenv = 
    { avars: (Sym.t * (BT.t * Sym.t)) list;
      lvars: LS.t SymMap.t;
      rvars: (RE.t * used) SymMap.t;
      cvars: LC.t SymMap.t;
    }

  type t = lenv

  let empty = 
    { avars = [];
      lvars = SymMap.empty;
      rvars = SymMap.empty;
      cvars = SymMap.empty;
    }

  let print_constraint_names = false

  let pp lenv =
    (separate hardline
       [ inline_item "computational" 
           (pp_list (fun (n,(t,r)) -> typ (Sym.pp n) (parens (BT.pp false t ^^^ bar ^^^ (Sym.pp r))))
              lenv.avars)
       ; inline_item "logical" 
           (pp_list (fun (n,t) -> typ (Sym.pp n) (LS.pp false t)) 
              (SymMap.bindings lenv.lvars))
       ; inline_item "unused resources" 
           (pp_list (fun (_n,t) -> Resources.pp false t)
              (filter_map (fun (n,(t,u)) -> if u = Unused then Some (n,t) else None) 
                 (SymMap.bindings lenv.rvars)))
       ; inline_item "used resources" 
           (pp_list (fun (_n,t) -> Resources.pp false t)
              (filter_map (fun (n,(t,u)) -> if u <> Unused then Some (n,t) else None) 
                 (SymMap.bindings lenv.rvars)))
       ; inline_item "constraints" 
           (pp_list (fun (_n,t) -> LogicalConstraints.pp false t)
              (SymMap.bindings lenv.cvars))
       ]
    )

    let add_avar env (name,t) = { env with avars = (name,t) :: env.avars } 
    let add_lvar env (name,t) = { env with lvars = SymMap.add name t env.lvars } 
    let add_rvar env (name,t) = { env with rvars = SymMap.add name t env.rvars } 
    let add_cvar env (name,t) = { env with cvars = SymMap.add name t env.cvars } 

    let get_avar (loc : Loc.t) env (name: Sym.t) = lookup_sym_list loc env.avars name
    let get_lvar (loc : Loc.t) env (name: Sym.t) = lookup_sym_map loc env.lvars name
    let get_r (loc : Loc.t) env (name: Sym.t) = 
      let* (t,u) = lookup_sym_map loc env.rvars name in
      match u with
      | Unused -> return t
      | Used where -> fail loc (Resource_used (t,where))
    let get_c (loc : Loc.t) env (name: Sym.t) = lookup_sym_map loc env.cvars name
      
    let remove_avar loc env name = 
      let* avars = remove_sym_list loc env.avars name in
      return { env with avars }
    let remove_avars loc env names = 
      fold_leftM (remove_avar loc) env names

    let use_resource loc env sym = 
      let* t = get_r loc env sym in
      return { env with rvars = SymMap.add sym (t,Used loc) env.rvars }

    let check_resource_used loc env sym = 
      let* found = lookup_sym_map loc env.rvars sym in
      match found with
      | (_,Used _) -> return ()
      | (t,Unused) -> fail loc (Generic_error (RE.pp false t ^^^ !^"unused"))

    let all_constraints env = 
      List.map snd (SymMap.bindings env.cvars)
    
end



module Env = struct

  type t = 
    { global : Global.t; 
      local : Local.t;  }

  type env = t

  let with_fresh_local genv = 
    { global = genv; 
      local = Local.empty }

  let add_avar env (name,t) = { env with local = Local.add_avar env.local (name,t) }
  let add_lvar env (name,t) = { env with local = Local.add_lvar env.local (name,t) }
  let add_rvar env (name,t) = { env with local = Local.add_rvar env.local (name,t) }
  let add_cvar env (name,t) = { env with local = Local.add_cvar env.local (name,t) }
  let add_c env t = add_cvar env (Sym.fresh (), t)
  let remove_avar loc env name = 
    let* lenv = Local.remove_avar loc env.local name in
    return { env with local = lenv }
  let remove_avars loc env names = 
    let* lenv = Local.remove_avars loc env.local names in
    return { env with local = lenv }


  let get_avar (loc : Loc.t) (env: env) (name: Sym.t) = 
    Local.get_avar loc env.local name

  let get_lvar (loc : Loc.t) (env: env) (name: Sym.t) = 
    Local.get_lvar loc env.local name

  let get_r (loc : Loc.t) (env: env) (name: Sym.t) = 
    Local.get_r loc env.local name

  let get_c (loc : Loc.t) (env: env) (name: Sym.t) = 
    Local.get_c loc env.local name

  let check_resource_used loc env sym = 
    Local.check_resource_used loc env.local sym

  let check_resources_used loc env syms = 
    iterM (fun sym -> check_resource_used loc env sym) syms

  let filter_resources p env = 
    SymMap.fold (fun sym t acc -> 
        let* acc = acc in
        let* holds = p sym t in 
        match holds with 
        | Some x -> return (x :: acc) 
        | None -> return acc
      )
      env.local.rvars (return [])


  (* let add_vars env bindings = fold_left add_var env bindings
   * let add_uvars env bindings = fold_left add_uvar env bindings
   * let get_vars loc env vars = mapM (fun sym -> get_var loc env sym) vars
   * let remove_vars env names = fold_left remove_var env names *)

  let use_resource loc env sym = 
    let* lenv = Local.use_resource loc env.local sym in
    return { env with local = lenv }

  let check_resource_used loc env sym = 
    Local.check_resource_used loc env.local sym

  let all_constraints env = 
    Local.all_constraints env.local

end

