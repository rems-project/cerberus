open Pp
open List
open Except
open TypeErrors
open VarTypes

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


let lookup_sym (loc : Loc.t) (env: 'v SymMap.t) (name: Sym.t) =
  match SymMap.find_opt name env with
  | None -> fail loc (Unbound_name name)
  | Some v -> return v

let lookup_impl (loc : Loc.t) (env: 'v ImplMap.t) i =
  match ImplMap.find_opt i env with
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

  let get_fun_decl loc genv sym = lookup_sym loc genv.fun_decls sym
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

  type lenv = { vars: VarTypes.t SymMap.t }

  type t = lenv

  let empty = 
    { vars = SymMap.empty }

  let print_constraint_names = false

  let pp lenv =
    let (a,l,r,c) = 
      SymMap.fold (fun name b (a,l,r,c) ->
          match b with
          | A _ -> ((name,b) :: a,l,r,c)
          | L _ -> (a,(name,b) :: l,r,c)
          | R _ -> (a,l,(name,b) :: r,c)
          | C _ -> (a,l,r,(name,b) :: c)
        ) lenv.vars ([],[],[],[])
    in
    let pp_vars vars = pp_list (fun (n,t) -> typ (Sym.pp n) (VarTypes.pp false t)) vars in
    (separate hardline
       [ inline_item "computational" (pp_vars a)
       ; inline_item "logical" (pp_vars l)
       ; inline_item "resources" (pp_vars r)
       ; inline_item "constraints" (pp_vars c)
       ]
    )

    let add_var env (name,t) = { vars = SymMap.add name t env.vars} 

end



module Env = struct

  type t = 
    { global : Global.t; 
      local : Local.t;  }

  type env = t

  let with_fresh_local genv = 
    { global = genv; 
      local = Local.empty }

  let add_var env (name,b) = {env with local = Local.add_var env.local (name,b)}
  let add_uvar env b = {env with local = Local.add_var env.local (Sym.fresh (),b)}
  (* let remove_var env sym = { env with local = Local.remove_var env.local sym } *)

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) = 
    let* found = lookup_sym loc env.local.vars name in
    match found with
    | R (t,Used where) -> fail loc (Resource_used (t,where))
    | t -> return t

  let get_Avar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    let* found = get_var loc env sym in
    match found with
    | A t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    let* found = get_var loc env sym in
    match found with
    | L t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    let* found = get_var loc env sym in
    match found with
    | R (t,Used where) -> fail loc (Resource_used (t,where))
    | R (t,Unused) -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    let* found = get_var loc env sym in
    match found with
    | C t -> return (t, env)
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Constraint; has = kind t})

  let get_ALvar loc env var = 
    tryM 
      (let* (Base bt) = get_Lvar loc env var in 
       return bt)
      (get_Avar loc env var)

  let filter_vars p env = 
    SymMap.fold (fun sym t acc -> 
        let* acc = acc in
        let* holds = p sym t in 
        match holds with 
        | Some x -> return (x :: acc) 
        | None -> return acc
      )
      env.local.vars (return [])


  let add_vars env bindings = fold_left add_var env bindings
  let add_uvars env bindings = fold_left add_uvar env bindings
  let get_vars loc env vars = mapM (fun sym -> get_var loc env sym) vars

  let use_resource loc env sym = 
    let* t = get_Rvar loc env sym in
    return (add_var env (sym, R (t, Used loc)))

  let get_all_constraints env = 
    SymMap.fold (fun _ b acc -> match b with C c -> c :: acc | _ -> acc)
      env.local.vars []



end

