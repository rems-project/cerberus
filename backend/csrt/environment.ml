open Cerb_frontend
open PPrint
open Pp_tools
open List
open VarTypes
open Binders
open Except
open TypeErrors


module Loc = Location
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts

module GEnv = struct 

  open Implementation

  module ImplMap = 
    Map.Make
      (struct 
        type t = implementation_constant
        let compare = implementation_constant_compare 
       end)

  type t = 
    { struct_decls : Types.t SymMap.t; 
      fun_decls : (Loc.t * FunctionTypes.t * Sym.t) SymMap.t; (* third item is return name *)
      impl_fun_decls : FunctionTypes.t ImplMap.t;
      impl_constants : BT.t ImplMap.t;
      names : NameMap.t
    } 

  type genv = t


  let empty = 
    { struct_decls = SymMap.empty; 
      fun_decls = SymMap.empty;
      impl_fun_decls = ImplMap.empty;
      impl_constants = ImplMap.empty;
      names = NameMap.empty }

  let get_impl_const_type (genv: genv) (i: implementation_constant) = 
    ImplMap.find i genv.impl_constants

  let get_impl_fun_type (genv: genv) (i: implementation_constant) = 
    ImplMap.find i genv.impl_fun_decls


  let pp_struct_decls decls = 
    separate_map (break 1)
      (fun (sym, bs) -> item (Sym.pp sym) (Types.pp bs))
      (SymMap.bindings decls)

  let pp_fun_decls decls = 
    separate_map (break 1) 
      (fun (sym, (_, t, _ret)) -> typ (Sym.pp sym) (FunctionTypes.pp t))
      (SymMap.bindings decls)

  let pp_name_map m = 
    separate_map (break 1) 
      (fun (name,sym) -> item (!^name) (Sym.pp sym))
      (NameMap.all_names m)

  let pp_items genv = 
    [ (1, h2 "Structs")
    ; (1, pp_struct_decls genv.struct_decls)
    ; (1, h2 "Functions")
    ; (1, pp_fun_decls genv.fun_decls)
    ; (1, h2 "Names")
    ; (1, pp_name_map genv.names)
    ]
  let pp genv = lines (map snd (pp_items genv))

end

module LEnv = struct

  type lenv = VarTypes.t SymMap.t

  type t = lenv

  let empty = SymMap.empty

  let pp_avars = 
    flow_map (comma ^^ break 1)
    (fun (sym, t) -> typ (Sym.pp sym) (BT.pp t))

  let pp_lvars = 
    flow_map (comma ^^ break 1)
    (fun (sym, t) -> typ (Sym.pp sym) (LS.pp t))

  let pp_rvars = 
    flow_map (comma ^^ break 1)
    (fun (sym, t) -> typ (Sym.pp sym) (RE.pp t))

  let pp_cvars = 
    flow_map (comma ^^ break 1)
    (fun (sym, t) -> typ (Sym.pp sym) (LC.pp t))

  let pp lenv =
    let (a,l,r,c) = 
      SymMap.fold (fun name b (a,l,r,c) ->
          match b with
          | A t -> (((name,t) :: a),l,r,c)
          | L t -> (a,((name,t) :: l),r,c)
          | R t -> (a,l,((name,t) :: r),c)
          | C t -> (a,l,r,((name,t) :: c))
        ) lenv ([],[],[],[])
    in
    (separate (break 1)
       [ item !^"A" (pp_avars a)
       ; item !^"L" (pp_lvars l)
       ; item !^"R" (pp_rvars r)
       ; item !^"C" (pp_cvars c)
    ])

    let add_var env b = SymMap.add b.name b.bound env
    let remove_var env sym = SymMap.remove sym env

end



module Env = struct

  type t = 
    { local : LEnv.t ; 
      global : GEnv.t }

  type env = t

  let empty = 
    { local = LEnv.empty; 
      global = GEnv.empty }

  let with_fresh_local genv = 
    { global = genv; 
      local = LEnv.empty }

  let add_var env b = {env with local = LEnv.add_var env.local b}
  let remove_var env sym = { env with local = LEnv.remove_var env.local sym }

  let add_vars env bindings = fold_left add_var env bindings
  let remove_vars env bindings = fold_left remove_var env bindings

  let add_Avar env (name, t) = add_var env {name; bound = A t}
  let add_Lvar env (name, t) = add_var env {name; bound = L t}
  let add_Rvar env (name, t) = add_var env {name; bound = R t}
  let add_Cvar env (name, t) = add_var env {name; bound = C t}

  let add_Avars env vars = List.fold_left add_Avar env vars

  let lookup (loc : Loc.t) (env: 'v SymMap.t) (name: Sym.t) =
    match SymMap.find_opt name env with
    | None -> fail loc (Unbound_name name)
    | Some v -> return v

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) =
    lookup loc env.local name >>= function
    | A t -> return (`A t)
    | L t -> return (`L t)
    | R t -> return (`R (t, remove_var env name))
    | C t -> return (`C t)


  let kind = function
    | `A _ -> Argument
    | `L _ -> Logical
    | `R _ -> Resource
    | `C _ -> Constraint

  let get_Avar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `A t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `L t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `R (t, env) -> return (t, env)
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `C t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Constraint; has = kind t})

  let get_owned_resource loc env owner_sym = 
    let relevant = 
      SymMap.fold (fun name b acc ->
          match b with
          | (R t) -> if RE.owner t = owner_sym then (name,t) :: acc else acc
          | _ -> acc
        ) env.local []
    in
    match relevant with
    | [] -> return None
    | [owned] -> return (Some owned)
    | _ -> fail loc (Unreachable "multiple owners of resource")


  open Implementation
  let get_impl_const_type (env: env) (i: implementation_constant) = 
    GEnv.get_impl_const_type env.global i
  let get_impl_fun_type (env: env) (i: implementation_constant) = 
    GEnv.get_impl_fun_type env.global i


end

