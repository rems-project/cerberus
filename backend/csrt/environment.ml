open Cerb_frontend
open PPrint
open Pp_tools
open List
open VarTypes
open Binders
open Except
open TypeErrors


module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts







module ImplMap = 
  Map.Make
    (struct 
      type t = Implementation.implementation_constant
      let compare = Implementation.implementation_constant_compare 
     end)


let lookup_sym (loc : Loc.t) (env: 'v SymMap.t) (name: Sym.t) =
  match SymMap.find_opt name env with
  | None -> fail loc (Unbound_name name)
  | Some v -> return v

let lookup_impl (loc : Loc.t) (env: 'v ImplMap.t) i =
  match ImplMap.find_opt i env with
  | None -> fail loc (Unbound_impl_const i)
  | Some v -> return v



module GEnv = struct 

  type t = 
    { struct_decls : Types.t SymMap.t; 
      fun_decls : (Loc.t * FunctionTypes.t * Sym.t) SymMap.t; (* third item is return name *)
      impl_fun_decls : FunctionTypes.t ImplMap.t;
      impl_constants : BT.t ImplMap.t;
      names : NameMap.t
    } 


  let empty = 
    { struct_decls = SymMap.empty; 
      fun_decls = SymMap.empty;
      impl_fun_decls = ImplMap.empty;
      impl_constants = ImplMap.empty;
      names = NameMap.empty }

  let add_struct_decl genv sym typ = 
    { genv with struct_decls = SymMap.add sym typ genv.struct_decls }

  let add_fun_decl genv fsym (loc, typ, ret_sym) = 
    { genv with fun_decls = SymMap.add fsym (loc,typ,ret_sym) genv.fun_decls }

  let add_impl_fun_decl genv i typ = 
    { genv with impl_fun_decls = ImplMap.add i typ genv.impl_fun_decls }

  let add_impl_constant genv i typ = 
    { genv with impl_constants = ImplMap.add i typ genv.impl_constants }


  let get_struct_decl loc genv sym = 
    match SymMap.find_opt sym genv.struct_decls with
    | Some decl -> return decl 
    | None -> 
       let err = !^"struct" ^^^ Sym.pp sym ^^^ !^"not defined" in
       fail loc (Generic_error err)


  let get_fun_decl loc genv sym = 
    lookup_sym loc genv.fun_decls sym

  let get_impl_fun_decl loc genv i = 
    lookup_impl loc genv.impl_fun_decls i

  let get_impl_constant loc genv i = 
    lookup_impl loc genv.impl_constants i

  let get_names genv = genv.names

  let record_name genv loc string sym =
    { genv with names = NameMap.record loc string sym genv.names }

  let record_name_without_loc genv string sym =
    { genv with names = NameMap.record_without_loc string sym genv.names }


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

  let pp genv = 
    lines (map snd (pp_items genv))

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
    { global : GEnv.t; 
      local : LEnv.t;  }

  type env = t

  let with_fresh_local genv = 
    { global = genv; 
      local = LEnv.empty }

  let add_var env b = {env with local = LEnv.add_var env.local b}
  let remove_var env sym = { env with local = LEnv.remove_var env.local sym }

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) =
    lookup_sym loc env.local name >>= function
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

  (* internal, have to make mli file *)
  let unsafe_owned_resource loc env owner_sym = 
    let relevant = 
      SymMap.fold (fun name b acc ->
          match b with
          | (R t) -> if RE.owner t = owner_sym then (name,t) :: acc else acc
          | _ -> acc
        ) env.local []
    in
    match relevant with
    | [] -> return None
    | [(s,r)] -> return (Some (s,r))
    | _ -> fail loc (Unreachable "multiple owners of resource")

  (* returns only name, so safe *)
  let owned_resource loc env owner_sym = 
    unsafe_owned_resource loc env owner_sym >>= function
    | Some (name,_) -> return (Some name)
    | None -> return None

  (* returns only name, so safe *)
  let rec recursively_owned_resources loc env owner_sym = 
    unsafe_owned_resource loc env owner_sym >>= function
    | Some (res,t) -> 
       let owned = RE.owned t in
       mapM (recursively_owned_resources loc env) owned >>= fun owneds ->
       return (res :: List.concat owneds)
    | None -> 
       return []


end

