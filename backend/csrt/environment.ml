open Cerb_frontend
open PPrint
open Pp_tools
open List
open VarTypes
open Binders
open Except
open TypeErrors

module SymSet = Set.Make(Sym)


module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts



let print_resource_names = false
let print_constraint_names = false


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



module Global = struct 

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
    pp_env_list None 
      (SymMap.bindings decls) 
      (fun (sym, bs) -> typ (Sym.pp sym) (Types.pp bs))
             

  let pp_fun_decls decls = 
    pp_env_list None
      (SymMap.bindings decls)
      (fun (sym, (_, t, _ret)) -> typ (Sym.pp sym) (FunctionTypes.pp t))

  let pp_name_map m = 
    pp_env_list None
      (NameMap.all_names m)
      (fun (name,sym) -> item name (Sym.pp sym))

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

module Local = struct

  type lenv = VarTypes.t SymMap.t

  type t = lenv

  let empty = SymMap.empty

  let pp_avars avars = 
    pp_env_list (Some brackets) avars
      (fun (sym, t) -> typ (Sym.pp sym) (BT.pp t))

  let pp_lvars lvars = 
    pp_env_list (Some brackets) lvars
      (fun (sym, t) -> typ (Sym.pp sym) (LS.pp t))

  let pp_rvars rvars = 
    pp_env_list (Some brackets) rvars
      (fun (sym, t) -> 
        if print_resource_names then typ (Sym.pp sym) (RE.pp t) 
        else (RE.pp t))

  let pp_cvars cvars = 
    pp_env_list (Some brackets) cvars
      (fun (sym, t) -> 
        if print_constraint_names then typ (Sym.pp sym) (LC.pp t) 
        else (LC.pp t))

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
    (flow (break 1)
       [ inline_item "computational" (pp_avars a)
       ; inline_item "logical" (pp_lvars l)
       ; inline_item "resources" (pp_rvars r)
       ; inline_item "constraints" (pp_cvars c)
       ]
    )

    let add_var env b = SymMap.add b.name b.bound env
    let remove_var env sym = SymMap.remove sym env

end



module Env = struct

  type t = 
    { global : Global.t; 
      local : Local.t;  }

  type env = t

  let with_fresh_local genv = 
    { global = genv; 
      local = Local.empty }

  let add_var env b = {env with local = Local.add_var env.local b}
  let remove_var env sym = { env with local = Local.remove_var env.local sym }

  let internal_get_var (loc : Loc.t) (env: t) (name: Sym.t) =
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
    internal_get_var loc env sym >>= function
    | `A t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    internal_get_var loc env sym >>= function
    | `L t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    internal_get_var loc env sym >>= function
    | `R (t, env) -> return (t, env)
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    internal_get_var loc env sym >>= function
    | `C t -> return t
    | t -> fail loc (Var_kind_error {sym; expected = VarTypes.Constraint; has = kind t})

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) = 
    lookup_sym loc env.local name >>= function
    | R t -> return (R t, remove_var env name)
    | t -> return (t, env)

  let filter_vars p env = 
    SymMap.fold (fun sym t acc -> if p sym t then sym :: acc else acc) 
      env.local []


  (* internal only *)
  let unsafe_owned_resource env owner_sym = 
    SymMap.fold (fun name b acc ->
        match b with
        | (R t) -> 
           begin match RE.owner t with
           | None -> []
           | Some owner ->
              if owner = owner_sym 
              then (name,t) :: acc
              else acc
           end
        | _ -> acc
      ) env.local [] 

  (* returns only name, so safe *)
  let owned_resources env owner_sym = 
    let resources = unsafe_owned_resource env owner_sym in
    map fst resources

  (* returns only name, so safe *)
  let rec recursively_owned_resources env owner_sym = 
    let resources = unsafe_owned_resource env owner_sym in
    let names = List.map fst resources in
    let owned = List.concat_map (fun (_,t) -> RE.owned t) resources in
    let owneds = concat_map (recursively_owned_resources env) owned in
    names @ owneds


  let get_all_constraints env = 
    SymMap.fold (fun _ b acc -> match b with C c -> c :: acc | _ -> acc)
      env.local []

  let get_constraints_about env sym =
    SymMap.fold (fun _ b acc -> 
        match b with
        | C c -> if SymSet.mem sym (LC.syms_in c) then c :: acc else acc
        | _ -> acc
      ) 
      env.local []

end

