open Utils
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
      struct_layouts : ((Sym.t * num) list) SymMap.t; 
      fun_decls : (Loc.t * FunctionTypes.t * Sym.t) SymMap.t; (* third item is return name *)
      impl_fun_decls : FunctionTypes.t ImplMap.t;
      impl_constants : BT.t ImplMap.t;
      names : NameMap.t
    } 


  let empty = 
    { struct_decls = SymMap.empty; 
      struct_layouts = SymMap.empty; 
      fun_decls = SymMap.empty;
      impl_fun_decls = ImplMap.empty;
      impl_constants = ImplMap.empty;
      names = NameMap.empty }

  let add_struct_decl genv sym typ = 
    { genv with struct_decls = SymMap.add sym typ genv.struct_decls }

  let add_struct_layout genv sym l = 
    { genv with struct_layouts = SymMap.add sym l genv.struct_layouts }

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

  let get_struct_layout loc genv sym = 
    match SymMap.find_opt sym genv.struct_layouts with
    | Some layout -> return layout
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
    pp_list None 
      (fun (sym, bs) -> typ (bold (Sym.pp sym)) (Types.pp bs))
      (SymMap.bindings decls) 
             

  let pp_fun_decls decls = 
    pp_list None
      (fun (sym, (_, t, _ret)) -> typ (bold (Sym.pp sym)) (FunctionTypes.pp t))
      (SymMap.bindings decls)

  let pp_name_map m = 
    pp_list None
      (fun (name,sym) -> item name (Sym.pp sym))
      (NameMap.all_names m)

  let pp_items genv = 
    [ (1, h2 "Structs")
    ; (1, pp_struct_decls genv.struct_decls)
    ; (1, h2 "Functions")
    ; (1, pp_fun_decls genv.fun_decls)
    ; (1, h2 "Names")
    ; (1, pp_name_map genv.names)
    ]

  let pp genv = separate (break 1) (map snd (pp_items genv))

end

module Local = struct

  type lenv = 
    { vars: VarTypes.t SymMap.t }

  type t = lenv

  let empty = 
    { vars = SymMap.empty }

  let pp_avars vars = pp_list (Some brackets) (Binders.pp BT.pp) vars 
  let pp_lvars vars = pp_list (Some brackets) (Binders.pp LS.pp) vars
  let pp_rvars vars = pp_list (Some brackets) (Binders.pp RE.pp) vars 
  let pp_cvars vars = pp_list (Some brackets) (Binders.pp LC.pp) vars

  let pp lenv =
    let (a,l,r,c) = 
      SymMap.fold (fun name b (a,l,r,c) ->
          match b with
          | A t -> (({name;bound = t} :: a),l,r,c)
          | L t -> (a,({name; bound= t} :: l),r,c)
          | R t -> (a,l,({name; bound = t} :: r),c)
          | C t -> (a,l,r,({name; bound = t} :: c))
        ) lenv.vars ([],[],[],[])
    in
    (flow (break 1)
       [ inline_item "computational" (pp_avars a)
       ; inline_item "logical" (pp_lvars l)
       ; inline_item "resources" (pp_rvars r)
       ; inline_item "constraints" (pp_cvars c)
       ]
    )


    let add_var env b = 
      { vars = SymMap.add b.name b.bound env.vars} 

    let remove_var env sym = 
      { vars = SymMap.remove sym env.vars} 

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

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) = 
    lookup_sym loc env.local.vars name >>= function
    | R t -> return (R t, remove_var env name)
    (* | A (Struct s) -> return (A (Struct s), remove_var env name)
     * | L (Base (Struct s)) -> return (L (Base (Struct s)), remove_var env name) *)
    | t -> return (t, env)

  let get_Avar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | (A t, env) -> return (t, env)
    | (t,_) -> fail loc (Var_kind_error {sym; expected = VarTypes.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | (L t, env) -> return (t, env)
    | (t,_) -> fail loc (Var_kind_error {sym; expected = VarTypes.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | (R t, env) -> return (t, env)
    | (t,_) -> fail loc (Var_kind_error {sym; expected = VarTypes.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | (C t, env) -> return (t, env)
    | (t,_) -> fail loc (Var_kind_error {sym; expected = VarTypes.Constraint; has = kind t})

  let filter_vars p env = 
    SymMap.fold (fun sym t acc -> if p sym t then sym :: acc else acc) 
      env.local.vars []


  let resources_associated_with env sym = 
    filter_vars (fun _ t ->
        match t with
        | R t -> RE.associated t = sym
        | _ -> false
      ) env


  let resources_for_loc env loc_sym = 
    filter_vars (fun sym t ->
        match t with
        | R t ->
          begin match RE.footprint t with
          | None -> false
          | Some (loc,size) -> loc = loc_sym 
          end
        | _ -> false
      ) env


  let get_all_constraints env = 
    SymMap.fold (fun _ b acc -> match b with C c -> c :: acc | _ -> acc)
      env.local.vars []

  let get_constraints_about env sym =
    SymMap.fold (fun _ b acc -> 
        match b with
        | C c -> if SymSet.mem sym (LC.syms_in c) then c :: acc else acc
        | _ -> acc
      ) 
      env.local.vars []

  let is_struct_open env struct_sym = 
    SymMap.fold (fun r t acc -> 
        match t with
        | R (OpenedStruct (s,field_names)) when s = struct_sym ->
           Some (r,field_names)
        | _ -> acc
      ) 
      env.local.vars None

end

