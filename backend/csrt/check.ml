open PPrint
open Utils
open Cerb_frontend
open Mucore
open Except
open List
open Sym
open Uni
open Pp_tools
open LogicalConstraints
open Resources
open IndexTerms
open BaseTypes
open VarTypes
open TypeErrors
open Environment
open FunctionTypes
open Binders
open Types
open Nat_big_num


open Global
open Env

module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module FT = FunctionTypes

module SymSet = Set.Make(Sym)


let budget = Some 5



let add_vars env bindings = fold_left add_var env bindings
let remove_vars env names = fold_left remove_var env names
let get_vars loc env vars = 
  fold_leftM (fun (acc,env) sym ->
      get_var loc env sym >>= fun (t,env) ->
      return (acc@[t], env)
    ) ([],env) vars

let add_Avar env b = add_var env {name = b.name; bound = A b.bound}
let add_Lvar env b = add_var env {name = b.name; bound = L b.bound}
let add_Rvar env b = add_var env {name = b.name; bound = R b.bound}
let add_Cvar env b = add_var env {name = b.name; bound = C b.bound}
let add_Avars env vars = List.fold_left add_Avar env vars
let add_Lvars env vars = List.fold_left add_Lvar env vars
let add_Rvars env vars = List.fold_left add_Rvar env vars
let add_Cvars env vars = List.fold_left add_Cvar env vars

let get_ALvar loc env var = 
  tryM (get_Avar loc env var)
    (get_Lvar loc env var >>= fun (Base bt, env) -> 
     return (bt, env))


let get_Rvars loc env vars = 
  fold_leftM (fun (acc,env) sym ->
      get_Rvar loc env sym >>= fun (t,env) ->
      return (acc@[t], env)
    ) ([],env) vars




let makeA name bt = {name; bound = A bt}
let makeL name ls = {name; bound = L ls}
let makeR name re = {name; bound = R re}
let makeC name lc = {name; bound = C lc}

let makeU t = {name = fresh (); bound = t}
let makeUA bt = makeA (fresh ()) bt
let makeUL bt = makeL (fresh ()) bt
let makeUR bt = makeR (fresh ()) bt
let makeUC bt = makeC (fresh ()) bt




let integer_value_to_num loc iv = 
  match Impl_mem.eval_integer_value iv with
  | Some v -> return v
  | None -> fail loc Integer_value_error

let size_of_ctype loc ct = 
  integer_value_to_num loc (Impl_mem.sizeof_ival ct)
      







(* types recording undefined behaviour, error cases, etc. *)
module UU = struct

  type u = 
   | Undefined of Loc.t * Undefined.undefined_behaviour
   | Unspecified of Loc.t (* * Ctype.ctype *)
   | StaticError of Loc.t * (string * Sym.t)

  type 'a or_u = 
    | Normal of 'a
    | Bad of u

  type ut = Types.t or_u

  let pp_ut = function
    | Normal t -> Types.pp t
    | Bad u -> !^"bad"

end

open UU




let constraint_holds loc env c =
  Solver.constraint_holds loc (Env.get_all_constraints env) c

let is_unreachable loc env =
  constraint_holds loc env (LC (Bool false))


let rec check_constraints_hold loc env = function
  | [] -> return ()
  | {name; bound = c} :: constrs ->
     debug_print 2 (action "checking constraint") >>= fun () ->
     debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
     debug_print 2 (blank 3 ^^ item "constraint" (LogicalConstraints.pp c)) >>= fun () ->
     constraint_holds loc env c >>= function
     | true -> 
        debug_print 2 (blank 3 ^^ !^(greenb "constraint holds")) >>= fun () ->
        check_constraints_hold loc env constrs
     | false -> 
        debug_print 2 (blank 3 ^^ !^(greenb "constraint does not hold")) >>= fun () ->
        fail loc (Call_error (Unsat_constraint (name, c)))


let vars_equal_to loc env sym bt = 
  let similar = 
    filter_vars (fun sym' t -> 
      match t with 
      | A bt' | L (Base bt') -> sym <> sym' && BT.type_equal bt bt'
      | _ -> false
    ) env 
  in
  filter_mapM (fun sym' -> 
      constraint_holds loc env (LC (S (sym,bt) %= S (sym',bt))) >>= fun holds ->
      return (if holds then Some sym' else None)
    ) similar






(* convert from other types *)

let rec bt_of_core_base_type loc cbt =
  let open Core in
  let bt_of_core_object_type loc ot =
    match ot with
    | OTy_integer -> return BT.Int
    | OTy_pointer -> return BT.Loc
    | OTy_array cbt -> return BT.Array
    | OTy_struct sym -> return (Struct sym)
    | OTy_union _sym -> fail loc (Unsupported !^"todo: unions")
    | OTy_floating -> fail loc (Unsupported !^"todo: float")
  in
  match cbt with
  | BTy_unit -> return BT.Unit
  | BTy_boolean -> return BT.Bool
  | BTy_object ot -> bt_of_core_object_type loc ot
  | BTy_loaded ot -> bt_of_core_object_type loc ot
  | BTy_list bt -> 
     bt_of_core_base_type loc bt >>= fun bt ->
     return (List bt)
  | BTy_tuple bts -> 
     mapM (bt_of_core_base_type loc) bts >>= fun bts ->
     return (Tuple bts)
  | BTy_storable -> fail loc (Unsupported !^"BTy_storable")
  | BTy_ctype -> fail loc (Unsupported !^"ctype")


let integer_value_min loc it = 
  integer_value_to_num loc (Impl_mem.min_ival it)

let integer_value_max loc it = 
  integer_value_to_num loc (Impl_mem.max_ival it)

let integerType_constraint loc name it =
  integer_value_min loc it >>= fun min ->
  integer_value_max loc it >>= fun max ->
  return (LC ((Num min %<= S (name, Int)) %& (S (name, Int) %<= Num max)))

let integerType loc name it =
  integerType_constraint loc name it >>= fun constr ->
  return ((name,Int), [], [], [makeUC constr])

let floatingType loc =
  fail loc (Unsupported !^"floats")

let rec ctype_aux loc name (Ctype.Ctype (annots, ct)) =
  let loc = update_loc loc annots in
  let open Ctype in
  match ct with
  | Void -> (* check *)
     return ((name,Unit), [], [], [])
  | Basic (Integer it) -> 
     integerType loc name it
  | Array (ct, _maybe_integer) -> 
     return ((name,BT.Array),[],[],[])
  | Pointer (_qualifiers, ct) ->
     ctype_aux loc (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
     let r = makeUR (Points (S (name, Loc), S (pointee_name, bt))) :: r in
     let l = makeL pointee_name (Base bt) :: l in
     return ((name,Loc),l,r,c)
  | Atomic ct ->              (* check *)
     ctype_aux loc name ct
  | Struct sym -> 
     return ((name, BT.Struct sym),[],[],[])
  | Union sym -> 
     fail loc (Unsupported !^"todo: union types")
  | Basic (Floating _) -> 
     floatingType loc 
  | Function _ -> 
     fail loc (Unsupported !^"function pointers")


let ctype loc (name : Sym.t) (ct : Ctype.ctype) =
  ctype_aux loc name ct >>= fun ((name,bt), l,r,c) ->
  return (makeA name bt :: l @ r @ c)

let make_pointer_ctype ct = 
  let open Ctype in
  (* fix *)
  let q = {const = false; restrict = false; volatile = false} in
  Ctype ([], Pointer (q, ct))













let check_base_type loc mname has expected =
  if BT.type_equal has expected 
  then return ()
  else 
    let msm = (Mismatch {mname; has = (A has); expected = A expected}) in
    fail loc (Call_error msm)


type aargs = ((BT.t Binders.t) * Loc.t) list

let rec make_Aargs loc env asyms = 
  match asyms with
  | [] -> return ([], env)
  | asym :: asyms ->
     let (name, loc) = aunpack loc asym in
     get_Avar loc env name >>= fun (t,env) ->
     make_Aargs loc env asyms >>= fun (rest, env) ->
     return (({name; bound = t}, loc) :: rest, env)




let resources_owned_by_var_or_equals loc env owner =
  get_ALvar loc env owner >>= fun (bt,_env) ->
  vars_equal_to loc env owner bt >>= fun equal_to_owner ->
  debug_print 3 (blank 3 ^^ !^"equal to" ^^^ Sym.pp owner ^^ colon ^^^
                   pp_env_list None equal_to_owner Sym.pp) >>= fun () ->
  let owneds = concat_map (fun o -> map (fun r -> (o,r)) (owned_resources env o))
                 (owner :: equal_to_owner) in
  return owneds
  




let make_Aargs_bind_lrc loc env rt =
  let open Alrc.Types in
  let rt = from_type rt in
  let env = add_Lvars env rt.l in
  let env = add_Rvars env rt.r in
  let env = add_Cvars env rt.c in
  let (rt : aargs) = (List.map (fun b -> (b,loc))) rt.a in
  (rt,env)


let check_Aargs_typ (mtyp : BT.t option) (aargs: aargs) : (BT.t option, 'e) m =
  fold_leftM (fun mt ({name = sym; bound = bt},loc) ->
      match mt with
      | None -> 
         return (Some bt)
      | Some t -> 
         check_base_type loc (Some sym) bt t >>= fun () ->
         return (Some t)
    ) mtyp aargs


let pp_unis unis = 
  let pp_entry (sym, {spec; resolved}) =
    match resolved with
    | Some res -> 
       (typ (Sym.pp sym) (LS.pp spec)) ^^^ !^"resolved as" ^^^ (Sym.pp res)
    | None -> (typ (Sym.pp sym) (LS.pp spec)) ^^^ !^"unresolved"
  in
  pp_env_list None (SymMap.bindings unis) pp_entry






let struct_member_type loc env struct_type field = 
  get_struct_decl loc env.global struct_type >>= fun binders ->
  match List.find_opt (fun b -> b.name = field) binders with
  | None -> 
     let err = !^"struct" ^^^ Sym.pp struct_type ^^^ 
                  !^"does not have field" ^^^ Sym.pp field in
     fail loc (Generic_error err)
  | Some b ->
     return b.bound


let unpack_struct loc env sym struct_type = 
  debug_print 2 (blank 3 ^^ (!^"unpacking struct" ^^^ Sym.pp sym)) >>= fun () ->
  match get_open_struct env sym with
  | None -> 
     Global.get_struct_decl loc env.global struct_type >>= fun fields ->
     let rec aux acc_bindings acc_name_mapping fields =
       match fields with
       | [] -> (acc_bindings, acc_name_mapping)
       | {name;bound} :: fields ->
          let sym = fresh () in
          let acc_bindings = acc_bindings @ [{name = sym; bound}] in
          let acc_name_mapping = acc_name_mapping @ [(name, sym)] in
          let fields = Types.subst name sym fields in
          aux acc_bindings acc_name_mapping fields
     in
     let (bindings, name_mapping) = aux [] [] fields in
     let env = add_open_struct env sym {field_names = name_mapping} in
     return (bindings, env)
  | Some {field_names} -> 
     (* already open *)
     let vars = List.map snd field_names in
     get_vars loc env vars >>= fun (ts, env) ->
     let t = map (fun (s,t) -> {name = s; bound = t}) (List.combine vars ts) in
     return (t, env)

let recursively_unpack_structs loc env bs = 
  let rec aux loc env acc_bindings todo_bindings = 
    match todo_bindings with
    | [] -> return (acc_bindings, env)
    | b :: todo_bindings ->
       match b.bound with
       | A (Struct s) | L (Base (Struct s)) -> 
          unpack_struct loc env b.name s >>= fun (newbindings,env) ->
          aux loc env (acc_bindings@[b]) (newbindings@todo_bindings)
       | _ -> 
          aux loc env (acc_bindings@[b]) todo_bindings
  in
  aux loc env [] bs
  


let rec pack_struct loc env struct_type args =
  get_struct_decl loc env.global struct_type >>= fun spec ->
  let args_and_specs = List.combine args spec in
  let subst_in_spec (old_sym : Sym.t) (new_sym : Sym.t) args_and_specs = 
    List.map (fun (b1,b2) -> (b1, Binders.subst VarTypes.subst old_sym new_sym b2)) 
      args_and_specs
  in
  let rec check env args_and_specs =
    match args_and_specs with
    | [] -> return env
    | (b1,b2) :: args_and_specs ->
       match b1.bound, get_open_struct env b1.name, b2.bound with
       | C _, _, C c2 ->
          begin constraint_holds loc env c2 >>= function
          | true -> check env args_and_specs
          | false -> fail loc (Return_error (Unsat_constraint (b2.name, c2)))
          end
       | A (Struct s1), Some fields, A (Struct s2) when s1 = s2 ->
          pack_open_struct loc env b1.name s1 fields >>= fun env ->
          check env (subst_in_spec b2.name b1.name args_and_specs)
       | A t1, _, A t2 when BT.type_equal t1 t2 ->
          check env (subst_in_spec b2.name b1.name args_and_specs)
       | L (Base (Struct s1)), Some fields, L (Base (Struct s2)) when s1 = s2 ->
          pack_open_struct loc env b1.name s1 fields >>= fun env ->
          check env (subst_in_spec b2.name b1.name args_and_specs)
       | L t1, _, L t2 when LS.type_equal t1 t2 ->
          check env (subst_in_spec b2.name b1.name args_and_specs)
       | R t1, _,  R t2 when RE.type_equal env t1 t2 ->
          check env args_and_specs
       | _, _, _ ->
          let msm = Mismatch {mname = Some b1.name; has = b1.bound; 
                              expected = b2.bound} in
          fail loc (Return_error (msm))
  in
  check env args_and_specs


and pack_open_struct loc env sym struct_type {Local.field_names} =
  let env = remove_open_struct env sym in
  let arg_syms = List.map snd field_names in
  get_vars loc env arg_syms >>= fun (arg_typs,env) ->
  let args = List.map from_tuple (List.combine arg_syms arg_typs) in
  pack_struct loc env struct_type args






(* begin: functions used for subtype and call_typ *)

let match_As errf loc env (args : aargs) (specs : (BT.t Binders.t) list) =
  let rec aux env acc_substs args specs =
    match args, specs with
    | [], [] -> 
       return (acc_substs,env)
    | (arg,loc) :: _, [] -> 
       fail loc (errf (Surplus_A (arg.name, arg.bound)))
    | [], spec :: _ -> 
       fail loc (errf (Missing_A (spec.name, spec.bound)))
    | ((arg,arg_loc) :: args), (spec :: specs) ->
       begin match arg.bound, get_open_struct env arg.name, spec.bound with
       | Struct s1, Some fields, Struct s2 when s1 = s2 ->
          pack_open_struct arg_loc env arg.name s1 fields >>= fun env ->
          aux env (acc_substs@[(spec.name,arg.name)]) args specs
       | _, _, _ when BT.type_equal arg.bound spec.bound ->
          aux env (acc_substs@[(spec.name,arg.name)]) args specs
       | _, _, _ ->
          let msm = Mismatch {mname = Some arg.name; 
                              has = A arg.bound; expected = A spec.bound} in
          fail loc (errf msm)
       end
  in
  aux env [] args specs

let record_lvars_for_unification (specs : (LS.t Binders.t) list) =
  let rec aux acc_unis acc_substs specs = 
    match specs with
    | [] -> (acc_unis,acc_substs)
    | spec :: specs ->
       let sym = Sym.fresh () in
       let uni = { spec = spec.bound; resolved = None } in
       let acc_unis = SymMap.add sym uni acc_unis in
       let acc_substs = acc_substs@[(spec.name,sym)] in
       aux acc_unis acc_substs specs
  in
  aux SymMap.empty [] specs

let match_Rs errf loc env (unis : ((LS.t, Sym.t) Uni.t) SymMap.t) specs =
  let rec aux env acc_substs unis specs = 
    match specs with
    | [] -> return (acc_substs,unis,env)
    | spec :: specs -> 
       match RE.owner spec.bound with
       | None -> fail loc (errf (Missing_R (spec.name, spec.bound)))
       | Some owner ->
          (* TODO: unsafe env *)
          resources_owned_by_var_or_equals loc env owner >>= fun owneds ->
          let rec try_resources = function
            | [] -> 
               fail loc (errf (Missing_R (spec.name, spec.bound)))
            | (o,r) :: owned_resources ->
               get_Rvar loc env r >>= fun (resource',env) ->
               let resource' = RE.subst o owner resource' in
               debug_print 3 (action ("trying resource" ^ pps (RE.pp resource'))) >>= fun () ->
               match RE.unify spec.bound resource' unis with
               | None -> try_resources owned_resources
               | Some unis ->
                  find_resolved env unis >>= fun (_,new_substs) ->
                  let new_substs = (spec.name,r) :: (map snd new_substs) in
                  let specs = 
                    fold_left (fun r (s, s') -> Binders.subst_list Resources.subst s s' r) 
                      specs new_substs
                  in
                  aux env (acc_substs@new_substs) unis specs
          in
          try_resources owneds
  in
  aux env [] unis specs


let match_Ls errf loc env (args : (LS.t Binders.t) list) (specs : (LS.t Binders.t) list) =
  let rec aux env acc_substs args specs = 
    match args, specs with
    | [], [] -> 
       return (acc_substs,env)
    | (arg :: args), (spec :: specs) ->
       begin match arg.bound, get_open_struct env arg.name, spec.bound with
       | LS.Base (Struct s1), Some fields, LS.Base (Struct s2) when s1 = s2 ->
          pack_open_struct loc env arg.name s1 fields >>= fun env ->
          aux env (acc_substs@[(spec.name,arg.name)]) args specs
       | _, _, _ when BT.type_equal arg.bound spec.bound ->
         (* apply this substitution and continue *)
          aux env (acc_substs@[(spec.name,arg.name)]) args specs
       | _, _, _ ->
          let msm = Mismatch {mname = Some arg.name; 
                              has = L arg.bound; expected = L spec.bound} in
          fail loc (errf msm)
       end
    | _ -> fail loc (Unreachable !^"surplus/missing L")
  in
  aux env [] args specs 


let ensure_unis_resolved loc env unis =
  find_resolved env unis >>= fun (unresolved,resolved) ->
  if SymMap.is_empty unresolved then 
    return resolved
  else
    let (usym, spec) = SymMap.find_first (fun _ -> true) unresolved in
    fail loc (Call_error (Unconstrained_l (usym,spec)))

(* end: functions used for subtype and call_typ *)






let call_typ loc_call env ftyp (args : aargs) =
    
  let open Alrc.Types in
  let open Alrc.FunctionTypes in
  let ftyp = Alrc.FunctionTypes.from_function_type ftyp in
  debug_print 1 (action "function call type") >>= fun () ->
  debug_print 2 (blank 3 ^^ item "ftyp" (Alrc.FunctionTypes.pp ftyp)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "args" (pp_env_list None args (fun ({name;bound},_) -> Sym.pp name))) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 2 PPrint.empty >>= fun () ->

  match_As (fun e -> Call_error e) loc_call env args ftyp.arguments2.a >>= fun (substs,env) ->
  let ftyp = fold_left (fun ftyp (sym,sym') -> subst sym sym' ftyp) 
               (updateAargs ftyp []) substs in

  let (unis,substs) = record_lvars_for_unification ftyp.arguments2.l in
  let ftyp = fold_left (fun ftyp (sym,sym') -> subst sym sym' ftyp) 
               (updateLargs ftyp []) substs in

  match_Rs (fun e -> Call_error e) loc_call env unis ftyp.arguments2.r >>= fun (substs,unis,env) ->
  let ftyp = fold_left (fun f (s, s') -> subst s s' f) (updateRargs ftyp []) substs in

  ensure_unis_resolved loc_call env unis >>= fun resolved ->

  fold_leftM (fun (ts,env) (_,(_,sym)) -> 
      get_ALvar loc_call env sym >>= fun (t,env) ->
      return (ts@[{name=sym; bound = LS.Base t}], env)
    ) ([],env) resolved >>= fun (largs,env) ->
  let lspecs = map (fun (spec,(sym,_)) -> {name=sym;bound=spec}) resolved in

  match_Ls (fun e -> Call_error e) loc_call env largs lspecs >>= fun (substs,env) ->
  let ftyp = fold_left (fun f (s, s') -> subst s s' f) ftyp substs in
  
  check_constraints_hold loc_call env ftyp.arguments2.c >>= fun () ->
  return ((to_function_type ftyp).return, env)



let subtype loc_ret env args rtyp =

  let open Alrc.Types in
  let rtyp = Alrc.Types.from_type rtyp in
  debug_print 1 (action "function return type") >>= fun () ->
  debug_print 2 (blank 3 ^^ item "rtyp" (Alrc.Types.pp rtyp)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "returned" (pp_env_list None args (fun ({name;bound},_) -> Sym.pp name))) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 2 PPrint.empty >>= fun () ->

  match_As (fun e -> Call_error e) loc_ret env args rtyp.a >>= fun (substs,env) ->
  let rtyp = List.fold_left (fun ftyp (sym,sym') -> subst sym sym' ftyp) 
               {rtyp with a = []} substs  in

  let (unis,substs) = record_lvars_for_unification rtyp.l in
  let rtyp = List.fold_left (fun rtyp (sym,sym') -> subst sym sym' rtyp) 
               {rtyp with l = []} substs in

  match_Rs (fun e -> Call_error e) loc_ret env unis rtyp.r >>= fun (substs,unis,env) ->
  let rtyp = fold_left (fun f (s, s') -> subst s s' f) {rtyp with r =  []} substs in

  ensure_unis_resolved loc_ret env unis >>= fun resolved ->

  fold_leftM (fun (ts,env) (_,(_,sym)) -> 
      get_ALvar loc_ret env sym >>= fun (t,env) ->
      return (ts@[{name=sym; bound = LS.Base t}], env)
    ) ([],env) resolved >>= fun (largs,env) ->
  let lspecs = map (fun (spec,(sym,_)) -> {name=sym;bound=spec}) resolved in

  match_Ls (fun e -> Call_error e) loc_ret env largs lspecs >>= fun (substs,env) ->
  let rtyp = fold_left (fun f (s, s') -> subst s s' f) rtyp substs in

  check_constraints_hold loc_ret env rtyp.c >>= fun () ->
  return env





let infer_ctor loc ctor (aargs : aargs) = 
  match ctor with
  | M_Ctuple -> 
     let name = fresh () in
     let bts = fold_left (fun bts (b,_) -> bts @ [b.bound]) [] aargs in
     let bt = Tuple bts in
     let constrs = 
       mapi (fun i (b,_) -> 
           makeUC (LC (Nth (of_int i, S (name,bt) %= S (b.name,b.bound)))))
         aargs
     in
     return ([makeA name bt]@constrs)
  | M_Carray -> 
     check_Aargs_typ None aargs >>= fun _ ->
     return [{name = fresh (); bound = A Array}]
  | M_CivCOMPL
  | M_CivAND
  | M_CivOR
  | M_CivXOR -> 
     fail loc (Unsupported !^"todo: Civ..")
  | M_Cspecified ->
     let name = fresh () in
     begin match aargs with
     | [({name = sym;bound = bt},_)] -> 
        return [makeA name bt; makeUC (LC (S (sym,bt) %= S (name,bt)))]
     | args ->
        let err = Printf.sprintf "Cspecified applied to %d argument(s)" 
                    (List.length args) in
        fail loc (Generic_error !^err)
     end
  | M_Cnil cbt -> fail loc (Unsupported !^"lists")
  | M_Ccons -> fail loc (Unsupported !^"lists")
  | M_Cfvfromint -> fail loc (Unsupported !^"floats")
  | M_Civfromfloat -> fail loc (Unsupported !^"floats")




(* let make_load_type loc ct : (FunctionTypes.t,'e) m = 
 *   let pointer_name = fresh () in
 *   ctype_aux loc (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
 *   let a = makeA pointer_name Loc in
 *   let l = makeL pointee_name (Base bt) :: l in
 *   let r = makeUR (Points (S (pointer_name, Loc), S (pointee_name, bt))) :: r in
 *   let addr_argument = a :: l @ r @ c in
 *   let ret_name = fresh () in
 *   let ret = makeA ret_name bt :: r @ [makeUC (LC (S (ret_name, bt) %= (S (pointee_name,bt))))] in
 *   return {arguments = addr_argument; return = ret} *)




(* let make_load_field_type loc ct : (FunctionTypes.t,'e) m = 
 *   let pointer_name = fresh () in
 *   ctype_aux loc (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
 *   let a = makeA pointer_name Loc in
 *   let l = makeL pointee_name (Base bt) :: l in
 *   let r = makeUR (Points (S (pointer_name, Loc), S (pointee_name, bt))) :: r in
 *   let addr_argument = a :: l @ r @ c in
 *   let ret_name = fresh () in
 *   let ret = makeA ret_name bt :: r @ [makeUC (LC (S (ret_name, bt) %= (S (pointee_name,bt))))] in
 *   return {arguments = addr_argument; return = ret} *)






(* have to also allow for Block of bigger size potentially *)
let make_initial_store_type loc ct = 
  let pointer_name = fresh () in
  size_of_ctype loc ct >>= fun size ->
  let p = [makeA pointer_name Loc; makeUR (Block (S (pointer_name, Loc), Num size))] in
  begin 
    ctype_aux loc (fresh ()) ct >>= fun ((value_name,bt),l,r,c) ->
    let value = makeA value_name bt :: l @ r @ c in
    let ret = makeUA Unit :: [makeUR (Points (S (pointer_name, Loc), S (value_name, bt)))] in
    return (value,ret)
  end >>= fun (value,ret) ->
  return {arguments = p @ value; return = ret}


let make_store_type loc ct : (FunctionTypes.t,'e) m = 
  let pointer_name = fresh () in
  ctype loc pointer_name (make_pointer_ctype ct) >>= fun address ->
  begin 
    ctype_aux loc (fresh ()) ct >>= fun ((value_name,bt),l,r,c) ->
    let value = makeA value_name bt :: l @ r @ c in
    let ret = makeUA Unit :: [makeUR (Points (S (pointer_name, Loc), S (value_name, bt)))] in
    return (value,ret)
  end >>= fun (value,ret) ->
  return {arguments = address @ value; return = ret}

(* similar to store type *)
let make_fun_arg_type sym loc ct =
  ctype loc sym (make_pointer_ctype ct) >>= fun pointer_and_value_before ->
  begin 
    ctype_aux loc (fresh ()) ct >>= fun ((value_name,bt),l,r,c) ->
    let ret =
      makeL value_name (Base bt) :: 
      (makeUR (Points (S (sym, Loc), S (value_name, bt)))) ::
      l @ r @ c 
    in
    return ret
  end >>= fun to_return ->
  return (pointer_and_value_before, to_return)



(* maybe replace this function: this does not look at symbols equal to
   sym for ownership currently *)
(* TODO: unsafe env *)
let is_uninitialised_pointer loc env sym = 
  get_Avar loc env sym >>= fun (bt, env) ->
  let resource_names = owned_resources env sym in
  get_Rvars loc env resource_names >>= fun (resources,_env) ->
  match bt, resources with
  | Loc, [Block _] -> return true
  | _,_ -> return false


let is_owned_pointer loc env sym = 
  debug_print 3 (action "checking whether owned pointer") >>= fun () ->
  debug_print 3 (blank 3 ^^ item "sym" (Sym.pp sym)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  get_Avar loc env sym >>= fun (bt, env) ->
  if bt <> Loc then return None
  else
    resources_owned_by_var_or_equals loc env sym >>= fun owneds ->
    let owneds = List.map snd owneds in
    get_Rvars loc env owneds >>= fun (resources,_env) ->
    let named_resources = List.combine owneds resources in
    let relevant = 
      (filter_map (fun (name,r) ->
           match r with
           | Points (_,S (pointee,bt)) -> Some (name,(pointee,bt) )
           | _ -> None) named_resources)
    in
    match relevant with
    | [] -> 
       debug_print 3 (blank 3 ^^ !^"no") >>= fun () ->
       return None
    | [(r,(p,bt))] -> 
       debug_print 3 (blank 3 ^^ !^"yes, to" ^^^ Sym.pp p ^^ hardline) >>= fun () ->
       return (Some (r,(p,bt)))
    | (r,(p,bt))::_::_ -> 
       (* this can happen, maybe normally, but at least when we're on
          a control-flow path that the constraint solver knows to be
          unreachable: with an inconsistent set of assumptions *)
       warn (!^"pointer" ^^^ Sym.pp sym ^^^ !^"owning multiple resources") >>= fun () ->
       debug_print 3 (blank 3 ^^ !^"yes, to" ^^^ Sym.pp p ^^ hardline) >>= fun () ->
       return (Some (r,(p,bt)))
    (* | _ -> fail loc (Unreachable (!^"pointer" ^^^ Sym.pp sym ^^^ !^"owning multiple resources")) *)




let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()






let infer_ptrval name loc env ptrval = 
  Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let typ = [makeA name Loc; makeUC (LC (Null (S (name, Loc))))] in
      return typ )
    ( fun sym -> 
      fail loc (Unsupported !^"function pointers") )
    ( fun _prov loc ->
      let typ = [makeA name Loc; makeUC (LC (S (name, Loc) %= Num loc))] in
      return typ )
    ( fun () -> fail loc (Unreachable !^"unspecified pointer value") )


let rec infer_mem_value loc env mem = 
  let open Ctype in
  Impl_mem.case_mem_value mem
    ( fun _ctyp -> fail loc (Unsupported !^"ctypes as values") )
    ( fun it _sym -> 
      (* todo: do something with sym *)
      ctype loc (fresh ()) (Ctype ([], Basic (Integer it))) >>= fun t ->
      return (t, env) )
    ( fun it iv -> 
      let name = fresh () in
      integer_value_to_num loc iv >>= fun v ->
      let val_constr = LC (S (name, Int) %= Num v) in
      integerType_constraint loc name it >>= fun type_constr ->
      Solver.constraint_holds loc [val_constr] type_constr >>= function
      | true -> return ([makeA name Int; makeUC val_constr], env)
      | false -> fail loc (Generic_error !^"Integer value does not satisfy range constraint")
    )
    ( fun ft fv -> floatingType loc )
    ( fun _ctype ptrval ->
      (* maybe revisit and take ctype into account *)
      infer_ptrval (fresh ()) loc env ptrval >>= fun t -> 
      return (t, env) )
    ( fun mem_values -> infer_array loc env mem_values )
    ( fun sym fields -> infer_struct loc env (sym,fields) )
    ( fun sym id mv -> infer_union loc env sym id mv )


(* here we're not using the 'pack_struct' logic because we're
   inferring resources and logical variables *)
and infer_struct loc env (sym,fields) =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  get_struct_decl loc env.global sym >>= fun binders ->
  fold_leftM (fun (args,env) (_id,_ct,mv) ->
      infer_mem_value loc env mv >>= fun (t, env) ->
      let (t,env) = make_Aargs_bind_lrc loc env t in
      return (args@t, env)
    ) ([],env) fields >>= fun (args,env) ->
  let packing_type = 
    { arguments = binders; 
      return = [{name = fresh (); bound = A (Struct sym)}] } in
  call_typ loc env packing_type args 


and infer_union loc env sym id mv =
  fail loc (Unsupported !^"todo: union types")

and infer_array loc env mem_values = 
  fail loc (Unsupported !^"todo: mem_value arrays")

let infer_object_value loc env ov =
  let name = fresh () in
  match ov with
  | M_OVinteger iv ->
     integer_value_to_num loc iv >>= fun i ->
     let t = makeA name Int in
     let constr = makeUC (LC (S (name, Int) %= Num i)) in
     return ([t; constr], env)
  | M_OVpointer p -> 
     infer_ptrval name loc env p >>= fun t ->
     return (t,env)
  | M_OVarray items ->
     make_Aargs loc env items >>= fun (args_bts,env) ->
     check_Aargs_typ None args_bts >>= fun _ ->
     return ([makeA name Array], env)
  | M_OVstruct (sym, fields) -> 
     infer_struct loc env (sym,fields)
  | M_OVunion (sym,id,mv) -> 
     infer_union loc env sym id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")


let infer_value loc env v : (Types.t * Env.t,'e) m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc env ov
  | M_Vunit ->
     return ([makeUA Unit], env)
  | M_Vtrue ->
     let name = fresh () in
     return ([makeA name Bool; makeUC (LC (S (name, Bool)))], env)
  | M_Vfalse -> 
     let name = fresh () in
     return ([makeA name Bool; makeUC (LC (Not (S (name, Bool))))], env)
  | M_Vlist (cbt, asyms) ->
     bt_of_core_base_type loc cbt >>= fun bt ->
     make_Aargs loc env asyms >>= fun (aargs, env) ->
     check_Aargs_typ (Some bt) aargs >>= fun _ ->
     return ([makeUA (List bt)], env)
  | M_Vtuple asyms ->
     make_Aargs loc env asyms >>= fun (aargs,env) ->
     let bts = fold_left (fun bts (b,_) -> bts @ [b.bound]) [] aargs in
     let name = fresh () in
     let bt = Tuple bts in
     let constrs = 
       mapi (fun i (b, _) -> 
           makeUC (LC (Nth (of_int i, S (name,bt) %= S (b.name,b.bound)))))
         aargs
     in
     return ((makeA name bt) :: constrs, env)






(* let rec check_pattern_and_bind loc env ret (M_Pattern (annots, pat_)) =
 *   let loc = precise_loc loc annots in
 *   match pat_ with
 *   | M_CaseBase (None, cbt) -> 
 *      match ret with
 *      | [
 *   | M_CaseBase (msym, cbt) -> 
 *   | M_CaseCtor (ctor, pats) -> 
 *   match ctor with
 *   | M_Ctuple -> 
 *   | M_Carray -> 
 *   | M_CivCOMPL
 *   | M_CivAND
 *   | M_CivOR
 *   | M_CivXOR -> 
 *      fail loc (Unsupported "todo: Civ..")
 *   | M_Cspecified ->
 *   | M_Cnil cbt -> fail loc (Unsupported "lists")
 *   | M_Ccons -> fail loc (Unsupported "lists")
 *   | M_Cfvfromint -> fail loc (Unsupported "floats")
 *   | M_Civfromfloat -> fail loc (Unsupported "floats") *)



(* let check_name_disjointness names_and_locations = 
 *   fold_leftM (fun names_so_far (name,loc) ->
 *       if not (SymSet.mem name names_so_far )
 *       then return (SymSet.add name names_so_far)
 *       else fail loc (Name_bound_twice name)
 *     ) SymSet.empty names_and_locations
 * 
 * 
 * let rec collect_pattern_names loc (M_Pattern (annots, pat)) = 
 *   let loc = update_loc loc annots in
 *   match pat with
 *   | M_CaseBase (None, _) -> []
 *   | M_CaseBase (Some sym, _) -> [(sym,update_loc loc annots)]
 *   | M_CaseCtor (_, pats) -> concat_map (collect_pattern_names loc) pats
 * 
 * 
 * let infer_pat loc pat = 
 * 
 *   let rec aux pat = 
 *     let (M_Pattern (annots, pat_)) = pat in
 *     let loc = update_loc loc annots in
 *     match pat_ with
 *     | M_CaseBase (None, cbt) ->
 *        type_of_core_base_type loc cbt >>= fun bt ->
 *        return ([((Sym.fresh (), bt), loc)], (bt, loc))
 *     | M_CaseBase (Some sym, cbt) ->
 *        bt_of_core_base_type loc cbt >>= fun bt ->
 *        return ([((sym, bt), loc)], (bt, loc))
 *     | M_CaseCtor (ctor, args) ->
 *        mapM aux args >>= fun bindingses_args_bts ->
 *        let bindingses, args_bts = List.split bindingses_args_bts in
 *        let bindings = List.concat bindingses in
 *        ctor_typ loc ctor args_bts >>= fun bt ->
 *        return (bindings, (bt, loc))
 *   in
 * 
 *   check_name_disjointness (collect_pattern_names loc pat) >>
 *   aux pat >>= fun (bindings, (bt, loc)) ->
 *   let (bindings,_) = List.split bindings in
 *   return (bindings, bt, loc) *)

     
let infer_pat loc (M_Pattern (annots, pat_)) = 
  fail loc (Unsupported !^"todo: implement infer_pat")


let binop_typ op = 
  let open Core in
  match op with
  | OpAdd -> (((Int, Int), Int), fun v1 v2 -> Add (v1, v2))
  | OpSub -> (((Int, Int), Int), fun v1 v2 -> Sub (v1, v2))
  | OpMul -> (((Int, Int), Int), fun v1 v2 -> Mul (v1, v2))
  | OpDiv -> (((Int, Int), Int), fun v1 v2 -> Div (v1, v2))
  | OpRem_t -> (((Int, Int), Int), fun v1 v2 -> Rem_t (v1, v2))
  | OpRem_f -> (((Int, Int), Int), fun v1 v2 -> Rem_f (v1, v2))
  | OpExp -> (((Int, Int), Int), fun v1 v2 -> Exp (v1, v2))
  | OpEq -> (((Int, Int), Bool), fun v1 v2 -> EQ (v1, v2))
  | OpGt -> (((Int, Int), Bool), fun v1 v2 -> GT (v1, v2))
  | OpLt -> (((Int, Int), Bool), fun v1 v2 -> LT (v1, v2))
  | OpGe -> (((Int, Int), Bool), fun v1 v2 -> GE (v1, v2))
  | OpLe -> (((Int, Int), Bool), fun v1 v2 -> LE (v1, v2))
  | OpAnd -> (((Bool, Bool), Bool), fun v1 v2 -> And (v1, v2))
  | OpOr -> (((Bool, Bool), Bool), fun v1 v2 -> Or (v1, v2))


  



let ensure_bad_unreachable loc env bad = 
  is_unreachable loc env >>= function
  | true -> return env
  | false -> 
     match bad with
     | Undefined (loc,ub) -> fail loc (TypeErrors.Undefined ub)
     | Unspecified loc -> fail loc TypeErrors.Unspecified
     | StaticError (loc, (err,pe)) -> fail loc (TypeErrors.StaticError (err,pe))
  


(* todo: which location should we use? *)
let check_field_access loc env sym access = 

  debug_print 2 (action "checking field access") >>= fun () ->
  debug_print 2 (blank 3 ^^ item "sym" (Sym.pp sym)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "access" (Id.pp access.field)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 2 PPrint.empty >>= fun () ->

  is_owned_pointer loc env sym >>= function
  | None -> fail loc (Generic_error !^"no ownership justifying struct access")
  | Some (resource,(pointee,bt)) ->
     begin match bt, get_open_struct env pointee with
     | Struct struct_type, Some {field_names}
          when struct_type = access.struct_type -> 
        return field_names
     | Struct struct_type, None
          when struct_type = access.struct_type -> 
        fail loc (Generic_error !^"check_field_access: record not open")
     | _ ->
        (* fix this to not refer to closed structs *)
        let msm = Mismatch { mname=Some pointee; has= A bt; 
                             expected= A (Struct access.struct_type)}  in
        fail loc (Call_error (msm)) 
     end >>= fun field_names ->
  NameMap.sym_of loc (Id.s access.field) (get_names env.global) >>= fun field ->
  let fvar = List.assoc field field_names in
  return ((resource,pointee),(fvar,access.loc))

(* change data structures to avoid empty list failure *)
let rec check_field_accesses loc env sym accesses =
  match accesses with
  | [] -> fail loc (Unreachable !^"empty access list")
  | [access] -> 
     check_field_access loc env sym access
  | access :: accesses ->
     check_field_access loc env sym access >>= fun (_,(sym,loc)) ->
     check_field_accesses loc env sym accesses >>= fun ((resource,sym),(sym2,loc)) ->
     return ((resource,sym),(sym2,loc))


let infer_pexpr loc env (pe : 'bty mu_pexpr) = 

  debug_print 1 (action "inferring pure expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr budget pe)) >>= fun () ->

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in

  begin match pe_ with
  | M_PEsym sym ->
     let name = fresh () in
     get_Avar loc env sym >>= fun (bt,env) ->
     let typ = [makeA name bt; makeUC (LC (S (sym, bt) %= S (name, bt)))] in
     return (Normal typ, env)
  | M_PEimpl i ->
     get_impl_constant loc env.global i >>= fun t ->
     return (Normal [makeUA t], env)
  | M_PEval v ->
     infer_value loc env v >>= fun (t, env) ->
     return (Normal t, env)
  | M_PEconstrained _ ->
     fail loc (Unsupported !^"todo: PEconstrained")
  | M_PEundef (loc,undef) ->
     return (Bad (Undefined (loc, undef)), env)
  | M_PEerror (err,asym) ->
     let (sym, loc) = aunpack loc asym in
     return (Bad (StaticError (loc, (err,sym))), env)
  | M_PEctor (ctor, args) ->
     make_Aargs loc env args >>= fun (aargs, env) ->
     infer_ctor loc ctor aargs >>= fun rt ->
     return (Normal rt, env)
  | M_PEarray_shift _ ->
     fail loc (Unsupported !^"todo: PEarray_shift")
  | M_PEmember_shift (asym, struct_type, fid) ->
     let (sym, loc) = aunpack loc asym in
     get_Avar loc env sym >>= fun (bt,env) ->
     begin match bt with
     | Loc ->
        let bt = StructField (sym, [{loc; struct_type; field=fid}]) in
        return (Normal [makeUA bt], env)
     | StructField (sym, accesses) ->
        let bt = StructField (sym, accesses@[{loc; struct_type; field=fid}]) in
        return (Normal [makeUA bt], env)
     | bt ->
        fail loc (Unreachable !^"member_shift applied to non-pointer")
     end
  | M_PEnot asym ->
     let (sym,loc) = aunpack loc asym in
     get_Avar loc env sym >>= fun (bt,env) ->
     check_base_type loc (Some sym) Bool bt >>= fun () ->
     let ret = fresh () in 
     let rt = [makeA sym Bool; makeUC (LC (S (ret,Bool) %= Not (S (sym,Bool))))] in
     return (Normal rt, env)
  | M_PEop (op,asym1,asym2) ->
     let (sym1,loc1) = aunpack loc asym1 in
     let (sym2,loc2) = aunpack loc asym2 in
     get_Avar loc1 env sym1 >>= fun (bt1,env) ->
     get_Avar loc2 env sym2 >>= fun (bt2,env) ->
     let (((ebt1,ebt2),rbt),c) = binop_typ op in
     check_base_type loc1 (Some sym1) bt1 ebt1 >>= fun () ->
     let ret = fresh () in
     let constr = LC ((c (S (sym1,bt1)) (S (sym1,bt2))) %= S (ret,rbt)) in
     return (Normal [makeA ret rbt; makeUC constr], env)
  | M_PEstruct _ ->
     fail loc (Unsupported !^"todo: PEstruct")
  | M_PEunion _ ->
     fail loc (Unsupported !^"todo: PEunion")
  | M_PEmemberof _ ->
     fail loc (Unsupported !^"todo: M_PEmemberof")
  | M_PEcall (fname, asyms) ->
     begin match fname with
     | Core.Impl impl -> 
        get_impl_fun_decl loc env.global impl
     | Core.Sym sym ->
        get_fun_decl loc env.global sym >>= fun (_loc,decl_typ,_ret_name) ->
        return decl_typ
     end >>= fun decl_typ ->
     make_Aargs loc env asyms >>= fun (args,env) ->
     call_typ loc env decl_typ args >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_PEcase _ -> fail loc (Unreachable !^"PEcase in inferring position")
  | M_PElet _ -> fail loc (Unreachable !^"PElet in inferring position")
  | M_PEif _ -> fail loc (Unreachable !^"PElet in inferring position")
  end >>= fun (typ,env) ->
  
  debug_print 3 (blank 3 ^^ item "inferred" (UU.pp_ut typ)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->
  return (typ,env)


let rec check_pexpr loc env (e : 'bty mu_pexpr) typ = 

  debug_print 1 (action "checking pure expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr budget e)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in

  match e_ with
  | M_PEif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun (t1,env) -> 
     check_base_type loc1 (Some sym1) t1 Bool >>= fun () ->
     check_pexpr loc (add_var env (makeUC (LC (S (sym1,Bool))))) e2 typ >>= fun _env ->
     check_pexpr loc (add_var env (makeUC (LC (Not (S (sym1,Bool)))))) e3 typ
  | M_PEcase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     get_Avar eloc env esym >>= fun (bt,env) ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat loc pat >>= fun (bindings, bt', ploc) ->
         check_base_type ploc None bt' bt >>= fun () ->
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_pexpr loc env' pe typ
       ) pats_es >>= fun _ ->
     return env
  | M_PElet (p, e1, e2) ->
     begin match p with 
     | M_Symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           let rt = rename newname rt in
           recursively_unpack_structs loc env rt >>= fun (rt,env) ->
           check_pexpr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           let rt = rename newname rt in
           recursively_unpack_structs loc env rt >>= fun (rt,env) ->
           check_pexpr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_Pat (M_Pattern (annots, M_CaseCtor _)) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported !^"todo: ctor pattern")
     end
  | _ ->
     infer_pexpr loc env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt -> 
        let (rt,env) = make_Aargs_bind_lrc loc env rt in
        subtype loc env rt typ
     | Bad bad -> ensure_bad_unreachable loc env bad
     end



let rec infer_expr loc env (e : ('a,'bty) mu_expr) = 

  debug_print 1 (action "inferring expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr budget e)) >>= fun () ->

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in

  begin match e_ with
  | M_Epure pe -> 
     infer_pexpr loc env pe
  | M_Ememop memop ->
     begin match memop with
     | M_PtrEq _ (* (asym 'bty * asym 'bty) *)
     | M_PtrNe _ (* (asym 'bty * asym 'bty) *)
     | M_PtrLt _ (* (asym 'bty * asym 'bty) *)
     | M_PtrGt _ (* (asym 'bty * asym 'bty) *)
     | M_PtrLe _ (* (asym 'bty * asym 'bty) *)
     | M_PtrGe _ (* (asym 'bty * asym 'bty) *)
     | M_Ptrdiff _ (* (actype 'bty * asym 'bty * asym 'bty) *)
     | M_IntFromPtr _ (* (actype 'bty * asym 'bty) *)
     | M_PtrFromInt _ (* (actype 'bty * asym 'bty) *)
       -> fail loc (Unsupported !^"todo: ememop")
     | M_PtrValidForDeref (a_ct, asym) ->
        let (ct, ct_loc) = aunpack loc a_ct in
        ctype_aux loc (fresh ()) (make_pointer_ctype ct) >>= fun ((name,bt),l,r,c) ->
        let ret_name = fresh () in
        let ptr_typ = (makeA name bt) :: l @ r @ c in
        (* todo: plug in some other constraint *)
        let constr = LC (S (ret_name,Bool)) in
        let decl_typ = FT.make ptr_typ ([makeA ret_name Bool; makeUC constr]@r) in
        make_Aargs loc env [asym] >>= fun (args,env) ->
        call_typ loc env decl_typ args >>= fun (rt, env) ->
        return (Normal rt, env)
     | M_PtrWellAligned _ (* (actype 'bty * asym 'bty  ) *)
     | M_PtrArrayShift _ (* (asym 'bty * actype 'bty * asym 'bty  ) *)
     | M_Memcpy _ (* (asym 'bty * asym 'bty * asym 'bty) *)
     | M_Memcmp _ (* (asym 'bty * asym 'bty * asym 'bty) *)
     | M_Realloc _ (* (asym 'bty * asym 'bty * asym 'bty) *)
     | M_Va_start _ (* (asym 'bty * asym 'bty) *)
     | M_Va_copy _ (* (asym 'bty) *)
     | M_Va_arg _ (* (asym 'bty * actype 'bty) *)
     | M_Va_end _ (* (asym 'bty) *) 
       -> fail loc (Unsupported !^"todo: ememop")
     end
  | M_Eaction (M_Paction (_pol, M_Action (aloc,_,action_))) ->
     begin match action_ with
     | M_Create (asym,a_ct,_prefix) -> 
        let (ct, ct_loc) = aunpack loc a_ct in
        let (sym, a_loc) = aunpack loc asym in
        get_Avar loc env sym >>= fun (a_bt,env) ->
        check_base_type loc (Some sym) Int a_bt >>= fun () ->
        let name = fresh () in
        size_of_ctype loc ct >>= fun size ->
        let rt = [makeA name Loc; makeUR (Block (S (name, Loc), Num size))] in
        return (Normal rt, env)
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
        fail loc (Unsupported !^"todo: CreateReadOnly")
     | M_Alloc (ct, sym, _prefix) -> 
        fail loc (Unsupported !^"todo: Alloc")
     | M_Kill (_is_dynamic, asym) -> 
        let (sym,loc) = aunpack loc asym in
        let resources = recursively_owned_resources env sym in
        let env = remove_vars env resources in
        return (Normal [makeUA Unit], env)
     | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
        let (ct, _ct_loc) = aunpack loc a_ct in
        let (sym1,loc1) = aunpack loc asym1 in
        let (val_sym,val_loc) = aunpack loc asym2 in
        get_Avar loc1 env sym1 >>= fun (bt1,env) ->
        get_Avar val_loc env val_sym >>= fun (val_bt,env) ->
        begin match is_structfield bt1 with
        | Some (sym,accesses) ->
           check_field_accesses loc env sym accesses >>= fun ((resource,old_struct),(fsym,floc)) ->
           get_Avar floc env fsym >>= fun (fbt,env) ->
           (* revisit when unpacking logical structs differently *)
           ctype loc (fresh ()) ct >>= fun consume_before_t ->
           ctype loc (fresh ()) ct >>= fun consume_value_t ->
           let ret = [makeUA Unit] in
           let ftyp = {arguments = consume_before_t @ consume_value_t; 
                       return = ret} in
           let args : aargs = [({name=fsym;bound=fbt},floc);({name=val_sym;bound=val_bt},val_loc)] in
           call_typ loc env ftyp args >>= fun (rt, env) ->
           begin match get_open_struct env old_struct with
           | None -> fail loc (Unreachable (!^"store: open struct is not open: " ^^ 
                                 Sym.pp old_struct))
           | Some {field_names} ->
              let field_names = List.map (fun (f,s) -> (f,Sym.subst fsym val_sym s)) 
                                  field_names in
              let env = remove_open_struct env old_struct in
              get_var loc env old_struct >>= fun (t,env) -> (* removes old_struct *)
              let new_struct = fresh () in
              let env = add_open_struct env new_struct {field_names} in
              let env = add_var env {name=new_struct;bound= t} in
              get_Rvar loc env resource >>= fun (r,env) ->
              let env = remove_var env resource in
              let env = add_Rvar env {name=resource; bound= RE.subst old_struct new_struct r} in
              return (Normal rt, env)
           end
        | None ->
           is_uninitialised_pointer loc1 env sym1 >>= begin function
            | true -> make_initial_store_type loc ct 
            | false -> make_store_type loc ct
           end >>= fun decl_typ ->
           let args = [({name=sym1;bound=bt1},loc1);({name=val_sym;bound=val_bt},val_loc)] in
           call_typ loc env decl_typ args >>= fun (rt, env) ->
           return (Normal rt, env)
        end
     | M_Load (_a_ct, asym, _mo) -> 
        let (sym,_) = aunpack loc asym in
        let ret = fresh () in
        get_Avar loc env sym >>= fun (bt,env) ->
        begin match is_structfield bt with
        | Some (sym,accesses) ->
           check_field_accesses loc env sym accesses >>= fun ((_,pointee),(fsym,floc)) ->
           get_Avar floc env fsym >>= fun (fbt,env) ->
           let constr = LC (S (ret, fbt) %= (S (fsym,fbt))) in
           let rt = [makeA ret fbt; makeUC constr] in
           return (Normal rt, env)
        | None ->
           begin is_owned_pointer loc env sym >>= function
            | Some (_r,(pointee,bt)) ->
               let constr = LC (S (ret,bt) %= S (pointee,bt)) in
               return (Normal [makeA ret bt; makeUC constr], env)
            | None -> fail loc (Generic_error !^"no ownership justifying load")
           end
        end
     | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) -> 
        fail loc (Unsupported !^"todo: RMW")
     | M_Fence mo -> 
        fail loc (Unsupported !^"todo: Fence")
     | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) -> 
        fail loc (Unsupported !^"todo: CompareExchangeStrong")
     | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) -> 
        fail loc (Unsupported !^"todo: CompareExchangeWeak")
     | M_LinuxFence mo -> 
        fail loc (Unsupported !^"todo: LinuxFemce")
     | M_LinuxLoad (ct, sym1, mo) -> 
        fail loc (Unsupported !^"todo: LinuxLoad")
     | M_LinuxStore (ct, sym1, sym2, mo) -> 
        fail loc (Unsupported !^"todo: LinuxStore")
     | M_LinuxRMW (ct, sym1, sym2, mo) -> 
        fail loc (Unsupported !^"todo: LinuxRMW")
     end
  | M_Eskip -> 
     return (Normal [makeUA Unit], env)
  | M_Eccall (_a, asym, asd, asyms) ->
     fail loc (Unsupported !^"todo: Eccall")
  | M_Eproc _ ->
     fail loc (Unsupported !^"todo: Eproc")
  | M_Ebound (n, e) ->
     infer_expr loc env e
  | M_End _ ->
     fail loc (Unsupported !^"todo: End")
  | M_Esave _ ->
     fail loc (Unsupported !^"todo: Esave")
  | M_Erun _ ->
     fail loc (Unsupported !^"todo: Erun")
  | M_Ecase _ -> fail loc (Unreachable !^"Ecase in inferring position")
  | M_Elet _ -> fail loc (Unreachable !^"Elet in inferring position")
  | M_Eif _ -> fail loc (Unreachable !^"Eif in inferring position")
  | M_Ewseq _ -> fail loc (Unsupported !^"Ewseq in inferring position")
  | M_Esseq _ -> fail loc (Unsupported !^"Esseq in inferring position")
  end >>= fun (typ,env) ->

  debug_print 3 (blank 3 ^^ item "inferred" (UU.pp_ut typ)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->
  return (typ,env)


let rec check_expr loc env (e : ('a,'bty) mu_expr) typ = 

  debug_print 1 (action "checking expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr budget e)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun (t1,env) -> 
     check_base_type loc1 (Some sym1) t1 Bool >>= fun () ->
     let then_constr = makeUC (LC (S (sym1,Bool))) in
     let else_constr = makeUC (LC (Not (S (sym1,Bool)))) in
     check_expr loc (add_var env then_constr) e2 typ >>= fun _env ->
     check_expr loc (add_var env else_constr) e3 typ
  | M_Ecase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     get_Avar eloc env esym >>= fun (bt,env) ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat loc pat >>= fun (bindings, bt', ploc) ->
         check_base_type ploc None bt' bt >>= fun () ->
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_expr loc env' pe typ
       ) pats_es >>= fun _ ->
     return env     
  | M_Epure pe -> 
     check_pexpr loc env pe typ
  | M_Elet (p, e1, e2) ->
     begin match p with 
     | M_Symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           let rt = rename newname rt in
           recursively_unpack_structs loc env rt >>= fun (rt,env) ->
           check_expr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           let rt = rename newname rt in
           recursively_unpack_structs loc env rt >>= fun (rt,env) ->
           check_expr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_Pat (M_Pattern (annots, M_CaseCtor _)) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported !^"todo: ctor pattern")
     end
  | M_Ewseq (p, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (p, e1, e2) ->
     begin match p with 
     | M_Pattern (annots, M_CaseBase (mnewname,_cbt))
     | M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))])) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_expr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           let rt = rename newname rt in
           recursively_unpack_structs loc env rt >>= fun (rt,env) ->
           check_expr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_Pattern (annots, M_CaseCtor _) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported !^"todo: ctor pattern")
     end
  | M_Esave (_ret, args, body) ->
     fold_leftM (fun env (sym, (_, asym)) ->
         let (vsym,loc) = aunpack loc asym in
         get_Avar loc env vsym >>= fun (bt,env) ->
         return (add_var env (makeA sym bt))
       ) env args >>= fun env ->
     check_expr loc env body typ
  | _ ->
     infer_expr loc env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt ->
        let (rt,env) = make_Aargs_bind_lrc loc env rt in
        subtype loc env rt typ
     | Bad bad -> ensure_bad_unreachable loc env bad
     end
     





let check_proc loc fsym genv body ftyp = 
  debug_print 1 (h1 ("Checking procedure " ^ (pps (Sym.pp fsym)))) >>= fun () ->
  let env = with_fresh_local genv in
  recursively_unpack_structs loc env ftyp.arguments >>= fun (args,env) ->
  let env = add_vars env args in
  check_expr loc env body ftyp.return >>= fun _env ->
  debug_print 1 (!^(greenb "...checked ok")) >>= fun () ->
  return ()

let check_fun loc fsym genv body ftyp = 
  debug_print 1 (h1 ("Checking function " ^ (pps (Sym.pp fsym)))) >>= fun () ->
  let env = with_fresh_local genv in
  recursively_unpack_structs loc env ftyp.arguments >>= fun (args,env) ->
  let env = add_vars env args in
  check_pexpr loc env body ftyp.return >>= fun _env ->
  debug_print 1 (!^(greenb "...checked ok")) >>= fun () ->
  return ()


let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) =

  let check_consistent loc ftyp args ret = 

    let forget = 
      filter_map (function {name; bound = A t} -> Some {name;bound = t} | _ -> None) 
    in

    let binding_of_core_base_type loc (sym,cbt) = 
      bt_of_core_base_type loc cbt >>= fun bt ->
      return {name=sym;bound= bt}
    in

    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    if BT.types_equal (forget ftyp.arguments) args &&
         BT.types_equal (forget ftyp.return) ([ret])
    then return ()
    else 
      let inject = map (fun b -> {name = b.name; bound = A b.bound}) in
      let defn = {arguments = inject args; return = inject [ret]} in
      let err = 
        flow (break 1) 
          ((words "Function definition of") @ 
             [Sym.pp fsym] @
             words ("inconsistent. Should be")@
             [FunctionTypes.pp ftyp ^^ comma]@  [!^"is"] @
               [FunctionTypes.pp defn])
                               
      in
      fail loc (Generic_error err)
  in
  match fn with
  | M_Fun (ret, args, body) ->
     get_fun_decl Loc.unknown genv fsym >>= fun decl ->
     let (loc,ftyp,ret_name) = decl in
     check_consistent loc ftyp args (ret_name,ret) >>= fun () ->
     check_fun loc fsym genv body ftyp
  | M_Proc (loc, ret, args, body) ->
     get_fun_decl loc genv fsym >>= fun decl ->
     let (loc,ftyp,ret_name) = decl in
     check_consistent loc ftyp args (ret_name,ret) >>= fun () ->
     check_proc loc fsym genv body ftyp
  | M_ProcDecl _
  | M_BuiltinDecl _ -> 
     return ()


let check_functions (type a bty) env (fns : (bty,a) mu_fun_map) =
  pmap_iterM (check_function env) fns

                             


let record_fun sym (loc,_attrs,ret_ctype,args,is_variadic,_has_proto) genv =
  if is_variadic then fail loc (Variadic_function sym) else
    fold_leftM (fun (args,returns) (msym, ct) ->
        make_fun_arg_type (sym_or_fresh msym) loc ct >>= fun (arg,ret) ->
        return (args@arg, returns@ret)
      ) ([],[]) args >>= fun (arguments, returns) ->
    let ret_name = Sym.fresh () in
    ctype loc ret_name ret_ctype >>= fun ret ->
    let ftyp = {arguments; return = ret@returns} in
    return (add_fun_decl genv sym (loc, ftyp, ret_name))

let record_funinfo genv funinfo = 
  pmap_foldM record_fun funinfo genv


(* check the types? *)
let record_impl impl impl_decl genv = 
  match impl_decl with
  | M_Def (bt, _p) -> 
     bt_of_core_base_type Loc.unknown bt >>= fun bt ->
     return (add_impl_constant genv impl bt)
  | M_IFun (bt, args, _body) ->
     mapM (fun (sym,a_bt) -> 
         bt_of_core_base_type Loc.unknown a_bt >>= fun a_bt ->
         return (makeA sym a_bt)) args >>= fun args_ts ->
     bt_of_core_base_type Loc.unknown bt >>= fun bt ->
     let ftyp = {arguments = args_ts; return = [makeUA bt]} in
     return (add_impl_fun_decl genv impl ftyp)
                        


let record_impls genv impls = pmap_foldM record_impl impls genv



let record_tagDef sym def genv =

  match def with
  | Ctype.UnionDef _ -> 
     fail Loc.unknown (Unsupported !^"todo: union types")
  | Ctype.StructDef (fields, _) ->

     fold_leftM (fun (names,fields) (id, (_attributes, _qualifier, ct)) ->
       let id = Id.s id in
       let name = Sym.fresh_pretty id in
       let names = (id, name) :: names in
       ctype Loc.unknown name ct >>= fun newfields ->
       return (names, fields @ newfields)
     ) ([],[]) fields >>= fun (names,fields) ->

     let genv = add_struct_decl genv sym fields in
     let genv = fold_left (fun genv (id,sym) -> 
                    record_name_without_loc genv id sym) genv names in
     return genv


let record_tagDefs genv tagDefs = 
  pmap_foldM record_tagDef tagDefs genv







let pp_fun_map_decl funinfo = 
  let pp = Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (Pp_utils.to_plain_string pp)


let print_initial_environment genv = 
  debug_print 1 (h1 "initial environment") >>= fun () ->
  debug_print 1 (Global.pp genv)


let check mu_file =
  pp_fun_map_decl mu_file.mu_funinfo;
  let genv = Global.empty in
  record_tagDefs genv mu_file.mu_tagDefs >>= fun genv ->
  record_funinfo genv mu_file.mu_funinfo >>= fun genv ->
  print_initial_environment genv >>= fun () ->
  check_functions genv mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception (loc,err) -> 
     report_type_error loc err;
     raise (Failure "type error")







(* todo: 
   - correctly unpack logical structs,
   - make call_typ accept non-A arguments
   - struct handling in constraint solver
   - more struct rules
   - revisit rules implemented using store rule
 *)
