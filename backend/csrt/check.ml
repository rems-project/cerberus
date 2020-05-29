open Subst
open Tools
open Pp
open Except
open List
open Sym
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


open Global
open Env

module CF=Cerb_frontend
open CF.Mucore

module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module FT = FunctionTypes

module SymSet = Set.Make(Sym)


let pp_budget = Some 7



let error pp =
  CB.Pipeline.run_pp None 
    (hardline ^^
     hardline ^^ 
     !^(redb "[!] Error") ^/^ pp ^^
     hardline
    );
  exit 1




let assoc_err loc list entry err =
  match List.assoc_opt list entry with
  | Some result -> return result
  | None -> fail loc (Unreachable (!^"list assoc failed:" ^^^ !^err))





(* types recording undefined behaviour, error cases, etc. *)
module UU = struct

  type u = 
   | Undefined of Loc.t * CF.Undefined.undefined_behaviour
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







let vars_equal_to loc env sym ls = 
  let similar = 
    filter_vars (fun sym' t -> 
      match t with 
      | A bt' -> sym <> sym' && LS.type_equal ls (LS.Base bt')
      | L ls' -> sym <> sym' && LS.type_equal ls ls'
      | _ -> false
    ) env 
  in
  filter_mapM (fun sym' -> 
      let c = (LC (S (sym,ls) %= S (sym',ls))) in
      let* holds = Solver.constraint_holds loc env c in
      return (if holds then Some sym' else None)
    ) similar






(* convert from other types *)

let rec bt_of_core_base_type loc cbt =
  let open CF.Core in
  let bt_of_core_object_type loc ot =
    match ot with
    | OTy_integer -> return BT.Int
    | OTy_pointer -> return BT.Loc
    | OTy_array cbt -> return BT.Array
    | OTy_struct sym -> return (ClosedStruct (Tag sym))
    | OTy_union _sym -> fail loc (Unsupported !^"todo: unions")
    | OTy_floating -> fail loc (Unsupported !^"todo: float")
  in
  match cbt with
  | BTy_unit -> return BT.Unit
  | BTy_boolean -> return BT.Bool
  | BTy_object ot -> bt_of_core_object_type loc ot
  | BTy_loaded ot -> bt_of_core_object_type loc ot
  | BTy_list bt -> 
     let* bt = bt_of_core_base_type loc bt in
     return (List bt)
  | BTy_tuple bts -> 
     let* bts = mapM (bt_of_core_base_type loc) bts in
     return (Tuple bts)
  | BTy_storable -> fail loc (Unsupported !^"BTy_storable")
  | BTy_ctype -> fail loc (Unsupported !^"ctype")




let integerType_constraint loc about it =
  let* min = Memory.integer_value_min loc it in
  let* max = Memory.integer_value_max loc it in
  return (LC ((Num min %<= S (about,Base Int)) %& 
                (S (about,Base Int) %<= Num max)))

let integerType loc name it =
  let* constr = integerType_constraint loc name it in
  return ((name,Int), [], [], [makeUC constr])

let floatingType loc =
  fail loc (Unsupported !^"floats")

let rec ctype_aux owned packed loc name (CF.Ctype.Ctype (annots, ct_)) =
  let loc = update_loc loc annots in
  match ct_ with
  | Void -> return ((name,Unit), [], [], [])
  | Basic (Integer it) -> integerType loc name it
  | Array (ct, _maybe_integer) -> return ((name,BT.Array),[],[],[])
  | Pointer (_qualifiers, ct) ->
     if owned then
       let* ((pointee_name,bt),l,r,c) = ctype_aux owned packed loc (fresh ()) ct in
       let* size = Memory.size_of_ctype loc ct in
       let r = makeUR (Points {pointer = name; pointee = Some pointee_name; 
                               typ = ct; size}) :: r in
       let l = makeL pointee_name (Base bt) :: l in
       return ((name,Loc),l,r,c)
     else
       return ((name,Loc),[],[],[])
  (* fix *)
  | Atomic ct -> ctype_aux owned packed loc name ct
  | Struct sym -> return ((name, ClosedStruct (Tag sym)),[],[],[])
  | Basic (Floating _) -> floatingType loc 
  | Union sym -> fail loc (Unsupported !^"todo: union types")
  | Function _ -> fail loc (Unsupported !^"function pointers")



let ctype owned packed loc (name : Sym.t) (ct : CF.Ctype.ctype) =
  let* ((name,bt),l,r,c) = ctype_aux owned packed loc name ct in
  return (makeA name bt :: l @ r @ c)

let make_pointer_ctype ct = 
  let open CF.Ctype in
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
     let* (t,env) = get_Avar loc env name in
     let* (rest,env) = make_Aargs loc env asyms in
     return (({name; bound = t}, loc) :: rest, env)



let make_Aargs_bind_lrc loc env rt =
  let open Alrc.Types in
  let rt = from_type rt in
  let env = add_Lvars env rt.l in
  let env = add_Rvars env rt.r in
  let env = add_Cvars env rt.c in
  let (rt : aargs) = (List.map (fun b -> (b,loc))) rt.a in
  (rt,env)




let resources_associated_with_var_or_equals loc env owner =
  let* (bt,_env) = get_ALvar loc env owner in
  let* equal_to_owner = vars_equal_to loc env owner (Base bt) in
  let* () = debug_print 3 (blank 3 ^^ !^"equal to" ^^^ Sym.pp owner ^^ colon ^^^
                             pp_list None Sym.pp equal_to_owner) in
  let owneds = 
    concat_map (fun o -> map (fun r -> (o,r)) (resources_associated_with env o))
      (owner :: equal_to_owner) 
  in
  return owneds
  




let points_to loc env sym = 
  let* owneds = resources_associated_with_var_or_equals loc env sym in
  let resource_names = List.map snd owneds in
  let* (resources,_env) = get_Rvars loc env resource_names in
  let named_resources = List.combine resource_names resources in
  let check = function
    | (r, Points p) :: _ -> return (Some (r,p))
    | [] -> return None
  in
  check named_resources






let check_Aargs_typ (mtyp : BT.t option) (aargs: aargs) : BT.t option m =
  fold_leftM (fun mt ({name = sym; bound = bt},loc) ->
      match mt with
      | None -> 
         return (Some bt)
      | Some t -> 
         let* () = check_base_type loc (Some sym) bt t in
         return (Some t)
    ) mtyp aargs


let pp_unis unis = 
  let pp_entry (sym, Uni.{spec; resolved}) =
    match resolved with
    | Some res -> 
       (typ (Sym.pp sym) (LS.pp true spec)) ^^^ !^"resolved as" ^^^ (Sym.pp res)
    | None -> (typ (Sym.pp sym) (LS.pp true spec)) ^^^ !^"unresolved"
  in
  pp_list None pp_entry (SymMap.bindings unis)





  


(* begin: shared logic for function calls, function returns, struct packing *)

let match_As errf loc env (args : aargs) (specs : (BT.t Binders.t) list) =
  let* () = debug_print 2 (action "matching computational variables") in

  let rec aux env acc_substs args specs =
    let* () = debug_print 2 (blank 3 ^^ item "args" (pps Sym.pp (BT.pp false) (List.map fst args))) in
    let* () = debug_print 2 (blank 3 ^^ item "spec" (pps Sym.pp (BT.pp false) specs)) in
    match args, specs with
    | [], [] -> 
       let* () = debug_print 2 (blank 3 ^^ !^"done.") in
       return (acc_substs,env)
    | (arg,loc) :: _, [] -> 
       fail loc (errf (Surplus_A (arg.name, arg.bound)))
    | [], spec :: _ -> 
       fail loc (errf (Missing_A (spec.name, spec.bound)))
    | ((arg,arg_loc) :: args), (spec :: specs) ->
       if BT.type_equal arg.bound spec.bound then
         aux env (acc_substs@[{substitute=spec.name;swith= arg.name}]) args specs
       else
         let msm = Mismatch {mname = Some arg.name; 
                             has = A arg.bound; expected = A spec.bound} in
         fail loc (errf msm)
  in
  aux env [] args specs

let record_lvars_for_unification (specs : (LS.t Binders.t) list) =
  let rec aux acc_unis acc_substs specs = 
    match specs with
    | [] -> (acc_unis,acc_substs)
    | spec :: specs ->
       let sym = Sym.fresh () in
       let uni = Uni.{ spec = spec.bound; resolved = None } in
       let acc_unis = SymMap.add sym uni acc_unis in
       let acc_substs = acc_substs@[{substitute=spec.name; swith= sym}] in
       aux acc_unis acc_substs specs
  in
  aux SymMap.empty [] specs


let match_Ls errf loc env (args : (LS.t Binders.t) list) (specs : (LS.t Binders.t) list) =
  let* () = debug_print 2 (action "matching logical variables") in
  let* () = debug_print 2 (blank 3 ^^ item "args" (pps Sym.pp (LS.pp false) args)) in
  let* () = debug_print 2 (blank 3 ^^ item "spec" (pps Sym.pp (LS.pp false) specs)) in
  let rec aux env acc_substs args specs = 
    match args, specs with
    | [], [] -> 
       let* () = debug_print 2 (blank 3 ^^ !^"done.") in
       return (acc_substs,env)
    | (arg :: args), (spec :: specs) ->
       if LS.type_equal arg.bound spec.bound then
         aux env (acc_substs@[{substitute=spec.name;swith=arg.name}]) args specs
       else
         let msm = Mismatch {mname = Some arg.name; 
                             has = L arg.bound; expected = L spec.bound} in
         fail loc (errf msm)
    | _ -> fail loc (Unreachable !^"surplus/missing L")
  in
  aux env [] args specs 


let ensure_unis_resolved loc env unis =
  let (unresolved,resolved) = Uni.find_resolved env unis in
  if SymMap.is_empty unresolved then return resolved else
    let (usym, spec) = SymMap.find_first (fun _ -> true) unresolved in
    fail loc (Call_error (Unconstrained_l (usym,spec)))



let match_Rs errf loc env (unis : ((LS.t, Sym.t) Uni.t) SymMap.t) specs =
  let* () = debug_print 2 (action "matching resources") in
  let rec aux env acc_substs unis specs = 
    let* () = debug_print 2 (blank 3 ^^ item "spec" (pps Sym.pp (RE.pp false) specs)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
    match specs with
    | [] -> 
       let* () = debug_print 2 (blank 3 ^^ !^"done.") in
       return (acc_substs,unis,env)
    | spec :: specs -> 
       let owner = RE.associated spec.bound in
       (* TODO: unsafe env *)
       let* owneds = resources_associated_with_var_or_equals loc env owner in
       let rec try_resources = function
         | [] -> 
            fail loc (errf (Missing_R (spec.name, spec.bound)))
         | (o,r) :: owned_resources ->
            let* (resource',env) = get_Rvar loc env r in
            let resource' = RE.subst_var {substitute=o; swith=owner} resource' in
            let* () = debug_print 3 (action ("trying resource" ^ plain (RE.pp false resource'))) in
            match RE.unify spec.bound resource' unis with
            | None -> try_resources owned_resources
            | Some unis ->
               let (_,new_substs) = Uni.find_resolved env unis in
               let new_substs = {substitute=spec.name; swith=r} :: (map snd new_substs) in
               let specs = 
                 fold_left (fun r subst -> 
                     Binders.subst_list Sym.subst Resources.subst_var subst r) 
                   specs new_substs
               in
               aux env (acc_substs@new_substs) unis specs
       in
       try_resources owneds
  in
  aux env [] unis specs

(* end: shared logic for function calls, function returns, struct packing *)



(* TODO: remove all the Ctype auxiliary things *)
let rec unpack_struct logical loc genv tag = 
  let* () = debug_print 2 (blank 3 ^^ (!^"unpacking struct")) in
  let* decl = Global.get_struct_decl loc genv tag in
  let rec aux acc_bindings acc_fields (fields : (member * VarTypes.t Binders.t) list) =
    match fields with
    | [] -> 
       return (acc_bindings, acc_fields)
    | (Member id, {name=lname;bound = A (ClosedStruct tag2)}) :: fields ->
       let* ((newsym,bt),newbindings) = unpack_struct false loc genv tag2 in
       let acc_fields = acc_fields @ [(Member id, newsym)] in
       let acc_bindings = acc_bindings @ newbindings @ [{name=newsym;bound = if logical then L (Base bt) else A bt}] in
       let fields = map (fun (mem,binding) -> (mem,Binders.subst VarTypes.subst_var {substitute=lname;swith=newsym} binding)) fields in
       aux acc_bindings acc_fields fields
    | (Member id, {name=lname; bound = L (Base (ClosedStruct tag2))}) :: fields ->
       let* ((newsym,bt),newbindings) = unpack_struct true loc genv tag2 in
       let acc_bindings = acc_bindings @ newbindings @ [{name=newsym;bound = L (Base bt)}] in
       let fields = map (fun (mem,binding) -> (mem,Binders.subst VarTypes.subst_var {substitute=lname;swith=newsym} binding)) fields in
       aux acc_bindings acc_fields fields
    | (Member id, {name=lname;bound}) :: fields ->
       let newsym = fresh () in
       begin match bound with 
       | A bt -> 
          let acc_bindings = acc_bindings @ [{name=newsym;bound = if logical then L (Base bt) else A bt}] in
          let acc_fields = acc_fields @ [(Member id, newsym)] in
          let fields = map (fun (mem,binding) -> (mem,Binders.subst VarTypes.subst_var {substitute=lname;swith=newsym} binding)) fields in
          aux acc_bindings acc_fields fields
       | _ -> 
          let acc_bindings = acc_bindings @ [{name=newsym;bound}] in
          let fields = map (fun (mem,binding) -> (mem,Binders.subst VarTypes.subst_var {substitute=lname;swith=newsym} binding)) fields in
          aux acc_bindings acc_fields fields
       end
  in
  let* (bindings, fields) = aux [] [] decl.typ in
  let* size = Memory.size_of_struct_type loc tag in
  return ((fresh (), OpenStruct (tag, fields)),bindings)




let rec unpack_structs loc genv bindings = 
  match bindings with
  | {name;bound = A (ClosedStruct typ)} :: bindings ->
     let* ((newname,bt),newbindings) = unpack_struct false loc genv typ in
     let subst = {substitute=name;swith=newname} in
     let* newbindings' = unpack_structs loc genv (subst_var subst bindings) in
     return (makeA newname bt :: newbindings @ newbindings')
  | {name;bound = L (Base (ClosedStruct typ))} :: bindings ->
     let* ((newname,bt),newbindings) = unpack_struct true loc genv typ in
     let subst = {substitute=name;swith= newname} in
     let* newbindings' = unpack_structs loc genv (subst_var subst bindings) in
     return (makeL newname (Base bt) :: newbindings @ newbindings')
  | b :: bindings ->
     let* newbindings = unpack_structs loc genv bindings in
     return (b :: newbindings)
  | [] -> 
     return []


let open_struct_to_stored_struct loc genv tag fieldmap = 
  let* decl = get_struct_decl loc genv tag in
  let* (addr_fieldmap,addrs,points_tos) =
    fold_leftM (fun (fieldmap,addrs,points_tos) (field,fval) ->
        let* cl = assoc_err loc field decl.mcl.fields "check store field access" in
        let faddr = fresh () in
        let fieldmap = fieldmap@[(field,faddr)] in
        let addrs = addrs@[faddr] in
        let* size = Memory.size_of_ctype loc cl.ct in
        let points_tos = points_tos@[Points {pointer=faddr;pointee=Some fval;typ=cl.ct;size}] in
        return (fieldmap, addrs, points_tos)
      )
      ([],[],[]) fieldmap
  in
  let addr_bindings = map (fun name -> makeL name (Base Loc)) addrs in
  let pointsto_bindings = map makeUR points_tos in
  return ((tag,addr_fieldmap), addr_bindings@pointsto_bindings)





let deal_with_structs loc genv bindings = 
  let* bindings = unpack_structs loc genv bindings in
  let rec aux acc_bindings loc genv bindings = 
    match bindings with
    | {name;bound = L (Base (OpenStruct (tag,fieldmap)))} :: bindings ->
       let* ((tag,fieldmap),newbindings) =
         open_struct_to_stored_struct loc genv tag fieldmap in
       let acc_bindings = acc_bindings @ newbindings @ [makeA name (StoredStruct (tag,fieldmap))] in
       aux acc_bindings loc genv bindings 
    | b :: bindings ->
       let acc_bindings = acc_bindings@[b] in
       aux acc_bindings loc genv bindings
    | [] -> 
       return acc_bindings
  in
  aux [] loc genv bindings










(* use Neel's resource map and use pack_struct to package the aargs
   part of a struct and *as many resources* of the struct definition
   as possible *)

let stored_struct_to_open_struct remove_ownership loc env tag fieldmap =
  let rec aux env acc_vals = function
    | (field, faddr) :: fields ->
       let* (bt,env) = get_Avar loc env faddr in
       let* () = match bt with
         | Loc -> return ()
         | _ -> fail loc (Generic_error !^"stored struct with non-loc field address")
       in
       let* does_point = points_to loc env faddr in
       let* (r,pointee) = match does_point with
         | Some (r,{pointee=Some pointee; _}) -> return (r,pointee)
         | Some (_,{pointee=None; _}) -> 
            fail loc (Generic_error !^"cannot load uninitialised location" )
         | _ -> fail loc (Generic_error !^"missing ownership for loading" )
       in
       let env = if remove_ownership then remove_var env r else env in
       aux env (acc_vals@[(field,pointee)]) fields
    | [] -> return (acc_vals, env)
  in
  let* (fieldmap,env) = aux env [] fieldmap in
  return ((tag,fieldmap),env)



let rec pack_struct loc env typ aargs = 
  let* decl = get_struct_decl loc env.global typ in
  let* env = subtype loc env aargs (List.map snd decl.typ) "packing struct" in
  return ((fresh (), ClosedStruct typ), env)

and pack_open_struct loc env tag fieldmap =
  let arg_syms = List.map snd fieldmap in
  let* (arg_typs,env) = get_ALvars loc env arg_syms in
  let args = List.map from_tuple (List.combine arg_syms arg_typs) in
  let aargs = List.map (fun b -> (b,loc)) args in
  pack_struct loc env tag aargs


and pack_structs_aargs loc env args =
  let aargs_subst subst aargs = 
    let (just_args,locs) = List.split aargs in
    let aargs = Binders.subst_list Sym.subst BT.subst_var subst just_args in
    List.combine aargs locs
  in
  let rec aux acc env = function
    | ({name;bound = OpenStruct (tag,fieldmap)},loc) :: args ->
       let* ((newname,bt),env) = pack_open_struct loc env tag fieldmap in
       aux (acc@[({name=newname;bound = bt},loc)]) env 
         (aargs_subst {substitute=name; swith=newname} args)
    | ({name;bound = StoredStruct (tag,fieldmap)},loc) :: args ->
       let* ((tag,fieldmap),env) = 
         stored_struct_to_open_struct true loc env tag fieldmap in
       let* ((newname,bt),env) = pack_open_struct loc env tag fieldmap in
       aux (acc@[({name=newname;bound = bt},loc)]) env 
         (aargs_subst {substitute=name; swith=newname} args)
    | (b,loc) :: args -> 
       aux (acc@[(b,loc)]) env args
    | [] -> return (acc, env)
  in
  aux [] env args

and pack_structs_largs loc env args =
  let* () = debug_print 2 (action "packing structs") in
  let rec aux acc env = function
    | {name;bound = LS.Base (OpenStruct (tag,fieldmap))} :: args
    | {name;bound = LS.Base (StoredStruct (tag,fieldmap))} :: args -> 
       let* ((newname,bt),env) = pack_open_struct loc env tag fieldmap in
       let subst = {substitute=name;swith= newname} in
       aux (acc@[{name=newname;bound = LS.Base bt}]) env 
         (Binders.subst_list Sym.subst LS.subst_var subst args)
    | b :: args -> 
       aux (acc@[b]) env args
    | [] -> return (acc, env)
  in
  aux [] env args



and subtype loc_ret env (args : aargs) (rtyp : Types.t) ppdescr =

  let open Alrc.Types in
  let rtyp = Alrc.Types.from_type rtyp in
  let* () = debug_print 1 (action ppdescr) in
  let* () = debug_print 2 (blank 3 ^^ item "rtyp" (Alrc.Types.pp rtyp)) in
  let* () = debug_print 2 (blank 3 ^^ item "returned" (pps Sym.pp (BT.pp false) (List.map fst args))) in
  let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 2 PPrint.empty in

  let* (args,env) = pack_structs_aargs loc_ret env args in

  let* (substs,env) = match_As (fun e -> Call_error e) loc_ret env args rtyp.a in
  let rtyp = subst_vars substs {rtyp with a = []} in

  let (unis,substs) = record_lvars_for_unification rtyp.l in
  let rtyp = subst_vars substs {rtyp with l = []} in

  let* (substs,unis,env) = match_Rs (fun e -> Call_error e) loc_ret env unis rtyp.r in
  let rtyp = subst_vars substs {rtyp with r = []} in

  let* resolved = ensure_unis_resolved loc_ret env unis in

  let* (largs,env) =
    fold_leftM (fun (ts,env) (_,subst) -> 
        let* (bt,env) = get_ALvar loc_ret env subst.swith in
        return (ts@[{name=subst.swith; bound = LS.Base bt}], env)
      ) ([],env) resolved
  in

  let* (largs,env) = pack_structs_largs loc_ret env largs in
  let lspecs = map (fun (spec,subst) -> {name=subst.substitute;bound=spec}) resolved in

  let* (substs,env) = match_Ls (fun e -> Call_error e) loc_ret env largs lspecs in
  let rtyp = subst_vars substs rtyp in

  let* () = Solver.check_constraints_hold loc_ret env rtyp.c in
  return env



let call_typ loc_call env (args : aargs) (ftyp : FunctionTypes.t) =
    
  let open Alrc.Types in
  let open Alrc.FunctionTypes in
  let ftyp = Alrc.FunctionTypes.from_function_type ftyp in
  let* () = debug_print 1 (action "function call type") in
  let* () = debug_print 2 (blank 3 ^^ item "ftyp" (Alrc.FunctionTypes.pp ftyp)) in
  let* () = debug_print 2 (blank 3 ^^ item "args" (pps Sym.pp (BT.pp false) (List.map fst args))) in
  let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 2 PPrint.empty in

  let* (args,env) = pack_structs_aargs loc_call env args in

  let* (substs,env) = match_As (fun e -> Call_error e) loc_call env args ftyp.arguments2.a in
  let ftyp = subst_vars substs (updateAargs ftyp []) in

  let (unis,substs) = record_lvars_for_unification ftyp.arguments2.l in
  let ftyp = subst_vars substs (updateLargs ftyp []) in

  let* (substs,unis,env) = match_Rs (fun e -> Call_error e) loc_call env unis ftyp.arguments2.r in
  let ftyp = subst_vars substs (updateRargs ftyp []) in

  let* resolved = ensure_unis_resolved loc_call env unis in

  let* (largs,env) =
    fold_leftM (fun (ts,env) (_,subst) -> 
        let* (bt,env) = get_ALvar loc_call env subst.swith in
        return (ts@[{name=subst.swith; bound = LS.Base bt}], env)
      ) ([],env) resolved
  in
  let* (largs,env) = pack_structs_largs loc_call env largs in
  let lspecs = map (fun (spec,subst) -> {name=subst.substitute;bound=spec}) resolved in

  let* (substs,env) = match_Ls (fun e -> Call_error e) loc_call env largs lspecs in
  let ftyp = subst_vars substs ftyp in
  
  let* () = Solver.check_constraints_hold loc_call env ftyp.arguments2.c in

  let rt = ((to_function_type ftyp).return) in
  return (rt, env)










let infer_ctor loc ctor (aargs : aargs) = 
  match ctor with
  | M_Ctuple -> 
     let name = fresh () in
     let bts = fold_left (fun bts (b,_) -> bts @ [b.bound]) [] aargs in
     let bt = Tuple bts in
     let constrs = 
       mapi (fun i (b,_) -> 
           makeUC (LC (Nth (Num.of_int i, S (name,Base bt) %= S (b.name, Base b.bound)))))
         aargs
     in
     return ([makeA name bt]@constrs)
  | M_Carray -> 
     let* _ = check_Aargs_typ None aargs in
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
        return [makeA name bt; makeUC (LC (S (sym,Base bt) %= S (name,Base bt)))]
     | args ->
        let err = Printf.sprintf "Cspecified applied to %d argument(s)" 
                    (List.length args) in
        fail loc (Generic_error !^err)
     end
  | M_Cnil cbt -> fail loc (Unsupported !^"lists")
  | M_Ccons -> fail loc (Unsupported !^"lists")
  | M_Cfvfromint -> fail loc (Unsupported !^"floats")
  | M_Civfromfloat -> fail loc (Unsupported !^"floats")






(* brittle. revisit later *)
let make_fun_arg_type sym loc ct =
  let* size = Memory.size_of_ctype loc ct in
  let* arg = ctype true true loc sym (make_pointer_ctype ct) in

  let rec return_resources (lvars,resources) arg = 
    match arg with
    | [] -> return (lvars,resources)
    | b :: arg ->
       match b.bound with
       | Points p -> 
          begin match p.pointee with
          | Some s ->
             let name = fresh () in
             let lvars = lvars @ [(s,name)] in
             let resources = resources@[makeUR (Points {p with pointee = Some name})] in
             return_resources (lvars, resources) arg
          | None ->
             fail loc (Unreachable !^"uninitialised memory in argument list")
          end
  in
  let alrc_arg = Alrc.Types.from_type arg in
  let* (lvar_substs,return_resources) = return_resources ([],[]) alrc_arg.r in

  let return_logical = 
    filter_map (fun b -> 
        match List.assoc_opt b.name lvar_substs with
        | None -> None
        | Some name -> Some (makeL name b.bound)
      ) alrc_arg.l
  in

  let return_constraints = 
    filter_map (fun b ->
        match SymSet.elements (LC.vars_in b.bound) with
        | [n] -> 
           begin match List.assoc_opt n lvar_substs with
           | Some name -> Some (makeUC (LC.subst_var {substitute=n;swith= name} b.bound))
           | None -> None
           end
        | _ -> None
      ) alrc_arg.c
  in
  return (arg, return_logical@return_resources@return_constraints)









    



let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()






let infer_ptrval name loc env ptrval = 
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let typ = [makeA name Loc; makeUC (LC (Null (S (name, Base Loc))))] in
      return typ )
    ( fun sym -> 
      return [makeA name (FunctionPointer sym)] )
    ( fun _prov loc ->
      let typ = [makeA name Loc; makeUC (LC (S (name, Base Loc) %= Num loc))] in
      return typ )
    ( fun () -> fail loc (Unreachable !^"unspecified pointer value") )


let rec infer_mem_value loc env mem = 
  let open CF.Ctype in
  CF.Impl_mem.case_mem_value mem
    ( fun _ctyp -> fail loc (Unsupported !^"ctypes as values") )
    ( fun it _sym -> 
      (* todo: do something with sym *)
      let* t = ctype false false loc (fresh ()) (Ctype ([], Basic (Integer it))) in
      return (t, env) )
    ( fun it iv -> 
      let name = fresh () in
      let* v = Memory.integer_value_to_num loc iv in
      let val_constr = LC (S (name, Base Int) %= Num v) in
      let* type_constr = integerType_constraint loc name it in
      let* solved = Solver.constraint_holds_given_constraints loc env [val_constr] type_constr in
      match solved with
      | true -> return ([makeA name Int; makeUC val_constr], env)
      | false -> fail loc (Generic_error !^"Integer value does not satisfy range constraint")
    )
    ( fun ft fv -> floatingType loc )
    ( fun _ctype ptrval ->
      (* maybe revisit and take ctype into account *)
      let* t = infer_ptrval (fresh ()) loc env ptrval in
      return (t, env) )
    ( fun mem_values -> infer_array loc env mem_values )
    ( fun sym fields -> infer_struct loc env (sym,fields) )
    ( fun sym id mv -> infer_union loc env sym id mv )


(* here we're not using the 'pack_struct' logic because we're
   inferring resources and logical variables *)
and infer_struct loc env (tag,fields) =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let* (aargs,env) =
    fold_leftM (fun (aargs,env) (_id,_ct,mv) ->
        let* (t, env) = infer_mem_value loc env mv in
        let (t,env) = make_Aargs_bind_lrc loc env t in
        return (aargs@t, env)
      ) ([],env) fields
  in
  let* ((n,bt),env) = pack_struct loc env (Tag tag) aargs in
  return ([makeA n bt], env)


and infer_union loc env sym id mv =
  fail loc (Unsupported !^"todo: union types")

and infer_array loc env mem_values = 
  fail loc (Unsupported !^"todo: mem_value arrays")

let infer_object_value loc env ov =
  let name = fresh () in
  match ov with
  | M_OVinteger iv ->
     let* i = Memory.integer_value_to_num loc iv in
     let t = makeA name Int in
     let constr = makeUC (LC (S (name, Base Int) %= Num i)) in
     return ([t; constr], env)
  | M_OVpointer p -> 
     let* t = infer_ptrval name loc env p in
     return (t,env)
  | M_OVarray items ->
     let* (args_bts,env) = make_Aargs loc env items in
     let* _ = check_Aargs_typ None args_bts in
     return ([makeA name Array], env)
  | M_OVstruct (tag, fields) -> 
     infer_struct loc env (tag,fields)
  | M_OVunion (sym,id,mv) -> 
     infer_union loc env sym id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")


let infer_value loc env v : (Types.t * Env.t) m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc env ov
  | M_Vunit ->
     return ([makeUA Unit], env)
  | M_Vtrue ->
     let name = fresh () in
     return ([makeA name Bool; makeUC (LC (S (name, Base Bool)))], env)
  | M_Vfalse -> 
     let name = fresh () in
     return ([makeA name Bool; makeUC (LC (Not (S (name, Base Bool))))], env)
  | M_Vlist (cbt, asyms) ->
     let* bt = bt_of_core_base_type loc cbt in
     let* (aargs, env) = make_Aargs loc env asyms in
     let _ = check_Aargs_typ (Some bt) aargs in
     return ([makeUA (List bt)], env)
  | M_Vtuple asyms ->
     let* (aargs,env) = make_Aargs loc env asyms in
     let bts = fold_left (fun bts (b,_) -> bts @ [b.bound]) [] aargs in
     let name = fresh () in
     let bt = Tuple bts in
     let constrs = 
       mapi (fun i (b, _) -> 
           makeUC (LC (Nth (Num.of_int i, S (name,Base bt) %= S (b.name,Base b.bound)))))
         aargs
     in
     return ((makeA name bt) :: constrs, env)







let infer_pat loc (M_Pattern (annots, pat_)) = 
  fail loc (Unsupported !^"todo: implement infer_pat")


let binop_typ op = 
  let open CF.Core in
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
  let* unreachable = Solver.is_unreachable loc env in
  if unreachable then return () else
    match bad with
    | Undefined (loc,ub) -> fail loc (TypeErrors.Undefined ub)
    | Unspecified loc -> fail loc TypeErrors.Unspecified
    | StaticError (loc, (err,pe)) -> fail loc (TypeErrors.StaticError (err,pe))
  









let infer_pexpr loc env (pe : 'bty mu_pexpr) = 

  let* () = debug_print 1 (action "inferring pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget pe)) in

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in

  let* (typ,env) = match pe_ with
    | M_PEsym sym ->
       let name = fresh () in
       let* (bt,env) = get_Avar loc env sym in
       let typ = [makeA name bt; makeUC (LC (S (sym, Base bt) %= S (name, Base bt)))] in
       return (Normal typ, env)
    | M_PEimpl i ->
       let* t = get_impl_constant loc env.global i in
       return (Normal [makeUA t], env)
    | M_PEval v ->
       let* (t, env) = infer_value loc env v in
       return (Normal t, env)
    | M_PEconstrained _ ->
       fail loc (Unsupported !^"todo: PEconstrained")
    | M_PEundef (loc,undef) ->
       return (Bad (Undefined (loc, undef)), env)
    | M_PEerror (err,asym) ->
       let (sym, loc) = aunpack loc asym in
       return (Bad (StaticError (loc, (err,sym))), env)
    | M_PEctor (ctor, args) ->
       let* (aargs, env) = make_Aargs loc env args in
       let* rt = infer_ctor loc ctor aargs in
       return (Normal rt, env)
    | M_PEarray_shift _ ->
       fail loc (Unsupported !^"todo: PEarray_shift")
    | M_PEmember_shift (asym, tag, id) ->
       let member = Member (Id.s id) in
       let tag = Tag tag in
       let (sym, aloc) = aunpack loc asym in
       let* (bt,env) = get_Avar loc env sym in
       let* () = match bt with
         | Loc -> return ()
         | _ -> fail aloc (Generic_error !^"member shift applied to non-pointer")
       in
       let* does_point = points_to aloc env sym in
       let* pointee = match does_point with
         | Some (_,{pointee=Some pointee; _}) -> return pointee
         | Some (_,{pointee=None; _}) -> 
            fail loc (Generic_error !^"member-shift at uninitialised location" )
         | _ -> fail loc (Generic_error !^"missing ownership of member-shift location" )
       in
       let* (bt,env) = get_Lvar loc env pointee in
       let* fieldmap = match bt with
         (* TODO: proper equality *)
         | Base (StoredStruct (tag',fieldmap)) when tag = tag' -> return fieldmap
         | Base (StoredStruct (tag',fieldmap)) -> 
            fail loc (Generic_error !^"struct access incompatible with this struct type")
         | _ -> 
            fail loc (Generic_error !^"struct access to non-struct")
       in
       let* faddr = assoc_err loc member fieldmap "check store field access" in
       (* let* (fbt,env) = get_Lvar loc env faddr in *)
       let ret = fresh () in
       let constr = LC (S (ret, Base Loc) %= S (faddr, Base Loc)) in
       return (Normal [makeA ret Loc; makeUC constr], env)
    | M_PEnot asym ->
       let (sym,loc) = aunpack loc asym in
       let* (bt,env) = get_Avar loc env sym in
       let* () = check_base_type loc (Some sym) Bool bt in
       let ret = fresh () in 
       let constr = (LC (S (ret,Base Bool) %= Not (S (sym,Base Bool)))) in
       let rt = [makeA sym Bool; makeUC constr] in
       return (Normal rt, env)
    | M_PEop (op,asym1,asym2) ->
       let (sym1,loc1) = aunpack loc asym1 in
       let (sym2,loc2) = aunpack loc asym2 in
       let* (bt1,env) = get_Avar loc1 env sym1 in
       let* (bt2,env) = get_Avar loc2 env sym2 in
       let (((ebt1,ebt2),rbt),c) = binop_typ op in
       let* () = check_base_type loc1 (Some sym1) bt1 ebt1 in
       let ret = fresh () in
       let constr = LC ((c (S (sym1,Base bt1)) (S (sym1,Base bt2))) %= S (ret,Base rbt)) in
       return (Normal [makeA ret rbt; makeUC constr], env)
    | M_PEstruct _ ->
       fail loc (Unsupported !^"todo: PEstruct")
    | M_PEunion _ ->
       fail loc (Unsupported !^"todo: PEunion")
    | M_PEmemberof _ ->
       fail loc (Unsupported !^"todo: M_PEmemberof")
    | M_PEcall (fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            get_impl_fun_decl loc env.global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ,_ret_name) = get_fun_decl loc env.global sym in
            return decl_typ
       in
       let* (args,env) = make_Aargs loc env asyms in
       let* (rt, env) = call_typ loc env args decl_typ in
       return (Normal rt, env)
    | M_PEcase _ -> fail loc (Unreachable !^"PEcase in inferring position")
    | M_PElet _ -> fail loc (Unreachable !^"PElet in inferring position")
    | M_PEif _ -> fail loc (Unreachable !^"PElet in inferring position")
  in
  
  let* () = debug_print 3 (blank 3 ^^ item "inferred" (UU.pp_ut typ)) in
  let* () = debug_print 1 PPrint.empty in
  return (typ,env)


let rec check_pexpr loc env (e : 'bty mu_pexpr) typ = 

  let* () = debug_print 1 (action "checking pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in

  (* think about this *)
  let* unreachable = Solver.is_unreachable loc env in
  if unreachable then warn !^"stopping to type check: unreachable" else

  match e_ with
  | M_PEif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     let* (t1,env) = get_Avar loc env sym1 in
     let* () = check_base_type loc1 (Some sym1) t1 Bool in
     let* () = check_pexpr loc (add_var env (makeUC (LC (S (sym1,Base Bool))))) e2 typ in
     let* () = check_pexpr loc (add_var env (makeUC (LC (Not (S (sym1,Base Bool)))))) e3 typ in
     return ()
  | M_PEcase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     let* (bt,env) = get_Avar eloc env esym in
     let* _ = 
       mapM (fun (pat,pe) ->
           (* check pattern type against bt *)
           let* (bindings, bt', ploc)= infer_pat loc pat in
           let* () = check_base_type ploc None bt' bt in
           (* check body type against spec *)
           let env' = add_Avars env bindings in
           check_pexpr loc env' pe typ
         ) pats_es
     in
     return ()
  | M_PElet (p, e1, e2) ->
     begin match p with 
     | M_Symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        let* (rt, env) = infer_pexpr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = deal_with_structs loc env.global rt in
           let* rt = rename newname rt in
           check_pexpr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        let* (rt, env) = infer_pexpr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = deal_with_structs loc env.global rt in
           let* rt = rename newname rt in
           check_pexpr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_Pat (M_Pattern (annots, M_CaseCtor _)) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported !^"todo: ctor pattern")
     end
  | _ ->
     let* (rt, env) = infer_pexpr loc env e in
     begin match rt with
     | Normal rt -> 
        let (rt,env) = make_Aargs_bind_lrc loc env rt in
        let* env = subtype loc env rt typ "function return type" in
        return ()
     | Bad bad -> ensure_bad_unreachable loc env bad
     end



let rec infer_expr loc env (e : ('a,'bty) mu_expr) = 

  let* () = debug_print 1 (action "inferring expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in

  let* (typ,env) = match e_ with
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
       | M_PtrValidForDeref (_a_ct, asym) ->
          let (sym, loc) = aunpack loc asym in
          let ret_name = fresh () in
          let* (bt, env)= get_Avar loc env sym in
          let* () = check_base_type loc (Some sym) bt Loc in
          (* check more things? *)
          let* points = points_to loc env sym in
          let constr = match points with
            | Some _ -> LC (S (ret_name,Base Bool)) 
            | None -> LC (Not (S (ret_name,Base Bool))) 
          in
          let ret = [makeA ret_name Bool; makeUC constr] in
          return (Normal ret, env)
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
          let* (a_bt,env) = get_Avar loc env sym in
          let* () = check_base_type loc (Some sym) Int a_bt in
          let name = fresh () in
          let* size = Memory.size_of_ctype loc ct in
          let r = (Points {pointer = name; pointee = None; typ = ct; size}) in
          let rt = [makeA name Loc; makeUR r] in
          return (Normal rt, env)
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (_is_dynamic, asym) -> 
          let (sym,loc) = aunpack loc asym in
          (* have remove resources of location instead? *)
          let resources = resources_associated_with env sym in
          let env = remove_vars env resources in
          return (Normal [makeUA Unit], env)


       | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* size = Memory.size_of_ctype loc ct in
          let (psym,ploc) = aunpack loc asym1 in
          let (vsym,vloc) = aunpack loc asym2 in
          let* (pbt,env) = get_Avar ploc env psym in
          let* (vbt,env) = get_Avar vloc env vsym in
          (* for consistency check value against Core annotation *)
          let* _ =
            let* t = ctype false false loc (fresh ()) ct in
            subtype loc env [({name=vsym;bound=vbt},vloc)] t 
              "checking store value against ctype annotaion"
          in
          let* () = match pbt with
            | Loc -> return ()
            | _ -> fail ploc (Generic_error !^"store argument has to be a pointer")
          in
          let* does_point = points_to ploc env psym in
          let* (r,p) = match does_point with
            | None -> fail loc (Generic_error !^"missing ownership of store location" )
            | Some (r,p) -> return (r,p)
          in
          let* _ = 
            let* t = ctype false false loc (fresh ()) p.typ in
            subtype loc env [({name=vsym;bound=vbt},vloc)] t
              "checking store value against expected type"
          in
          
          let newsym = fresh () in
          let* (vbt,env) = match vbt with
            | OpenStruct (tag,fieldmap) -> 
               let* ((tag,fieldmap), bindings) = open_struct_to_stored_struct loc env.global tag fieldmap in
               let env = add_vars env bindings in
               return (StoredStruct (tag,fieldmap), env)
            | vbt -> 
               return (vbt, env)
          in
          let env = add_var env (makeL newsym (Base vbt)) in
          let env = add_var env (makeUC (LC (S (newsym,Base vbt) %= S (vsym,Base vbt)))) in

          let* env = 
            match p.pointee with 
            | None -> 
               let env = remove_var env r in
               return env
            | Some pointee ->
               let* (bt,env) = get_Lvar loc env pointee in
               match bt with
               | Base (StoredStruct (_,fieldmap)) ->
                  let _addrs = List.map snd fieldmap in
                  (* TODO: recursively cleanup: remove pointed resources *)
                  let env = remove_var env r in
                  return env
               | _ -> 
                  let env = remove_var env r in
                  return env
          in
          let env = add_var env (makeUR (Points {p with pointee = Some newsym})) in
          return (Normal [makeUA Unit],env)

       | M_Load (a_ct, asym, _mo) -> 
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* size = Memory.size_of_ctype loc ct in
          let (psym,ploc) = aunpack loc asym in
          let* (pbt,env) = get_Avar ploc env psym in
          (* check pointer *)
          let* () = match pbt with
            | Loc -> return ()
            | _ -> let err = "Load argument has to be a pointer or a struct field" in
                   fail ploc (Generic_error !^err)
          in
          let* does_point = points_to ploc env psym in
          let* (pointee,ct') = match does_point with
            | Some (r,{pointee = Some pointee;typ;_}) -> return (pointee,typ)
            | Some (r,_) -> fail loc (Generic_error !^"load location uninitialised" )
            | None -> fail loc (Generic_error !^"missing ownership of load location" )
          in 

          let ret = fresh () in
          let* (bt,env) = get_ALvar ploc env pointee in
          let* (bt,constr) = match bt with
            | StoredStruct (tag,fieldmap) ->
               let* ((tag,fieldmap),env) = 
                 stored_struct_to_open_struct false loc env tag fieldmap in
               (* TODO: fix constraint *)
               let constr = LC (S (ret, Base bt) %= (S (pointee,Base bt))) in
               return (bt,constr)
            | bt ->
               let constr = LC (S (ret, Base bt) %= (S (pointee,Base bt))) in
               return (bt,constr)
          in
          let* _ = 
            let* t = ctype false false loc (fresh ()) ct' in
            subtype loc env [({name=pointee;bound=bt},ploc)] t 
              "checking load value against expected type"
          in
          return (Normal [makeA ret bt; makeUC constr],env)

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
    | M_Eccall (_, _ctype, fun_asym, arg_asyms) ->
       let* (args,env) = make_Aargs loc env arg_asyms in
       let (sym1,loc1) = aunpack loc fun_asym in
       let* (bt,env) = get_Avar loc1 env sym1 in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail loc1 (Generic_error !^"not a function pointer")
       in
       let* (_loc,decl_typ,_ret_name) = get_fun_decl loc env.global fun_sym in
       let* (rt, env) = call_typ loc env args decl_typ in
       return (Normal rt, env)
    | M_Eproc (_, fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            get_impl_fun_decl loc env.global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ,_ret_name) = get_fun_decl loc env.global sym in
            return decl_typ
       in
       let* (args,env) = make_Aargs loc env asyms in
       let* (rt, env) = call_typ loc env args decl_typ in
       return (Normal rt, env)
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
  in

  let* () = debug_print 3 (blank 3 ^^ item "inferred" (UU.pp_ut typ)) in
  let* () = debug_print 1 PPrint.empty in
  return (typ,env)


let rec check_expr loc env (e : ('a,'bty) mu_expr) typ = 

  let* () = debug_print 1 (action "checking expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in


  (* think about this *)
  let* unreachable = Solver.is_unreachable loc env in
  if unreachable then warn !^"stopping to type check: unreachable" else

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     let* (t1,env) = get_Avar loc env sym1 in
     let* () = check_base_type loc1 (Some sym1) t1 Bool in
     let then_constr = makeUC (LC (S (sym1,Base Bool))) in
     let else_constr = makeUC (LC (Not (S (sym1,Base Bool)))) in
     let* () = check_expr loc (add_var env then_constr) e2 typ in
     let* () = check_expr loc (add_var env else_constr) e3 typ in
     return ()
  | M_Ecase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     let* (bt,env) = get_Avar eloc env esym in
     let* _ = 
       mapM (fun (pat,pe) ->
           (* check pattern type against bt *)
           let* (bindings, bt', ploc) = infer_pat loc pat in
           let* () = check_base_type ploc None bt' bt in
           (* check body type against spec *)
           let env' = add_Avars env bindings in
           check_expr loc env' pe typ
         ) pats_es
     in
     return ()
  | M_Epure pe -> 
     check_pexpr loc env pe typ
  | M_Elet (p, e1, e2) ->
     begin match p with 
     | M_Symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        let* (rt, env) = infer_pexpr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = deal_with_structs loc env.global rt in
           let* rt = rename newname rt in
           check_expr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        let* (rt, env) = infer_pexpr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = deal_with_structs loc env.global rt in
           let* rt = rename newname rt in
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
        let* (rt, env) = infer_expr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = deal_with_structs loc env.global rt in
           let* rt = rename newname rt in
           check_expr loc (add_vars env rt) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_Pattern (annots, M_CaseCtor _) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported !^"todo: ctor pattern")
     end
  | M_Esave (_ret, args, body) ->
     let* env = 
       fold_leftM (fun env (sym, (_, asym)) ->
           let (vsym,loc) = aunpack loc asym in
           let* (bt,env) = get_Avar loc env vsym in
           return (add_var env (makeA sym bt))
         ) env args
     in
     check_expr loc env body typ
  | _ ->
     let* (rt, env) = infer_expr loc env e in
     begin match rt with
     | Normal rt ->
        let (rt,env) = make_Aargs_bind_lrc loc env rt in
        let* env = subtype loc env rt typ "function return type" in
        return ()
     | Bad bad -> ensure_bad_unreachable loc env bad
     end
     


let check_proc loc fsym genv body ftyp = 
  let* () = debug_print 1 (h1 ("Checking procedure " ^ (plain (Sym.pp fsym)))) in
  let env = with_fresh_local genv in
  let* args = deal_with_structs loc genv ftyp.arguments in
  let env = add_vars env args in
  let* _env = check_expr loc env body ftyp.return in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in
  return ()

let check_fun loc fsym genv body ftyp = 
  let* () = debug_print 1 (h1 ("Checking function " ^ (plain (Sym.pp fsym)))) in
  let env = with_fresh_local genv in
  let* args = deal_with_structs loc genv ftyp.arguments in
  let env = add_vars env args in
  let* _env = check_pexpr loc env body ftyp.return in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in
  return ()


let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) =

  let check_consistent loc ftyp args ret = 

    let forget = 
      filter_map (function {name; bound = A t} -> Some {name;bound = t} | _ -> None) 
    in

    let binding_of_core_base_type loc (sym,cbt) = 
      let* bt = bt_of_core_base_type loc cbt in
      return {name=sym;bound= bt}
    in

    let* args = mapM (binding_of_core_base_type loc) args in
    let* ret = binding_of_core_base_type loc ret in
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
     let* decl = get_fun_decl Loc.unknown genv fsym in
     let (loc,ftyp,ret_name) = decl in
     let* () = check_consistent loc ftyp args (ret_name,ret) in
     check_fun loc fsym genv body ftyp
  | M_Proc (loc, ret, args, body) ->
     let* decl = get_fun_decl loc genv fsym in
     let (loc,ftyp,ret_name) = decl in
     let* () = check_consistent loc ftyp args (ret_name,ret) in
     check_proc loc fsym genv body ftyp
  | M_ProcDecl _
  | M_BuiltinDecl _ -> 
     return ()


let check_functions (type a bty) env (fns : (bty,a) mu_fun_map) =
  pmap_iterM (check_function env) fns

                             
(* let process_attributes *)


let record_fun sym (loc,attrs,ret_ctype,args,is_variadic,_has_proto) genv =
  if is_variadic then fail loc (Variadic_function sym) else
    let* (arguments, returns, names) = 
      fold_leftM (fun (args,returns,names) (msym, ct) ->
          let name = sym_or_fresh msym in
          let* (arg,ret) = make_fun_arg_type name loc ct in
          return (args@arg, returns@ret, name::names)
        ) ([],[],[]) args
    in
    let ret_name = Sym.fresh () in
    let* ret = ctype true true loc ret_name ret_ctype in
    let ftyp = {arguments; return = ret@returns} in
    return (add_fun_decl genv sym (loc, ftyp, ret_name))

let record_funinfo genv funinfo = 
  pmap_foldM record_fun funinfo genv


(* check the types? *)
let record_impl impl impl_decl genv = 
  match impl_decl with
  | M_Def (bt, _p) -> 
     let* bt = bt_of_core_base_type Loc.unknown bt in
     return (add_impl_constant genv impl bt)
  | M_IFun (bt, args, _body) ->
     let* args_ts = 
       mapM (fun (sym,a_bt) -> 
           let* a_bt = bt_of_core_base_type Loc.unknown a_bt in
           return (makeA sym a_bt)) args
     in
     let* bt = bt_of_core_base_type Loc.unknown bt in
     let ftyp = {arguments = args_ts; return = [makeUA bt]} in
     return (add_impl_fun_decl genv impl ftyp)
                        


let record_impls genv impls = pmap_foldM record_impl impls genv



let record_tagDef file sym def genv =

  (* like ctype_aux *)
  let rec aux owned packed loc (Member id : member) (CF.Ctype.Ctype (annots, ct_)) =
    let loc = update_loc loc annots in
    match ct_ with
    | Void -> 
       return [(Member id, makeUA Unit)]
    | Basic (Integer it) -> 
       let name = fresh () in
       let newid = id ^ "_range_constraint" in
       let* lc = integerType_constraint loc name it in
       return [(Member id, makeA name Int); (Member newid, makeUC lc)]
    | Array (ct, _maybe_integer) -> 
       return [(Member id, makeUA BT.Array)]
    | Pointer (_qualifiers, ct) -> 
       return [(Member id, makeUA Loc)]
    (* fix *)
    | Atomic ct -> 
       aux owned packed loc (Member id) ct
    | Struct sym -> 
       return [(Member id, makeUA (BT.ClosedStruct (Tag sym)))]
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in


  match def with
  | CF.Ctype.UnionDef _ -> 
     fail Loc.unknown (Unsupported !^"todo: union types")
  | CF.Ctype.StructDef (fields, _) ->
     let* typ =
       fold_leftM (fun typ (id, (_attributes, _qualifier, ct)) ->
           let* newfields = aux false true Loc.unknown (Member (Id.s id)) ct in
           return (typ@newfields)
         ) [] fields
     in
     let* mcl = Memory.struct_ct_and_layout file Loc.unknown genv (Tag sym) fields in
     let decl = {typ;mcl} in
     let genv = add_struct_decl genv (Tag sym) decl in
     return genv


let record_tagDefs file genv tagDefs = 
  pmap_foldM (record_tagDef file) tagDefs genv







let pp_fun_map_decl funinfo = 
  let pp = CF.Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (plain pp)


let print_initial_environment genv = 
  let* () = debug_print 1 (h1 "initial environment") in
  let* () = debug_print 1 (Global.pp genv) in
  return ()


let check mu_file =
  pp_fun_map_decl mu_file.mu_funinfo;
  let genv = Global.empty in
  let* genv = record_tagDefs mu_file genv mu_file.mu_tagDefs in
  let* genv = record_funinfo genv mu_file.mu_funinfo in
  let* () = print_initial_environment genv in
  check_functions genv mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception (loc,err) -> 
     let pped = TypeErrors.pp loc err in
     error pped







(* todo: 
   - correctly unpack logical structs,
   - make call_typ accept non-A arguments
   - struct handling in constraint solver
   - more struct rules
   - revisit rules implemented using store rule
 *)
