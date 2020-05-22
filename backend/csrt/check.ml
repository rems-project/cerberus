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


let pp_budget = Some 7


let assoc_err loc list entry err =
  match List.assoc_opt list entry with
  | Some result -> return result
  | None -> fail loc (Generic_error (!^"list assoc failed:" ^^^ !^err))



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
  tryM (get_Lvar loc env var >>= fun (Base bt, env) -> return (bt, env))
    (get_Avar loc env var)


let get_Avars loc env vars = 
  fold_leftM (fun (acc,env) sym ->
      get_Avar loc env sym >>= fun (t,env) ->
      return (acc@[t], env)
    ) ([],env) vars

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
  let s = Impl_mem.sizeof_ival ct in
  integer_value_to_num loc s

let size_of_struct_type loc sym =
  size_of_ctype loc (Ctype.Ctype ([], Ctype.Struct sym))






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
      Solver.constraint_holds loc env c >>= fun holds ->
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
    | OTy_struct sym -> return (Struct (S_Id sym))
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

let integerType_constraint loc about it =
  integer_value_min loc it >>= fun min ->
  integer_value_max loc it >>= fun max ->
  return (LC ((Num min %<= about) %& (about %<= Num max)))

let integerType loc name it =
  integerType_constraint loc (S (name, LS.Base Int)) it >>= fun constr ->
  return ((name,Int), [], [], [makeUC constr])

let floatingType loc =
  fail loc (Unsupported !^"floats")

let rec ctype_aux owned packed loc name (Ctype.Ctype (annots, ct_)) =
  let loc = update_loc loc annots in
  let open Ctype in
  match ct_ with
  | Void -> return ((name,Unit), [], [], [])
  | Basic (Integer it) -> integerType loc name it
  | Array (ct, _maybe_integer) -> return ((name,BT.Array),[],[],[])
  | Pointer (_qualifiers, ct) ->
     if owned then
       ctype_aux owned packed loc (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
       size_of_ctype loc ct >>= fun size ->
       let r = makeUR (Points {pointer = name; pointee = Some pointee_name; 
                               offset = zero; typ = ct; size}) :: r in
       let l = makeL pointee_name (Base bt) :: l in
       return ((name,Loc),l,r,c)
     else
       return ((name,Loc),[],[],[])
  (* fix *)
  | Atomic ct -> ctype_aux owned packed loc name ct
  | Struct sym -> return ((name, BT.Struct (S_Id sym)),[],[],[])
  | Basic (Floating _) -> floatingType loc 
  | Union sym -> fail loc (Unsupported !^"todo: union types")
  | Function _ -> fail loc (Unsupported !^"function pointers")



let ctype owned packed loc (name : Sym.t) (ct : Ctype.ctype) =
  ctype_aux owned packed loc name ct >>= fun ((name,bt), l,r,c) ->
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


type aargs = (((Sym.t,BT.t) Binders.t) * Loc.t) list

let rec make_Aargs loc env asyms = 
  match asyms with
  | [] -> return ([], env)
  | asym :: asyms ->
     let (name, loc) = aunpack loc asym in
     get_Avar loc env name >>= fun (t,env) ->
     make_Aargs loc env asyms >>= fun (rest, env) ->
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
  get_ALvar loc env owner >>= fun (bt,_env) ->
  vars_equal_to loc env owner (Base bt) >>= fun equal_to_owner ->
  debug_print 3 (blank 3 ^^ !^"equal to" ^^^ Sym.pp owner ^^ colon ^^^
                   pp_list None Sym.pp equal_to_owner) >>= fun () ->
  let owneds = concat_map (fun o -> map (fun r -> (o,r)) 
                                      (resources_associated_with env o))
                 (owner :: equal_to_owner) in
  return owneds
  






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
       (typ (Sym.pp sym) (LS.pp true spec)) ^^^ !^"resolved as" ^^^ (Sym.pp res)
    | None -> (typ (Sym.pp sym) (LS.pp true spec)) ^^^ !^"unresolved"
  in
  pp_list None pp_entry (SymMap.bindings unis)





  


(* begin: shared logic for function calls, function returns, struct packing *)

let match_As errf loc env (args : aargs) (specs : ((Sym.t,BT.t) Binders.t) list) =
  debug_print 2 (action "matching computational variables") >>= fun () ->

  let rec aux env acc_substs args specs =
    debug_print 2 (blank 3 ^^ item "args" (pps Sym.pp (BT.pp false) (List.map fst args))) >>= fun () ->
    debug_print 2 (blank 3 ^^ item "spec" (pps Sym.pp (BT.pp false) specs)) >>= fun () ->
    match args, specs with
    | [], [] -> 
       debug_print 2 (blank 3 ^^ !^"done.") >>= fun () ->
       return (acc_substs,env)
    | (arg,loc) :: _, [] -> 
       fail loc (errf (Surplus_A (arg.name, arg.bound)))
    | [], spec :: _ -> 
       fail loc (errf (Missing_A (spec.name, spec.bound)))
    | ((arg,arg_loc) :: args), (spec :: specs) ->
       if BT.type_equal arg.bound spec.bound then
         aux env (acc_substs@[(spec.name,arg.name)]) args specs
       else
         let msm = Mismatch {mname = Some arg.name; 
                             has = A arg.bound; expected = A spec.bound} in
         fail loc (errf msm)
  in
  aux env [] args specs

let record_lvars_for_unification (specs : ((Sym.t,LS.t) Binders.t) list) =
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


let match_Ls errf loc env (args : ((Sym.t,LS.t) Binders.t) list) (specs : ((Sym.t,LS.t) Binders.t) list) =
  debug_print 2 (action "matching logical variables") >>= fun () ->
  debug_print 2 (blank 3 ^^ item "args" (pps Sym.pp (LS.pp false) args)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "spec" (pps Sym.pp (LS.pp false) specs)) >>= fun () ->
  let rec aux env acc_substs args specs = 
    match args, specs with
    | [], [] -> 
       debug_print 2 (blank 3 ^^ !^"done.") >>= fun () ->
       return (acc_substs,env)
    | (arg :: args), (spec :: specs) ->
       if LS.type_equal arg.bound spec.bound then
         aux env (acc_substs@[(spec.name,arg.name)]) args specs
       else
         let msm = Mismatch {mname = Some arg.name; 
                             has = L arg.bound; expected = L spec.bound} in
         fail loc (errf msm)
    | _ -> fail loc (Unreachable !^"surplus/missing L")
  in
  aux env [] args specs 


let ensure_unis_resolved loc env unis =
  find_resolved env unis >>= fun (unresolved,resolved) ->
  if SymMap.is_empty unresolved then return resolved else
    let (usym, spec) = SymMap.find_first (fun _ -> true) unresolved in
    fail loc (Call_error (Unconstrained_l (usym,spec)))



let match_Rs errf loc env (unis : ((LS.t, Sym.t) Uni.t) SymMap.t) specs =
  debug_print 2 (action "matching resources") >>= fun () ->
  let rec aux env acc_substs unis specs = 
    debug_print 2 (blank 3 ^^ item "spec" (pps Sym.pp (RE.pp false) specs)) >>= fun () ->
    debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
    match specs with
    | [] -> 
       debug_print 2 (blank 3 ^^ !^"done.") >>= fun () ->
       return (acc_substs,unis,env)
    | spec :: specs -> 
       let owner = RE.associated spec.bound in
       (* TODO: unsafe env *)
       resources_associated_with_var_or_equals loc env owner >>= fun owneds ->
       let rec try_resources = function
         | [] -> 
            fail loc (errf (Missing_R (spec.name, spec.bound)))
         | (o,r) :: owned_resources ->
            get_Rvar loc env r >>= fun (resource',env) ->
            let resource' = RE.subst_var o owner resource' in
            debug_print 3 (action ("trying resource" ^ plain (RE.pp false resource'))) >>= fun () ->
            match RE.unify spec.bound resource' unis with
            | None -> try_resources owned_resources
            | Some unis ->
               find_resolved env unis >>= fun (_,new_substs) ->
               let new_substs = (spec.name,r) :: (map snd new_substs) in
               let specs = 
                 fold_left (fun r (s, s') -> 
                     Binders.subst_list Sym.subst Resources.subst_var s s' r) 
                   specs new_substs
               in
               aux env (acc_substs@new_substs) unis specs
       in
       try_resources owneds
  in
  aux env [] unis specs

(* end: shared logic for function calls, function returns, struct packing *)



(* TODO: remove all the Ctype auxiliary things *)
let rec unpack_struct loc genv (S_Id struct_typ) = 
  debug_print 2 (blank 3 ^^ (!^"unpacking struct")) >>= fun () ->
  Global.get_struct_decl loc genv struct_typ >>= fun decl ->
  let rec aux acc_bindings acc_fields (fields : ((string,VarTypes.t) Binders.t) list) =
    match fields with
    | [] -> 
       return (acc_bindings, acc_fields)
    | {name; bound = A (Struct sym)} :: fields ->
       unpack_struct loc genv sym >>= fun ((newsym,bt),newbindings) ->
       assoc_err loc name decl.ctypes "struct field ctype not found" >>= fun ctype ->
       assoc_err loc name decl.offsets "struct field ctype not found" >>= fun offset ->
       let acc_fields = acc_fields @ [(name, (offset, ctype, Some newsym))] in
       let acc_bindings = acc_bindings @ newbindings @ [{name=newsym;bound = A bt}] in
       let fields = Binders.subst_list Id.subst VarTypes.concretise_field name newsym fields in
       aux acc_bindings acc_fields fields
    | {name; bound = L (Base (Struct sym))} :: fields ->
       unpack_struct loc genv sym >>= fun ((newsym,bt),newbindings) ->
       let acc_bindings = acc_bindings @ newbindings @ [{name=newsym;bound = L (Base bt)}] in
       let fields = Binders.subst_list Id.subst VarTypes.concretise_field name newsym fields in
       aux acc_bindings acc_fields fields
    | {name;bound} :: fields ->
       let newsym = fresh () in
       begin match bound with 
       | A bt -> 
          assoc_err loc name decl.ctypes "struct field ctype not found" >>= fun ctype ->
          assoc_err loc name decl.offsets "struct field ctype not found" >>= fun offset ->
          let acc_bindings = acc_bindings @ [{name=newsym;bound = A bt}] in
          let acc_fields = acc_fields @ [(name, (offset, ctype, Some newsym))] in
          let fields = Binders.subst_list Id.subst VarTypes.concretise_field name newsym fields in
          aux acc_bindings acc_fields fields
       | _ -> 
          let acc_bindings = acc_bindings @ [{name=newsym;bound}] in
          let fields = Binders.subst_list Id.subst VarTypes.concretise_field name newsym fields in
          aux acc_bindings acc_fields fields
       end
  in
  aux [] [] decl.typ >>= fun (bindings, fields) ->
  size_of_struct_type loc struct_typ >>= fun size ->
  let s = {typ = S_Id struct_typ; size; fields} in
  return ((fresh (), OpenStruct s),bindings)


(* let rec unpack_structs loc genv bindings = 
 *   let rec aux lvars acc_bindings = function
 *     | [] -> return acc_bindings
 *     | b :: bindings ->
 *        match b with
 *        | {name; bound = L (Base (Struct typ))} ->
 *           aux (SymMap.add name typ lvars) acc_bindings bindings
 *        | ({name; bound = R (Points {pointee = Some v; _})} as b) ->
 *           begin match SymMap.find_opt v lvars with
 *           | Some typ -> 
 *              unpack_struct loc genv typ >>= fun (openstruct, newbindings) ->
 *              (\* TODO: generate constraints using substs and v *\)
 *              aux 
 *                lvars 
 *                (acc_bindings @ [makeR name (OpenStruct openstruct)])
 *                bindings
 *           | None ->
 *              aux lvars (acc_bindings @ [b]) bindings
 *           end
 *        | b ->
 *           aux lvars (acc_bindings @ [b]) bindings
 *   in
 *   aux SymMap.empty [] bindings *)

let rec unpack_structs loc genv bindings = 
  match bindings with
  | {name;bound = A (Struct typ)} :: bindings ->
     unpack_struct loc genv typ >>= fun ((newname,bt),newbindings) ->
     unpack_structs loc genv (subst_var name newname bindings) >>= fun newbindings' ->
     return (makeA newname bt :: newbindings @ newbindings')
  | {name;bound = L (Base (Struct typ))} :: bindings ->
     unpack_struct loc genv typ >>= fun ((newname,bt),newbindings) ->
     unpack_structs loc genv (subst_var name newname bindings) >>= fun newbindings' ->
     return (makeL newname (Base bt) :: newbindings @ newbindings')
  | b :: bindings ->
     unpack_structs loc genv bindings >>= fun newbindings ->
     return (b :: newbindings)
  | [] -> 
     return []





(* use Neel's resource map and use pack_struct to package the aargs
   part of a struct and *as many resources* of the struct definition
   as possible *)
let rec pack_struct loc env (S_Id struct_type) aargs = 
  get_struct_decl loc env.global struct_type >>= fun decl ->
  let rec aux = function
    | [] -> []
    | {name;bound} :: spec ->
       let newsym = fresh () in
       let spec = Binders.subst_list Id.subst VarTypes.concretise_field name newsym spec in
       {name=newsym;bound} :: aux spec
  in
  subtype loc env aargs (aux decl.typ) "packing struct" >>= fun env ->
  return ((fresh (), Struct (S_Id struct_type)), env)

and pack_open_struct loc env open_struct =
  mapM (fun (fid,(_,_,marg)) ->
      match marg with
      | None -> fail loc (Generic_error (!^"Struct cannot be packed:" ^^^ 
                            !^fid ^^^ !^"uninitialised"))
      | Some arg -> return arg
    ) open_struct.fields >>= fun arg_syms ->
  get_Avars loc env arg_syms >>= fun (arg_typs,env) ->
  let args = List.map from_tuple (List.combine arg_syms arg_typs) in
  let aargs = List.map (fun b -> (b,loc)) args in
  pack_struct loc env open_struct.typ aargs


and pack_structs_aargs loc env args =
  let aargs_subst sym with_sym aargs = 
    let (just_args,locs) = List.split aargs in
    let aargs = Binders.subst_list Sym.subst BT.subst_var sym with_sym just_args in
    List.combine aargs locs
  in
  let rec aux acc env = function
    | ({name;bound = OpenStruct s},loc) :: args -> 
       pack_open_struct loc env s >>= fun ((newname,bt),env) ->
       aux (acc@[({name=newname;bound = bt},loc)]) env 
         (aargs_subst name newname args)
    | (b,loc) :: args -> 
       aux (acc@[(b,loc)]) env args
    | [] -> return (acc, env)
  in
  aux [] env args

and pack_structs_largs loc env args =
  debug_print 2 (action "packing structs") >>= fun () ->
  let rec aux acc env = function
    | {name;bound = LS.Base (OpenStruct s)} :: args -> 
       pack_open_struct loc env s >>= fun ((newname,bt),env) ->
       aux (acc@[{name=newname;bound = LS.Base bt}]) env 
         (Binders.subst_list Sym.subst LS.subst_var name newname args)
    | b :: args -> 
       aux (acc@[b]) env args
    | [] -> return (acc, env)
  in
  aux [] env args



and subtype loc_ret env (args : aargs) (rtyp : Types.t) ppdescr =

  let open Alrc.Types in
  let rtyp = Alrc.Types.from_type rtyp in
  debug_print 1 (action ppdescr) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "rtyp" (Alrc.Types.pp rtyp)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "returned" (pps Sym.pp (BT.pp false) (List.map fst args))) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 2 PPrint.empty >>= fun () ->

  pack_structs_aargs loc_ret env args >>= fun (args,env) ->

  match_As (fun e -> Call_error e) loc_ret env args rtyp.a >>= fun (substs,env) ->
  let rtyp = List.fold_left (fun ftyp (sym,sym') -> subst_var sym sym' ftyp) 
               {rtyp with a = []} substs  in

  let (unis,substs) = record_lvars_for_unification rtyp.l in
  let rtyp = List.fold_left (fun rtyp (sym,sym') -> subst_var sym sym' rtyp) 
               {rtyp with l = []} substs in

  match_Rs (fun e -> Call_error e) loc_ret env unis rtyp.r >>= fun (substs,unis,env) ->
  let rtyp = fold_left (fun f (s, s') -> subst_var s s' f) {rtyp with r =  []} substs in

  ensure_unis_resolved loc_ret env unis >>= fun resolved ->

  fold_leftM (fun (ts,env) (_,(_,sym)) -> 
      get_ALvar loc_ret env sym >>= fun (bt,env) ->
      return (ts@[{name=sym; bound = LS.Base bt}], env)
    ) ([],env) resolved >>= fun (largs,env) ->
  pack_structs_largs loc_ret env largs >>= fun (largs,env) ->
  let lspecs = map (fun (spec,(sym,_)) -> {name=sym;bound=spec}) resolved in

  match_Ls (fun e -> Call_error e) loc_ret env largs lspecs >>= fun (substs,env) ->
  let rtyp = fold_left (fun f (s, s') -> subst_var s s' f) rtyp substs in

  Solver.check_constraints_hold loc_ret env rtyp.c >>= fun () ->
  return env



let call_typ loc_call env (args : aargs) (ftyp : FunctionTypes.t) =
    
  let open Alrc.Types in
  let open Alrc.FunctionTypes in
  let ftyp = Alrc.FunctionTypes.from_function_type ftyp in
  debug_print 1 (action "function call type") >>= fun () ->
  debug_print 2 (blank 3 ^^ item "ftyp" (Alrc.FunctionTypes.pp ftyp)) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "args" (pps Sym.pp (BT.pp false) (List.map fst args))) >>= fun () ->
  debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 2 PPrint.empty >>= fun () ->

  pack_structs_aargs loc_call env args >>= fun (args,env) ->

  match_As (fun e -> Call_error e) loc_call env args ftyp.arguments2.a >>= fun (substs,env) ->
  let ftyp = fold_left (fun ftyp (sym,sym') -> subst_var sym sym' ftyp) 
               (updateAargs ftyp []) substs in

  let (unis,substs) = record_lvars_for_unification ftyp.arguments2.l in
  let ftyp = fold_left (fun ftyp (sym,sym') -> subst_var sym sym' ftyp) 
               (updateLargs ftyp []) substs in

  match_Rs (fun e -> Call_error e) loc_call env unis ftyp.arguments2.r >>= fun (substs,unis,env) ->
  let ftyp = fold_left (fun f (s, s') -> subst_var s s' f) (updateRargs ftyp []) substs in

  ensure_unis_resolved loc_call env unis >>= fun resolved ->

  fold_leftM (fun (ts,env) (_,(_,sym)) -> 
      get_ALvar loc_call env sym >>= fun (bt,env) ->
      return (ts@[{name=sym; bound = LS.Base bt}], env)
    ) ([],env) resolved >>= fun (largs,env) ->
  pack_structs_largs loc_call env largs >>= fun (largs,env) ->
  let lspecs = map (fun (spec,(sym,_)) -> {name=sym;bound=spec}) resolved in

  match_Ls (fun e -> Call_error e) loc_call env largs lspecs >>= fun (substs,env) ->
  let ftyp = fold_left (fun f (s, s') -> subst_var s s' f) ftyp substs in
  
  Solver.check_constraints_hold loc_call env ftyp.arguments2.c >>= fun () ->

  let rt = ((to_function_type ftyp).return) in
  (* unpack_structs loc_call env.global rt >>= fun rt -> *)
  return (rt, env)







let infer_ctor loc ctor (aargs : aargs) = 
  match ctor with
  | M_Ctuple -> 
     let name = fresh () in
     let bts = fold_left (fun bts (b,_) -> bts @ [b.bound]) [] aargs in
     let bt = Tuple bts in
     let constrs = 
       mapi (fun i (b,_) -> 
           makeUC (LC (Nth (of_int i, S (name,Base bt) %= S (b.name, Base b.bound)))))
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
  size_of_ctype loc ct >>= fun size ->
  ctype true true loc sym (make_pointer_ctype ct) >>= fun arg ->

  let rec return_resources (lvars,resources) arg = 
    match arg with
    | [] -> return (lvars,resources)
    | b :: arg ->
       match b.bound with
       (* | Block b -> 
        *    return_resources (lvars, resources@[makeUR (Block b)]) arg  *)
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
       (* | PackedStruct {sym = n} -> 
        *    begin match List.assoc_opt n lvars with
        *    | None -> 
        *       return_resources (lvars,resources) arg
        *    | Some name -> 
        *       let resources = resources@[makeUR (PackedStruct {sym = name})] in
        *       return_resources (lvars, resources) arg
        *    end *)
  in
  let alrc_arg = Alrc.Types.from_type arg in
  return_resources ([],[]) alrc_arg.r >>= fun (lvar_substs,return_resources) ->

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
           | Some name -> Some (makeUC (LC.subst_var n name b.bound))
           | None -> None
           end
        | _ -> None
      ) alrc_arg.c
  in
  return (arg, return_logical@return_resources@return_constraints)






let points_to loc env sym = 
  resources_associated_with_var_or_equals loc env sym >>= fun owneds ->
  let resource_names = List.map snd owneds in
  get_Rvars loc env resource_names >>= fun (resources,_env) ->
  let named_resources = List.combine resource_names resources in
  let check = function
    | (r, Points p) :: _ -> return (Some (r,p))
    (* | _ :: named_resources -> check named_resources *)
    | [] -> return None
  in
  check named_resources


    



let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()






let infer_ptrval name loc env ptrval = 
  Impl_mem.case_ptrval ptrval
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
  let open Ctype in
  Impl_mem.case_mem_value mem
    ( fun _ctyp -> fail loc (Unsupported !^"ctypes as values") )
    ( fun it _sym -> 
      (* todo: do something with sym *)
      ctype false false loc (fresh ()) (Ctype ([], Basic (Integer it))) >>= fun t ->
      return (t, env) )
    ( fun it iv -> 
      let name = fresh () in
      integer_value_to_num loc iv >>= fun v ->
      let val_constr = LC (S (name, Base Int) %= Num v) in
      integerType_constraint loc (S (name,Base Int)) it >>= fun type_constr ->
      Solver.constraint_holds_given_constraints loc env [val_constr] type_constr >>= function
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
and infer_struct loc env (struct_type,fields) =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  fold_leftM (fun (aargs,env) (_id,_ct,mv) ->
      infer_mem_value loc env mv >>= fun (t, env) ->
      let (t,env) = make_Aargs_bind_lrc loc env t in
      return (aargs@t, env)
    ) ([],env) fields >>= fun (aargs,env) ->
  pack_struct loc env (S_Id struct_type) aargs >>= fun ((n,bt),env) ->
  return ([makeA n bt], env)


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
     let constr = makeUC (LC (S (name, Base Int) %= Num i)) in
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
     return ([makeA name Bool; makeUC (LC (S (name, Base Bool)))], env)
  | M_Vfalse -> 
     let name = fresh () in
     return ([makeA name Bool; makeUC (LC (Not (S (name, Base Bool))))], env)
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
           makeUC (LC (Nth (of_int i, S (name,Base bt) %= S (b.name,Base b.bound)))))
         aargs
     in
     return ((makeA name bt) :: constrs, env)







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
  Solver.is_unreachable loc env >>= function
  | true -> return env
  | false -> 
     match bad with
     | Undefined (loc,ub) -> fail loc (TypeErrors.Undefined ub)
     | Unspecified loc -> fail loc TypeErrors.Unspecified
     | StaticError (loc, (err,pe)) -> fail loc (TypeErrors.StaticError (err,pe))
  









let infer_pexpr loc env (pe : 'bty mu_pexpr) = 

  debug_print 1 (action "inferring pure expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget pe)) >>= fun () ->

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in

  begin match pe_ with
  | M_PEsym sym ->
     let name = fresh () in
     get_Avar loc env sym >>= fun (bt,env) ->
     let typ = [makeA name bt; makeUC (LC (S (sym, Base bt) %= S (name, Base bt)))] in
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
        let bt = StructField (sym, [{loc; struct_type = S_Id struct_type; field=Id.s fid}]) in
        return (Normal [makeUA bt], env)
     | StructField (sym, accesses) ->
        let bt = StructField (sym, accesses@[{loc; struct_type = S_Id struct_type; field=Id.s fid}]) in
        return (Normal [makeUA bt], env)
     | bt ->
        fail loc (Unreachable !^"member_shift applied to non-pointer")
     end
  | M_PEnot asym ->
     let (sym,loc) = aunpack loc asym in
     get_Avar loc env sym >>= fun (bt,env) ->
     check_base_type loc (Some sym) Bool bt >>= fun () ->
     let ret = fresh () in 
     let rt = [makeA sym Bool; makeUC (LC (S (ret,Base Bool) %= Not (S (sym,Base Bool))))] in
     return (Normal rt, env)
  | M_PEop (op,asym1,asym2) ->
     let (sym1,loc1) = aunpack loc asym1 in
     let (sym2,loc2) = aunpack loc asym2 in
     get_Avar loc1 env sym1 >>= fun (bt1,env) ->
     get_Avar loc2 env sym2 >>= fun (bt2,env) ->
     let (((ebt1,ebt2),rbt),c) = binop_typ op in
     check_base_type loc1 (Some sym1) bt1 ebt1 >>= fun () ->
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
     begin match fname with
     | Core.Impl impl -> 
        get_impl_fun_decl loc env.global impl
     | Core.Sym sym ->
        get_fun_decl loc env.global sym >>= fun (_loc,decl_typ,_ret_name) ->
        return decl_typ
     end >>= fun decl_typ ->
     make_Aargs loc env asyms >>= fun (args,env) ->
     call_typ loc env args decl_typ >>= fun (rt, env) ->
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
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget e)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in

  (* think about this *)
  Solver.is_unreachable loc env >>= fun unreachable ->
  if unreachable then 
    warn !^"stopping to type check: unreachable" >>= fun () ->
    return env 
  else

  match e_ with
  | M_PEif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun (t1,env) -> 
     check_base_type loc1 (Some sym1) t1 Bool >>= fun () ->
     check_pexpr loc (add_var env (makeUC (LC (S (sym1,Base Bool))))) e2 typ >>= fun _env ->
     check_pexpr loc (add_var env (makeUC (LC (Not (S (sym1,Base Bool)))))) e3 typ
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
           unpack_structs loc env.global rt >>= fun rt ->
           check_pexpr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           unpack_structs loc env.global rt >>= fun rt ->
           check_pexpr loc (add_vars env (rename newname rt)) e2 typ
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
        subtype loc env rt typ "function return type"
     | Bad bad -> ensure_bad_unreachable loc env bad
     end



let rec infer_expr loc env (e : ('a,'bty) mu_expr) = 

  debug_print 1 (action "inferring expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) >>= fun () ->

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
     | M_PtrValidForDeref (_a_ct, asym) ->
        let (sym, loc) = aunpack loc asym in
        let ret_name = fresh () in
        get_Avar loc env sym >>= fun (bt, env) ->
        check_base_type loc (Some sym) bt Loc >>= fun () ->
        (* check more things? *)
        points_to loc env sym >>= fun points ->
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
        get_Avar loc env sym >>= fun (a_bt,env) ->
        check_base_type loc (Some sym) Int a_bt >>= fun () ->
        let name = fresh () in
        size_of_ctype loc ct >>= fun size ->
        let r = (Points {pointer = name; offset = zero; 
                         pointee = None; typ = ct; size}) in
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
        size_of_ctype loc ct >>= fun size ->

        let (psym,ploc) = aunpack loc asym1 in
        let (vsym,vloc) = aunpack loc asym2 in
        get_Avar ploc env psym >>= fun (pbt,env) ->
        get_Avar vloc env vsym >>= fun (vbt,env) ->

        (* for consistency check value against Core annotation *)
        begin 
          ctype false false loc (fresh ()) ct >>= fun t ->
          subtype loc env [({name=vsym;bound=vbt},vloc)] t 
            "checking store value against ctype annotaion"
        end >>= fun _ ->

        (* begin match vbt with
         * | Struct struct_type -> unpack_struct loc env vsym struct_type
         * | _ -> return ((vsym,vbt),env)
         * end >>= fun ((vsym,vbt),env) -> *)

        (* check pointer *)
        begin match pbt with
        | Loc -> return (psym,[])
        | StructField (sym,accesses) -> return (sym,accesses)
        | _ -> 
           let err = "Store argument has to be a pointer or a struct field" in
           fail ploc (Generic_error !^err)
        end >>= fun (pointer,path) ->


        begin points_to ploc env pointer >>= function 
         | None -> fail loc (Generic_error !^"missing ownership of store location" )
         | Some (r,p) -> return (r,p)
        end >>= fun (r,p) ->

        let rec check_access_and_update expected_ct base access =
          debug_print 2 (action "checking store access") >>= fun () ->
          debug_print 3 (blank 3 ^^ item "expected ctyp" (Pp_core_ctype.pp_ctype expected_ct)) >>= fun () ->
          debug_print 2 (blank 3 ^^ item "base" (match base with Some s -> Sym.pp s | None -> !^"(none)")) >>= fun () ->
          debug_print 2 (blank 3 ^^ item "access" (pp_field_access access)) >>= fun () ->
          match base, access with
          | _, [] -> 
             if not (Ctype.ctypeEqual expected_ct ct) then fail loc (Unreachable !^"store: ctype mismatch") else
             begin 
               ctype false false loc (fresh ()) expected_ct >>= fun t ->
               subtype loc env [({name=vsym;bound=vbt},vloc)] t
                 "checking store value against expected type"
             end >>= fun _ ->
             let newsym = fresh () in
             let env = add_var env (makeL newsym (Base vbt)) in
             let env = add_var env (makeUC (LC (S (newsym,Base vbt) %= S (vsym,Base vbt)))) in
             return (vsym,env)
          | None, _ -> fail ploc (Generic_error !^"cannot dereference uninitialised struct field")
          | Some base, fa :: access ->
             (* maybe do get_Lvar? See comment in Load rule *)
             get_ALvar ploc env base >>= fun (bt,env) ->
             begin match bt with
             | OpenStruct s when BT.type_equal fa.struct_type s.typ ->
               assoc_err loc fa.field s.fields "check store field access" >>= 
                 fun (_offset,expected_ct,fvar) ->
               check_access_and_update expected_ct fvar access >>= fun (new_field_sym,env) ->
               let fields = 
                 map (fun (efield,(offset,typ,value)) -> 
                     if efield = fa.field 
                     then (efield,(offset,typ, Some new_field_sym))
                     else (efield,(offset,typ, None))
                   ) s.fields
               in
               let newsym = fresh () in
               let a = makeA newsym (OpenStruct {s with fields = fields}) in
               let env = add_var env a in
               return (newsym,env)
             | OpenStruct s -> fail loc (Unreachable !^"store struct type mismatch") 
             | _  ->fail loc (Generic_error !^"cannot access field of non-struct type") 
             end 
        in
        check_access_and_update p.typ p.pointee path >>= fun (newsym,env) ->
        let env = remove_var env r in
        let env = add_var env (makeUR (Points {p with pointee = Some newsym})) in
        return (Normal [makeUA Unit],env)

     | M_Load (a_ct, asym, _mo) -> 

        let (ct, _ct_loc) = aunpack loc a_ct in
        size_of_ctype loc ct >>= fun size ->

        let (psym,ploc) = aunpack loc asym in
        get_Avar ploc env psym >>= fun (pbt,env) ->

        (* check pointer *)
        begin match pbt with
        | Loc -> return (psym,[])
        | StructField (sym,accesses) -> return (sym,accesses)
        | _ -> 
           let err = "Load argument has to be a pointer or a struct field" in
           fail ploc (Generic_error !^err)
        end >>= fun (pointer,path) ->

        begin points_to ploc env pointer >>= function 
         | None -> fail loc (Generic_error !^"missing ownership of load location" )
         | Some (r,p) -> return (r,p)
        end >>= fun (r,p) ->

        let rec check_access_and_read field_ct base access =
          debug_print 2 (action "checking load access") >>= fun () ->
          debug_print 3 (blank 3 ^^ item "expected ctyp" (Pp_core_ctype.pp_ctype field_ct)) >>= fun () ->
          debug_print 2 (blank 3 ^^ item "base" (match base with Some s -> Sym.pp s | None -> !^"(none)")) >>= fun () ->
          debug_print 2 (blank 3 ^^ item "access" (pp_field_access access)) >>= fun () ->
          match base, access with
          | None, _ -> fail ploc (Generic_error !^"read from uninitialised memory")
          | Some s, [] -> 
             if not (Ctype.ctypeEqual field_ct ct) then fail loc (Unreachable !^"load: ctype mismatch") else
               (* maybe do get_Lvar? I.e. require the pointee to be
                  logical? Then we have to unpack structs to have no
                  computational fields *)
               get_ALvar ploc env s >>= fun (bt,env) ->
               (* begin match bt with
                * | OpenStruct o -> pack_open_struct loc env o
                * | _ -> return ((s,bt),env)
                * end >>= fun ((s,bt),env) -> *)
               let ret = fresh () in
               let constr = LC (S (ret, Base bt) %= (S (s,Base bt))) in
               begin 
                 ctype false false loc (fresh ()) field_ct >>= fun t ->
                 subtype loc env [({name=s;bound=bt},ploc)] t 
                   "checking load value against expected type"
               end >>= fun _ ->
               return (Normal [makeA ret bt; makeUC constr],env)
          | Some base, fa :: access ->
             get_Lvar ploc env base >>= fun (Base bt,env) ->
             begin match bt with
             | OpenStruct s when BT.type_equal fa.struct_type s.typ ->
                (* debug_print 3 (action "checking field access") >>= fun () ->
                 * debug_print 3 (item "checking field access") >>= fun () -> *)
               assoc_err loc fa.field s.fields "check load field access" >>= fun 
                 (_offset,field_ct,fvar) ->
               check_access_and_read field_ct fvar access
             | OpenStruct s -> fail loc (Unreachable !^"load: struct type mismatch") 
             | _  ->fail loc (Generic_error !^"cannot access field of non-struct type") 
             end 
        in
        check_access_and_read p.typ p.pointee path

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
     make_Aargs loc env arg_asyms >>= fun (args,env) ->
     let (sym1,loc1) = aunpack loc fun_asym in
     get_Avar loc1 env sym1 >>= fun (bt,env) ->
     begin match bt with
     | FunctionPointer sym -> return sym
     | _ -> fail loc1 (Generic_error !^"not a function pointer")
     end >>= fun fun_sym ->
     get_fun_decl loc env.global fun_sym >>= fun (_loc,decl_typ,_ret_name) ->
     call_typ loc env args decl_typ >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_Eproc (_, fname, asyms) ->
     begin match fname with
     | Core.Impl impl -> 
        get_impl_fun_decl loc env.global impl
     | Core.Sym sym ->
        get_fun_decl loc env.global sym >>= fun (_loc,decl_typ,_ret_name) ->
        return decl_typ
     end >>= fun decl_typ ->
     make_Aargs loc env asyms >>= fun (args,env) ->
     call_typ loc env args decl_typ >>= fun (rt, env) ->
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
  end >>= fun (typ,env) ->

  debug_print 3 (blank 3 ^^ item "inferred" (UU.pp_ut typ)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->
  return (typ,env)


let rec check_expr loc env (e : ('a,'bty) mu_expr) typ = 

  debug_print 1 (action "checking expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->


  (* think about this *)
  Solver.is_unreachable loc env >>= fun unreachable ->
  if unreachable then 
    warn !^"stopping to type check: unreachable" >>= fun () ->
    return env 
  else


  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun (t1,env) -> 
     check_base_type loc1 (Some sym1) t1 Bool >>= fun () ->
     let then_constr = makeUC (LC (S (sym1,Base Bool))) in
     let else_constr = makeUC (LC (Not (S (sym1,Base Bool)))) in
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
           unpack_structs loc env.global rt >>= fun rt ->
           check_expr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> 
           unpack_structs loc env.global rt >>= fun rt ->
           check_expr loc (add_vars env (rename newname rt)) e2 typ
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
           unpack_structs loc env.global rt >>= fun rt ->
           check_expr loc (add_vars env (rename newname rt)) e2 typ
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
        subtype loc env rt typ "function return type"
     | Bad bad -> ensure_bad_unreachable loc env bad
     end
     


let check_proc loc fsym genv body ftyp = 
  debug_print 1 (h1 ("Checking procedure " ^ (plain (Sym.pp fsym)))) >>= fun () ->
  let env = with_fresh_local genv in
  unpack_structs loc genv ftyp.arguments >>= fun args ->
  let env = add_vars env args in
  check_expr loc env body ftyp.return >>= fun _env ->
  debug_print 1 (!^(greenb "...checked ok")) >>= fun () ->
  return ()

let check_fun loc fsym genv body ftyp = 
  debug_print 1 (h1 ("Checking function " ^ (plain (Sym.pp fsym)))) >>= fun () ->
  let env = with_fresh_local genv in
  unpack_structs loc genv ftyp.arguments >>= fun args ->
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

                             
(* let process_attributes *)


let record_fun sym (loc,attrs,ret_ctype,args,is_variadic,_has_proto) genv =
  if is_variadic then fail loc (Variadic_function sym) else
    fold_leftM (fun (args,returns,names) (msym, ct) ->
        let name = sym_or_fresh msym in
        make_fun_arg_type name loc ct >>= fun (arg,ret) ->
        return (args@arg, returns@ret, name::names)
      ) ([],[],[]) args >>= fun (arguments, returns, names) ->
    let ret_name = Sym.fresh () in
    ctype true true loc ret_name ret_ctype >>= fun ret ->
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



let record_tagDef file sym def genv =

  (* like ctype_aux *)
  let rec aux owned packed loc (id : string) (Ctype.Ctype (annots, ct_)) =
    let loc = update_loc loc annots in
    let open Ctype in
    match ct_ with
    | Void -> return [{name=id; bound = A Unit}]
    | Basic (Integer it) -> 
       let newid = id ^ "_range_constraint" in
       integerType_constraint loc (StructDefField (id,Int)) it >>= fun lc ->
       return [{name=id; bound = A Int}; {name=newid; bound = C lc}]
    | Array (ct, _maybe_integer) -> 
       return [{name=id;bound=A BT.Array}]
    | Pointer (_qualifiers, ct) -> 
       return [{name=id;bound = A Loc}]
    (* fix *)
    | Atomic ct -> 
       aux owned packed loc id ct
    | Struct sym -> 
       return [{name=id; bound = A (BT.Struct (S_Id sym))}]
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in


  match def with
  | Ctype.UnionDef _ -> 
     fail Loc.unknown (Unsupported !^"todo: union types")
  | Ctype.StructDef (fields, _) ->

     fold_leftM (fun (typ,ctypes,offsets) (id, (_attributes, _qualifier, ct)) ->
       let sid = Id.s id in
       aux false true Loc.unknown sid ct >>= fun newfields ->
       let offset_ival = Impl_mem.offsetof_ival file.Mucore.mu_tagDefs sym id in
       integer_value_to_num Loc.unknown offset_ival >>= fun offset ->
       return (typ@newfields, ctypes@[(sid,ct)], offsets@[(sid,offset)])
     ) ([],[],[]) fields >>= fun (typ,ctypes,offsets) ->

     let decl = {typ;ctypes;offsets} in
     let genv = add_struct_decl genv sym decl in
     return genv


let record_tagDefs file genv tagDefs = 
  pmap_foldM (record_tagDef file) tagDefs genv







let pp_fun_map_decl funinfo = 
  let pp = Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (Pp_utils.to_plain_string pp)


let print_initial_environment genv = 
  debug_print 1 (h1 "initial environment") >>= fun () ->
  debug_print 1 (Global.pp genv)


let check mu_file =
  pp_fun_map_decl mu_file.mu_funinfo;
  let genv = Global.empty in
  record_tagDefs mu_file genv mu_file.mu_tagDefs >>= fun genv ->
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
