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






let add_vars env bindings = fold_left add_var env bindings
let remove_vars env names = fold_left remove_var env names
let get_vars loc env vars = 
  fold_leftM (fun (acc,env) sym ->
      get_var loc env sym >>= fun (t,env) ->
      return (acc@[t], env)
    ) ([],env) vars

let add_Avar env (name, t) = add_var env {name; bound = A t}
let add_Cvar env (name, t) = add_var env {name; bound = C t}
let add_Avars env vars = List.fold_left add_Avar env vars
let add_Cvars env vars = List.fold_left add_Cvar env vars

let get_ALvar loc env var = 
  tryM (get_Avar loc env var)
    (get_Lvar loc env var >>= fun (Base bt) -> return bt)


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

  let rec all_normal : ('a or_u) list -> 'a list or_u = function
    | [] -> Normal []
    | Bad u :: _ -> Bad u
    | Normal a :: rest -> 
       match all_normal rest with
       | Normal rest -> Normal (a :: rest)
       | Bad b -> Bad b

  let pp_ut = function
    | Normal t -> Types.pp t
    | Bad u -> !^"bad"


end

open UU




let is_unreachable loc env =
  Solver.constraint_holds loc env (LC (Bool false))

let rec check_constraints_hold loc env = function
  | [] -> return ()
  | {name; bound = c} :: constrs ->
     debug_print 2 (action "checking constraint") >>= fun () ->
     debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
     debug_print 2 (blank 3 ^^ item "constraint" (LogicalConstraints.pp c)) >>= fun () ->
     Solver.constraint_holds loc env c >>= function
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
      Solver.constraint_holds loc env (LC (S (sym,bt) %= S (sym',bt))) >>= fun holds ->
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
    | OTy_union _sym -> fail loc (Unsupported "todo: unions")
    | OTy_floating -> fail loc (Unsupported "todo: float")
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
  | BTy_storable -> fail loc (Unsupported "BTy_storable")
  | BTy_ctype -> fail loc (Unsupported "ctype")



let integerType loc name it =
  integer_value_to_num loc (Impl_mem.min_ival it) >>= fun min ->
  integer_value_to_num loc (Impl_mem.max_ival it) >>= fun max ->
  let c = makeUC (LC ((Num min %<= S (name, Int)) %& 
                      (S (name, Int) %<= Num max))) in
  return ((name,Int), [], [], [c])

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
     fail loc (Unsupported "todo: union types")
  | Basic (Floating _) -> 
     fail loc (Unsupported "floats")
  | Function _ -> 
     fail loc (Unsupported "function pointers")


let ctype loc (name : Sym.t) (ct : Ctype.ctype) =
  ctype_aux loc name ct >>= fun ((name,bt), l,r,c) ->
  return (makeA name bt :: l @ r @ c)

let make_pointer_ctype ct = 
  let open Ctype in
  (* fix *)
  let q = {const = false; restrict = false; volatile = false} in
  Ctype ([], Pointer (q, ct))





let subtype loc env rt1 rt2 = 

  let rec check env rt1 rt2 =
    match rt1, rt2 with
    | [], [] -> 
       return env
    | {name; bound = A r1} :: _, [] -> 
       fail loc (Return_error (Surplus_A (name, r1)))
    | {name; bound = L r1} :: _, [] -> 
       fail loc (Return_error (Surplus_L (name, r1)))
    | {name; bound = R r1} :: _, [] -> 
       fail loc (Return_error (Surplus_R (name, r1)))

    | [], {name; bound = A r2} :: _ -> 
       fail loc (Return_error (Missing_A (name, r2)))
    | [], {name; bound = L r2} :: _ -> 
       fail loc (Return_error (Missing_L (name, r2)))
    | [], {name; bound = R r2} :: _ -> 
       fail loc (Return_error (Missing_R (name, r2)))
    | ({name; bound = C c1} as b) :: rt1', _ ->
       check (add_var env b) rt1' rt2
    | _, {name = n2; bound = C c2} :: rt2' ->
       begin Solver.constraint_holds loc env c2 >>= function
       | true -> check env rt1 rt2'
       | false ->
         fail loc (Return_error (Unsat_constraint (n2, c2)))
       end
    | (r1 :: rt1), (r2 :: rt2) ->
       match r1, r2 with
       | ({name = n1; bound = A t1} as b), {name = n2; bound = A t2} 
            when BT.type_equal t1 t2 ->
          check (add_var env b) rt1 (Types.subst n2 n1 rt2)
       | ({name = n1; bound = L t1} as b), {name = n2; bound = L t2} 
            when LS.type_equal t1 t2 ->
          check (add_var env b) rt1 (Types.subst n2 n1 rt2)
       | {name = n1; bound = R t1}, {name = n2; bound = R t2} 
            when RE.type_equal env t1 t2 ->
          check env rt1 rt2
       | _, _ ->
          let msm = Mismatch {mname = Some r1.name; 
                              has = r1.bound; 
                              expected = r2.bound} in
          fail loc (Return_error (msm))
  in

  check env rt1 rt2








let make_create_type loc ct : (FunctionTypes.t,'e) m = 
  let arguments = [makeUA Int] in
  let name = fresh () in
  size_of_ctype loc ct >>= fun size ->
  let rt = [makeA name Loc; makeUR (Block (S (name, Loc), Num size))] in
  return {arguments; return = rt}


let make_load_type loc ct : (FunctionTypes.t,'e) m = 
  let pointer_name = fresh () in
  ctype_aux loc (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
  let a = makeA pointer_name Loc in
  let l = makeL pointee_name (Base bt) :: l in
  let r = makeUR (Points (S (pointer_name, Loc), S (pointee_name, bt))) :: r in
  let addr_argument = a :: l @ r @ c in
  let ret_name = fresh () in
  let ret = makeA ret_name bt :: r @ [makeUC (LC (S (ret_name, bt) %= (S (pointee_name,bt))))] in
  return {arguments = addr_argument; return = ret}


let make_load_field_type loc ct access : (FunctionTypes.t,'e) m = 
  fail loc (Unsupported "make_load_field_type not implemented yet")

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


(* maybe replace this function: this does not look at symbols equal to
   sym for ownership currently *)
let is_uninitialised_pointer loc env sym = 
  get_Avar loc env sym >>= fun bt ->
  let resource_names = owned_resources env sym in
  get_Rvars loc env resource_names >>= fun (resources,_) ->
  match resources with
  | [Block _] -> return (bt = Loc)
  | _ -> return false


let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()



let check_base_type loc mname has expected =
  if BT.type_equal has expected 
  then return ()
  else fail loc (Call_error (Mismatch {mname; has; expected}))


type aargs = ((Sym.t * BT.t) * Loc.t) list

let make_Aargs loc env tsyms = 
  mapM (fun asym ->
      let (sym, loc) = aunpack loc asym in
      get_Avar loc env sym >>= fun t ->
      return ((sym, t), loc)) tsyms


let check_Aargs_typ (mtyp : BT.t option) (aargs: aargs) : (BT.t option, 'e) m =
  fold_leftM (fun mt ((sym,bt),loc) ->
      match mt with
      | None -> 
         return (Some bt)
      | Some t -> 
         check_base_type loc (Some sym) (A bt) (A t) >>= fun () ->
         return (Some t)
    ) mtyp aargs



let infer_object_value loc env ov =

  let name = fresh () in

  match ov with
  | M_OVinteger iv ->
     integer_value_to_num loc iv >>= fun i ->
     let t = makeA name Int in
     let constr = makeUC (LC (S (name, Int) %= Num i)) in
     return [t; constr]
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       ( fun _cbt -> 
         return [makeA name Loc; makeUC (LC (Null (S (name, Loc))))] )
       ( fun sym -> 
         fail loc (Unsupported "function pointers") )
       ( fun _prov loc ->
         return [makeA name Loc; makeUC (LC (S (name, Loc) %= Num loc))] )
       ( fun () -> fail loc (Unreachable "unspecified pointer value") )
  | M_OVarray items ->
     make_Aargs loc env items >>= fun args_bts ->
     check_Aargs_typ None args_bts >>= fun _ ->
     return [makeA name Array]
  | M_OVstruct (sym, fields) ->
     fail loc (Unsupported "todo: struct")
  | M_OVunion _ -> 
     fail loc (Unsupported "todo: union types")
  | M_OVfloating iv ->
     fail loc (Unsupported "floats")


let infer_value loc env v : (Types.t,'e) m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc env ov
  | M_Vunit ->
     return [makeUA Unit]
  | M_Vtrue ->
     let name = fresh () in
     return [makeA name Bool; makeUC (LC (S (name, Bool)))]
  | M_Vfalse -> 
     let name = fresh () in
     return [makeA name Bool; makeUC (LC (Not (S (name, Bool))))]
  | M_Vlist (cbt, asyms) ->
     bt_of_core_base_type loc cbt >>= fun bt ->
     make_Aargs loc env asyms >>= fun aargs ->
     check_Aargs_typ (Some bt) aargs >>= fun _ ->
     return [makeUA (List bt)]
  | M_Vtuple [] ->
     fail loc (Generic_error !^"empty tuple")
  | M_Vtuple asyms ->
     make_Aargs loc env asyms >>= fun aargs ->
     let (args,_) = List.split aargs in
     let (names,bts) = List.split args in
     let a = List.map makeUA bts in
     return a




let pp_unis unis = 
  let pp_entry (sym, {spec; resolved}) =
    match resolved with
    | Some res -> 
       (typ (Sym.pp sym) (LS.pp spec)) ^^^ !^"resolved as" ^^^ (Sym.pp res)
    | None -> (typ (Sym.pp sym) (LS.pp spec)) ^^^ !^"unresolved"
  in
  pp_env_list None (SymMap.bindings unis) pp_entry



let call_typ loc_call env ftyp args =
    
  let open Alrc.Types in
  let open Alrc.FunctionTypes in

  let ftyp = Alrc.FunctionTypes.from_function_type ftyp in


  debug_print 1 (action "function call type") >>= fun () ->

  let print ftyp args env unis = 
    debug_print 2 (action "checking and refining function call type") >>= fun () ->
    debug_print 2 (blank 3 ^^ item "ftyp" (Alrc.FunctionTypes.pp ftyp)) >>= fun () ->
    debug_print 2 (blank 3 ^^ item "args" (pp_env_list None args (fun (a,_) -> Sym.pp a))) >>= fun () ->
    debug_print 2 (blank 3 ^^ item "unis" (pp_unis unis)) >>= fun () ->
    debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
    debug_print 2 PPrint.empty
  in

  let unis = SymMap.empty in

  let rec do_a args ftyp = 
    print ftyp args env unis >>= fun () ->
    match args, ftyp.arguments2.a with
    | [], [] -> return (ftyp,args)
    | ((sym,loc) :: args), ({name = n; bound = t} :: decl_args) ->
       get_Avar loc env sym >>= fun t' ->
       if BT.type_equal t' t then 
         let ftyp = subst n sym {ftyp with arguments2 = {ftyp.arguments2 with a = decl_args}} in
         do_a args ftyp
       else 
         let msm = Mismatch {mname = Some sym; has = A t'; expected = A t} in
         fail loc (Call_error msm)
    | (sym,loc) :: _, [] -> 
       get_Avar loc env sym >>= fun bt ->
       fail loc (Call_error (Surplus_A (sym, bt)))
    | [], {name = n; bound =  t} :: _ ->
       fail loc_call (Call_error (Missing_A (n, t)))
  in

  do_a args ftyp >>= fun (ftyp,args) ->

  let rec do_l ftyp unis = 
    print ftyp args env unis >>= fun () ->
    match ftyp.arguments2.l with
    | [] -> return (ftyp, unis)
    | {name = n; bound = t} :: decl_args ->
       let sym = Sym.fresh () in
       let uni = { spec = t; resolved = None } in
       let unis = SymMap.add sym uni unis in
       let ftyp = subst n sym {ftyp with arguments2 = {ftyp.arguments2 with l = decl_args}} in
       do_l ftyp unis
  in
  do_l ftyp unis >>= fun (ftyp,unis) -> 

  let rec do_r ftyp env unis = 
    print ftyp args env unis >>= fun () ->
    match ftyp.arguments2.r with
    | [] -> return (ftyp,env,unis)
    | {name = n; bound = resource} :: decl_args -> 
       begin match RE.owner resource with
       | None -> fail loc_call (Call_error (Missing_R (n, resource)))
       | Some owner ->
          get_ALvar loc_call env owner >>= fun bt ->
          vars_equal_to loc_call env owner bt >>= fun equal_to_owner ->
          let owneds = concat_map (fun o -> map (fun r -> (o,r)) (owned_resources env o))
                         (owner :: equal_to_owner) in
          let rec try_resources = function
            | [] -> 
               fail loc_call (Call_error (Missing_R (n, resource)))
            | (o,r) :: owned_resources ->
               get_Rvar loc_call env r >>= fun (resource',env) ->
               let resource' = RE.subst o owner resource' in
               debug_print 3 (action ("trying resource" ^ pps (RE.pp resource'))) >>= fun () ->
               match RE.unify resource resource' unis with
               | None -> try_resources owned_resources
               | Some unis ->
                  debug_print 2 (blank 3 ^^ item "** unis" (pp_unis unis)) >>= fun () ->
                  let ftyp = subst n r {ftyp with arguments2 = {ftyp.arguments2 with r = decl_args}} in
                  find_resolved env unis >>= fun (_,substs) ->
                  let ftyp = fold_left (fun f (s, s') -> subst s s' f) ftyp substs in
                  do_r ftyp env unis
          in
          try_resources owneds
       end
  in

  do_r ftyp env unis >>= fun (ftyp,env,unis) ->

  debug_print 2 (blank 3 ^^ item "** unis" (pp_unis unis)) >>= fun () ->    

  find_resolved env unis >>= fun (unresolved,substs) ->
  if not (SymMap.is_empty unresolved) then
    let (usym, {spec; resolved}) =
      SymMap.find_first (fun _ -> true) unresolved in
    fail loc_call (Call_error (Unconstrained_l (usym,spec)))
  else
    let ftyp = fold_left (fun f (s, s') -> subst s s' f) ftyp substs in
    check_constraints_hold loc_call env ftyp.arguments2.c >>= fun () ->
    let ftyp = to_function_type ftyp in
    return (ftyp.return,env)



let infer_ctor loc ctor (aargs : aargs) = 
  match ctor with
  | M_Ctuple -> 
     let name = fresh () in
     let (names_bts,_) = List.split aargs in
     let (names,bts) = List.split names_bts in
     let bt = Tuple bts in
     let constrs = 
       mapi (fun i (sym,ibt) -> 
           makeUC (LC (Nth (of_int i, S (name,bt) %= S (sym,ibt)))))
         names_bts 
     in
     return ([makeA name bt]@constrs)
  | M_Carray -> 
     check_Aargs_typ None aargs >>= fun _ ->
     return [{name = fresh (); bound = A Array}]
  | M_CivCOMPL
  | M_CivAND
  | M_CivOR
  | M_CivXOR -> 
     fail loc (Unsupported "todo: Civ..")
  | M_Cspecified ->
     let name = fresh () in
     begin match aargs with
     | [((sym,bt),_)] -> 
        return [makeA name bt; makeUC (LC (S (sym,bt) %= S (name,bt)))]
     | args ->
        let err = Printf.sprintf "Cspecified applied to %d argument(s)" 
                    (List.length args) in
        fail loc (Generic_error !^err)
     end
  | M_Cnil cbt -> fail loc (Unsupported "lists")
  | M_Ccons -> fail loc (Unsupported "lists")
  | M_Cfvfromint -> fail loc (Unsupported "floats")
  | M_Civfromfloat -> fail loc (Unsupported "floats")


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
  fail loc (Unsupported "todo: implement infer_pat")


let binop_typ op = 
  let open Core in
  let (((at1,at2), rt), vc) =
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
  in
  let a1, a2, ar = fresh (), fresh (), fresh () in
  let constr = LC ((vc (S (a1,at1)) (S (a2,at2))) %= S (ar,rt)) in
  {arguments = [makeA a1 at1; makeA a2 at2];
   return = [makeA ar rt; makeUC constr ]}
  



let ensure_bad_unreachable loc env bad = 
  is_unreachable loc env >>= function
  | true -> return () 
  | false -> 
     match bad with
     | Undefined (loc,ub) -> fail loc (TypeErrors.Undefined ub)
     | Unspecified loc -> fail loc TypeErrors.Unspecified
     | StaticError (loc, (err,pe)) -> fail loc (TypeErrors.StaticError (err,pe))


let struct_member_type loc env strct field = 
  get_struct_decl loc env.global strct >>= fun binders ->
  match List.find_opt (fun b -> b.name = field) binders with
  | None -> 
     let err = (!^"struct" ^^^ Sym.pp strct ^^^ 
                  !^"does not have field" ^^^ Sym.pp field) in
     fail loc (Generic_error err)
  | Some b ->
     return b.bound



let infer_pexpr loc env (pe : 'bty mu_pexpr) = 

  debug_print 1 (action "inferring pure expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pe)) >>= fun () ->

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in

  begin match pe_ with
  | M_PEsym sym ->
     let name = fresh () in
     get_Avar loc env sym >>= fun bt ->
     let typ = [makeA name bt; makeUC (LC (S (sym, bt) %= S (name, bt)))] in
     return (Normal typ, env)
  | M_PEimpl i ->
     get_impl_constant loc env.global i >>= fun t ->
     return (Normal [makeUA t], env)
  | M_PEval v ->
     infer_value loc env v >>= fun t ->
     return (Normal t, env)
  | M_PEconstrained _ ->
     fail loc (Unsupported "todo: PEconstrained")
  | M_PEundef (loc,undef) ->
     return (Bad (Undefined (loc, undef)), env)
  | M_PEerror (err,asym) ->
     let (sym, loc) = aunpack loc asym in
     return (Bad (StaticError (loc, (err,sym))), env)
  | M_PEctor (ctor, args) ->
     make_Aargs loc env args >>= fun aargs ->
     infer_ctor loc ctor aargs >>= fun rt ->
     return (Normal rt, env)
  | M_PEarray_shift _ ->
     fail loc (Unsupported "todo: PEarray_shift")
  | M_PEmember_shift (asym, strct, Identifier (_floc,fid)) ->
     let (pointer, _loc) = aunpack loc asym in
     NameMap.sym_of loc fid (get_names env.global) >>= fun field ->
     let bt = StructField {pointer; strct; field} in
     return (Normal [makeUA bt], env)
  | M_PEnot asym ->
     let a, ar = fresh (), fresh () in
     let ret = [makeA ar Bool; makeUC (LC (S (ar,Bool) %= Not (S (a,Bool))))] in
     let decl_typ = {arguments = [makeA a Bool]; return = ret} in
     call_typ loc env decl_typ [aunpack loc asym] >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_PEop (op,asym1,asym2) ->
     let decl_typ = binop_typ op in
     let args = [aunpack loc asym1; aunpack loc asym2] in
     call_typ loc env decl_typ args >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_PEstruct _ ->
     fail loc (Unsupported "todo: PEstruct")
  | M_PEunion _ ->
     fail loc (Unsupported "todo: PEunion")
  | M_PEmemberof _ ->
     fail loc (Unsupported "todo: M_PEmemberof")
  | M_PEcall (fname, asyms) ->
     begin match fname with
     | Core.Impl impl -> 
        get_impl_fun_decl loc env.global impl
     | Core.Sym sym ->
        get_fun_decl loc env.global sym >>= fun (_loc,decl_typ,_ret_name) ->
        return decl_typ
     end >>= fun decl_typ ->
     call_typ loc env decl_typ (List.map (aunpack loc) asyms) >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_PEcase _ -> fail loc (Unreachable "PEcase in inferring position")
  | M_PElet _ -> fail loc (Unreachable "PElet in inferring position")
  | M_PEif _ -> fail loc (Unreachable "PElet in inferring position")
  end >>= fun (typ,env) ->
  
  debug_print 3 (blank 3 ^^ item "interred" (UU.pp_ut typ)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->
  return (typ,env)


let rec check_pexpr loc env (e : 'bty mu_pexpr) typ = 

  debug_print 1 (action "checking pure expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr e)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->


  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_PEif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     check_base_type loc1 (Some sym1) (A t1) (A Bool) >>= fun () ->
     check_pexpr loc (add_var env (makeUC (LC (S (sym1,Bool))))) e2 typ >>= fun _env ->
     check_pexpr loc (add_var env (makeUC (LC (Not (S (sym1,Bool)))))) e3 typ
  | M_PEcase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat loc pat >>= fun (bindings, bt', ploc) ->
         check_base_type ploc None (A bt') (A bt) >>= fun () ->
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_pexpr loc env' pe typ
       ) pats_es >>= fun _ ->
     return env
  | M_PElet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_pexpr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> 
           ensure_bad_unreachable loc env bad >>= fun () ->
           return env
        end
     | M_normal_pattern (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_pexpr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad >>= fun () ->
                     return env
        end        
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor _)) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported "todo: ctor pattern")
     end
  | _ ->
     infer_pexpr loc env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt -> subtype loc env rt typ
     | Bad bad -> ensure_bad_unreachable loc env bad >>= fun () ->
                  return env
     end        



let rec infer_expr loc env (e : ('a,'bty) mu_expr) = 

  debug_print 1 (action "inferring expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr e)) >>= fun () ->

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
       -> fail loc (Unsupported "todo: ememop")
     | M_PtrValidForDeref (a_ct, asym) ->
        let (ct, ct_loc) = aunpack loc a_ct in
        ctype_aux loc (fresh ()) (make_pointer_ctype ct) >>= fun ((name,bt),l,r,c) ->
        let ret_name = fresh () in
        let ptr_typ = (makeA name bt) :: l @ r @ c in
        (* todo: plug in some other constraint *)
        let constr = LC (S (ret_name,Bool)) in
        let decl_typ = FT.make ptr_typ ([makeA ret_name Bool; makeUC constr]@r) in
        call_typ loc env decl_typ [aunpack loc asym] >>= fun (rt, env) ->
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
       -> fail loc (Unsupported "todo: ememop")
     end
  | M_Eaction (M_Paction (_pol, M_Action (aloc,_,action_))) ->
     begin match action_ with
     | M_Create (asym,a_ct,_prefix) -> 
        let (ct, ct_loc) = aunpack loc a_ct in
        make_create_type loc ct >>= fun decl_typ ->
        call_typ loc env decl_typ [aunpack loc asym] >>= fun (rt, env) ->
        return (Normal rt, env)
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
        fail loc (Unsupported "todo: CreateReadOnly")
     | M_Alloc (ct, sym, _prefix) -> 
        fail loc (Unsupported "todo: Alloc")
     | M_Kill (_is_dynamic, asym) -> 
        let (sym,loc) = aunpack loc asym in
        let resources = recursively_owned_resources env sym in
        let env = remove_vars env resources in
        return (Normal [makeUA Unit], env)
     | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
        let (ct, _ct_loc) = aunpack loc a_ct in
        let (sym1,loc1) = aunpack loc asym1 in
        is_uninitialised_pointer loc1 env sym1 >>= begin function
         | true -> make_initial_store_type loc ct 
         | false -> make_store_type loc ct
        end >>= fun decl_typ ->
        let args = [aunpack loc asym1; aunpack loc asym2] in
        call_typ loc env decl_typ args >>= fun (rt, env) ->
        return (Normal rt, env)
     | M_Load (a_ct, asym, _mo) -> 
        let (ct, _ct_loc) = aunpack loc a_ct in
        let (sym,_) = aunpack loc asym in
        get_Avar loc env sym >>= fun bt ->
        begin match is_structfield bt with
        | Some access ->
           make_load_field_type loc ct access >>= fun decl_typ ->
           call_typ loc env decl_typ [aunpack loc asym] >>= fun (rt, env) ->
           return (Normal rt, env)
        | None ->
           make_load_type loc ct >>= fun decl_typ ->
           call_typ loc env decl_typ [aunpack loc asym] >>= fun (rt, env) ->
           return (Normal rt, env)
        end
     | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) -> 
        fail loc (Unsupported "todo: RMW")
     | M_Fence mo -> 
        fail loc (Unsupported "todo: Fence")
     | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) -> 
        fail loc (Unsupported "todo: CompareExchangeStrong")
     | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) -> 
        fail loc (Unsupported "todo: CompareExchangeWeak")
     | M_LinuxFence mo -> 
        fail loc (Unsupported "todo: LinuxFemce")
     | M_LinuxLoad (ct, sym1, mo) -> 
        fail loc (Unsupported "todo: LinuxLoad")
     | M_LinuxStore (ct, sym1, sym2, mo) -> 
        fail loc (Unsupported "todo: LinuxStore")
     | M_LinuxRMW (ct, sym1, sym2, mo) -> 
        fail loc (Unsupported "todo: LinuxRMW")
     end
  | M_Eskip -> 
     return (Normal [makeUA Unit], env)
  | M_Eccall (_a, asym, asd, asyms) ->
     fail loc (Unsupported "todo: Eccall")
  | M_Eproc _ ->
     fail loc (Unsupported "todo: Eproc")
  | M_Ebound (n, e) ->
     infer_expr loc env e
  | M_End _ ->
     fail loc (Unsupported "todo: End")
  | M_Esave _ ->
     fail loc (Unsupported "todo: Esave")
  | M_Erun _ ->
     fail loc (Unsupported "todo: Erun")
  | M_Ecase _ -> fail loc (Unreachable "Ecase in inferring position")
  | M_Elet _ -> fail loc (Unreachable "Elet in inferring position")
  | M_Eif _ -> fail loc (Unreachable "Eif in inferring position")
  | M_Ewseq _ -> fail loc (Unsupported "Ewseq in inferring position")
  | M_Esseq _ -> fail loc (Unsupported "Esseq in inferring position")
  end >>= fun (typ,env) ->

  debug_print 3 (blank 3 ^^ item "interred" (UU.pp_ut typ)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->
  return (typ,env)


let rec check_expr loc env (e : ('a,'bty) mu_expr) typ = 

  debug_print 1 (action "checking expression type") >>= fun () ->
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ)) >>= fun () ->
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) >>= fun () ->
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr e)) >>= fun () ->
  debug_print 1 PPrint.empty >>= fun () ->

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     check_base_type loc1 (Some sym1) (A t1) (A Bool) >>= fun () ->
     let then_constr = (Sym.fresh (), LC (S (sym1,Bool))) in
     let else_constr = (Sym.fresh (), LC (Not (S (sym1,Bool)))) in
     check_expr loc (add_Cvar env then_constr) e2 typ >>= fun _env ->
     check_expr loc (add_Cvar env else_constr) e3 typ
  | M_Ecase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat loc pat >>= fun (bindings, bt', ploc) ->
         check_base_type ploc None (A bt') (A bt) >>= fun () ->
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_expr loc env' pe typ
       ) pats_es >>= fun _ ->
     return env     
  | M_Epure pe -> 
     check_pexpr loc env pe typ
  | M_Elet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_expr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad >>= fun () ->
                     return env
        end
     | M_normal_pattern (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_expr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad >>= fun () -> 
                     return env
        end        
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor _)) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported "todo: ctor pattern")
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
        | Normal rt -> check_expr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad >>= fun () ->
                     return env
        end        
     | M_Pattern (annots, M_CaseCtor _) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported "todo: ctor pattern")
     end
  | M_Esave (_ret, args, body) ->
     fold_leftM (fun env (sym, (_, asym)) ->
         let (vsym,loc) = aunpack loc asym in
         get_Avar loc env vsym >>= fun bt ->
         return (add_Avar env (sym,bt))
       ) env args >>= fun env ->
     check_expr loc env body typ
  | _ ->
     infer_expr loc env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt -> subtype loc env rt typ
     | Bad bad -> ensure_bad_unreachable loc env bad >>= fun () ->
                  return env
     end
     





let check_proc loc fsym genv body ftyp = 
  debug_print 1 (h1 ("Checking procedure " ^ (pps (Sym.pp fsym)))) >>= fun () ->
  let env = with_fresh_local genv in
  let env = add_vars env ftyp.arguments in
  check_expr loc env body ftyp.return >>= fun _env ->
  debug_print 1 (!^(greenb "...checked ok")) >>= fun () ->
  return ()

let check_fun loc fsym genv body ftyp = 
  debug_print 1 (h1 ("Checking function " ^ (pps (Sym.pp fsym)))) >>= fun () ->
  let env = with_fresh_local genv in
  let env = add_vars env ftyp.arguments in
  check_pexpr loc env body ftyp.return >>= fun _env ->
  debug_print 1 (!^(greenb "...checked ok")) >>= fun () ->
  return ()


let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) =
  let forget = 
    filter_map (function {name; bound = A t} -> Some (name,t) | _ -> None) in
  let binding_of_core_base_type loc (sym,cbt) = 
    bt_of_core_base_type loc cbt >>= fun bt ->
    return (makeA sym bt)
  in
  let check_consistent loc ftyp args ret = 
    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    let _ = forget args in
    if BT.types_equal (forget ftyp.arguments) (forget args) &&
         BT.types_equal (forget ftyp.return) (forget [ret])
    then return ()
    else 
      let defn = {arguments = args; return = [ret]} in
      let err = 
        Printf.sprintf "Function definition inconsistent. Should be %s, is %s"
          (pps (FunctionTypes.pp ftyp)) (pps (FunctionTypes.pp defn))
      in
      fail loc (Generic_error !^err)
  in
  match fn with
  | M_Fun (ret, args, body) ->
     get_fun_decl Loc.unknown genv fsym  >>= fun decl ->
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
    let make_arg_t (msym,ct) = ctype loc (sym_or_fresh msym) (make_pointer_ctype ct) in
    let ret_name = Sym.fresh () in
    mapM make_arg_t args >>= fun args_types ->
    let arguments = concat args_types in
    ctype loc ret_name ret_ctype >>= fun ret ->
    let ftyp = {arguments; return = ret} in
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
     fail Loc.unknown (Unsupported "todo: union types")
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
