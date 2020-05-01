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


let debug_level = ref 0
let debug_print pp = Pp_tools.print_for_level !debug_level pp





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

end

open UU





(* TODO: plug in cosntraint solver *)
let constraint_holds env (LC c) = 
  true

let is_unreachable env =
  constraint_holds env (LC (Bool false))

let rec constraints_hold loc env = function
  | [] -> return ()
  | (n, t) :: constrs ->
     if constraint_holds env t 
     then constraints_hold loc env constrs
     else fail loc (Call_error (Unsat_constraint (n, t)))







(* infer base types of index terms *)
let rec infer_it loc env it = 
  match it with
  | Num _ -> return BT.Int
  | Bool _ -> return BT.Bool

  | Add (it,it')
  | Sub (it,it')
  | Mul (it,it')
  | Div (it,it')
  | Exp (it,it')
  | Rem_t (it,it')
  | Rem_f (it,it') ->
     check_it loc env it BT.Int >>
     check_it loc env it' BT.Int >>
     return BT.Int

  | EQ (it,it')
  | NE (it,it')
  | LT (it,it')
  | GT (it,it')
  | LE (it,it')
  | GE (it,it') ->
     check_it loc env it BT.Int >>
     check_it loc env it' BT.Int >>
     return BT.Bool

  | Null it ->
     check_it loc env it BT.Loc >>
     return BT.Bool

  | And (it,it')
  | Or (it,it') ->
     check_it loc env it BT.Int >>
     check_it loc env it' BT.Int >>
     return BT.Bool

  | Not it ->
     check_it loc env it BT.Bool >>
     return BT.Bool

  (* | List (it, its) ->
   *    infer_it loc env it >>= fun bt ->
   *    check_it loc env it bt >>
   *    return (List bt) *)

  | S sym ->
     tryM
       (get_Avar loc env sym)
       (get_Lvar loc env sym >>= fun (Base t) -> return t)


and check_it loc env it bt =
  infer_it loc env it >>= fun bt' ->
  if bt = bt' then return ()
  else fail loc (Illtyped_it it)

and check_its loc env its bt = 
  match its with
  | [] -> return ()
  | it :: its -> 
     check_it loc env it bt >>
     check_its loc env its bt









(* convert from other types *)

let bt_of_core_base_type loc cbt =
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
  | BTy_list bt -> fail loc (Unsupported "lists")
  | BTy_tuple bts -> 
     fail loc (Unsupported "tuples")
     (* mapM (bt_of_core_base_type loc) bts >>= fun bts ->
      * let nbts = List.map (fun bt -> (Sym.fresh (), bt)) bts in
      * return (Tuple nbts) *)
  | BTy_storable -> fail loc (Unsupported "BTy_storable")
  | BTy_ctype -> fail loc (Unsupported "ctype")



let integerType loc name it =
  integer_value_to_num loc (Impl_mem.min_ival it) >>= fun min ->
  integer_value_to_num loc (Impl_mem.max_ival it) >>= fun max ->
  let c = makeUC (LC ((S name %>= Num min) %& (S name %<= Num max))) in
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
     let r = makeUR (Points (S name, S pointee_name)) :: r in
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

  let open Binders in

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
       if constraint_holds env c2 
       then check env rt1 rt2'
       else fail loc (Return_error (Unsat_constraint (n2, c2)))
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
  let rt = [makeA name Loc; makeUR (Block (S name, Num size))] in
  let ftyp = FunctionTypes.F {arguments; return = rt} in
  return ftyp


let make_load_type loc ct : (FunctionTypes.t,'e) m = 
  let pointer_name = fresh () in
  ctype_aux loc (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
  let a = makeA pointer_name Loc in
  let l = makeL pointee_name (Base bt) :: l in
  let r = makeUR (Points (S pointer_name, S pointee_name)) :: r in
  let addr_argument = a :: l @ r @ c in
  let ret = makeA pointee_name bt :: r in
  let ftyp = FunctionTypes.F {arguments = addr_argument; return = ret} in
  return ftyp


let make_load_field_type loc ct access : (FunctionTypes.t,'e) m = 
  fail loc (Unsupported "make_load_field_type not implemented yet")

(* have to also allow for Block of bigger size potentially *)
let make_initial_store_type loc ct = 
  let pointer_name = fresh () in
  size_of_ctype loc ct >>= fun size ->
  let p = [makeA pointer_name Loc; makeUR (Block (S pointer_name, Num size))] in
  begin 
    ctype_aux loc (fresh ()) ct >>= fun ((value_name,bt),l,r,c) ->
    let value = makeA value_name bt :: l @ r @ c in
    let ret = makeUA Unit :: [makeUR (Points (S pointer_name, S value_name))] in
    return (value,ret)
  end >>= fun (value,ret) ->
  let ftyp = FunctionTypes.F {arguments = p @ value; return = ret} in
  return ftyp


let make_store_type loc ct : (FunctionTypes.t,'e) m = 
  let pointer_name = fresh () in
  ctype loc pointer_name (make_pointer_ctype ct) >>= fun address ->
  begin 
    ctype_aux loc (fresh ()) ct >>= fun ((value_name,bt),l,r,c) ->
    let value = makeA value_name bt :: l @ r @ c in
    let ret = makeUA Unit :: [makeUR (Points (S pointer_name, S value_name))] in
    return (value,ret)
  end >>= fun (value,ret) ->
  let ftyp = FunctionTypes.F {arguments = address @ value; return = ret} in
  return ftyp


let is_uninitialised_pointer loc env sym = 
  get_Avar loc env sym >>= fun bt ->
  get_owned_resource loc env sym >>= function
  | Some ((_, Block _),_) -> return (bt = Loc)
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
         check_base_type loc (Some sym) (A bt) (A t) >>
         return (Some t)
    ) mtyp aargs



let infer_object_value loc env ov =

  let name = fresh () in

  match ov with
  | M_OVinteger iv ->
     integer_value_to_num loc iv >>= fun i ->
     let t = makeA name Int in
     let constr = makeUC (LC (S name %= Num i)) in
     return [t; constr]
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       ( fun _cbt -> 
         return [makeA name Loc; makeUC (LC (Null (S name)))] )
       ( fun sym -> 
         fail loc (Unsupported "function pointers") )
       ( fun _prov loc ->
         return [makeA name Loc; makeUC (LC (S name %= Num loc))] )
       ( fun () -> fail loc (Unreachable "unspecified pointer value") )
  | M_OVarray items ->
     make_Aargs loc env items >>= fun args_bts ->
     check_Aargs_typ None args_bts >>
     return [makeA name Array]
  | M_OVstruct (sym, fields) ->
     fail loc (Unsupported "todo: struct")
  | M_OVunion _ -> 
     fail loc (Unsupported "todo: union types")

  | M_OVfloating iv ->
     fail loc (Unsupported "floats")

let infer_loaded_value loc env lv = 
  match lv with
 | M_LVspecified ov -> infer_object_value loc env ov


let infer_value loc env v : (Types.t,'e) m = 
  match v with
  | M_Vobject ov ->
     infer_object_value loc env ov
  | M_Vloaded lv ->
     infer_loaded_value loc env lv
  | M_Vunit ->
     return [makeUA Unit]
  | M_Vtrue ->
     let name = fresh () in
     return [makeA name Bool; makeUC (LC (S name))]
  | M_Vfalse -> 
     let name = fresh () in
     return [makeA name Bool; makeUC (LC (Not (S name)))]
  | M_Vlist (cbt, asyms) ->
     fail loc (Unsupported "lists")
  | M_Vtuple args ->
     fail loc (Unsupported "todo: tuples")
     (* make_Aargs loc env args >>= fun aargs ->
      * return (List.map (fun ((name,bt),_) -> makeA name bt) aargs) *)




let pp_unis unis = 
  let pp_entry (sym, {spec_name; spec; resolved}) =
    match resolved with
    | Some res -> 
       (typ (Sym.pp sym) (LS.pp spec)) ^^^ !^"resolved as" ^^^ (Sym.pp res)
    | None -> (typ (Sym.pp sym) (LS.pp spec)) ^^^ !^"unresolved"
  in
  pp_env_list None (SymMap.bindings unis) pp_entry



let call_typ loc_call env decl_typ args =

  let find_resolved env unis = 
    SymMap.foldM
      (fun usym ({spec_name : Sym.t; spec; resolved} as uni) (unresolved,substs) ->
        match resolved with
        | None ->
           return (SymMap.add usym uni unresolved, substs)
        | Some sym -> 
           let (LS.Base bt) = spec in
           check_it loc_call env (S sym) bt >>
           return (unresolved, (usym, sym) :: substs)
      ) unis (SymMap.empty, [])
  in

  let rec check_and_refine env args (F ftyp) unis constrs = 
    
    debug_print 2 (action "checking and refining function call type");
    debug_print 2 (blank 3 ^^ item "ftyp" (FunctionTypes.pp (F ftyp)));
    debug_print 2 (blank 3 ^^ item "args" (pp_env_list None args (fun (a,_) -> Sym.pp a)));
    debug_print 2 (blank 3 ^^ item "unis" (pp_unis unis));
    debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local));
    debug_print 2 PPrint.empty;


    match ftyp.arguments with
    | [] -> 
       begin match args with
       | [] -> 
          find_resolved env unis >>= fun (unresolved,substs) ->
          if not (SymMap.is_empty unresolved) then
            let (usym, {spec_name : Sym.t; spec; resolved}) =
              SymMap.find_first (fun _ -> true) unresolved in
            fail loc_call (Call_error (Unconstrained_l (spec_name,spec)))
          else
            let ret = 
              fold_left (fun ret (s, subst) -> Types.subst s subst ret)
                ftyp.return substs 
            in
            let constrs = 
              fold_left (fun constrs (s, subst) -> 
                  map (fun (n,lc) -> (n, LC.subst s subst lc)) constrs)
                 constrs substs
            in
            constraints_hold loc_call env constrs >>
              return (ret,env)
          
       | (sym,loc) :: args -> 
          get_Avar loc env sym >>= fun bt ->
          fail loc (Call_error (Surplus_A (sym, bt)))
       end

    | {name = n; bound =  A t} :: decl_args ->
       begin match args with
       | (sym,loc) :: args ->
          get_Avar loc env sym >>= fun t' ->
          if BT.type_equal t' t then 
            let ftyp = FunctionTypes.subst n sym (F {ftyp with arguments = decl_args}) in
            check_and_refine env args ftyp unis constrs
          else 
            let msm = Mismatch {mname = Some sym; has = A t'; expected = A t} in
            fail loc (Call_error msm)
       | [] ->
          fail loc_call (Call_error (Missing_A (n, t)))
       end

    | {name = n; bound = R t} :: decl_args -> 
       begin match RE.owner t with
       | None -> fail loc_call (Call_error (Missing_R (n, t)))
       | Some owner ->
          owned_resource loc_call env owner >>= begin function
          | None -> fail loc_call (Call_error (Missing_R (n, t)))
          | Some sym -> 
             get_Rvar loc_call env sym >>= fun (t',env) ->
             tryM (RE.unify t t' unis)
               (let err = Mismatch {mname = Some sym; has = R t'; expected = R t} in
                fail loc_call (Call_error err)) >>= fun unis ->
             let ftyp = FunctionTypes.subst n sym (F {ftyp with arguments = decl_args}) in
             find_resolved env unis >>= fun (_,substs) ->
             let ftyp = fold_left (fun f (s, s') -> FunctionTypes.subst s s' f) ftyp substs in
             check_and_refine env args ftyp unis constrs
         end
       end

    | {name = n; bound = L t} :: decl_args -> 
       let sym = Sym.fresh () in
       let uni = { spec_name = n; spec = t; resolved = None } in
       let unis' = SymMap.add sym uni unis in
       let ftyp' = FunctionTypes.subst n sym (F {ftyp with arguments = decl_args}) in
       check_and_refine env args ftyp' unis' constrs

    | {name = n; bound = C t} :: decl_args ->        
       let constrs' = (constrs @ [(n, t)]) in
       check_and_refine env args (F {ftyp with arguments = decl_args}) unis constrs'

  in

  check_and_refine env args decl_typ SymMap.empty []


let infer_ctor loc ctor (aargs : aargs) = 
  match ctor with
  | M_Ctuple -> 
     fail loc (Unsupported "tuples")
     (* return (List.map (fun ((name,bt),_) -> makeA name bt) aargs) *)
  | M_Carray -> 
     check_Aargs_typ None aargs >> 
     return [{name = fresh (); bound = A Array}]
  | M_CivCOMPL
  | M_CivAND
  | M_CivOR
  | M_CivXOR -> 
     fail loc (Unsupported "todo: Civ..")
  | M_Cspecified ->
    begin match aargs with
    | [((name,bt),_)] -> 
       return [{name; bound = A bt}]
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

     
let infer_pat loc pat = 
  fail loc (Unsupported "todo: implement infer_pat")



(* todo: replace with call_typ *)
let make_binop_constr op (v1 : IT.t) (v2 : IT.t) =
  let open Core in
  match op with
  | OpAdd -> Add (v1, v2)
  | OpSub -> Sub (v1, v2)
  | OpMul -> Mul (v1, v2)
  | OpDiv -> Div (v1, v2) 
  | OpRem_t -> Rem_t (v1, v2)
  | OpRem_f -> Rem_f (v1, v2)
  | OpExp -> Exp (v1, v2)
  | OpEq -> EQ (v1, v2)
  | OpGt -> GT (v1, v2)
  | OpLt -> LT (v1, v2)
  | OpGe -> GE (v1, v2)
  | OpLe -> LE (v1, v2)
  | OpAnd -> And (v1, v2)
  | OpOr -> Or (v1, v2)


let binop_type op = 
  let open Core in
  let a1, a2, ar = fresh (), fresh (), fresh () in
  let constr = LC (S ar %= (make_binop_constr op (S a1) (S a2))) in
  let at, rt = match op with
    | OpAdd
    | OpSub
    | OpMul
    | OpDiv
    | OpRem_t
    | OpRem_f
    | OpExp -> ([makeA a1 Int; makeA a2 Int], [makeA ar Int; makeUC constr])
    | OpEq
    | OpGt
    | OpLt
    | OpGe
    | OpLe -> ([makeA a1 Int; makeA a2 Int], [makeA ar Bool; makeUC constr])
    | OpAnd
    | OpOr -> ([makeA a1 Bool; makeA a2 Bool], [makeA ar Bool; makeUC constr])
  in
  F {arguments = at; return = rt}
  



let ensure_bad_unreachable env bad = 
  if is_unreachable env then return () else 
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

  debug_print 1 (action "inferring pure expression type");
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local));
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pe));
  debug_print 1 PPrint.empty;

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in
  match pe_ with
  | M_PEsym sym ->
     get_Avar loc env sym >>= fun bt ->
     recursively_owned_resources loc env sym >>= fun resource_names ->
     get_vars loc env resource_names >>= fun (resources,env) ->
     let constraints = List.map snd (constraints_about env sym) in
     let new_constraints = map makeUC constraints in
     let typ = makeA sym bt::List.map makeU resources@new_constraints in
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
     let ret = [makeA ar Bool; makeUC (LC (S ar %= Not (S a)))] in
     let decl_typ = F {arguments = [makeA a Bool]; return = ret} in
     call_typ loc env decl_typ [aunpack loc asym] >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_PEop (op,asym1,asym2) ->
     let decl_typ = binop_type op in
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


let rec check_pexpr loc env (e : 'bty mu_pexpr) typ = 

  debug_print 1 (action "checking pure expression type");
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ));
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local));
  debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr e));
  debug_print 1 PPrint.empty;


  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_PEif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     check_base_type loc1 (Some sym1) (A t1) (A Bool) >>
     check_pexpr loc (add_var env (makeUC (LC (S sym1 %= Bool true)))) e2 typ >>
     check_pexpr loc (add_var env (makeUC (LC (S sym1 %= Bool true)))) e3 typ
  | M_PEcase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat loc pat >>= fun (bindings, bt', ploc) ->
         check_base_type ploc None (A bt') (A bt) >>
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_pexpr loc env' pe typ
       ) pats_es >>
     return env
  | M_PElet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (annots, _, newname)) ->
        let loc = update_loc loc annots in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_pexpr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable env bad >> return env
        end
     | M_normal_pattern (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_pexpr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable env bad >> return env
        end        
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor _)) ->
        let _loc = update_loc loc annots in
        fail loc (Unsupported "todo: ctor pattern")
     end
  | _ ->
     infer_pexpr loc env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt -> subtype loc env rt typ
     | Bad bad -> ensure_bad_unreachable env bad >> return env
     end        



let rec infer_expr loc env (e : ('a,'bty) mu_expr) = 

  debug_print 1 (action "inferring expression type");
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local));
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr e));
  debug_print 1 PPrint.empty;

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
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
        let constr = LC (S ret_name %= Bool true) in
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
        recursively_owned_resources loc env sym >>= fun resources ->
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


let rec check_expr loc env (e : ('a,'bty) mu_expr) typ = 

  debug_print 1 (action "checking expression type");
  debug_print 1 (blank 3 ^^ item "type" (Types.pp typ));
  debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local));
  debug_print 3 (blank 3 ^^ item "expression" (pp_expr e));
  debug_print 1 PPrint.empty;

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = aunpack loc asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     check_base_type loc1 (Some sym1) (A t1) (A Bool) >>
     let then_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     let else_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     check_expr loc (add_Cvar env then_constr) e2 typ >>
     check_expr loc (add_Cvar env else_constr) e3 typ
  | M_Ecase (asym, pats_es) ->
     let (esym,eloc) = aunpack loc asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat loc pat >>= fun (bindings, bt', ploc) ->
         check_base_type ploc None (A bt') (A bt) >>
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_expr loc env' pe typ
       ) pats_es >>
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
        | Bad bad -> ensure_bad_unreachable env bad >> return env
        end
     | M_normal_pattern (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_normal_pattern (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        infer_pexpr loc env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_expr loc (add_vars env (rename newname rt)) e2 typ
        | Bad bad -> ensure_bad_unreachable env bad >> return env
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
        | Bad bad -> ensure_bad_unreachable env bad >> return env
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
     | Bad bad -> ensure_bad_unreachable env bad >> return env
     end
     





let check_proc loc fsym genv body (F decl_typ) = 
  debug_print 1 (h1 ("Checking procedure " ^ (pps (Sym.pp fsym))));
  let env = with_fresh_local genv in
  let env = add_vars env decl_typ.arguments in
  check_expr loc env body decl_typ.return >>= fun _env ->
  debug_print 1 (!^(good "...checked ok"));
  return ()

let check_fun loc fsym genv body (F decl_typ) = 
  debug_print 1 (h1 ("Checking function " ^ (pps (Sym.pp fsym))));
  let env = with_fresh_local genv in
  let env = add_vars env decl_typ.arguments in
  check_pexpr loc env body decl_typ.return >>= fun _env ->
  debug_print 1 (!^(good "...checked ok"));
  return ()


let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) =
  let forget = 
    filter_map (function {name; bound = A t} -> Some (name,t) | _ -> None) in
  let binding_of_core_base_type loc (sym,cbt) = 
    bt_of_core_base_type loc cbt >>= fun bt ->
    return (makeA sym bt)
  in
  let check_consistent loc decl args ret = 
    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    let (F decl_typ) = decl in
    let _ = forget args in
    if BT.types_equal (forget decl_typ.arguments) (forget args) &&
         BT.types_equal (forget decl_typ.return) (forget [ret])
    then return ()
    else 
      let defn = F {arguments = args; return = [ret]} in
      let err = 
        Printf.sprintf "Function definition inconsistent. Should be %s, is %s"
          (pps (FunctionTypes.pp decl)) (pps (FunctionTypes.pp defn))
      in
      fail loc (Generic_error !^err)
  in
  match fn with
  | M_Fun (ret, args, body) ->
     get_fun_decl Loc.unknown genv fsym  >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_fun loc fsym genv body decl_typ
  | M_Proc (loc, ret, args, body) ->
     get_fun_decl loc genv fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_proc loc fsym genv body decl_typ
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
    let ft = F {arguments; return = ret} in
    return (add_fun_decl genv sym (loc, ft, ret_name))

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
     let decl_typ = F {arguments = args_ts; return = [makeUA bt]} in
     return (add_impl_fun_decl genv impl decl_typ)
                        


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
  debug_print 1 (h1 "initial environment");
  debug_print 1 (Global.pp genv)


let check mu_file =
  pp_fun_map_decl mu_file.mu_funinfo;
  let genv = Global.empty in
  record_tagDefs genv mu_file.mu_tagDefs >>= fun genv ->
  record_funinfo genv mu_file.mu_funinfo >>= fun genv ->
  print_initial_environment genv;
  check_functions genv mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception (loc,err) -> 
     report_type_error loc err;
     raise (Failure "type error")
