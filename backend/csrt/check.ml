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
open ReturnTypes


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
module RT = ReturnTypes
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




let bind_and_anames env rt = 
  let rec aux acc_names env = function
    | Computational (name,bound,t) ->
       let newname = fresh () in
       aux 
         (acc_names @ [newname])
         (add_Avar env (newname,bound)) 
         (subst_var {substitute=name; swith=newname} t)
    | Logical (name,bound,t) ->
       let newname = fresh () in
       aux
         acc_names
         (add_Lvar env (newname,bound)) 
         (subst_var {substitute=name; swith=newname} t)
    | Resource (bound,t) ->
       aux acc_names (add_URvar env bound) t
    | Constraint (bound,t) ->
       aux acc_names (add_UCvar env bound) t
    | I -> 
       (acc_names,env)
  in
  aux [] env rt

let bind env rt = snd (bind_and_anames env rt)


let rec bind_to_name env given_name = function
  | Computational (name,bound,t) ->
     bind (add_Avar env (given_name,bound))
       (subst_var {substitute=name; swith=given_name} t)
  | Logical (name,bound,t) ->
     let newname = fresh () in
     bind_to_name (add_Lvar env (newname,bound)) given_name 
       (subst_var {substitute=name; swith=newname} t)
  | Resource (bound,t) ->
     bind_to_name (add_URvar env bound) given_name t
  | Constraint (bound,t) ->
     bind_to_name (add_UCvar env bound) given_name t
  | I -> 
     env
     





(* types recording undefined behaviour, error cases, etc. *)
module UU = struct

  type u = 
   | Undefined of Loc.t * CF.Undefined.undefined_behaviour
   | Unspecified of Loc.t (* * Ctype.ctype *)
   | StaticError of Loc.t * (string * Sym.t)

  type 'a or_u = 
    | Normal of 'a
    | Bad of u

  type ut = RT.t or_u

  let pp_ut = function
    | Normal t -> RT.pp t
    | Bad u -> !^"bad"

end

open UU







let vars_equal_to loc env sym ls = 
  let* () = debug_print 4 (blank 3 ^^ !^"vars_equal_to" ^^^ Sym.pp sym) in
  let* () = debug_print 4 (blank 3 ^^ item "env" (Local.pp env.local)) in
  let similar = 
    filter_vars (fun sym' t -> 
      match t with 
      | A bt' -> sym <> sym' && LS.type_equal ls (LS.Base bt')
      | L ls' -> sym <> sym' && LS.type_equal ls ls'
      | _ -> false
    ) env 
  in

  let* () = debug_print 4 (blank 3 ^^ item "similar" (pp_list Sym.pp similar)) in

  filter_mapM (fun sym' -> 
      let c = LC (S sym %= S sym') in
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
  return (LC ((Num min %<= S about) %& (S about %<= Num max)))

let integerType loc name it =
  let* constr = integerType_constraint loc name it in
  return ((name,Int), constr)

let floatingType loc =
  fail loc (Unsupported !^"floats")



let rec ctype_aux owned loc name (CF.Ctype.Ctype (annots, ct_)) =
  let open RT in
  let loc = update_loc loc annots in
  match ct_ with
  | Void -> 
     return ((name, BT.Unit), I)
  | Basic (Integer it) -> 
     let* ((name,bt), constr) = integerType loc name it in
     return ((name, bt), Constraint (constr, I))
  | Array (ct, _maybe_integer) -> 
     return ((name,BT.Array), I)
  | Pointer (_qualifiers, ct) ->
     if owned then
       let* ((pointee_name,bt),t) = ctype_aux owned loc (fresh ()) ct in
       let* size = Memory.size_of_ctype loc ct in
       let points = Points {pointer = name; pointee = Some pointee_name; 
                            typ = ct; size} in
       let t = Logical (pointee_name, Base bt, Resource (points, t)) in
       return ((name,Loc),t)
     else
       return ((name,Loc),I)
  (* fix *)
  | Atomic ct -> ctype_aux owned loc name ct
  | Struct sym -> return ((name, ClosedStruct (Tag sym)),I)
  | Basic (Floating _) -> floatingType loc 
  | Union sym -> fail loc (Unsupported !^"todo: union types")
  | Function _ -> fail loc (Unsupported !^"function pointers")



let ctype owned loc (name : Sym.t) (ct : CF.Ctype.ctype) =
  let* ((name,bt),t) = ctype_aux owned loc name ct in
  return (Computational (name,bt,t))

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


type aargs = ((Sym.t * BT.t) * Loc.t) list

let pp_aargs =
  pp_list (fun ((n,t),(_l:Loc.t)) -> typ (Sym.pp n) (BT.pp false t))


let rec aargs_from_anames_locs loc env names_locs = 
  match names_locs with
  | [] -> return ([], env)
  | (name,loc) :: names_locs ->
     let* (t,env) = get_Avar loc env name in
     let* (rest,env) = aargs_from_anames_locs loc env names_locs in
     return (((name,t), loc) :: rest, env)

let aargs loc env asyms = 
  aargs_from_anames_locs loc env (List.map (aunpack loc) asyms)


let aargs_and_bind_rt loc env rt = 
  let (anames,env) = bind_and_anames env rt in
  aargs_from_anames_locs loc env (map (fun n -> (n,loc)) anames)




let resources_associated_with_var_or_equals loc env owner =
  let* (bt,_env) = get_ALvar loc env owner in
  let* equal_to_owner = vars_equal_to loc env owner (Base bt) in
  let* () = debug_print 3 (blank 3 ^^ !^"equal to" ^^^ Sym.pp owner ^^ colon ^^^
                             pp_list Sym.pp equal_to_owner) in
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
  fold_leftM (fun mt ((sym,bt),loc) ->
      match mt with
      | None -> 
         return (Some bt)
      | Some t -> 
         let* () = check_base_type loc (Some sym) bt t in
         return (Some t)
    ) mtyp aargs


let pp_unis unis = 
  let pp_entry (sym, Uni.{resolved}) =
    match resolved with
    | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ (Sym.pp res)
    | None -> Sym.pp sym ^^^ !^"unresolved"
  in
  pp_list pp_entry (SymMap.bindings unis)





  





let ensure_unis_resolved loc env unis =
  let (unresolved,resolved) = Uni.find_resolved env unis in
  match unresolved with
  | [] -> return resolved
  | usym :: _ -> fail loc (Call_error (Unconstrained_l usym))




(* TODO: remove all the Ctype auxiliary things *)
let rec unpack_struct logical loc genv tag = 
  let* () = debug_print 2 (blank 3 ^^ (!^"unpacking struct")) in
  let* decl = Global.get_struct_decl loc genv tag in
  let rec aux acc_bindings acc_fields (fields : RT.t) =
    match fields with
    | I -> 
       return (acc_bindings, acc_fields)
    | Computational (lname, ClosedStruct tag2, fields) ->
       let* (Member id) = Tools.rassoc_err loc lname decl.fnames "unpack_struct" in
       let* ((newsym,bt),newbindings) = unpack_struct logical loc genv tag2 in
       let acc_fields = acc_fields @ [(Member id, newsym)] in
       let acc_bindings = 
         if logical then acc_bindings @@ newbindings @@ Logical (newsym, Base bt, I)
         else acc_bindings @@ newbindings @@ Computational (newsym, bt, I)
       in
       let fields = RT.subst_var {substitute=lname;swith=newsym} fields in
       aux acc_bindings acc_fields fields
    | Logical (lname, Base (ClosedStruct tag2), fields) ->
       let* ((newsym,bt),newbindings) = unpack_struct true loc genv tag2 in
       let acc_bindings = acc_bindings @@ newbindings @@ Logical (newsym, Base bt, I) in
       let fields = RT.subst_var {substitute=lname;swith=newsym} fields in
       aux acc_bindings acc_fields fields
    | Computational (lname,bt,fields) ->
       let* (Member id) = Tools.rassoc_err loc lname decl.fnames "unpack_struct" in
       let newsym = fresh () in
       let acc_bindings = 
         if logical then acc_bindings @@ Logical (newsym, Base bt, I)
         else acc_bindings @@ Computational (newsym, bt, I) 
       in
       let acc_fields = acc_fields @ [(Member id, newsym)] in
       let fields = RT.subst_var {substitute=lname;swith=newsym} fields in
       aux acc_bindings acc_fields fields
    | Logical (lname,bound,fields) ->
       let newsym = fresh () in
       let acc_bindings = acc_bindings @@ Logical (newsym,bound,I) in
       let fields = RT.subst_var {substitute=lname;swith=newsym} fields in
       aux acc_bindings acc_fields fields
    | Resource (bound,fields) ->
       let acc_bindings = acc_bindings @@ Resource (bound,I) in
       aux acc_bindings acc_fields fields
    | Constraint (bound, fields) ->
       let acc_bindings = acc_bindings @@ Constraint (bound, I) in
       aux acc_bindings acc_fields fields
  in
  let* (bindings, fields) = aux I [] decl.typ in
  let* size = Memory.size_of_struct_type loc tag in
  return ((fresh (), OpenStruct (tag, fields)),bindings)




let rec unpack_structs loc genv bindings = 
  match bindings with
  | Computational (name, ClosedStruct typ, bindings) ->
     let* ((newname,bt),newbindings) = unpack_struct false loc genv typ in
     let subst = {substitute=name;swith=newname} in
     let* bindings' = unpack_structs loc genv (subst_var subst bindings) in
     return (newbindings @@ (Computational (newname, bt, bindings')))
  | Logical (name, Base (ClosedStruct typ), bindings) ->
     let* ((newname,bt),newbindings) = unpack_struct true loc genv typ in
     let subst = {substitute=name;swith= newname} in
     let* bindings' = unpack_structs loc genv (subst_var subst bindings) in
     return (newbindings @@ (Logical (newname, Base bt, bindings')))
  | Computational (name, bound, bindings) ->
     let* bindings' = unpack_structs loc genv bindings in
     return (Computational (name, bound, bindings'))
  | Logical (name, bound, bindings) ->
     let* bindings' = unpack_structs loc genv bindings in
     return (Logical (name, bound, bindings'))
  | Resource (bound, bindings) ->
     let* bindings' = unpack_structs loc genv bindings in
     return (Resource (bound, bindings'))
  | Constraint (bound, bindings) ->
     let* bindings' = unpack_structs loc genv bindings in
     return (Constraint (bound, bindings'))
  | I -> 
     return I


let open_struct_to_stored_struct loc genv tag fieldmap = 
  let* decl = get_struct_decl loc genv tag in
  let* (addr_fieldmap,bindings) =
    fold_leftM (fun (fieldmap,bindings) (field,fval) ->
        let* ct = assoc_err loc field decl.ctypes "check store field access" in
        let faddr = fresh () in
        let fieldmap = fieldmap@[(field,faddr)] in
        let* size = Memory.size_of_ctype loc ct in
        let points = Points {pointer=faddr;pointee=Some fval;typ=ct;size} in
        let bindings = bindings @@ Logical (faddr, Base Loc, Resource (points, I)) in
        return (fieldmap, bindings)
      )
      ([],I) fieldmap
  in
  return ((tag,addr_fieldmap), bindings)





let unpack_and_store_structs loc genv bindings = 
  let* bindings = unpack_structs loc genv bindings in
  let rec aux acc_bindings loc genv bindings = 
    match bindings with
    | Logical (name, Base (OpenStruct (tag,fieldmap)), bindings) ->
       let* ((tag,fieldmap),newbindings) =
         open_struct_to_stored_struct loc genv tag fieldmap in
       let acc_bindings = acc_bindings @@ newbindings @@ Logical (name, Base (StoredStruct (tag,fieldmap)), I) in
       aux acc_bindings loc genv bindings 
    | Computational (name, bound, bindings) ->
       let acc_bindings = acc_bindings@@ Computational (name, bound, I) in
       aux acc_bindings loc genv bindings
    | Logical (name, bound, bindings) ->
       let acc_bindings = acc_bindings@@ Logical (name, bound, I) in
       aux acc_bindings loc genv bindings
    | Resource (bound, bindings) ->
       let acc_bindings = acc_bindings@@ Resource (bound, I) in
       aux acc_bindings loc genv bindings
    | Constraint (bound, bindings) ->
       let acc_bindings = acc_bindings@@ Constraint (bound, I) in
       aux acc_bindings loc genv bindings
    | I -> 
       return acc_bindings
  in
  aux I loc genv bindings












let rec remove_subtree loc env pointer =
  let* does_point = points_to loc env pointer in
  match does_point with
  | Some (r,{pointee=Some pointee; _}) -> 
     let* (bt, env) = get_ALvar loc env pointee in
     let env = remove_var env r in
     begin match bt with
       | StoredStruct (tag,fieldmap) ->
          let rec aux env = function
            | (field, faddr) :: fields -> 
               let* env = remove_subtree loc env faddr in
               aux env fields
            | [] -> return env
          in
          aux env fieldmap
       | _ -> return env
     end
  | Some (r,{pointee=None; _}) -> 
     return (remove_var env r)
  | _ -> 
     return env





let stored_struct_to_open_struct remove_ownership loc env tag fieldmap =
  let rec aux env acc_vals = function
    | (field, faddr) :: fields ->
       let* (Base bt,env) = get_Lvar loc env faddr in
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




type subtype_spec = 
  { typ: RT.t; 
    lvars: (Sym.t * LS.t) list;
    constraints : LC.t list }

let rec lvar_subst_var s = function
  | [] -> []
  | (name,t) :: lvars -> 
     (name, LS.subst_var s t) :: lvar_subst_var s lvars

let constraints_subst_var s = List.map (LC.subst_var s) 

let subtype_spec_subst_var s spec = 
  { typ = RT.subst_var s spec.typ;
    lvars = lvar_subst_var s spec.lvars;
    constraints = constraints_subst_var s spec.constraints }

let subtype_spec_subst_vars = Subst.make_substs subtype_spec_subst_var



let rec subtype loc_ret env (args : aargs) (rtyp : RT.t) ppdescr =

  let* () = debug_print 1 (action ppdescr) in
  let* () = debug_print 2 PPrint.empty in

  (* let* (args,env) = pack_structs_aargs loc_ret env args in *)

  let rec aux env args unis spec = 
    let* () = debug_print 2 (blank 3 ^^ item "value" (pp_aargs args)) in
    let* () = debug_print 2 (blank 3 ^^ item "specification" (RT.pp spec.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
    match args, spec.typ with
    | [], I -> 
       begin match spec.lvars with
       | [] -> 
          let* () = Solver.check_constraints_hold loc_ret env spec.constraints in
          return env
       | (sname,sls) :: lvars ->
          match SymMap.find_opt sname unis with
          | Some Uni.{resolved = None} -> 
             fail loc_ret (Call_error (Unconstrained_l sname))
          | Some Uni.{resolved = Some aname} ->
             let* (abt,env) = get_ALvar loc_ret env aname in
             let* ((aname,abt),env) = pack_if_struct_aarg loc_ret env (aname,abt) in
             if LS.type_equal (LS.Base abt) sls then
               let spec = { spec with lvars } in
               let spec = subtype_spec_subst_var {substitute=sname;swith=aname} spec in
               aux env args unis spec
             else
               let msm = Mismatch {mname = Some aname; has = L (LS.Base abt); expected = L sls} in
               fail loc_ret (Return_error msm)
          | None ->
             fail loc_ret (Unreachable !^"did not find unification variable")
       end
    | [], Computational (sname,sbt,_) -> 
       fail loc_ret (Return_error (Missing_A (sname, sbt)))
    | ((aname,abt),loc) :: _, I -> 
       fail loc (Return_error (Surplus_A (aname, abt)))
    | ((aname,abt),arg_loc) :: args, Computational (sname,sbt,rtyp) ->
       let* ((aname,abt),env) = pack_if_struct_aarg arg_loc env (aname,abt) in
       if BT.type_equal abt sbt then
         let spec = { spec with typ = rtyp} in
         let spec = (subtype_spec_subst_var {substitute=sname;swith=aname} spec) in
         let env = match abt with 
           | ClosedStruct _ -> env 
           | _ -> add_Avar env (aname,abt)
         in
         aux env args unis spec
       else
         let msm = Mismatch {mname = Some aname; has = A abt; expected = A sbt} in
         fail loc_ret (Return_error msm)
    | _, Logical (sname,sls,rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = { spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp} in
       let spec = subtype_spec_subst_var {substitute=sname;swith=sym} spec in
       aux env args unis spec
    | _, Resource (re,rtyp) -> 
       let* owneds = resources_associated_with_var_or_equals loc_ret env (RE.associated re) in
       let rec try_resources = function
         | [] -> 
            fail loc_ret (Return_error (Missing_R re))
         | (o,r) :: owned_resources ->
            let* (resource',env) = get_Rvar loc_ret env r in
            let resource' = RE.subst_var {substitute=o; swith=RE.associated re} resource' in
            let* () = debug_print 3 (action ("trying resource " ^ plain (RE.pp false resource'))) in
            match RE.unify re resource' unis with
            | None -> try_resources owned_resources
            | Some unis ->
               let (_,new_substs) = Uni.find_resolved env unis in
               let spec = { spec with typ = rtyp } in
               let spec = subtype_spec_subst_vars new_substs spec in
               aux env args unis spec
       in
       try_resources owneds
    | _, Constraint (constr,rtyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = rtyp} in
       aux env args unis spec  
  in

  aux env args SymMap.empty { typ = rtyp ; lvars = []; constraints = []}






(* use Neel's resource map and use pack_struct to package the aargs
   part of a struct and *as many resources* of the struct definition
   as possible *)
and pack_struct loc env typ aargs = 
  let* decl = get_struct_decl loc env.global typ in
  let* env = subtype loc env aargs decl.typ "packing struct" in
  return ((fresh (), ClosedStruct typ), env)

and pack_open_struct loc env tag fieldmap =
  let arg_syms = List.map snd fieldmap in
  let* (arg_typs,env) = get_ALvars loc env arg_syms in
  let args = List.combine arg_syms arg_typs in
  let aargs = List.map (fun b -> (b,loc)) args in
  pack_struct loc env tag aargs

and pack_if_struct_aarg loc env (name,bt) = 
  match bt with
  | OpenStruct (tag,fieldmap) ->
     pack_open_struct loc env tag fieldmap
  | StoredStruct (tag,fieldmap) ->
     let* ((tag,fieldmap),env) = 
       stored_struct_to_open_struct true loc env tag fieldmap in
     pack_open_struct loc env tag fieldmap
  | _ -> return ((name,bt),env)

and pack_if_struct_larg loc env (name, LS.Base bt) =
  let* ((name,bt),env) = pack_if_struct_aarg loc env (name,bt) in
  return ((name, LS.Base bt), env)

and pack_structs_aargs loc env (args : aargs) =
  fold_leftM (fun (acc_args,env) (arg,loc) -> 
      let* (arg,env) = pack_if_struct_aarg loc env arg in
      return (acc_args@[(arg,loc)],env)
    ) ([],env) args

and pack_structs_largs loc env largs =
  fold_leftM (fun (acc_args,env) arg -> 
      let* (arg,env) = pack_if_struct_larg loc env arg in
      return (acc_args@[arg],env)
    ) ([],env) largs




type calltyp_spec = 
  { typ: FT.t; 
    lvars: (Sym.t * LS.t) list;
    constraints : LC.t list }

let calltyp_spec_subst_var s spec = 
  { typ = FT.subst_var s spec.typ;
    lvars = lvar_subst_var s spec.lvars;
    constraints = constraints_subst_var s spec.constraints }

let calltyp_spec_subst_vars = 
  Subst.make_substs calltyp_spec_subst_var


let calltyp loc_ret env (args : aargs) (rtyp : FT.t) =

  let open FT in

  let* () = debug_print 1 (action "function call type") in
  let* () = debug_print 2 PPrint.empty in

  (* let* (args,env) = pack_structs_aargs loc_ret env args in *)

  let rec aux env args unis (spec : calltyp_spec) = 
    let* () = debug_print 2 (blank 3 ^^ item "arguments" (pp_aargs args)) in
    let* () = debug_print 2 (blank 3 ^^ item "specification" (FT.pp spec.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
    match args, spec.typ with
    | [], Return rt -> 
       begin match spec.lvars with
       | [] -> 
          let* () = Solver.check_constraints_hold loc_ret env spec.constraints in
          return (rt,env)
       | (sname,sls) :: lvars ->
          match SymMap.find_opt sname unis with
          | Some Uni.{resolved = None} -> 
             fail loc_ret (Call_error (Unconstrained_l sname))
          | Some Uni.{resolved = Some aname} ->
             let* (abt,env) = get_ALvar loc_ret env aname in
             let* ((aname,abt),env) = pack_if_struct_aarg loc_ret env (aname,abt) in
             if LS.type_equal (LS.Base abt) sls then
               let spec = { spec with lvars } in
               let spec = calltyp_spec_subst_var {substitute=sname;swith=aname} spec in
               aux env args unis spec
             else
               let msm = Mismatch {mname = Some aname; has = L (LS.Base abt); expected = L sls} in
               fail loc_ret (Return_error msm)
          | None ->
             fail loc_ret (Unreachable !^"did not find unification variable")
       end
    | [], Computational (sname,sbt,_) -> 
       fail loc_ret (Return_error (Missing_A (sname, sbt)))
    | ((aname,abt),loc) :: _, Return _ -> 
       fail loc (Return_error (Surplus_A (aname, abt)))
    | ((aname,abt),arg_loc) :: args, Computational (sname,sbt,rtyp) ->
       let* ((aname,abt),env) = pack_if_struct_aarg arg_loc env (aname,abt) in
       if BT.type_equal abt sbt then
         let spec = { spec with typ = rtyp} in
         let spec = (calltyp_spec_subst_var {substitute=sname;swith=aname} spec) in
         aux env args unis spec
       else
         let msm = Mismatch {mname = Some aname; has = A abt; expected = A sbt} in
         fail loc_ret (Return_error msm)
    | _, Logical (sname,sls,rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = { spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp} in
       let spec = calltyp_spec_subst_var {substitute=sname;swith=sym} spec in
       aux env args unis spec
    | _, Resource (re,rtyp) -> 
       let* owneds = resources_associated_with_var_or_equals loc_ret env (RE.associated re) in
       let rec try_resources = function
         | [] -> 
            fail loc_ret (Return_error (Missing_R re))
         | (o,r) :: owned_resources ->
            let* (resource',env) = get_Rvar loc_ret env r in
            let resource' = RE.subst_var {substitute=o; swith=RE.associated re} resource' in
            let* () = debug_print 3 (action ("trying resource " ^ plain (RE.pp false resource'))) in
            match RE.unify re resource' unis with
            | None -> try_resources owned_resources
            | Some unis ->
               let (_,new_substs) = Uni.find_resolved env unis in
               let spec = { spec with typ = rtyp } in
               let spec = calltyp_spec_subst_vars new_substs spec in
               aux env args unis spec
       in
       try_resources owneds
    | _, Constraint (constr,rtyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = rtyp} in
       aux env args unis spec  
  in

  aux env args SymMap.empty { typ = rtyp ; lvars = []; constraints = []}




let tuple_constr (name,bt) aargs = 
  let rec aux i = function
    | [] -> IT.Bool true
    | ((ni,ti),_) :: rest ->
       let constr = aux (i+1) rest in
       Nth (Num.of_int i, S name %= S ni) %& constr
  in
  LC (aux 0 aargs)


let infer_ctor loc ctor (aargs : aargs) = 
  match ctor with
  | M_Ctuple -> 
     let name = fresh () in
     let bts = fold_left (fun bts ((_,b),_) -> bts @ [b]) [] aargs in
     let bt = Tuple bts in
     let constr = tuple_constr (name,bt) aargs in
     return (Computational (name, bt, Constraint (constr, I)))
  | M_Carray -> 
     let* _ = check_Aargs_typ None aargs in
     return (Computational (fresh (), Array, I))
  | M_CivCOMPL
  | M_CivAND
  | M_CivOR
  | M_CivXOR -> 
     fail loc (Unsupported !^"todo: Civ..")
  | M_Cspecified ->
     let name = fresh () in
     begin match aargs with
     | [((sym,bt),_)] -> 
        return (Computational (name, bt, Constraint (LC (S sym %= S name),I)))
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
let make_fun_arg_type asym loc ct =

  let ct = make_pointer_ctype ct in

  let rec aux (aname,rname) (CF.Ctype.Ctype (annots, ct_)) =
    match ct_ with
    | Void -> 
       let arg = (BT.Unit, fun ft -> ft) in
       let ret = (BT.Unit, fun rt -> rt) in
       return (arg,ret)
    | Basic (Integer it) -> 
       let* ((_,abt), aconstr) = integerType loc aname it in
       let* ((_,rbt), rconstr) = integerType loc rname it in
       let arg = (abt, FT.mconstraint aconstr) in
       let ret = (rbt, RT.mconstraint rconstr) in
       return (arg, ret)
    | Array (ct, _maybe_integer) ->
       let arg = (Array, fun ft -> ft) in
       let ret = (Array, fun ft -> ft) in
       return (arg, ret)
    | Pointer (_qualifiers, ct) ->
       let aname2 = fresh () in
       let rname2 = fresh () in
       let* ((abt,ftt),(rbt,rtt)) = aux (aname2,rname2) ct in
       let* size = Memory.size_of_ctype loc ct in
       let arg = 
         let apoints = Points {pointer = aname; pointee = Some aname2; typ = ct; size}  in
         (Loc, comps [FT.mlogical aname2 (Base abt); FT.mresource apoints; ftt])
       in
       let ret = 
         let rpoints = Points {pointer = aname; pointee = Some rname2; typ = ct; size} in
         (Loc, comps [RT.mlogical rname2 (Base rbt); RT.mresource rpoints; rtt])
       in
       return (arg, ret)
    (* fix *)
    | Atomic ct -> 
       aux (aname,rname) ct
    | Struct sym -> 
       let arg = (ClosedStruct (Tag sym), fun ft -> ft) in
       let ret = (ClosedStruct (Tag sym), fun rt -> rt) in
       return (arg, ret)
    | Basic (Floating _) -> floatingType loc 
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in

  let* ((abt,ftt),(_,rtt)) = aux (asym, fresh ()) ct in
  
  let arg = comp (FT.mcomputational asym abt) ftt in
  let ret = rtt in

  return (arg,ret)


    



let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()






let infer_ptrval loc env ptrval = 
  let name = fresh () in
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let constr = (LC (Null (S name))) in
      let typ = Computational (name, Loc, Constraint (constr, I)) in
      return typ )
    ( fun sym -> 
      return (Computational (name, FunctionPointer sym, I)) )
    ( fun _prov loc ->
      
      let constr = LC (S name %= Num loc) in
      let typ = Computational (name, Loc, Constraint (constr, I)) in
      return typ )
    ( fun () -> fail loc (Unreachable !^"unspecified pointer value") )


let rec infer_mem_value loc env mem = 
  let open CF.Ctype in
  CF.Impl_mem.case_mem_value mem
    ( fun _ctyp -> fail loc (Unsupported !^"ctypes as values") )
    ( fun it _sym -> 
      (* todo: do something with sym *)
      let* t = ctype false loc (fresh ()) (Ctype ([], Basic (Integer it))) in
      return (t, env) )
    ( fun it iv -> 
      let name = fresh () in
      let* v = Memory.integer_value_to_num loc iv in
      let val_constr = LC (S name %= Num v) in
      let* type_constr = integerType_constraint loc name it in
      let* solved = Solver.constraint_holds_given_constraints loc 
                      (add_var env (name, A BT.Int)) [val_constr] type_constr in
      match solved with
      | true -> return (Computational (name, Int, Constraint (val_constr, I)), env)
      | false -> fail loc (Generic_error !^"Integer value does not satisfy range constraint")
    )
    ( fun ft fv -> floatingType loc )
    ( fun _ctype ptrval ->
      (* maybe revisit and take ctype into account *)
      let* t = infer_ptrval loc env ptrval in
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
        let* (t,env) = aargs_and_bind_rt loc env t in
        return (aargs@t, env)
      ) ([],env) fields
  in
  let* ((n,bt),env) = pack_struct loc env (Tag tag) aargs in
  return (Computational (n, bt, I), env)


and infer_union loc env sym id mv =
  fail loc (Unsupported !^"todo: union types")

and infer_array loc env mem_values = 
  fail loc (Unsupported !^"todo: mem_value arrays")

let infer_object_value loc env ov =
  match ov with
  | M_OVinteger iv ->
     let name = fresh () in
     let* i = Memory.integer_value_to_num loc iv in
     let constr = (LC (S name %= Num i)) in
     let t = Computational (name, Int, Constraint (constr, I)) in
     return (t, env)
  | M_OVpointer p -> 
     let* t = infer_ptrval loc env p in
     return (t,env)
  | M_OVarray items ->
     let name = fresh () in
     let* (args_bts,env) = aargs loc env items in
     let* _ = check_Aargs_typ None args_bts in
     return (Computational (name, Array, I), env)
  | M_OVstruct (tag, fields) -> 
     infer_struct loc env (tag,fields)
  | M_OVunion (sym,id,mv) -> 
     infer_union loc env sym id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")


let infer_value loc env v : (ReturnTypes.t * Env.t) m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc env ov
  | M_Vunit ->
     return (Computational (fresh (), Unit, I), env)
  | M_Vtrue ->
     let name = fresh () in
     let constr = LC (S name) in
     return (Computational (name, Bool, Constraint (constr, I)), env)
  | M_Vfalse -> 
     let name = fresh () in
     let constr = LC (Not (S name)) in
     return (Computational (name, Bool, Constraint (constr,I)), env)
  | M_Vlist (cbt, asyms) ->
     let* bt = bt_of_core_base_type loc cbt in
     let* (aargs, env) = aargs loc env asyms in
     let _ = check_Aargs_typ (Some bt) aargs in
     return (Computational (fresh (), List bt, I), env)
  | M_Vtuple asyms ->
     let* (aargs,env) = aargs loc env asyms in
     let bts = fold_left (fun bts ((_,b),_) -> bts @ [b]) [] aargs in
     let name = fresh () in
     let bt = Tuple bts in
     let constr = tuple_constr (name, bt) aargs in
     return (Computational (name, bt, Constraint (constr, I)), env)







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
       let constr = LC (S sym %= S name) in
       let typ = Computational (name, bt, Constraint (constr, I)) in
       return (Normal typ, env)
    | M_PEimpl i ->
       let* t = get_impl_constant loc env.global i in
       return (Normal (Computational (fresh (), t, I)), env)
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
       let* (aargs, env) = aargs loc env args in
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
       let* (bt,env) = get_ALvar loc env pointee in
       let* fieldmap = match bt with
         (* TODO: proper equality *)
         | StoredStruct (tag',fieldmap) when tag = tag' -> return fieldmap
         | StoredStruct (tag',fieldmap) -> 
            fail loc (Generic_error !^"struct access incompatible with this struct type")
         | _ -> 
            fail loc (Generic_error !^"struct access to non-struct")
       in
       let* faddr = assoc_err loc member fieldmap "check store field access" in
       (* let* (fbt,env) = get_Lvar loc env faddr in *)
       let ret = fresh () in
       let constr = LC (S ret %= S faddr) in
       return (Normal (Computational (ret, Loc, Constraint (constr,I))), env)
    | M_PEnot asym ->
       let (sym,loc) = aunpack loc asym in
       let* (bt,env) = get_Avar loc env sym in
       let* () = check_base_type loc (Some sym) Bool bt in
       let ret = fresh () in 
       let constr = (LC (S ret %= Not (S sym))) in
       let rt = Computational (sym, Bool, Constraint (constr, I)) in
       return (Normal rt, env)
    | M_PEop (op,asym1,asym2) ->
       let (sym1,loc1) = aunpack loc asym1 in
       let (sym2,loc2) = aunpack loc asym2 in
       let* (bt1,env) = get_Avar loc1 env sym1 in
       let* (bt2,env) = get_Avar loc2 env sym2 in
       let (((ebt1,ebt2),rbt),c) = binop_typ op in
       let* () = check_base_type loc1 (Some sym1) bt1 ebt1 in
       let ret = fresh () in
       let constr = LC ((c (S sym1) (S sym2)) %= S ret) in
       return (Normal (Computational (ret, rbt, Constraint (constr, I))), env)
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
       let* (args,env) = aargs loc env asyms in
       let* (rt, env) = calltyp loc env args decl_typ in
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
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
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
     let* () = check_pexpr loc (add_UCvar env (LC (S sym1))) e2 typ in
     let* () = check_pexpr loc (add_UCvar env (LC (Not (S sym1)))) e3 typ in
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
           let* rt = unpack_and_store_structs loc env.global rt in
           let env = bind_to_name env newname rt in
           check_pexpr loc env e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        let* (rt, env) = infer_pexpr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = unpack_and_store_structs loc env.global rt in
           let env = bind_to_name env newname rt in
           check_pexpr loc env e2 typ
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
        let* (rt,env) = aargs_and_bind_rt loc env rt in
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
            | Some _ -> LC (S ret_name) 
            | None -> LC (Not (S ret_name)) 
          in
          let ret = Computational (ret_name, Bool, Constraint (constr, I)) in
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
          let rt = Computational (name, Loc, Resource (r, I)) in
          return (Normal rt, env)
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (_is_dynamic, asym) -> 
          let (sym,loc) = aunpack loc asym in
          (* have remove resources of location instead? *)
          let* (a_bt,env) = get_Avar loc env sym in
          let* () = check_base_type loc (Some sym) Loc a_bt in
          let* env = remove_subtree loc env sym in
          return (Normal (Computational (Sym.fresh (), Unit, I)), env)
       | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* size = Memory.size_of_ctype loc ct in
          let (psym,ploc) = aunpack loc asym1 in
          let (vsym,vloc) = aunpack loc asym2 in
          let* (pbt,env) = get_Avar ploc env psym in
          let* (vbt,env) = get_Avar vloc env vsym in
          (* for consistency check value against Core annotation *)
          let* _ =
            let* t = ctype false loc (fresh ()) ct in
            subtype loc env [((vsym,vbt),vloc)] t 
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
            let* t = ctype false loc (fresh ()) p.typ in
            subtype loc env [((vsym,vbt),vloc)] t
              "checking store value against expected type"
          in
          
          let* size' = Memory.size_of_ctype loc p.typ in
          let* () = 
            if size = size' then return ()
            else fail loc (Generic_error !^"store of different size")
          in

          let* env = remove_subtree loc env p.pointer in
          let newsym = fresh () in
          let* rt = match vbt with
            | OpenStruct (tag,fieldmap) -> 
               let* ((tag,fieldmap), bindings) = open_struct_to_stored_struct loc env.global tag fieldmap in
               return (Computational (fresh (), Unit,
                       Logical (newsym, Base (StoredStruct (tag,fieldmap)),
                       Resource (Points {p with pointee = Some newsym}, I))))
            | vbt -> 
               return (Computational (fresh (), Unit,
                       Logical (newsym, Base vbt,
                       Constraint (LC (S newsym %= S vsym),
                       Resource (Points {p with pointee = Some newsym}, I)))))
          in
          return (Normal rt,env)

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
          let* (bt,constrs) = match bt with
            | StoredStruct (tag,addrmap) ->
               let* ((tag,valuemap),env) = 
                 stored_struct_to_open_struct false loc env tag addrmap in
               let bt = OpenStruct (tag,valuemap) in
               return (bt,I)
            | bt ->
               let constr = LC (S ret %= (S pointee)) in
               return (bt,Constraint (constr, I))
          in
          let* _ = 
            let* t = ctype false loc (fresh ()) ct in
            subtype loc env [((pointee,bt),ploc)] t 
              "checking load value against expected type"
          in
          return (Normal (Computational (ret, bt, constrs)),env)

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
       return (Normal (Computational (fresh (), Unit, I)), env)
    | M_Eccall (_, _ctype, fun_asym, arg_asyms) ->
       let* (args,env) = aargs loc env arg_asyms in
       let (sym1,loc1) = aunpack loc fun_asym in
       let* (bt,env) = get_Avar loc1 env sym1 in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail loc1 (Generic_error !^"not a function pointer")
       in
       let* (_loc,decl_typ,_ret_name) = get_fun_decl loc env.global fun_sym in
       let* (rt, env) = calltyp loc env args decl_typ in
       return (Normal rt, env)
    | M_Eproc (_, fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            get_impl_fun_decl loc env.global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ,_ret_name) = get_fun_decl loc env.global sym in
            return decl_typ
       in
       let* (args,env) = aargs loc env asyms in
       let* (rt, env) = calltyp loc env args decl_typ in
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
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
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
     let* () = check_expr loc (add_UCvar env (LC (S sym1))) e2 typ in
     let* () = check_expr loc (add_UCvar env (LC (Not (S sym1)))) e3 typ in
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
           let* rt = unpack_and_store_structs loc env.global rt in
           let env = bind_to_name env newname rt in
           check_expr loc env e2 typ
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_Pat (M_Pattern (annots, M_CaseBase (mnewname,_cbt)))
     | M_Pat (M_Pattern (annots, M_CaseCtor (M_Cspecified, [(M_Pattern (_, M_CaseBase (mnewname,_cbt)))]))) -> (* temporarily *)
        let loc = update_loc loc annots in
        let newname = sym_or_fresh mnewname in
        let* (rt, env) = infer_pexpr loc env e1 in
        begin match rt with
        | Normal rt -> 
           let* rt = unpack_and_store_structs loc env.global rt in
           let env = bind_to_name env newname rt in
           check_expr loc env e2 typ
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
           let* rt = unpack_and_store_structs loc env.global rt in
           let env = bind_to_name env newname rt in
           check_expr loc env e2 typ
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
           let env = add_UCvar env (LC (S sym %= S vsym)) in
           return (add_Avar env (sym, bt))
         ) env args
     in
     check_expr loc env body typ
  | _ ->
     let* (rt, env) = infer_expr loc env e in
     begin match rt with
     | Normal rt ->
        let* (rt,env) = aargs_and_bind_rt loc env rt in
        let* env = subtype loc env rt typ "function return type" in
        return ()
     | Bad bad -> ensure_bad_unreachable loc env bad
     end
     

let rec bind_arguments_rt env = function
  | Computational (name,bound,t) ->
     bind_arguments_rt (add_Avar env (name,bound)) t
  | Logical (name,bound,t) ->
     bind_arguments_rt (add_Lvar env (name,bound)) t
  | Resource (bound,t) ->
     bind_arguments_rt (add_URvar env bound) t
  | Constraint (bound,t) ->
     bind_arguments_rt (add_UCvar env bound) t
  | I -> 
     env

let check_proc loc fsym genv body ftyp = 
  let* () = debug_print 1 (h1 ("Checking procedure " ^ (plain (Sym.pp fsym)))) in
  let env = with_fresh_local genv in
  let (args_rt,ret) = FT.args_and_ret ftyp in
  let* args_rt = unpack_and_store_structs loc genv args_rt in
  let env = bind_arguments_rt env args_rt in
  let* _env = check_expr loc env body ret in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in
  return ()

let check_fun loc fsym genv body ftyp = 
  let* () = debug_print 1 (h1 ("Checking function " ^ (plain (Sym.pp fsym)))) in
  let env = with_fresh_local genv in
  let (args_rt,ret) = FT.args_and_ret ftyp in
  let* args_rt = unpack_and_store_structs loc genv args_rt in
  let env = bind_arguments_rt env args_rt in
  let* _env = check_pexpr loc env body ret in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in
  return ()


let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) =

  let check_consistent loc ftyp (args, ret) = 

    let rec forget_rt = function
      | RT.Computational (name,bt,t) ->
         RT.Computational (name,bt,forget_rt t)
      | RT.Logical (_,_,t)
      | RT.Resource (_,t)
      | RT.Constraint (_,t) ->
         forget_rt t
      | RT.I ->
         I
    in

    let rec forget_ft = function
      | FT.Computational (name,bt,t) ->
         FT.Computational (name,bt,forget_ft t)
      | FT.Logical (_,_,t)
      | FT.Resource (_,t)
      | FT.Constraint (_,t) ->
         forget_ft t
      | FT.Return rt ->
         FT.Return (forget_rt rt)
    in

    let* ftyp2 = 
      let* rbt = bt_of_core_base_type loc (snd ret) in
      let ret = (RT.Computational (fst ret, rbt, RT.I)) in
      let rec aux = function
        | [] -> return (FT.Return ret)
        | (name,cbt) :: args -> 
           let* t = aux args in
           let* bt = bt_of_core_base_type loc cbt in
           return (FT.Computational (name, bt, t))
      in
      aux args
    in

    if forget_ft ftyp = ftyp2 then return ()
    else 
      let err = 
        flow (break 1) 
          ((words "Function definition of") @ 
             [Sym.pp fsym] @
             words ("inconsistent. Should be")@
             [FunctionTypes.pp ftyp ^^ comma]@  [!^"is"] @
               [FunctionTypes.pp ftyp2])
                               
      in
      fail loc (Generic_error err)
  in
  match fn with
  | M_Fun (ret, args, body) ->
     let* decl = get_fun_decl Loc.unknown genv fsym in
     let (loc,ftyp,ret_name) = decl in
     let* () = check_consistent loc ftyp (args, (ret_name,ret)) in
     check_fun loc fsym genv body ftyp
  | M_Proc (loc, ret, args, body) ->
     let* decl = get_fun_decl loc genv fsym in
     let (loc,ftyp,ret_name) = decl in
     let* () = check_consistent loc ftyp (args, (ret_name,ret)) in
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
          return (comp args arg, comp returns ret, name::names)
        ) ((fun ft -> ft), (fun rt -> rt), []) args
    in
    let ret_name = Sym.fresh () in
    let* ret = ctype true loc ret_name ret_ctype in
    let ftyp = arguments (FT.Return (ret @@ returns I)) in
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
           return (FT.mcomputational sym a_bt)) args
     in
     let* bt = bt_of_core_base_type Loc.unknown bt in
     let ftyp = (comps args_ts) (Return (Computational (fresh (), bt, I))) in
     return (add_impl_fun_decl genv impl ftyp)
                        


let record_impls genv impls = pmap_foldM record_impl impls genv



let record_tagDef file sym def genv =

  (* like ctype_aux *)
  let rec aux owned loc (Member id : member) (CF.Ctype.Ctype (annots, ct_)) =
    let loc = update_loc loc annots in
    let name = fresh_pretty id in
    match ct_ with
    | Void -> 
       return (name, mcomputational name Unit)
    | Basic (Integer it) -> 
       let* lc = integerType_constraint loc name it in
       return (name, comp (mcomputational name Int) (mconstraint lc))
    | Array (ct, _maybe_integer) -> 
       return (name, mcomputational name BT.Array)
    | Pointer (_qualifiers, ct) -> 
       return (name, mcomputational name Loc)
    (* fix *)
    | Atomic ct -> 
       aux owned loc (Member id) ct
    | Struct sym -> 
       return (name, mcomputational name (BT.ClosedStruct (Tag sym)))
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in


  match def with
  | CF.Ctype.UnionDef _ -> 
     fail Loc.unknown (Unsupported !^"todo: union types")
  | CF.Ctype.StructDef (fields, _) ->
     let* (fnames,typ,ctypes) =
       fold_leftM (fun (mapping,typ,ctypes) (id, (_attributes, _qualifier, ct)) ->
           let* (name,typ') = aux false Loc.unknown (Member (Id.s id)) ct in
           return (mapping@[(Member (Id.s id),name)], 
                   comp typ typ', 
                   ctypes@[(Member (Id.s id),ct)])
         ) ([],(fun rt -> rt),[]) fields
     in
     let decl = {typ = typ I;fnames;ctypes} in
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







(* TODO: 
   - make call_typ and subtype accept non-A arguments

   - when applying substitution: be careful about the variable 
     types: e.g. when converting struct types

   - when un/packing structs: remember previous thing as logical 
     variable as part of binding

 *)
