open Subst
open Uni
open Tools
open Pp
open Except
open List
open Sym
open LogicalConstraints
open Resources
open IndexTerms
open BaseTypes
open LogicalSorts
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




(* (\* types recording undefined behaviour, error cases, etc. *\)
 * type bad = 
 *  | Undefined of Loc.t * CF.Undefined.undefined_behaviour
 *  | Unspecified of Loc.t (\* * Ctype.ctype *\)
 *  | StaticError of Loc.t * (string * Sym.t)
 * 
 * type 'a u = 
 *   | Normal of 'a
 *   | Bad of bad
 * 
 * type urt = RT.t u
 * 
 * let pp_urt = function
 *   | Normal t -> RT.pp t
 *   | Bad u -> !^"bad" *)



(* let ensure_bad_unreachable loc env bad = 
 *   let* (unreachable,_,_) = Solver.is_unreachable loc env in
 *   if unreachable then return () else
 *     match bad with
 *     | Undefined (loc,ub) -> fail loc (TypeErrors.Undefined ub)
 *     | Unspecified loc -> fail loc TypeErrors.Unspecified
 *     | StaticError (loc, (err,pe)) -> fail loc (TypeErrors.StaticError (err,pe)) *)



let check_base_type loc mname has expected =
  if BT.type_equal has expected 
  then return ()
  else 
    let msm = (Mismatch {mname; has = (Base has); expected = Base expected}) in
    fail loc (Call_error msm)









let bind_helper loc env rt o_aname = 
  let rec aux seen_computational resources env rt = 
    match rt with
    | Computational (lname,bound,rt) ->
       begin match seen_computational with
       | Some _ ->
         fail loc (Unreachable !^"multiple computational values in return type")
       | None ->
          let new_lname = fresh () in
          let env = add_lvar env (new_lname,Base bound) in
          let env = match o_aname with
            | Some aname -> add_avar env (aname,(bound,new_lname))
            | None -> env
          in
          let rt = subst_var {substitute=lname;swith=S new_lname} rt in
          aux (Some (bound,new_lname)) resources env rt
       end
    | Logical (lname,bound,rt) ->
       let new_lname = fresh () in
       let env = add_lvar env (new_lname,bound) in
       let rt = subst_var {substitute=lname; swith=S new_lname} rt in
       aux seen_computational resources env rt
    | Resource (bound,rt) ->
       let new_rname = fresh () in
       let env = add_rvar env (new_rname,(bound,Unused)) in
       aux seen_computational (new_rname::resources) env rt
    | Constraint (bound,rt) ->
       let env = add_c env bound in
       aux seen_computational resources env rt
    | I ->
       begin match seen_computational with
       | Some (abt,alname) -> return (env,(abt,alname),resources)
       | None -> fail loc (Unreachable !^"no computational values in return type")
       end
  in
  aux None [] env rt


let bind_to_name loc env rt aname =
  let* (env,_,resources) = bind_helper loc env rt (Some aname) in
  return (env,[aname],resources)

let bind_other loc env rt =
  bind_helper loc env rt None


let pattern_match loc env this pat expected_bt =
  let rec aux env anames this pat expected_bt = 
    match pat with
    | M_Pattern (annots, M_CaseBase (o_aname, mbt)) ->
       let* has_bt = Conversions.bt_of_core_base_type loc mbt in
       let* () = check_base_type loc None has_bt expected_bt in
       let* aname = match o_aname with
         | Some aname -> 
            if List.mem aname anames 
            then fail loc (Name_bound_twice aname)
            else return aname
         | None -> return (fresh ())
       in
       let new_lname = fresh () in 
       let env = add_lvar env (new_lname,Base has_bt) in
       let env = add_avar env (aname,(has_bt,new_lname)) in
       let env = add_c env (LC (this %= S new_lname)) in
       return (env, aname :: anames)
    | M_Pattern (annots, M_CaseCtor (constructor, pats)) ->
       match constructor with
       | M_Cnil mbt ->
          let* item_bt = Conversions.bt_of_core_base_type loc mbt in
          begin match pats with
          | [] ->
             if type_equal (List item_bt) expected_bt 
             then return (env,anames)
             else fail loc (Pattern_type_mismatch {has=List item_bt;expected=expected_bt})
          | _ -> 
             fail loc (Constructor_wrong_argument_number 
                         {constructor;expected=0;has=List.length pats})
          end
       | M_Ccons ->
          begin match expected_bt, pats with
          | List item_bt, [p1;p2] ->
             let* (env,anames) = aux env anames (Head this) p1 item_bt in
             aux env anames (Tail this) p2 expected_bt
          | List item_bt, _ ->
             fail loc (Constructor_wrong_argument_number 
                         {constructor;expected=2;has=List.length pats})
          | _, _ ->
             fail loc (Generic_error (!^"cons pattern incompatible with expected type" ^^^ 
                                        BT.pp false expected_bt))
          end
       | M_Ctuple ->
          begin match expected_bt with 
          | Tuple bts ->
             let rec components (env,anames) i pats bts =
               match pats, bts with
               | [], [] -> return (env,anames)
               | pat::pats, bt::bts ->
                  let* (env,anames) = aux env anames (Nth (i, this)) pat bt in
                  components (env,anames) (i+1) pats bts
               | _, _ ->
                  fail loc (Constructor_wrong_argument_number 
                              {constructor;expected=i+List.length pats;has=i+List.length pats})
             in
             components (env,anames) 0 pats bts
          | _ ->
             fail loc (Generic_error (!^"tuple pattern incompatible with expected type" ^^^ 
                                        BT.pp false expected_bt))
          end
       | M_Cspecified ->
          begin match pats with
          | [pat] ->
             aux env anames this pat expected_bt
          | _ ->
           fail loc (Constructor_wrong_argument_number 
                       {constructor;expected=1;has=List.length pats})
          end
       | M_Carray ->
          fail loc (Unsupported !^"todo: array types")
       | M_CivCOMPL
       | M_CivAND
       | M_CivOR
       | M_CivXOR
       | M_Cfvfromint
       | M_Civfromfloat 
         ->
          fail loc (Unsupported !^"todo: Civ..")
  in
  aux env [] this pat expected_bt
  


let pattern_match_rt (loc : Loc.t) env pat rt = 
  let rec aux opat env anames rnames rt =
    match opat, rt with
    | Some pat, Computational (lname,bound,rt) ->
       (* The pattern-matching might de-struct 'bound'. For easily
          making constraints carry over to those values, record
          (lname,bound) as a logical variable and record constraints
          about how the variables introduced in the pattern-matching
          relate to (name,bound). *)
       let new_lname = fresh () in
       let env = add_lvar env (new_lname,Base bound) in
       let* (env,anames') = pattern_match loc env (S new_lname) pat bound in
       let rt = subst_var {substitute=lname; swith=S new_lname} rt in
       aux None env (anames @ anames') rnames rt
    | None, Computational _ ->
       fail loc (Unreachable !^"return type with multiple computational values")
    | opat, Logical (lname,bound,rt) ->
       let new_lname = fresh () in
       let env = add_lvar env (new_lname,bound) in
       let rt = subst_var {substitute=lname; swith=S new_lname} rt in
       aux opat env anames rnames rt
    | opat, Resource (bound,rt) ->
       let new_rname = fresh () in
       let env = add_rvar env (new_rname, (bound,Unused)) in
       aux opat env anames (new_rname::rnames) rt
    | opat, Constraint (bound,rt) ->
       let env = add_c env bound in
       aux opat env anames rnames rt
    | Some _, I -> 
       fail loc (Unreachable !^"return type without computational value")
    | None, I -> 
       return (env,anames,rnames)
  in
  aux (Some pat) env [] [] rt







let at_most_one loc err_str = function
  | [] -> return None
  | [x] -> return (Some x)
  | _ -> fail loc (Generic_error err_str)


let points_to loc env loc_it = 
  let* points = 
    filter_resources (fun name t ->
        match t with
        | (RE.Points p,Unused) ->
           let c = LC (loc_it %= p.pointer) in
           let* (holds,_,_) = Solver.constraint_holds loc env c in
           return (if holds then Some (name,p) else None)
        | _ -> 
           return None
      ) env
  in
  at_most_one loc !^"multiple points-to for same pointer" points


let stored_struct_to_of_tag loc env loc_it tag = 
  let* stored = 
    filter_resources (fun name t ->
        match t with
        | (RE.StoredStruct s,Unused) when s.tag = tag ->
           let c = LC (loc_it %= s.pointer) in
           let* (holds,_,_) = Solver.constraint_holds loc env c in
           return (if holds then Some (name,s) else None)
        | _ -> 
           return None
      ) env
  in
  at_most_one loc !^"multiple points-to for same pointer" stored


(* revisit *)
let matching_resource loc env resource = 
  filter_resources (fun name t ->
      match resource, t  with
      | Points p, (RE.Points p',Unused) ->
         let c = LC (p.pointer %= p'.pointer) in
         let* (holds,_,_) = Solver.constraint_holds loc env c in
         return (if holds 
                 then Some (Points {p' with pointer = p.pointer},name) 
                 else None)
      | StoredStruct s, (RE.StoredStruct s',Unused) ->
         let c = LC (s.pointer %= s'.pointer) in
         let* (holds,_,_) = Solver.constraint_holds loc env c in
         return (if holds 
                 then Some (StoredStruct {s' with pointer = s.pointer},name)
                 else None)
      | _ -> 
         return None
    ) env


let loc_type loc env pointer = 
  let* resources = 
    filter_resources (fun name t ->
        match t with
        | (RE.Points p',Unused) ->
           let c = LC (pointer %= p'.pointer) in
           let* (holds,_,_) = Solver.constraint_holds loc env c in
           return (if holds then Some p'.typ else None)
        | (RE.StoredStruct ({tag = Tag tag; _} as s'),Unused) ->
           let c = LC (pointer %= s'.pointer) in
           let* (holds,_,_) = Solver.constraint_holds loc env c in
           let ct = CF.Ctype.Ctype ([], CF.Ctype.Struct tag) in
           return (if holds then Some ct else None)
        | _ -> 
           return None
      ) env
  in
  at_most_one loc !^"multiple resources for same pointer" resources











let pp_unis unis = 
  let pp_entry (sym, Uni.{resolved}) =
    match resolved with
    | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ IT.pp true res
    | None -> Sym.pp sym ^^^ !^"unresolved"
  in
  pp_list pp_entry (SymMap.bindings unis)



let rec remove_owned_subtree loc env is_field pointer ct =
  match ct with
  | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
     let* decl = Global.get_struct_decl loc env.global (Tag tag) in
     let* stored = stored_struct_to_of_tag loc env pointer (Tag tag) in
     begin match stored with
     | Some (r,stored) -> 
        fold_leftM (fun env (member,member_pointer) ->
            let* ct = Tools.assoc_err loc member decl.ctypes 
                        "remove_owned_subtree" in
            let* env = use_resource loc env r in
            remove_owned_subtree loc env true member_pointer ct
          ) env stored.members
     | None ->
        fail loc (Generic_error !^"missing ownership for de-allocating")
     end
  | _ ->
     let* points = points_to loc env pointer in
     begin match points with
     | Some (r,_) -> use_resource loc env r
     | None -> fail loc (Generic_error !^"missing ownership for de-allocating")
     end
  





let rec infer_index_term (loc : Loc.t) env (it : IT.t) = 
  match it with
  | Num _ -> return (Base Int)
  | Bool _ -> return (Base Bool)
  | Add (t,t')
  | Sub (t,t')
  | Mul (t,t')
  | Div (t,t')
  | Exp (t,t')
  | Rem_t (t,t')
  | Rem_f (t,t') 
    ->
     let* () = check_index_term loc env (Base Int) t in
     let* () = check_index_term loc env (Base Int) t' in
     return (Base Int)
  | EQ (t,t')
  | NE (t,t')
  | LT (t,t')
  | GT (t,t')
  | LE (t,t')
  | GE (t,t')
    ->
     let* () = check_index_term loc env (Base Int) t in
     let* () = check_index_term loc env (Base Int) t' in
     return (Base Bool)
  | Null t ->
     let* () = check_index_term loc env (Base Loc) t in
     return (Base Bool)
  | And (t,t')
  | Or (t,t')
    ->
     let* () = check_index_term loc env (Base Bool) t in
     let* () = check_index_term loc env (Base Bool) t' in
     return (Base Bool)
  | Not t ->
     let* () = check_index_term loc env (Base Bool) t in
     return (Base Bool)
  | Tuple its ->
     let* ts = 
       mapM (fun it -> 
           let* (Base bt) = infer_index_term loc env it in
           return bt
         ) its in
     return (Base (BT.Tuple ts))
  | Nth (n,it) ->
     let* t = infer_index_term loc env it in
     begin match t with
     | Base (Tuple ts) ->
        begin match List.nth_opt ts n with
        | Some t -> return (Base t)
        | None -> fail loc (Unreachable !^"inconsistently typed index term")
        end
     | _ -> fail loc (Unreachable !^"inconsistently typed index term")
     end
  (* | Struct (tag, members)->
   *    let* decl = Global.get_struct_decl loc genv tag in
   *    aux members decl *)
  | Member (tag, it,member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it in
     let* decl = Global.get_struct_decl loc env.global tag in
     let* bt = Tools.assoc_err loc member decl.raw 
                 "inconsistently typed index term" in
     return (Base bt)
  | MemberOffset (tag, it,member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it in
     let* decl = Global.get_struct_decl loc env.global tag in
     let* _ = Tools.assoc_err loc member decl.raw 
                 "inconsistently typed index term" in
     return (Base Loc)
  | Nil bt -> 
     return (Base bt)
  | Cons (it1,it2) ->
     let* (Base item_bt) = infer_index_term loc env it1 in
     let* () = check_index_term loc env (Base (List item_bt)) it2 in
     return (Base (List item_bt))
  | List (its,bt) ->
     let* _ = mapM (check_index_term loc env (Base bt)) its in
     return (Base bt)
  | Head it ->
     let* ls = infer_index_term loc env it in
     begin match ls with
     | Base (List bt) -> return (Base bt)
     | _ -> fail loc (Unreachable !^"inconsistently typed index term")
     end
  | Tail it ->
     let* ls = infer_index_term loc env it in
     begin match ls with
     | Base (List bt) -> return (Base (List bt))
     | _ -> fail loc (Unreachable !^"inconsistently typed index term")
     end
  | S s ->
     get_lvar loc env s

and check_index_term loc env (ls : LS.t) (it : IT.t) = 
  let* ls' = infer_index_term loc env it in
  if LS.type_equal ls ls' then return ()
  else fail loc (Unreachable !^"inconsistently typed index term")




let pp_argslocs =
  pp_list (fun ((n,(bt,lname)),(_l:Loc.t)) -> 
      typ (Sym.pp n) (parens (BT.pp false bt ^^^ bar ^^^ Sym.pp lname)))




let subtype loc_ret env args (rtyp : RT.t) ppdescr =

  let module STS = struct

    type t = 
      { typ: RT.t;
        lvars: (Sym.t * LS.t) list;
        constraints : LC.t list }

    let subst_var s spec = 
      { spec with 
        typ = RT.subst_var s spec.typ;
        constraints = List.map (LC.subst_var s) spec.constraints }

    let subst_vars = Subst.make_substs subst_var

  end in

  let* () = debug_print 1 (action ppdescr) in
  let* () = debug_print 2 PPrint.empty in

  let rec aux env args (unis : (IT.t Uni.t) SymMap.t) spec = 
    let* () = debug_print 2 (blank 3 ^^ item "value" (pp_argslocs args)) in
    let* () = debug_print 2 (blank 3 ^^ item "specification" (RT.pp spec.STS.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
    match args, spec.typ with
    | [], I -> 
       begin match spec.lvars, spec.constraints with
       | (sname,sls) :: lvars, _ ->
          begin match SymMap.find_opt sname unis with
          | Some Uni.{resolved = None} -> 
             fail loc_ret (Call_error (Unconstrained_l sname))
          | Some Uni.{resolved = Some it} ->
             let* als = infer_index_term loc_ret env it in
             if LS.type_equal als sls then
               let spec = STS.{ spec with lvars } in
               let spec = STS.subst_var {substitute=sname;swith=it} spec in
               aux env args unis spec
             else
               let msm = Mismatch {mname = None; has = als; expected = sls} in
               fail loc_ret (Return_error msm)
          | None ->
             fail loc_ret (Unreachable !^"did not find unification variable")
          end
       | [], (c :: constraints) -> 
          let spec = STS.{ spec with constraints } in
          let* (holds,_,_) = Solver.constraint_holds loc_ret env c in
          if holds then aux env args unis spec
          else fail loc_ret (Return_error (Unsat_constraint c))
       | [], [] ->
          return env
       end
    | [], Computational (sname,sbt,_) -> 
       fail loc_ret (Return_error (Missing_A (sname, sbt)))
    | ((aname,(abt,_lname)),loc) :: _, I -> 
       fail loc (Return_error (Surplus_A (aname, abt)))
    | ((aname,(abt,lname)),arg_loc) :: args, Computational (sname,sbt,rtyp) ->
       if BT.type_equal abt sbt then
         let spec = { spec with typ = rtyp} in
         let spec = STS.subst_var {substitute=sname;swith=S lname} spec in
         let env = add_lvar env (lname,Base abt) in
         aux env args unis spec
       else
         let msm = Mismatch {mname = Some aname; has = Base abt; expected = Base sbt} in
         fail loc_ret (Return_error msm)
    | _, Logical (sname,sls,rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = STS.{ spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp } in
       let spec = STS.subst_var {substitute=sname;swith=S sym} spec in
       aux env args unis spec
    | _, Resource (re,rtyp) -> 
       let* owneds = matching_resource loc_ret env re in
       let rec try_resources = function
         | [] -> 
            fail loc_ret (Return_error (Missing_R re))
         | (resource',r) :: owned_resources ->
            let* () = debug_print 3 (action ("trying resource " ^ plain (RE.pp false resource'))) in
            let* () = debug_print 3 (blank 3 ^^ item "unis " (pp_unis unis)) in
            match RE.unify re resource' unis with
            | None -> 
               let* () = debug_print 3 (blank 3 ^^ !^"no match") in
               try_resources owned_resources
            | Some unis ->
               let* () = debug_print 3 (blank 3 ^^ !^"match") in
               let* env = use_resource loc_ret env r in
               let (_,new_substs) = Uni.find_resolved env unis in
               let spec = STS.{ spec with typ = rtyp } in
               let spec = STS.subst_vars new_substs spec in
               aux env args unis spec
       in
       try_resources owneds
    | _, Constraint (constr,rtyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = rtyp} in
       aux env args unis spec  
  in

  aux env args SymMap.empty { typ = rtyp ; lvars = []; constraints = []}




let calltyp loc_call env args (rtyp : FT.t) =

  let module CTS = struct

    type calltyp_spec = 
      { typ: FT.t; 
        lvars: (Sym.t * LS.t) list;
        constraints : LC.t list }

    let subst_var s spec = 
      { spec with typ = FT.subst_var s spec.typ;
                  constraints = List.map (LC.subst_var s) spec.constraints }

    let subst_vars = Subst.make_substs subst_var

  end in

  let open FT in
  let open CTS in

  let* () = debug_print 1 (action "function call type") in
  let* () = debug_print 2 PPrint.empty in

  let rec aux env args unis (spec : calltyp_spec) = 
    let* () = debug_print 2 (blank 3 ^^ item "arguments" (pp_argslocs args)) in
    let* () = debug_print 2 (blank 3 ^^ item "specification" (FT.pp spec.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp env.local)) in
    match args, spec.typ with
    | [], Return rt -> 
       begin match spec.lvars, spec.constraints with
       | (sname,sls) :: lvars, _ ->
          begin match SymMap.find_opt sname unis with
          | Some Uni.{resolved = None} -> 
             fail loc_call (Call_error (Unconstrained_l sname))
          | Some Uni.{resolved = Some it} ->
             let* als = infer_index_term loc_call env it in
             if LS.type_equal als sls then
               let spec = CTS.{ spec with lvars } in
               let spec = CTS.subst_var {substitute=sname;swith=it} spec in
               aux env args unis spec
             else
               let msm = Mismatch {mname = None; has = als; expected = sls} in
               fail loc_call (Call_error msm)
          | None ->
             fail loc_call (Unreachable !^"did not find unification variable")
          end
       | [], (c :: constraints) -> 
          let spec = CTS.{ spec with constraints } in
          let* (holds,_,_) = Solver.constraint_holds loc_call env c in
          if holds then aux env args unis spec
          else fail loc_call (Return_error (Unsat_constraint c))
       | [], [] ->
          return (rt,env)
       end
    | [], Computational (sname,sbt,_) -> 
       fail loc_call (Call_error (Missing_A (sname, sbt)))
    | ((aname,(abt,_lname)),arg_loc) :: _, Return _ -> 
       fail arg_loc (Call_error (Surplus_A (aname, abt)))
    | ((aname,(abt,lname)),arg_loc) :: args, Computational (sname,sbt,rtyp) ->
       if BT.type_equal abt sbt then
         let spec = CTS.{ spec with typ = rtyp} in
         let spec = CTS.subst_var {substitute=sname;swith=S lname} spec in
         let env = add_lvar env (lname,Base abt) in
         aux env args unis spec
       else
         let msm = Mismatch {mname = Some aname; has = Base abt; expected = Base sbt} in
         fail loc_call (Call_error msm)
    | _, Logical (sname,sls,rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = CTS.{ spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp} in
       let spec = CTS.subst_var {substitute=sname;swith=S sym} spec in
       aux env args unis spec
    | _, Resource (re,rtyp) -> 
       let* owneds = matching_resource loc_call env re in
       let rec try_resources = function
         | [] -> 
            fail loc_call (Call_error (Missing_R re))
         | (resource',r) :: owned_resources ->
            let* () = debug_print 3 (action ("trying resource " ^ plain (RE.pp false resource'))) in
            let* () = debug_print 3 (blank 3 ^^ item "unis " (pp_unis unis)) in
            match RE.unify re resource' unis with
            | None -> try_resources owned_resources
            | Some unis ->
               let* env = use_resource loc_call env r in
               let (_,new_substs) = Uni.find_resolved env unis in
               let spec = CTS.{ spec with typ = rtyp } in
               let spec = CTS.subst_vars new_substs spec in
               aux env args unis spec
       in
       try_resources owneds
    | _, Constraint (constr,rtyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = rtyp} in
       aux env args unis spec  
  in

  aux env args SymMap.empty { typ = rtyp ; lvars = []; constraints = []}




let infer_tuple loc env asyms = 
  let new_lname = fresh () in
  let* (bts,constr,_) = 
    fold_leftM (fun (bts,constr,i) asym -> 
        let (sym, loc) = aunpack loc asym in
        let* (bt,lname) = get_avar loc env sym in
        let constr = (Nth (i, S new_lname) %= S lname) %& constr in
        return (bts@[bt],constr,i+1)
      ) ([],IT.Bool true, 0) asyms 
  in
  let bt = Tuple bts in
  return (Computational (new_lname, bt, Constraint (LC constr, I)))


let infer_constructor loc env constructor asyms = 
  match constructor with
  | M_Ctuple -> 
     infer_tuple loc env asyms
  | M_Carray -> 
     fail loc (Unsupported !^"todo: array types")
  | M_CivCOMPL
  | M_CivAND
  | M_CivOR
  | M_CivXOR -> 
     fail loc (Unsupported !^"todo: Civ..")
  | M_Cspecified ->
     let new_lname = fresh () in
     begin match asyms with
     | [asym] -> 
        let (sym, loc) = aunpack loc asym in
        let* (bt,lname) = get_avar loc env sym in
        let rt = Computational (new_lname, bt, 
                 Constraint (LC (S new_lname %= S lname),I)) in
        return rt
     | _ ->
        fail loc (Constructor_wrong_argument_number 
                    {constructor; has=List.length asyms; expected=1})
     end
  | M_Cnil mbt -> 
     let new_lname = fresh () in
     let* item_bt = Conversions.bt_of_core_base_type loc mbt in
     begin match asyms with
     | [] -> 
        let rt = Computational (new_lname, List item_bt, 
                 Constraint (LC (S new_lname %= Nil item_bt),I)) in
        return rt
     | _ ->
        fail loc (Constructor_wrong_argument_number 
                    {constructor; has=List.length asyms; expected=0})
     end     
  | M_Ccons -> 
     let new_lname = fresh () in
     begin match asyms with
     | [asym1;asym2] -> 
        let (sym1, loc1) = aunpack loc asym1 in
        let (sym2, loc2) = aunpack loc asym2 in
        let* (bt1,lname1) = get_avar loc env sym1 in
        let* (bt2,lname2) = get_avar loc env sym2 in
        let* () = check_base_type loc2 (Some sym2) bt2 (List bt1) in
        let rt = Computational (new_lname, bt2, 
                 Constraint (LC (S new_lname %= Cons (S lname1, S lname2)),I)) in
        return rt
     | _ ->
        fail loc (Constructor_wrong_argument_number 
                    {constructor; has=List.length asyms; expected=2})
     end
  | M_Cfvfromint -> fail loc (Unsupported !^"floats")
  | M_Civfromfloat -> fail loc (Unsupported !^"floats")




let infer_ptrval loc env ptrval = 
  let new_lname = fresh () in
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let constr = (LC (Null (S new_lname))) in
      let typ = Computational (new_lname, Loc, Constraint (constr, I)) in
      return typ )
    ( fun sym -> 
      return (Computational (new_lname, FunctionPointer sym, I)) )
    ( fun _prov loc ->      
      let constr = LC (S new_lname %= Num loc) in
      let typ = Computational (new_lname, Loc, Constraint (constr, I)) in
      return typ )
    ( fun () -> fail loc (Unreachable !^"unspecified pointer value") )


let rec infer_mem_value loc env mem = 
  let open CF.Ctype in
  CF.Impl_mem.case_mem_value mem
    ( fun _ctyp -> fail loc (Unsupported !^"ctypes as values") )
    ( fun it _sym -> 
      (* todo: do something with sym *)
      let* t = Conversions.ctype false loc (fresh ()) (Ctype ([], Basic (Integer it))) in
      return (t, env) )
    ( fun it iv -> 
      let new_lname = fresh () in
      let* v = Memory.integer_value_to_num loc iv in
      let val_constr = LC (S new_lname %= Num v) in
      let* type_constr = Conversions.integerType_constraint loc (S new_lname) it in
      let* (holds,_,_) = 
        Solver.constraint_holds_given_constraints loc 
          (add_lvar env (new_lname, Base BT.Int)) [val_constr] type_constr in
      match holds with
      | true -> return (Computational (new_lname, Int, Constraint (val_constr, I)), env)
      | false -> fail loc (Generic_error !^"Integer value does not satisfy range constraint")
    )
    ( fun ft fv -> Conversions.floatingType loc )
    ( fun _ctype ptrval ->
      (* maybe revisit and take ctype into account *)
      let* t = infer_ptrval loc env ptrval in
      return (t, env) )
    ( fun mem_values -> infer_array loc env mem_values )
    ( fun sym fields -> infer_struct loc env (sym,fields) )
    ( fun sym id mv -> infer_union loc env sym id mv )


and infer_struct loc env (tag,fields) =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let* decl = Global.get_struct_decl loc env.global (Tag tag) in
  let ret = fresh () in
  let rec check fields decl =
    match fields, decl with
    | (id,_ct,mv)::fields, (smember,sbt)::decl when Member (Id.s id) = smember ->
       let* (constrs,env) = check fields decl in
       let* (rt, env) = infer_mem_value loc env mv in
       let* (env,(abt,lname),rnames) = bind_other loc env rt in
       let* () = check_base_type loc None abt sbt in
       let constr = LC (Member (Tag tag, S ret, Member (Id.s id)) %= S lname) in
       let constrs = Constraint (constr, constrs) in
       return (constrs, env)
    | [], [] -> 
       return (I,env)
    | (id,_ct,mv)::fields, (smember,sbt)::decl ->
       fail loc (Unreachable !^"mismatch in fields in infer_struct")
    | [], (Member smember,sbt)::_ ->
       fail loc (Generic_error (!^"field" ^^^ !^smember ^^^ !^"missing"))
    | (id,_,_)::_, [] ->
       fail loc (Generic_error (!^"supplying unexpected field" ^^^ !^(Id.s id)))
  in
  let* (constrs,env) = check fields decl.raw in
  return (Computational (ret, Struct (Tag tag), constrs), env)


and infer_union loc env sym id mv =
  fail loc (Unsupported !^"todo: union types")

and infer_array loc env mem_values = 
  fail loc (Unsupported !^"todo: array types")

let infer_object_value loc env ov =
  match ov with
  | M_OVinteger iv ->
     let new_lname = fresh () in
     let* i = Memory.integer_value_to_num loc iv in
     let constr = (LC (S new_lname %= Num i)) in
     let t = Computational (new_lname, Int, Constraint (constr, I)) in
     return (t, env)
  | M_OVpointer p -> 
     let* t = infer_ptrval loc env p in
     return (t,env)
  | M_OVarray items ->
     fail loc (Unsupported !^"todo: array types")
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
     let new_lname = fresh () in
     let constr = LC (S new_lname) in
     return (Computational (new_lname, Bool, Constraint (constr, I)), env)
  | M_Vfalse -> 
     let new_lname = fresh () in
     let constr = LC (Not (S new_lname)) in
     return (Computational (new_lname, Bool, Constraint (constr,I)), env)
  | M_Vlist (cbt, asyms) ->
     let new_lname = fresh () in
     let* ibt = Conversions.bt_of_core_base_type loc cbt in
     let* lnames = 
       mapM (fun asym -> 
           let (sym, loc) = aunpack loc asym in
           let* (ibt',lname) = get_avar loc env sym in
           let* () = check_base_type loc (Some sym) ibt' ibt in
           return (S lname)
         ) asyms 
     in
     let rt = Computational (new_lname, List ibt, 
              Constraint (LC (S new_lname %= List (lnames,ibt)), I)) in
     return (rt, env)
  | M_Vtuple asyms ->
     let* rt = infer_tuple loc env asyms in
     return (rt,env)



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


  


let args_from_asyms loc env asyms =
  mapM (fun asym ->
      let (sym,loc) = aunpack loc asym in
      let* (abt,lname) = get_avar loc env sym in
      return ((sym,(abt,lname)),loc)
    ) asyms 


let infer_pexpr loc env pe : (RT.t * env) m = 

  let* () = debug_print 1 (action "inferring pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget pe)) in

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in

  let* (typ,env) = match pe_ with
    | M_PEsym sym ->
       let ret = fresh () in
       let* (bt,lname) = get_avar loc env sym in
       let constr = LC (S ret %= S lname) in
       let typ = Computational (ret, bt, Constraint (constr, I)) in
       return (typ, env)
    | M_PEimpl i ->
       let* t = get_impl_constant loc env.global i in
       return (Computational (fresh (), t, I), env)
    | M_PEval v ->
       infer_value loc env v
    | M_PEconstrained _ ->
       fail loc (Unsupported !^"todo: PEconstrained")
    | M_PEundef (loc,undef) ->
       fail loc (Undefined undef)
    | M_PEerror (err,asym) ->
       let (sym, loc) = aunpack loc asym in
       fail loc (StaticError (err,sym))
    | M_PEctor (ctor, args) ->
       let* rt = infer_constructor loc env ctor args in
       return (rt, env)
    | M_PEarray_shift _ ->
       fail loc (Unsupported !^"todo: PEarray_shift")
    | M_PEmember_shift (asym, tag, id) ->
       let ret = fresh () in
       let member = Member (Id.s id) in
       let tag = Tag tag in
       let (sym, aloc) = aunpack loc asym in
       let* (bt,lname) = get_avar loc env sym in
       let* () = check_base_type loc (Some sym) bt Loc in
       let* stored_struct = stored_struct_to_of_tag loc env (S lname) tag in
       let* members = match stored_struct with
         | Some (_,{members; _}) -> return members
         | _ -> fail loc (Generic_error (!^"this location does not contain a struct with tag" ^^^ pp_tag tag))
       in
       let* faddr = assoc_err loc member members "check store field access" in
       let constr = LC (S ret %= faddr) in
       return (Computational (ret, Loc, Constraint (constr,I)), env)
    | M_PEnot asym ->
       let (sym,loc) = aunpack loc asym in
       let* (bt,lname) = get_avar loc env sym in
       let* () = check_base_type loc (Some sym) Bool bt in
       let ret = fresh () in 
       let constr = (LC (S ret %= Not (S lname))) in
       let rt = Computational (sym, Bool, Constraint (constr, I)) in
       return (rt, env)
    | M_PEop (op,asym1,asym2) ->
       let (sym1,loc1) = aunpack loc asym1 in
       let (sym2,loc2) = aunpack loc asym2 in
       let* (bt1,lname1) = get_avar loc1 env sym1 in
       let* (bt2,lname2) = get_avar loc2 env sym2 in
       let (((ebt1,ebt2),rbt),c) = binop_typ op in
       let* () = check_base_type loc1 (Some sym1) bt1 ebt1 in
       let ret = fresh () in
       let constr = LC (S ret %= c (S lname1) (S lname2)) in
       return (Computational (ret, rbt, Constraint (constr, I)), env)
    | M_PEstruct _ ->
       fail loc (Unsupported !^"todo: PEstruct")
    | M_PEunion _ ->
       fail loc (Unsupported !^"todo: PEunion")
    | M_PEmemberof _ ->
       fail loc (Unsupported !^"todo: M_PEmemberof")
    | M_PEcall (CF.Core.Impl impl, asyms) ->
       let* decl_typ = get_impl_fun_decl loc env.global impl in
       let* args = args_from_asyms loc env asyms in
       calltyp loc env args decl_typ
    | M_PEcall (CF.Core.Sym sym, asyms) ->
       let* (_loc,decl_typ) = get_fun_decl loc env.global sym in
       let* args = args_from_asyms loc env asyms in
       calltyp loc env args decl_typ
    | M_PEcase _ -> fail loc (Unreachable !^"PEcase in inferring position")
    | M_PElet _ -> fail loc (Unreachable !^"PElet in inferring position")
    | M_PEif _ -> fail loc (Unreachable !^"PElet in inferring position")
  in
  
  let* () = debug_print 3 (blank 3 ^^ item "inferred" (RT.pp typ)) in
  let* () = debug_print 1 PPrint.empty in
  return (typ,env)


let if_env_reachable loc env f = 
  let* (unreachable,_,_) = Solver.is_unreachable loc env in
  if unreachable then 
    let* () = warn !^"stopping to type check: unreachable" in
    return None 
  else 
    let* env = f env in
    return (Some env)


let merge_environments loc before_env envs =
  match envs with
  | [] -> fail loc (Unreachable !^"all control flow paths unreachable")
  | [env] -> return env
  | _ -> fail loc (Unsupported !^"merge_environments")



let rec check_pexpr loc env (e : 'bty mu_pexpr) typ = 

  let* () = debug_print 1 (action "checking pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let* (unreachable,_,_) = Solver.is_unreachable loc env in
  if unreachable then fail loc (Unreachable !^"inconsistent environment") else 

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in

  match e_ with
  | M_PEif (casym, e1, e2) ->
     let csym, cloc = aunpack loc casym in
     let* (cbt,clname) = get_avar cloc env csym in
     let* () = check_base_type cloc (Some csym) cbt Bool in
     let* oenv1 = if_env_reachable loc
                    (add_c env (LC (S clname)))
                    (fun env -> check_pexpr loc env e1 typ) in
     let* oenv2 = if_env_reachable loc 
                    (add_c env (LC (Not (S clname))))
                    (fun env -> check_pexpr loc env e2 typ) in
     let envs = filter_map id [oenv1;oenv2] in
     merge_environments loc env envs
  | M_PEcase (asym, pats_es) ->
     let (sym,loc) = aunpack loc asym in
     let* (bt,lname) = get_avar loc env sym in
     let* envs = 
       filter_mapM (fun (pat,pe) ->
           let* (env,names) = pattern_match loc env (S lname) pat bt in
           if_env_reachable loc env
             (fun env -> 
               let* env = check_pexpr loc env pe typ in
               remove_avars loc env names
             )
         ) pats_es
     in
     merge_environments loc env envs
  | M_PElet (p, e1, e2) ->
     let* (rt, env) = infer_pexpr loc env e1 in
     let* (env,anames,rnames) = match p with
       | M_Symbol asym -> 
          let sym, loc = aunpack loc asym in
          bind_to_name loc env rt sym
       | M_Pat pat -> 
          pattern_match_rt loc env pat rt
     in
     let* env = check_pexpr loc env e2 typ in
     let* () = check_resources_used loc env rnames in
     remove_avars loc env anames
  | _ ->
     let* (rt, env) = infer_pexpr loc env e in
     let* (env,(abt,lname),rnames) = bind_other loc env rt in
     let* env = subtype loc env [((fresh (),(abt,lname)),loc)] 
                  typ "function return type" in
     let* () = check_resources_used loc env rnames in
     return env



let rec infer_expr loc env e = 

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
       | M_PtrValidForDeref (a_ct, asym) ->
          let (ct, ct_loc) = aunpack loc a_ct in
          let (sym, loc) = aunpack loc asym in
          let ret = fresh () in
          let* (bt,lname)= get_avar loc env sym in
          let* () = check_base_type loc (Some sym) bt Loc in
          (* check more things? *)
          let* constr = match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* stored = stored_struct_to_of_tag loc env (S lname) (Tag tag) in
               return (LC (S ret %= Bool (is_some stored)))
            | _ ->
               let* points = points_to loc env (S lname) in
               return (LC (S ret %= Bool (is_some points)))
          in
          let ret = Computational (ret, Bool, Constraint (constr, I)) in
          return (ret, env)
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
          let* (abt,_lname) = get_avar loc env sym in
          let* () = check_base_type loc (Some sym) Int abt in
          let ret = fresh () in
          let* size = Memory.size_of_ctype loc ct in
          let* rt = match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* (stored,lbindings,rbindings) = 
                 Conversions.make_stored_struct loc env.global (Tag tag) (S ret) None in
               return (Computational (ret, Loc, lbindings) @@
                       Resource (StoredStruct stored, rbindings))
            | _ ->
               let r = Points {pointer = S ret; pointee = None; typ = ct; size} in
               return (Computational (ret, Loc, Resource (r, I)))
          in
          return (rt, env)
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (_is_dynamic, asym) -> 
          let (sym,loc) = aunpack loc asym in
          (* have remove resources of location instead? *)
          let* (abt,lname) = get_avar loc env sym in
          let* () = check_base_type loc (Some sym) Loc abt in
          (* revisit *)
          let* otyp = loc_type loc env (S lname) in
          begin match otyp with
            | None -> fail loc (Generic_error !^"cannot deallocate unowned location")
            | Some typ -> 
               let* env = remove_owned_subtree loc env false (S lname) typ in
               return (Computational (Sym.fresh (), Unit, I), env)
          end
       | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
          let (psym,ploc) = aunpack loc asym1 in
          let (vsym,vloc) = aunpack loc asym2 in
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* (pbt,plname) = get_avar ploc env psym in
          let* (vbt,vlname) = get_avar vloc env vsym in
          let* size = Memory.size_of_ctype loc ct in
          let* () = match pbt with
            | Loc -> return ()
            | _ -> fail ploc (Generic_error !^"the first store argument is not a pointer")
          in
          (* for consistency check value against Core annotation *)
          let* _ =
            let* t = Conversions.ctype false loc (fresh ()) ct in
            subtype loc (add_lvar env (vlname,Base vbt)) 
              [((vsym,(vbt,vlname)),vloc)] t 
              "checking store value against ctype annotation"
          in
          let rec store env (pointer : IT.t) (is_field : bool) ct size (this: IT.t) =
            let* () = debug_print 3 (action ("checking store at pointer " ^ plain (IT.pp false pointer))) in
            let* () = debug_print 3 (blank 3 ^^ item "ct" (pp_ctype ct)) in
            let* () = debug_print 3 (blank 3 ^^ item "value" (IT.pp false this)) in
            begin match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* owned = stored_struct_to_of_tag loc env pointer (Tag tag) in
               let* (r,stored) = match owned with
                 | Some (r,stored) ->
                    if not (Num.equal size stored.size)
                    then fail loc (Generic_error !^"store of different size")
                    else return (r,stored)
                 | None -> fail loc (Generic_error !^"store location is not of struct type" )
               in
               let rec aux (env,acc_bindings) = function
                 | (member,member_pointer) :: members ->
                    let* decl = Global.get_struct_decl loc env.global (Tag tag) in
                    let* ct = Tools.assoc_err loc member decl.ctypes "struct store" in
                    let* size = Memory.size_of_ctype loc ct in
                    let* (env, bindings) = 
                      store env member_pointer true ct size (Member (Tag tag, this, member)) in
                    aux (env, acc_bindings@@bindings) members
                 | [] ->
                    return (env, acc_bindings)
               in
               aux (env,I) stored.members
            | _ ->                
               let* does_point = points_to ploc env pointer in
               let* (r,p) = match does_point with
                 | Some (r,p) -> 
                    if Num.equal size p.size
                    then return (r,p)
                    else fail loc (Generic_error !^"store of different size")
                 | None -> 
                    if is_field then fail loc (Generic_error !^"missing ownership of struct field" )
                    else fail loc (Generic_error !^"missing ownership of struct location" )
               in
               let* env = use_resource loc env r in
               let bindings = 
                 Resource (Points {p with pointee = Some this; typ = ct}, I) in
               return (env,bindings)
          end in
          let* (env,bindings) = store env (S plname) false ct size (S vlname) in
          let rt = Computational (fresh (), Unit, bindings) in
          return (rt, env)
       | M_Load (a_ct, asym, _mo) -> 
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* size = Memory.size_of_ctype loc ct in
          let (psym,ploc) = aunpack loc asym in
          let* (pbt,plname) = get_avar ploc env psym in
          (* check pointer *)
          let* () = match pbt with
            | Loc -> return ()
            | _ -> fail ploc (Generic_error !^"load argument is not a pointer")
          in
          let ret = fresh () in

          let rec load (pointer : IT.t) (is_field : bool) ct size (this : IT.t) : (BT.t * LC.t list, Loc.t * TypeErrors.t) Except.t = 
            let* () = debug_print 3 (action ("checking load at pointer " ^ plain (IT.pp false pointer))) in
            let* () = debug_print 3 (blank 3 ^^ item "ct" (pp_ctype ct)) in
            match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* owned = stored_struct_to_of_tag loc env pointer (Tag tag) in
               let* (r,stored) = match owned with
                 | Some (r,stored) -> 
                    if not (Num.equal size stored.size) 
                    then fail loc (Generic_error !^"load of different size")
                    else return (r,stored)
                 | None -> fail loc (Generic_error !^"load location does not contain a stored struct" )
               in 
               let rec aux acc_constrs = function
                 | (member,member_pointer) :: members ->
                    let* decl = Global.get_struct_decl loc env.global (Tag tag) in
                    let* spec_bt = Tools.assoc_err loc member decl.raw "struct load" in
                    let* ct = Tools.assoc_err loc member decl.ctypes "struct load" in
                    let* size = Memory.size_of_ctype loc ct in
                    let* (has_bt, constrs) = 
                      load member_pointer true ct size (Member (Tag tag, this, member)) in
                    let* () = check_base_type ploc None has_bt spec_bt in
                    aux (acc_constrs@constrs) members
                 | [] ->
                    return acc_constrs
               in
               let* constrs = aux [] stored.members in
               return (Struct (Tag tag), constrs)
            | _ ->
               let* does_point = points_to ploc env pointer in
               let* (pointee,ct') = match does_point with
                 | Some (r,{pointee = Some pointee;typ;size=size';_}) -> 
                    if not (Num.equal size size') 
                    then fail loc (Generic_error !^"load of different size")
                    else return (pointee,typ)
                 | Some (r,_) -> 
                    if is_field then fail loc (Generic_error !^"struct field uninitialised" )
                    else fail loc (Generic_error !^"load location uninitialised" )
                 | None -> 
                    if is_field then fail loc (Generic_error !^"missing ownership of struct field" )
                    else fail loc (Generic_error !^"missing ownership of load location" )
               in
               let* (Base bt) = infer_index_term ploc env pointee in
               let constr = LC (this %= pointee) in
               let* _ = 
                 let* t = Conversions.ctype false loc (fresh ()) ct in
                 let temp_lname = fresh () in
                 let temp_env = add_lvar env (temp_lname, Base bt) in
                 let temp_env = add_c temp_env (LC (S temp_lname %= pointee)) in
                 subtype loc temp_env [((fresh (),(bt,temp_lname)),ploc)] t 
                   "checking load value against expected type"
               in
               return (bt, [constr])
          in
          let* (bt,constrs) = load (S plname) false ct size (S ret) in
          let rec make_constrs = function
            | [] -> I
            | constr :: constrs -> Constraint (constr, make_constrs constrs)
          in
          return (Computational (ret, bt, make_constrs constrs),env)
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
       return (Computational (fresh (), Unit, I), env)
    | M_Eccall (_, _ctype, fun_asym, asyms) ->
       let (sym1,loc1) = aunpack loc fun_asym in
       let* (bt,_lname) = get_avar loc1 env sym1 in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail loc1 (Generic_error !^"not a function pointer")
       in
       let* (_loc,decl_typ) = get_fun_decl loc env.global fun_sym in
       let* args = args_from_asyms loc env asyms in
       calltyp loc env args decl_typ
    | M_Eproc (_, fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            get_impl_fun_decl loc env.global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ) = get_fun_decl loc env.global sym in
            return decl_typ
       in
       let* args = args_from_asyms loc env asyms in
       calltyp loc env args decl_typ
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

  let* () = debug_print 3 (blank 3 ^^ item "inferred" (RT.pp typ)) in
  let* () = debug_print 1 PPrint.empty in
  return (typ,env)


let rec check_expr loc env (e : ('a,'bty) mu_expr) typ = 

  let* () = debug_print 1 (action "checking expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp env.local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let* (unreachable,_,_) = Solver.is_unreachable loc env in
  if unreachable then fail loc (Unreachable !^"inconsistent environment") else 

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (casym, e1, e2) ->
     let csym, cloc = aunpack loc casym in
     let* (cbt,clname) = get_avar cloc env csym in
     let* () = check_base_type cloc (Some csym) cbt Bool in
     let* oenv1 = if_env_reachable loc
                    (add_c env (LC (S clname)))
                    (fun env -> check_expr loc env e1 typ) in
     let* oenv2 = if_env_reachable loc 
                    (add_c env (LC (Not (S clname))))
                    (fun env -> check_expr loc env e2 typ) in
     let envs = filter_map id [oenv1;oenv2] in
     merge_environments loc env envs
  | M_Ecase (asym, pats_es) ->
     let (sym,loc) = aunpack loc asym in
     let* (bt,lname) = get_avar loc env sym in
     let* envs = 
       filter_mapM (fun (pat,pe) ->
           let* (env,names) = pattern_match loc env (S lname) pat bt in
           if_env_reachable loc env
             (fun env -> 
               let* env = check_expr loc env pe typ in
               remove_avars loc env names
             )
         ) pats_es
     in
     merge_environments loc env envs
  | M_Epure pe -> 
     check_pexpr loc env pe typ
  | M_Elet (p, e1, e2) ->
     let* (rt, env) = infer_pexpr loc env e1 in
     let* (env,anames,rnames) = match p with 
       | M_Symbol asym ->
          let sym, loc = aunpack loc asym in
          bind_to_name loc env rt sym
       | M_Pat pat ->
          pattern_match_rt loc env pat rt
     in
     let* env = check_expr loc env e2 typ in
     let* () = check_resources_used loc env rnames in
     remove_avars loc env anames
  | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (pat, e1, e2) ->
     let* (rt, env) = infer_expr loc env e1 in
     let* (env,anames,rnames) = pattern_match_rt loc env pat rt in
     let* env = check_expr loc env e2 typ in
     let* () = check_resources_used loc env rnames in
     remove_avars loc env anames
  | M_Esave (_ret, args, body) ->
     let* env = 
       fold_leftM (fun env (sym, (_, asym)) ->
           let (vsym,loc) = aunpack loc asym in
           let new_lname = fresh () in
           let* (bt,lname) = get_avar loc env vsym in
           let env = (add_lvar env (new_lname, Base bt)) in
           let env = (add_avar env (sym, (bt,new_lname))) in
           let env = add_c env (LC (S new_lname %= S lname)) in
           return env
         ) env args
     in
     check_expr loc env body typ
  | _ ->
     let* (rt, env) = infer_expr loc env e in
     let* (env,(abt,lname),rnames) = bind_other loc env rt in
     let* env = subtype loc env [((fresh (),(abt,lname)),loc)] 
                  typ "function return type" in
     let* () = check_resources_used loc env rnames in
     return env
     



let check_function loc genv fsym args rbt body ftyp =
  
  let* () = match body with
    | `EXPR body -> debug_print 1 (h1 ("Checking procedure " ^ (plain (Sym.pp fsym)))) 
    | `PEXPR body -> debug_print 1 (h1 ("Checking function " ^ (plain (Sym.pp fsym)))) 
  in

  let rec rt_consistent orbt rt =
    match rt with
    | RT.Computational (sname,sbt,t) ->
       begin match orbt with
       | Some rbt when BT.type_equal rbt sbt ->
          rt_consistent None t
       | Some rbt ->
          let mismatch = Mismatch {mname = None; has = (Base rbt); expected = Base sbt} in
          fail loc (Return_error mismatch)
       | None ->
          fail loc (Unreachable !^"function has multiple computational return values")
       end
    | RT.Logical (_,_,t)
    | RT.Resource (_,t)
    | RT.Constraint (_,t) -> rt_consistent orbt t
    | RT.I ->
       begin match orbt with
       | Some abt -> 
          fail loc (Unreachable !^"function has no computational return value")
       | None -> return ()
       end
  in

  let rec check env args rbt body ftyp =
    match args, ftyp with
    | (aname,abt)::args, FT.Computational (lname,sbt,ftyp) 
         when BT.type_equal abt sbt ->
       let new_lname = fresh () in
       let ftyp' = FT.subst_var {substitute=lname;swith=S new_lname} ftyp in
       let env = add_lvar env (new_lname, Base abt) in
       let env = add_avar env (aname,(abt,new_lname)) in
       check env args rbt body ftyp'
    | (aname,abt)::args, FT.Computational (sname,sbt,ftyp) ->
       let mis = Mismatch {mname = Some aname; has = (Base abt); expected = Base sbt} in
       fail loc (Call_error mis)
    | [], FT.Computational (sname,sbt,ftyp) ->
       fail loc (Call_error (Missing_A (sname, sbt)))
    | args, FT.Logical (sname,sls,ftyp) ->
       let new_lname = fresh () in
       let ftyp' = FT.subst_var {substitute=sname;swith=S new_lname} ftyp in
       check (add_lvar env (new_lname,sls)) args rbt body ftyp'       
    | args, FT.Resource (re,ftyp) ->
       check (add_rvar env (fresh (), (re,Unused))) args rbt body ftyp
    | args, FT.Constraint (lc,ftyp) ->
       check (add_c env lc) args rbt body ftyp
    | [], FT.Return rt ->
       let* () = rt_consistent (Some rbt) rt in
       begin match body with
         | `EXPR body -> check_expr loc env body rt
         | `PEXPR body -> check_pexpr loc env body rt
       end
    | (aname,abt)::_, FT.Return _ ->
       fail loc (Call_error (Surplus_A (aname, abt)))
  in
  (* check environment has no resources? *)
  let* _env = check (with_fresh_local genv) args rbt body ftyp in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in       

  return ()



                             
(* TODO: 
  - make call_typ and subtype accept non-A arguments  *)
