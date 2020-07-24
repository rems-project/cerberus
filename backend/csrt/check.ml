open Subst
open Uni
open Environment
open Global
open Local
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
open ReturnTypes


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




let check_base_type loc has expected =
  if BT.equal has expected then return () else 
    fail loc (Mismatch {has = (Base has); expected = Base expected})


let bind_l rt =
  let rec aux rt delta = 
    match rt with
    | Logical (s,ls,rt) ->
       let s' = fresh () in
       aux (subst_var_l {s; swith=S s'} rt) (add (mL s' ls) delta)
    | Resource (re,rt) -> aux rt (add (mUR re) delta)
    | Constraint (lc,rt) -> aux rt (add (mUC lc) delta)
    | I -> delta
  in
  aux rt Local.empty


let bind name (Computational (s,bt,rt)) =
  let s' = fresh () in
  let local' = add (mA name (bt,s'))
               (add (mL s' (Base bt)) Local.empty) in
  let local'' = bind_l (subst_var_l {s;swith=S s'} rt) in
  local'' ++ local'
  
let bind_other loc (Computational (s,bt,rt)) =
  let s' = fresh () in
  let local' = add (mL s' (Base bt)) Local.empty in
  let local'' = bind_l (subst_var_l {s;swith=S s'} rt) in
  return (local'' ++ local', (bt,s'))


let pattern_match loc this pat expected_bt =
  let rec aux local' this pat expected_bt = 
    match pat with
    | M_Pattern (annots, M_CaseBase (o_s, mbt)) ->
       let* has_bt = Conversions.bt_of_core_base_type loc mbt in
       let* () = check_base_type loc has_bt expected_bt in
       let s' = fresh () in 
       let local' = add (mL s' (Base has_bt)) local' in
       let* local' = match o_s with
         | Some s -> 
            if is_bound s local' 
            then fail loc (Name_bound_twice s)
            else return (add (mA s (has_bt,s')) local')
         | None -> return local'
       in
       let local' = add (mUC (LC (this %= S s'))) local' in
       return local'
    | M_Pattern (annots, M_CaseCtor (constructor, pats)) ->
       match constructor with
       | M_Cnil mbt ->
          let* item_bt = Conversions.bt_of_core_base_type loc mbt in
          begin match pats with
          | [] ->
             if BT.equal (List item_bt) expected_bt 
             then return local'
             else fail loc (Mismatch {has=Base (List item_bt);
                                      expected=Base expected_bt})
          | _ -> 
             fail loc (Constructor_wrong_argument_number 
                         {constructor;expected=0;has=List.length pats})
          end
       | M_Ccons ->
          begin match expected_bt, pats with
          | List item_bt, [p1;p2] ->
             let* local' = aux local' (Head this) p1 item_bt in
             let* local' = aux local' (Tail this) p2 expected_bt in
             return local'
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
             let rec components local' i pats bts =
               match pats, bts with
               | [], [] -> return local'
               | pat::pats, bt::bts ->
                  let* local' = aux local' (Nth (i, this)) pat bt in
                  components local' (i+1) pats bts
               | _, _ ->
                  fail loc (Constructor_wrong_argument_number 
                              {constructor;
                               expected=i+List.length pats;
                               has=i+List.length pats})
             in
             let* local' = components local' 0 pats bts in
             return local'
          | _ ->
             fail loc (Generic_error (!^"tuple pattern incompatible with expected type" ^^^ 
                                        BT.pp false expected_bt))
          end
       | M_Cspecified ->
          begin match pats with
          | [pat] -> aux local' this pat expected_bt
          | _ -> fail loc (Constructor_wrong_argument_number 
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
  let* local' = aux Local.empty this pat expected_bt in
  let new_a = Local.filter_a (fun s _ _ -> Some s) local' in
  return (local',new_a)

  


let pattern_match_rt (loc : Loc.t) pat (Computational (s,bt,rt)) =
  (* The pattern-matching might de-struct 'bt'. For easily making
     constraints carry over to those values, record (lname,bound) as a
     logical variable and record constraints about how the variables
     introduced in the pattern-matching relate to (name,bound). *)
  let s' = fresh () in
  let local' = add (mL s' (Base bt)) Local.empty in
  let local'' = bind_l (subst_var_l {s; swith=S s'} rt) in
  let* (local''',_) = pattern_match loc (S s') pat bt in
  return (local''' ++ local'' ++ local')





let match_resource loc {local;global} shape = 
  let* found = 
    filter_rM (fun name t ->
        match shape, t  with
        | `Points pointer, RE.Points p' ->
           let* holds = Solver.equal loc {local;global} pointer p'.pointer in
           return (if holds then Some (Points p',name) else None)
        | `StoredStruct (pointer,tag), RE.StoredStruct s' when tag = s'.tag ->
           let* holds = Solver.equal loc {local;global} pointer s'.pointer in
           return (if holds then Some (StoredStruct s',name) else None)
        | _ -> 
           return None
      ) local
  in
  at_most_one loc !^"multiple matching resources" found


let points_to loc {local;global} loc_it = 
  let* points = 
    filter_rM (fun name t ->
        match t with
        | RE.Points p ->
           let* holds = Solver.equal loc {local;global} loc_it p.pointer in
           return (if holds then Some (name,p) else None)
        | _ -> 
           return None
      ) local
  in
  at_most_one loc !^"multiple points-to for same pointer" points


let stored_struct_to_of_tag loc {local;global} loc_it tag = 
  let* stored = 
    filter_rM (fun name t ->
        match t with
        | RE.StoredStruct s when s.tag = tag ->
           let* holds = Solver.equal loc {local;global} loc_it s.pointer in
           return (if holds then Some (name,s) else None)
        | _ -> 
           return None
      ) local
  in
  at_most_one loc !^"multiple points-to for same pointer" stored


let abstract_concrete_resource = function
  | Points p -> `Points p.pointer
  | StoredStruct s -> `StoredStruct (s.pointer,s.tag)

let match_concrete_resource loc {local;global} resource = 
  match_resource loc {local;global} (abstract_concrete_resource resource)




let guess_loc_type loc {local;global} pointer = 
  let* resources = 
    filter_rM (fun name t ->
        match t with
        | RE.Points p' ->
           let* holds = Solver.equal loc {local;global} pointer p'.pointer in
           return (if holds then Some p'.typ else None)
        | RE.StoredStruct ({tag = Tag tag; _} as s') ->
           let* holds = Solver.equal loc {local;global} pointer s'.pointer in
           let ct = CF.Ctype.Ctype ([], CF.Ctype.Struct tag) in
           return (if holds then Some ct else None)
      ) local
  in
  at_most_one loc !^"multiple resources for same pointer" resources





let pp_unis unis = 
  let pp_entry (sym, Uni.{resolved}) =
    match resolved with
    | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ IT.pp true res
    | None -> Sym.pp sym ^^^ !^"unresolved"
  in
  pp_list pp_entry (SymMap.bindings unis)



let rec remove_owned_subtree loc {local;global} is_field pointer ct =
  match ct with
  | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
     let* decl = Global.get_struct_decl loc global (Tag tag) in
     let* stored = stored_struct_to_of_tag loc {local;global} pointer (Tag tag) in
     begin match stored with
     | Some (r,stored) -> 
        fold_leftM (fun local (member,member_pointer) ->
            let* ct = Tools.assoc_err loc member decl.ctypes 
                                      (Unreachable !^"remove_owned_subtree") in
            let* local = use_resource loc local r [loc] in
            remove_owned_subtree loc {local;global} true member_pointer ct
          ) local stored.members
     | None ->
        fail loc (Generic_error !^"missing ownership for de-allocating")
     end
  | _ ->
     let* points = points_to loc {local;global} pointer in
     begin match points with
     | Some (r,_) -> 
        use_resource loc local r [loc]
     | None -> fail loc (Generic_error !^"missing ownership for de-allocating")
     end
  





let rec infer_index_term (loc : Loc.t) (env: Environment.t) (it : IT.t) = 
  match it with
  | Num _ -> return (Base Int)
  | Bool _ -> return (Base Bool)
  | Add (t,t') | Sub (t,t') | Mul (t,t') | Div (t,t') 
  | Exp (t,t') | Rem_t (t,t') | Rem_f (t,t')  ->
     let* () = check_index_term loc env (Base Int) t in
     let* () = check_index_term loc env (Base Int) t' in
     return (Base Int)
  | EQ (t,t') | NE (t,t') | LT (t,t')
  | GT (t,t') | LE (t,t') | GE (t,t') ->
     let* () = check_index_term loc env (Base Int) t in
     let* () = check_index_term loc env (Base Int) t' in
     return (Base Bool)
  | Null t ->
     let* () = check_index_term loc env (Base Loc) t in
     return (Base Bool)
  | And (t,t') | Or (t,t') | Impl (t,t') ->
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
  | Nth (n,it') ->
     let* t = infer_index_term loc env it' in
     begin match t with
     | Base (Tuple ts) ->
        begin match List.nth_opt ts n with
        | Some t -> return (Base t)
        | None -> fail loc (Illtyped_it it)
        end
     | _ -> fail loc (Illtyped_it it)
     end
  | Member (tag, it', member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc env.global tag in
     let* bt = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
     return (Base bt)
  | MemberOffset (tag, it', member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc env.global tag in
     let* _ = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
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
  | Head it' ->
     let* ls = infer_index_term loc env it' in
     begin match ls with
     | Base (List bt) -> return (Base bt)
     | _ -> fail loc (Illtyped_it it)
     end
  | Tail it' ->
     let* ls = infer_index_term loc env it in
     begin match ls with
     | Base (List bt) -> return (Base (List bt))
     | _ -> fail loc (Illtyped_it it)
     end
  | S s ->
     get_l loc env.local s

and check_index_term loc env (ls : LS.t) (it : IT.t) = 
  let* ls' = infer_index_term loc env it in
  if LS.equal ls ls' then return ()
  else fail loc (Illtyped_it it)



let pp_argslocs =
  pp_list (fun ((n,(bt,lname)),(_l:Loc.t)) -> 
      typ (Sym.pp n) (parens (BT.pp false bt ^^^ bar ^^^ Sym.pp lname)))




let subtype loc_ret {local;global} arg (rtyp : RT.t) ppdescr =

  let module STS = struct

    type t = 
      { typ: RT.l;
        lvars: (Sym.t * LS.t) list;
        constraints : LC.t list }

    let subst_var s spec = 
      { spec with 
        typ = RT.subst_var_l s spec.typ;
        constraints = List.map (LC.subst_var s) spec.constraints }

    let subst_vars = Subst.make_substs subst_var

  end in


  let ((aname,(abt,lname)),arg_loc) = arg in
  let Computational (sname,sbt,rtyp) = rtyp in

  let* () = 
    if BT.equal abt sbt then return ()
    else fail loc_ret (Mismatch {has = Base abt; expected = Base sbt})
  in

  let spec = STS.{ typ = rtyp ; lvars = []; constraints = []} in
  let spec = STS.subst_var {s=sname;swith=S lname} spec in
  let local = add (mL lname (Base abt)) local in

  let* () = debug_print 1 (action ppdescr) in
  let* () = debug_print 2 PPrint.empty in

  let* () = debug_print 2 (blank 3 ^^ item "value" (pp_argslocs [arg])) in
  let* () = debug_print 2 (blank 3 ^^ item "specification" (RT.pp_l spec.STS.typ)) in


  let rec aux local (unis : (IT.t Uni.t) SymMap.t) spec = 
    let* () = debug_print 2 (blank 3 ^^ item "specification" (RT.pp_l spec.STS.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp local)) in
    match spec.typ with
    | I -> 
       begin match spec.lvars, spec.constraints with
       | (sname,sls) :: lvars, _ ->
          begin match SymMap.find_opt sname unis with
          | Some Uni.{resolved = None} -> 
             fail loc_ret (Unconstrained_l sname)
          | Some Uni.{resolved = Some it} ->
             let* als = infer_index_term loc_ret {local;global} it in
             if LS.equal als sls then
               let spec = STS.{ spec with lvars } in
               let spec = STS.subst_var {s=sname;swith=it} spec in
               aux local unis spec
             else
               fail loc_ret (Mismatch {has = als; expected = sls})
          | None ->
             fail loc_ret (Unreachable !^"did not find unification variable")
          end
       | [], (c :: constraints) -> 
          let spec = STS.{ spec with constraints } in
          let* (holds,_,_) = Solver.constraint_holds loc_ret {local;global} c in
          if holds then aux local unis spec
          else fail loc_ret (Unsat_constraint c)
       | [], [] ->
          return local
       end
    | Logical (sname,sls,rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = STS.{ spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp } in
       let spec = STS.subst_var {s=sname;swith=S sym} spec in
       aux local unis spec
    | Resource (re,rtyp) -> 
       let* matched = match_concrete_resource loc_ret {local;global} re in
       begin match matched with
       | None -> 
          fail loc_ret (Missing_R re)
       | Some (resource',r) ->
          let* () = debug_print 3 (blank 3 ^^ item "unis" (pp_unis unis)) in
          match RE.unify_non_pointer re resource' unis with
          | None -> fail loc_ret (Missing_R re)
          | Some unis ->
             let* local = use_resource loc_ret local r [loc_ret] in
             let (_,new_substs) = Uni.find_resolved local unis in
             let spec = STS.{ spec with typ = rtyp } in
             let spec = STS.subst_vars new_substs spec in
             aux local unis spec
       end
    | Constraint (constr,rtyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = rtyp} in
       aux local unis spec  
  in

  aux local SymMap.empty spec




let calltyp loc_call {local;global} args (rtyp : FT.t) =

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

  let rec aux local args unis (spec : calltyp_spec) = 
    let* () = debug_print 2 (blank 3 ^^ item "arguments" (pp_argslocs args)) in
    let* () = debug_print 2 (blank 3 ^^ item "specification" (FT.pp spec.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (Local.pp local)) in
    match args, spec.typ with
    | [], Return rt -> 
       begin match spec.lvars, spec.constraints with
       | (sname,sls) :: lvars, _ ->
          begin match SymMap.find_opt sname unis with
          | Some Uni.{resolved = None} -> 
             fail loc_call (Unconstrained_l sname)
          | Some Uni.{resolved = Some it} ->
             let* als = infer_index_term loc_call {local;global} it in
             if LS.equal als sls then
               let spec = CTS.{ spec with lvars } in
               let spec = CTS.subst_var {s=sname;swith=it} spec in
               aux local args unis spec
             else
               fail loc_call (Mismatch {has = als; expected = sls})
          | None ->
             fail loc_call (Unreachable !^"did not find unification variable")
          end
       | [], (c :: constraints) -> 
          let spec = CTS.{ spec with constraints } in
          let* (holds,_,_) = Solver.constraint_holds loc_call {local;global} c in
          if holds then aux local args unis spec
          else fail loc_call (Unsat_constraint c)
       | [], [] ->
          return (rt,local)
       end
    | [], Computational (sname,sbt,_) -> 
       fail loc_call (Missing_A (sname, sbt))
    | ((aname,(abt,_lname)),arg_loc) :: _, Return _ -> 
       fail arg_loc (Surplus_A (aname, abt))
    | ((aname,(abt,lname)),arg_loc) :: args, Computational (sname,sbt,rtyp) ->
       if BT.equal abt sbt then
         let spec = CTS.{ spec with typ = rtyp} in
         let spec = CTS.subst_var {s=sname;swith=S lname} spec in
         let local = add (mL lname (Base abt)) local in
         aux local args unis spec
       else
         fail loc_call (Mismatch {has = Base abt; expected = Base sbt})
    | _, Logical (sname,sls,rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = CTS.{ spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp} in
       let spec = CTS.subst_var {s=sname;swith=S sym} spec in
       aux local args unis spec
    | _, Resource (re,rtyp) -> 
       let* matched = match_concrete_resource loc_call {local;global} re in
       begin match matched with
       | None -> 
          fail loc_call (Missing_R re)
       | Some (resource',r) ->
          let* () = debug_print 3 (action ("trying resource " ^ plain (RE.pp false resource'))) in
          let* () = debug_print 3 (blank 3 ^^ item "unis" (pp_unis unis)) in
          match RE.unify_non_pointer re resource' unis with
          | None -> fail loc_call (Missing_R re)
          | Some unis ->
             let* local = use_resource loc_call local r [loc_call] in
             let (_,new_substs) = Uni.find_resolved local unis in
             let spec = CTS.{ spec with typ = rtyp } in
             let spec = CTS.subst_vars new_substs spec in
             aux local args unis spec
       end
    | _, Constraint (constr,rtyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = rtyp} in
       aux local args unis spec  
  in

  aux local args SymMap.empty { typ = rtyp ; lvars = []; constraints = []}




let infer_tuple loc {local;global} asyms = 
  let new_lname = fresh () in
  let* (bts,constr,_) = 
    fold_leftM (fun (bts,constr,i) asym -> 
        let (sym, loc) = aunpack loc asym in
        let* (bt,lname) = get_a loc local sym in
        let constr = (Nth (i, S new_lname) %= S lname) %& constr in
        return (bts@[bt],constr,i+1)
      ) ([],IT.Bool true, 0) asyms 
  in
  let bt = Tuple bts in
  return (Computational (new_lname, bt, Constraint (LC constr, I)))


let infer_constructor loc {local;global} constructor asyms = 
  match constructor with
  | M_Ctuple -> 
     infer_tuple loc {local;global} asyms
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
        let* (bt,lname) = get_a loc local sym in
        return (Computational (new_lname, bt, 
                Constraint (LC (S new_lname %= S lname),I)))
     | _ ->
        fail loc (Constructor_wrong_argument_number 
                    {constructor; has=List.length asyms; expected=1})
     end
  | M_Cnil mbt -> 
     let new_lname = fresh () in
     let* item_bt = Conversions.bt_of_core_base_type loc mbt in
     if asyms = [] then
        return (Computational (new_lname, List item_bt, 
                Constraint (LC (S new_lname %= Nil item_bt),I)))
     else
        fail loc (Constructor_wrong_argument_number 
                    {constructor; has=List.length asyms; expected=0})
  | M_Ccons -> 
     let new_lname = fresh () in
     begin match asyms with
     | [asym1;asym2] -> 
        let (sym1, loc1) = aunpack loc asym1 in
        let (sym2, loc2) = aunpack loc asym2 in
        let* (bt1,lname1) = get_a loc local sym1 in
        let* (bt2,lname2) = get_a loc local sym2 in
        let* () = check_base_type loc2 bt2 (List bt1) in
        return (Computational (new_lname, bt2, 
                Constraint (LC (S new_lname %= Cons (S lname1, S lname2)),I)))
     | _ ->
        fail loc (Constructor_wrong_argument_number 
                    {constructor; has=List.length asyms; expected=2})
     end
  | M_Cfvfromint -> fail loc (Unsupported !^"floats")
  | M_Civfromfloat -> fail loc (Unsupported !^"floats")




let infer_ptrval loc {local;global} ptrval = 
  let new_lname = fresh () in
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let constr = (LC (Null (S new_lname))) in
      return (Computational (new_lname, Loc, Constraint (constr, I))) )
    ( fun sym -> 
      return (Computational (new_lname, FunctionPointer sym, I)) )
    ( fun _prov loc ->      
      let constr = LC (S new_lname %= Num loc) in
      return (Computational (new_lname, Loc, Constraint (constr, I))) )
    ( fun () -> fail loc (Unreachable !^"unspecified pointer value") )


let rec infer_mem_value loc {local;global} mem = 
  let open CF.Ctype in
  CF.Impl_mem.case_mem_value mem
    ( fun _ctyp -> fail loc (Unsupported !^"ctypes as values") )
    ( fun it _sym -> 
      (* todo: do something with sym *)
      let* t = Conversions.ctype false loc (fresh ()) (Ctype ([], Basic (Integer it))) in
      return t )
    ( fun it iv -> 
      let new_lname = fresh () in
      let* v = Memory.integer_value_to_num loc iv in
      let val_constr = LC (S new_lname %= Num v) in
      let* type_constr = Conversions.integerType_constraint loc (S new_lname) it in
      let* (holds,_,_) = 
        Solver.constraint_holds_given_constraints loc 
          {local=add (mL new_lname (Base BT.Int)) local; global} 
          [val_constr] type_constr in
      match holds with
      | true -> 
         return (Computational (new_lname, Int, Constraint (val_constr, I)))
      | false -> fail loc (Generic_error !^"Integer value does not satisfy range constraint")
    )
    ( fun ft fv -> Conversions.floatingType loc )
    ( fun _ctype ptrval ->
      (* maybe revisit and take ctype into account *)
      let* t = infer_ptrval loc {local;global} ptrval in
      return t )
    ( fun mem_values -> infer_array loc {local;global} mem_values )
    ( fun sym fields -> infer_struct loc {local;global} (sym,fields) )
    ( fun sym id mv -> infer_union loc {local;global} sym id mv )


and infer_struct loc {local;global} (tag,fields) =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  fail loc (Unsupported !^"implement again")
  (* let* decl = Global.get_struct_decl loc env.global (Tag tag) in
   * let ret = fresh () in
   * let rec check fields decl =
   *   match fields, decl with
   *   | (id,_ct,mv)::fields, (smember,sbt)::decl when Member (Id.s id) = smember ->
   *      let* (constrs,env) = check fields decl in
   *      let* (rt, env) = infer_mem_value loc env mv in
   *      let* (env,(abt,lname),rnames) = bind_other loc env rt in
   *      let* () = check_base_type loc None abt sbt in
   *      let constr = LC (Member (Tag tag, S ret, Member (Id.s id)) %= S lname) in
   *      let constrs = Constraint (constr, constrs) in
   *      return (constrs, env)
   *   | [], [] -> 
   *      return (I,env)
   *   | (id,_ct,mv)::fields, (smember,sbt)::decl ->
   *      fail loc (Unreachable !^"mismatch in fields in infer_struct")
   *   | [], (Member smember,sbt)::_ ->
   *      fail loc (Generic_error (!^"field" ^^^ !^smember ^^^ !^"missing"))
   *   | (id,_,_)::_, [] ->
   *      fail loc (Generic_error (!^"supplying unexpected field" ^^^ !^(Id.s id)))
   * in
   * let* (constrs,env) = check fields decl.raw in
   * return (Computational (ret, Struct (Tag tag), constrs), env) *)


and infer_union loc {local;global} sym id mv =
  fail loc (Unsupported !^"todo: union types")

and infer_array loc {local;global} mem_values = 
  fail loc (Unsupported !^"todo: array types")

let infer_object_value loc {local;global} ov =
  match ov with
  | M_OVinteger iv ->
     let new_lname = fresh () in
     let* i = Memory.integer_value_to_num loc iv in
     let constr = (LC (S new_lname %= Num i)) in
     return (Computational (new_lname, Int, Constraint (constr, I)))
  | M_OVpointer p -> 
     infer_ptrval loc {local;global} p
  | M_OVarray items ->
     fail loc (Unsupported !^"todo: array types")
  | M_OVstruct (tag, fields) -> 
     infer_struct loc {local;global} (tag,fields)
  | M_OVunion (sym,id,mv) -> 
     infer_union loc {local;global} sym id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")


let infer_value loc {local;global} v : ReturnTypes.t m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc {local;global} ov
  | M_Vunit ->
     return (Computational (fresh (), Unit, I))
  | M_Vtrue ->
     let new_lname = fresh () in
     let constr = LC (S new_lname) in
     return (Computational (new_lname, Bool, Constraint (constr, I)))
  | M_Vfalse -> 
     let new_lname = fresh () in
     let constr = LC (Not (S new_lname)) in
     return (Computational (new_lname, Bool, Constraint (constr,I)))
  | M_Vlist (cbt, asyms) ->
     let new_lname = fresh () in
     let* ibt = Conversions.bt_of_core_base_type loc cbt in
     let* lnames = 
       mapM (fun asym -> 
           let (sym, loc) = aunpack loc asym in
           let* (ibt',lname) = get_a loc local sym in
           let* () = check_base_type loc ibt' ibt in
           return (S lname)
         ) asyms 
     in
     return (Computational (new_lname, List ibt, 
             Constraint (LC (S new_lname %= List (lnames,ibt)), I)))
  | M_Vtuple asyms ->
     infer_tuple loc {local;global} asyms



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


  






let args_from_asyms loc local asyms =
  mapM (fun asym ->
      let (sym,loc) = aunpack loc asym in
      let* (abt,lname) = get_a loc local sym in
      return ((sym,(abt,lname)),loc)
    ) asyms 




(* let union_used loc urmap1 urmap2 = 
 *   let open Option in
 *   SymMap.fold (fun sym (r,where) m ->
 *       let* m = m in
 *       match SymMap.find_opt sym m with
 *       | Some (r',where') when RE.equal r r' -> 
 *          let m = SymMap.remove sym m in
 *          return (SymMap.add sym (r,where@where') m)
 *       | Some (r',where') ->
 *          fail
 *       | None ->
 *          return (SymMap.add sym (r,where) m)
 *     )
 *     urmap1
 *     (return urmap2)
 *   
 * 
 * let merge_resources loc {local;global} first others =
 * 
 *     let module T = TreeResources in
 *     let solver_eq = Solver.equal loc {local;global} in
 * 
 *     let* first_mt = T.merge_trees_of_map loc global solver_eq first in
 *     let* others_mt = mapM (T.merge_trees_of_map loc global solver_eq) others in
 * 
 *     let rec merge_mtrees mtrees1 mtrees2 =
 *       match mtrees1 with
 *       | [] ->
 *          if mtrees2 = [] then return [] 
 *          else fail loc (Generic_error !^"cannot merge environments")
 *       | (sym1,r1)::mtrees1 ->
 *          let* filtered = 
 *            filter_mapM (fun (sym2,r2) -> 
 *                match r1, r2 with 
 *                | T.TPoints p1, T.TPoints p2 ->
 *                   let* holds = solver_eq p1.pointer p2.pointer in
 *                   return (if holds then Some (sym2,r2) else None)
 *                | T.TStoredStruct s1, T.TStoredStruct s2 when s1.tag = s2.tag ->
 *                   let* holds = solver_eq s1.pointer s2.pointer in
 *                   return (if holds then Some (sym2,r2) else None)
 *                | _ -> 
 *                   return None
 *              ) mtrees2 
 *          in
 *          let* found = at_most_one loc !^"points-to not unique" filtered in
 *          begin match found with
 *          | None -> fail loc (Generic_error !^"cannot merge resources")
 *          | Some (sym2,r2) ->
 *             let mtrees2 = List.filter (fun (sym,_) -> not (Sym.equal sym sym2)) mtrees2 in
 *             let* merged = T.merge_merge_trees loc r1 r2 in
 *             let* mergeds = merge_mtrees mtrees1 mtrees2 in
 *             return ((sym1,merged) :: mergeds)
 *          end
 *     in
 * 
 *     let* merged_trees = fold_leftM merge_mtrees first_mt others_mt in
 *     let* (trees,news) = T.merge_trees_to_trees loc (map snd merged_trees) in
 *     let local = 
 *       fold_left 
 *         (fun local (name,bt,cs) -> 
 *           let local = add_l local (name, Base bt) in
 *           fold_left (fun local (LC c, it) -> 
 *               add_uc local (LC (c %==> (S name %= it)))) local cs 
 *         ) 
 *         local news 
 *     in
 *     return { local with rvars = T.trees_to_map trees }
 * 
 * 
 * let mapped_differently loc pp sym v v' =
 *   fail loc (Unreachable (Sym.pp sym ^^ !^" mapped to " ^^ 
 *                            pp v ^^ !^" and to " ^^ pp v'))
 * 
 * 
 * (\* similar to D. Walker Substructural type systems 1 *\)
 * let minus_symmap loc (equality,pp) m1 m2 =
 *   symmap_foldM (fun sym v acc ->
 *       match SymMap.find_opt sym m2 with
 *       | None -> return (SymMap.add sym v acc)
 *       | Some v' when equality v v' -> return acc
 *       | Some v' -> mapped_differently loc pp sym v v'
 *     ) m1 (SymMap.empty)
 * 
 * let union_symmap loc (equality,pp) m1 m2 = 
 *   symmap_foldM (fun sym v acc ->
 *       match SymMap.find_opt sym acc with
 *       | None -> return (SymMap.add sym v acc)
 *       | Some v' when equality v v' -> return acc
 *       | Some v' -> mapped_differently loc pp sym v v'
 *     ) m1 m2
 * 
 * 
 * let eq equality m1 m2 =
 *   let all_symbols = List.map fst (SymMap.bindings m1 @ SymMap.bindings m2) in
 *   List.for_all (fun sym ->
 *       match SymMap.find_opt sym m1, 
 *             SymMap.find_opt sym m2 with
 *       | None, None -> true
 *       | Some v1, Some v2 -> equality v1 v2
 *       | _ -> false
 *     ) all_symbols
 * 
 * 
 * let rec avars_equal avars1 avars2 = 
 *   match avars1, avars2 with
 *   | [], [] -> true
 *   | (cs1,(bt1,ls1))::avars1, (cs2,(bt2,ls2))::avars2 ->
 *      Sym.equal cs1 cs2 && BT.equal bt1 bt2 && Sym.equal ls1 ls2 &&
 *      avars_equal avars1 avars2
 *   | _ -> false
 * 
 * let merge_local_environments loc {local=old_local;global} paths =
 *   let* () = debug_print 1 (action "merging local environments") in
 *   let* () = debug_print 1 (blank 3 ^^ item "old" (Local.pp old_local)) in
 *   match paths with
 *   | [] -> fail loc (Unreachable !^"no reachable control-flow path")
 *   | (first_cond,first_local) :: others ->
 *      let* pre_local = 
 *        fold_leftM (fun acc (LC cond,new_local) -> 
 *            let err s = Generic_error !^("error computing pre_local: " ^ s) in
 *            let* () = debug_print 1 (blank 3 ^^ item "new" (Local.pp new_local)) in
 *            if avars_equal acc.avars new_local.avars then
 *              let* lvars = union_symmap loc (LS.equal,LS.pp false) acc.lvars new_local.lvars in
 *              let* cvar_diff = minus_symmap loc (LC.equal,LC.pp false) new_local.cvars old_local.cvars in
 *              let* cvars = union_symmap loc (LC.equal,LC.pp false) acc.cvars (SymMap.map (fun (LC c) -> LC (cond %==> c)) cvar_diff) in
 *              let* urvars = of_option loc (err "uvars") (union_used loc acc.urvars new_local.urvars) in
 *              return { acc with lvars; cvars }
 *            else 
 *              fail loc (Generic_error !^"error computing pre_local")
 *          ) {Local.empty with avars = first_local.avars;
 *                              cvars = old_local.cvars } paths
 *      in
 *      let* local = 
 *        merge_resources loc {local=pre_local;global}
 *                        (first_cond,first_local.rvars) 
 *                        (List.map (fun (cond,local) -> (cond,local.rvars)) others)
 *      in
 *      let* () = debug_print 1 (blank 3 ^^ item "merged" (Local.pp local)) in
 *      return local
 * 
 * 
 * let merge_path_rts loc rts = 
 *   let* () = debug_print 1 (action "merging return types") in
 *   let* () = debug_print 1 (blank 3 ^^ item "rts" (pp_list (fun (bt,(lc,lname)) -> (LC.pp false lc ^^ colon ^^^ BT.pp false bt ^^^ bar ^^^ (Sym.pp lname))) rts)) in
 *   let newname = fresh () in
 *   match rts with
 *   | [] -> fail loc (Unreachable !^"no reachable control-flow path")
 *   | (bt,_)::_ -> 
 *      let rec aux = function
 *        | [] -> return I
 *        | (has_bt,(LC c,lname))::rest ->
 *           let* () = check_base_type loc has_bt bt in
 *           let* rt = aux rest in
 *           return (Constraint (LC (c %==> (S newname %= S lname)), rt))
 *      in
 *      let* rt = aux rts in
 *      let rt = Computational (newname, bt, rt) in
 *      let* () = debug_print 1 (blank 3 ^^ item "merged" (RT.pp rt)) in
 *      return rt *)
     


(* FIX THIS *)
let merge_local_environments loc {local;global} = function
  | [] -> fail loc (Unreachable !^"no reachable control-flow path")
  | first::others ->
     return (snd first)


let ensure_reachable loc env= 
  let* unreachable = Solver.is_unreachable loc env in
  if unreachable 
  then fail loc (Unreachable !^"inconsistent environment") 
  else return ()


let rec infer_pexpr loc {local;global} pe : (RT.t * Local.t) m = 

  let* () = debug_print 1 (action "inferring pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget pe)) in

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = update_loc loc annots in

  let* (rt,local) = match pe_ with
    | M_PEsym sym ->
       let ret = fresh () in
       let* (bt,lname) = get_a loc local sym in
       let constr = LC (S ret %= S lname) in
       let rt = Computational (ret, bt, Constraint (constr, I)) in
       return (rt, local)
    | M_PEimpl i ->
       let* t = get_impl_constant loc global i in
       return (Computational (fresh (), t, I), local)
    | M_PEval v ->
       let* rt = infer_value loc {local;global} v in
       return (rt,local)
    | M_PEconstrained _ ->
       fail loc (Unsupported !^"todo: PEconstrained")
    | M_PEundef (loc,undef) ->
       fail loc (Undefined undef)
    | M_PEerror (err,asym) ->
       let (sym, loc) = aunpack loc asym in
       fail loc (StaticError (err,sym))
    | M_PEctor (ctor, args) ->
       let* rt = infer_constructor loc {local;global} ctor args in
       return (rt, local)
    | M_PEarray_shift _ ->
       fail loc (Unsupported !^"todo: PEarray_shift")
    | M_PEmember_shift (asym, tag, id) ->
       let ret = fresh () in
       let member = Member (Id.s id) in
       let tag = Tag tag in
       let (sym, aloc) = aunpack loc asym in
       let* (bt,lname) = get_a loc local sym in
       let* () = check_base_type loc bt Loc in
       let* stored_struct = stored_struct_to_of_tag loc {local;global} (S lname) tag in
       let* members = match stored_struct with
         | Some (_,{members; _}) -> return members
         | _ -> fail loc (Generic_error (!^"this location does not contain a struct with tag" ^^^ pp_tag tag))
       in
       let* faddr = assoc_err loc member members (Unreachable !^"check store field access") in
       let constr = LC (S ret %= faddr) in
       return (Computational (ret, Loc, Constraint (constr,I)), local)
    | M_PEnot asym ->
       let (sym,loc) = aunpack loc asym in
       let* (bt,lname) = get_a loc local sym in
       let* () = check_base_type loc Bool bt in
       let ret = fresh () in 
       let constr = (LC (S ret %= Not (S lname))) in
       let rt = Computational (sym, Bool, Constraint (constr, I)) in
       return (rt, local)
    | M_PEop (op,asym1,asym2) ->
       let (sym1,loc1) = aunpack loc asym1 in
       let (sym2,loc2) = aunpack loc asym2 in
       let* (bt1,lname1) = get_a loc1 local sym1 in
       let* (bt2,lname2) = get_a loc2 local sym2 in
       let (((ebt1,ebt2),rbt),c) = binop_typ op in
       let* () = check_base_type loc1 bt1 ebt1 in
       let ret = fresh () in
       let constr = LC (S ret %= c (S lname1) (S lname2)) in
       return (Computational (ret, rbt, Constraint (constr, I)), local)
    | M_PEstruct _ ->
       fail loc (Unsupported !^"todo: PEstruct")
    | M_PEunion _ ->
       fail loc (Unsupported !^"todo: PEunion")
    | M_PEmemberof _ ->
       fail loc (Unsupported !^"todo: M_PEmemberof")
    | M_PEcall (CF.Core.Impl impl, asyms) ->
       let* decl_typ = get_impl_fun_decl loc global impl in
       let* args = args_from_asyms loc local asyms in
       calltyp loc {local;global} args decl_typ
    | M_PEcall (CF.Core.Sym sym, asyms) ->
       let* (_loc,decl_typ) = get_fun_decl loc global sym in
       let* args = args_from_asyms loc local asyms in
       calltyp loc {local;global} args decl_typ
    | M_PElet (p, e1, e2) ->
       let* (rt, local) = infer_pexpr loc {local;global} e1 in
       let* local' = match p with
         | M_Symbol asym -> 
            let sym, loc = aunpack loc asym in
            return (bind sym rt)
         | M_Pat pat -> 
            pattern_match_rt loc pat rt
       in
       let local = local' ++ local in
       let* (rt2,local) = infer_pexpr loc {local;global} e2 in
       let* local = removeS loc (all_a local') local in
       let* () = ensure_resources_used loc local (all_r local') in
       return (rt2,local)
    | M_PEcase _ -> fail loc (Unreachable !^"PEcase in inferring position")
    | M_PEif (casym, e1, e2) -> fail loc (Unreachable !^"PEif in inferring position")
  in
  
  let* () = debug_print 3 (blank 3 ^^ item "inferred" (RT.pp rt)) in
  let* () = debug_print 1 PPrint.empty in
  return (rt,local)


let for_reachable loc {local;global} paths f =
  filter_mapM (fun (lc, local, e) ->
      let local = add (mUC lc) local in
      let* unreachable = Solver.is_unreachable loc {local;global} in
      if unreachable then return None else f
    ) paths


let rec check_pexpr loc {local;global} e typ : Local.t m = 

  let* () = debug_print 1 (action "checking pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = update_loc loc annots in
  
  let* () = ensure_reachable loc {local;global} in

  match e_ with
  | M_PEif (casym, e1, e2) ->
     let csym, cloc = aunpack loc casym in
     let* (cbt,clname) = get_a cloc local csym in
     let* () = check_base_type cloc cbt Bool in
     let* paths =
       filter_mapM (fun (lc, e) ->
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_pexpr loc {local;global} e typ in
             return (Some (lc, local))
         ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
     in
     merge_local_environments loc {local;global} paths
  | M_PEcase (asym, pats_es) ->
     let (sym,loc) = aunpack loc asym in
     let* (bt,lname) = get_a loc local sym in
     let* paths = 
       filter_mapM (fun (pat,pe) ->
           let* (local',anames) = pattern_match loc (S lname) pat bt in
           let local = local' ++ local in
           (* fix *)
           let lc = LC (Bool true) in
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_pexpr loc {local;global} e typ in
             let* local = removeS loc anames local in
             return (Some (lc, local))
         ) pats_es
     in
     merge_local_environments loc {local;global} paths
  | M_PElet (p, e1, e2) ->
     let* (rt, local) = infer_pexpr loc {local;global} e1 in
     let* local' = match p with
       | M_Symbol asym -> 
          let sym, loc = aunpack loc asym in
          return (bind sym rt)
       | M_Pat pat -> 
          pattern_match_rt loc pat rt
     in
     let local = local' ++ local in
     let* local = check_pexpr loc {local;global} e2 typ in
     let* () = ensure_resources_used loc local (all_r local') in
     removeS loc (all_a local') local
  | _ ->
     let* (rt, local) = infer_pexpr loc {local;global} e in
     let* (local',(abt,lname)) = bind_other loc rt in
     let local = local' ++ local in
     let* local = subtype loc {local;global} ((fresh (),(abt,lname)),loc)
                  typ "function return type" in
     let* () = ensure_resources_used loc local (all_r local') in
     return local



let rec infer_expr loc {local;global} e : (RT.t * Local.t) m = 

  let* () = debug_print 1 (action "inferring expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in

  let* (typ,local) : RT.t * Local.t = match e_ with
    | M_Epure pe -> 
       infer_pexpr loc {local;global} pe
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
          let* (bt,lname) = get_a loc local sym in
          let* () = check_base_type loc bt Loc in
          (* check more things? *)
          let* constr = match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* stored = stored_struct_to_of_tag loc {local;global} (S lname) (Tag tag) in
               return (LC (S ret %= Bool (is_some stored)))
            | _ ->
               let* points = points_to loc {local;global} (S lname) in
               return (LC (S ret %= Bool (is_some points)))
          in
          let ret = Computational (ret, Bool, Constraint (constr, I)) in
          return (ret, local)
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
          let* (abt,_lname) = get_a loc local sym in
          let* () = check_base_type loc Int abt in
          let ret = fresh () in
          let* size = Memory.size_of_ctype loc ct in
          let* rt = match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* (stored,lbindings,rbindings) = 
                 Conversions.make_stored_struct loc global (Tag tag) (S ret) None in
               return (Computational (ret, Loc, lbindings @@
                       Resource (StoredStruct stored, rbindings)))
            | _ ->
               let r = Points {pointer = S ret; pointee = None; typ = ct; size} in
               return (Computational (ret, Loc, Resource (r, I)))
          in
          return (rt, local)
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (_is_dynamic, asym) -> 
          let (sym,loc) = aunpack loc asym in
          (* have remove resources of location instead? *)
          let* (abt,lname) = get_a loc local sym in
          let* () = check_base_type loc Loc abt in
          (* revisit *)
          let* otyp = guess_loc_type loc {local;global} (S lname) in
          begin match otyp with
            | None -> fail loc (Generic_error !^"cannot deallocate unowned location")
            | Some typ -> 
               let* local = remove_owned_subtree loc {local;global} false (S lname) typ in
               return (Computational (Sym.fresh (), Unit, I), local)
          end
       | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
          let (psym,ploc) = aunpack loc asym1 in
          let (vsym,vloc) = aunpack loc asym2 in
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* (pbt,plname) = get_a ploc local psym in
          let* (vbt,vlname) = get_a vloc local vsym in
          let* size = Memory.size_of_ctype loc ct in
          let* () = match pbt with
            | Loc -> return ()
            | _ -> fail ploc (Generic_error !^"the first store argument is not a pointer")
          in
          (* for consistency check value against Core annotation *)
          let* _ =
            let* t = Conversions.ctype false loc (fresh ()) ct in
            subtype loc {local=add (mL vlname (Base vbt)) local; global} 
              ((vsym,(vbt,vlname)),vloc) t 
              "checking store value against ctype annotation"
          in
          let rec store (local: Local.t) (pointer: IT.t) (is_field: bool) ct size (this: IT.t) : (Local.t * RT.l) m =
            let* () = debug_print 3 (action ("checking store at pointer " ^ plain (IT.pp false pointer))) in
            let* () = debug_print 3 (blank 3 ^^ item "ctype" (pp_ctype ct)) in
            let* () = debug_print 3 (blank 3 ^^ item "value" (IT.pp false this)) in
            begin match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* owned = stored_struct_to_of_tag loc {local;global} pointer (Tag tag) in
               let* (r,stored) = match owned with
                 | Some (r,stored) ->
                    if not (Num.equal size stored.size)
                    then fail loc (Generic_error !^"store of different size")
                    else return (r,stored)
                 | None -> fail loc (Generic_error !^"store location is not of struct type" )
               in
               let rec aux (local,acc_bindings) = function
                 | (member,member_pointer) :: members ->
                    let* decl = Global.get_struct_decl loc global (Tag tag) in
                    let* ct = Tools.assoc_err loc member decl.ctypes (Unreachable !^"struct store") in
                    let* size = Memory.size_of_ctype loc ct in
                    let* (local, bindings) = 
                      store local member_pointer true ct size (Member (Tag tag, this, member)) in
                    aux (local, acc_bindings@@bindings) members
                 | [] ->
                    return (local, acc_bindings)
               in
               aux (local,I) stored.members
            | _ ->                
               let* does_point = points_to ploc {local;global} pointer in
               let* (r,p) = match does_point with
                 | Some (r,p) -> 
                    if Num.equal size p.size
                    then return (r,p)
                    else fail loc (Generic_error !^"store of different size")
                 | None -> 
                    if is_field then fail loc (Generic_error !^"missing ownership of struct field" )
                    else fail loc (Generic_error !^"missing ownership of store location" )
               in
               let* local = use_resource loc local r [loc] in
               let bindings = 
                 Resource (Points {p with pointee = Some this; typ = ct}, I) in
               return (local,bindings)
          end in
          let* (local,bindings) = store local (S plname) false ct size (S vlname) in
          let rt = Computational (fresh (), Unit, bindings) in
          return (rt, local)
       | M_Load (a_ct, asym, _mo) -> 
          let (ct, _ct_loc) = aunpack loc a_ct in
          let* size = Memory.size_of_ctype loc ct in
          let (psym,ploc) = aunpack loc asym in
          let* (pbt,plname) = get_a ploc local psym in
          (* check pointer *)
          let* () = match pbt with
            | Loc -> return ()
            | _ -> fail ploc (Generic_error !^"load argument is not a pointer")
          in
          let ret = fresh () in

          let rec load (pointer : IT.t) (is_field : bool) ct size (this : IT.t) : (BT.t * LC.t list, Loc.t * TypeErrors.t) Except.t = 
            let* () = debug_print 3 (action ("checking load at pointer " ^ plain (IT.pp false pointer))) in
            let* () = debug_print 3 (blank 3 ^^ item "ctype" (pp_ctype ct)) in
            match ct with
            | CF.Ctype.Ctype (_, CF.Ctype.Struct tag) -> 
               let* owned = stored_struct_to_of_tag loc {local;global} pointer (Tag tag) in
               let* (r,stored) = match owned with
                 | Some (r,stored) -> 
                    if not (Num.equal size stored.size) 
                    then fail loc (Generic_error !^"load of different size")
                    else return (r,stored)
                 | None -> fail loc (Generic_error !^"load location does not contain a stored struct" )
               in 
               let rec aux acc_constrs = function
                 | (member,member_pointer) :: members ->
                    let* decl = Global.get_struct_decl loc global (Tag tag) in
                    let* spec_bt = Tools.assoc_err loc member decl.raw (Unreachable !^"struct load") in
                    let* ct = Tools.assoc_err loc member decl.ctypes (Unreachable !^"struct load") in
                    let* size = Memory.size_of_ctype loc ct in
                    let* (has_bt, constrs) = 
                      load member_pointer true ct size (Member (Tag tag, this, member)) in
                    let* () = check_base_type ploc has_bt spec_bt in
                    aux (acc_constrs@constrs) members
                 | [] ->
                    return acc_constrs
               in
               let* constrs = aux [] stored.members in
               return (Struct (Tag tag), constrs)
            | _ ->
               let* does_point = points_to ploc {local;global} pointer in
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
               let* (Base bt) = infer_index_term ploc {local;global} pointee in
               let constr = LC (this %= pointee) in
               let* _ = 
                 let* t = Conversions.ctype false loc (fresh ()) ct in
                 let temp_lname = fresh () in
                 let temp_local = add (mL temp_lname (Base bt)) local in
                 let temp_local = add (mUC (LC (S temp_lname %= pointee))) temp_local in
                 subtype loc {local=temp_local;global} ((fresh (),(bt,temp_lname)),ploc) t 
                   "checking load value against expected type"
               in
               return (bt, [constr])
          in
          let* (bt,constrs) = load (S plname) false ct size (S ret) in
          let rec make_constrs = function
            | [] -> I
            | constr :: constrs -> Constraint (constr, make_constrs constrs)
          in
          return (Computational (ret, bt, make_constrs constrs),local)
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
       return (Computational (fresh (), Unit, I), local)
    | M_Eccall (_, _ctype, fun_asym, asyms) ->
       let (sym1,loc1) = aunpack loc fun_asym in
       let* (bt,_lname) = get_a loc1 local sym1 in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail loc1 (Generic_error !^"not a function pointer")
       in
       let* (_loc,decl_typ) = get_fun_decl loc global fun_sym in
       let* args = args_from_asyms loc local asyms in
       calltyp loc {local;global} args decl_typ
    | M_Eproc (_, fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            get_impl_fun_decl loc global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ) = get_fun_decl loc global sym in
            return decl_typ
       in
       let* args = args_from_asyms loc local asyms in
       calltyp loc {local;global} args decl_typ
    | M_Ebound (n, e) ->
       infer_expr loc {local;global} e
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
  return (typ,local)


let rec check_expr loc {local;global} (e : ('a,'bty) mu_expr) typ = 

  let* () = debug_print 1 (action "checking expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (Local.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let* () = ensure_reachable loc {local;global} in

  let (M_Expr (annots, e_)) = e in
  let loc = update_loc loc annots in
  match e_ with
  | M_Eif (casym, e1, e2) ->
     let csym, cloc = aunpack loc casym in
     let* (cbt,clname) = get_a cloc local csym in
     let* () = check_base_type cloc cbt Bool in
     let* paths =
       filter_mapM (fun (lc, e) ->
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_expr loc {local;global} e typ in
             return (Some (lc, local))
         ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
     in
     merge_local_environments loc {local;global} paths
  | M_Ecase (asym, pats_es) ->
     let (sym,loc) = aunpack loc asym in
     let* (bt,lname) = get_a loc local sym in
     let* paths = 
       filter_mapM (fun (pat,pe) ->
           let* (local',names) = pattern_match loc (S lname) pat bt in
           let local = local' ++ local in
           (* fix *)
           let lc = LC (Bool true) in
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_expr loc {local;global} e typ in
             let* local = removeS loc names local in
             return (Some (lc, local))
         ) pats_es
     in
     merge_local_environments loc {local;global} paths
  | M_Epure pe -> 
     check_pexpr loc {local;global} pe typ
  | M_Elet (p, e1, e2) ->
     let* (rt, local) = infer_pexpr loc {local;global} e1 in
     let* local' = match p with 
       | M_Symbol asym ->
          let sym, loc = aunpack loc asym in
          return (bind sym rt)
       | M_Pat pat ->
          pattern_match_rt loc pat rt
     in
     let local = local' ++ local in
     let* local = check_expr loc {local;global} e2 typ in
     let* () = ensure_resources_used loc local (all_r local') in
     removeS loc (all_a local') local
  | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (pat, e1, e2) ->
     let* (rt, local) = infer_expr loc {local;global} e1 in
     let* local' = pattern_match_rt loc pat rt in
     let local = local' ++ local in
     let* local = check_expr loc {local;global} e2 typ in
     let* () = ensure_resources_used loc local (all_r local') in
     removeS loc (all_a local') local
  | M_Esave (_ret, args, body) ->
     let* {local;global} = 
       fold_leftM (fun {local;global} (sym, (_, asym)) ->
           let (vsym,loc) = aunpack loc asym in
           let new_lname = fresh () in
           let* (bt,lname) = get_a loc local vsym in
           let local = add (mL new_lname (Base bt)) local in
           let local = add (mA sym (bt,new_lname)) local in
           let local = add (mUC (LC (S new_lname %= S lname))) local in
           return {local;global}
         ) {local;global} args
     in
     check_expr loc {local;global} body typ
  | _ ->
     let* (rt, local) = infer_expr loc {local;global} e in
     let* (local',(abt,lname)) = bind_other loc rt in
     let local = local' ++ local in
     let* local = subtype loc {local;global} ((fresh (),(abt,lname)),loc) 
                  typ "function return type" in
     let* () = ensure_resources_used loc local (all_r local') in
     return local
     



let check_function loc global fsym args rbt body ftyp =
  
  let* () = match body with
    | `EXPR body -> debug_print 1 (h1 ("Checking procedure " ^ (plain (Sym.pp fsym)))) 
    | `PEXPR body -> debug_print 1 (h1 ("Checking function " ^ (plain (Sym.pp fsym)))) 
  in

  let rt_consistent rbt (Computational (sname,sbt,t)) =
    if BT.equal rbt sbt then return ()
    else fail loc (Mismatch {has = (Base rbt); expected = Base sbt})
  in

  let rec check local args rbt body ftyp =
    match args, ftyp with
    | (aname,abt)::args, FT.Computational (lname,sbt,ftyp) 
         when BT.equal abt sbt ->
       let new_lname = fresh () in
       let ftyp' = FT.subst_var {s=lname;swith=S new_lname} ftyp in
       let local = add (mL new_lname (Base abt)) local in
       let local = add (mA aname (abt,new_lname)) local in
       check local args rbt body ftyp'
    | (aname,abt)::args, FT.Computational (sname,sbt,ftyp) ->
       fail loc (Mismatch {has = (Base abt); expected = Base sbt})
    | [], FT.Computational (sname,sbt,ftyp) ->
       fail loc (Missing_A (sname, sbt))
    | args, FT.Logical (sname,sls,ftyp) ->
       let new_lname = fresh () in
       let ftyp' = FT.subst_var {s=sname;swith=S new_lname} ftyp in
       check (add (mL new_lname sls) local) args rbt body ftyp'       
    | args, FT.Resource (re,ftyp) ->
       (* check linearity *)
       check (add (mR (fresh ()) re) local) args rbt body ftyp
    | args, FT.Constraint (lc,ftyp) ->
       check (add (mUC lc) local) args rbt body ftyp
    | [], FT.Return rt ->
       let* () = rt_consistent rbt rt in
       begin match body with
         | `EXPR body -> check_expr loc {local;global} body rt
         | `PEXPR body -> check_pexpr loc {local;global} body rt
       end
    | (aname,abt)::_, FT.Return _ ->
       fail loc (Surplus_A (aname, abt))
  in
  (* check environment has no resources? *)
  let* _env = check Local.empty args rbt body ftyp in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in       

  return ()



                             
(* TODO: 
  - make call_typ and subtype accept non-A arguments  
  - fix merging of environments/return types
  - points-to type indexing?
  - what about the sizes of base types?
 *)
