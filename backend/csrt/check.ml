module CF=Cerb_frontend
module L = Local
module G = Global
module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module ITT = IndexTermTyping
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module AT = ArgumentTypes
module FT = ArgumentTypes.Make(ReturnTypes)
module LT = ArgumentTypes.Make(False)
module SymSet = Set.Make(Sym)

open TypeErrors
open Environment
open Local
open Resultat
open LogicalConstraints
open CF.Mucore
open Pp




(*** meta types ***************************************************************)
type pattern = BT.t CF.Mucore.mu_pattern
type ctor = BT.t CF.Mucore.mu_ctor
type 'bty pexpr = ((BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_pexpr
type 'bty expr = ((BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_expr
type 'bty value = ((BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_value
type 'bty object_value = ((BT.t * RE.size),'bty) CF.Mucore.mu_object_value
type 'bty label_defs = (LT.t,(BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_label_defs

(*** mucore pp setup **********************************************************)
module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(Pp_typs)
(* let pp_budget () = Some !debug_level *)
let pp_budget () = Some !print_level
let pp_expr e = PP_MUCORE.pp_expr (pp_budget ()) e
let pp_pexpr e = PP_MUCORE.pp_pexpr (pp_budget ()) e



(*** variable binding **********************************************************)

let rec bind_logical (delta: L.t) : RT.l -> L.t = function
  | Logical ((s,ls),rt) ->
     let s' = Sym.fresh () in
     let rt' = RT.subst_var_l {before=s; after=S s'} rt in
     bind_logical (add (mL s' ls) delta) rt'
  | Resource (re,rt) -> bind_logical (add (mUR re) delta) rt
  | Constraint (lc,rt) -> bind_logical (add (mUC lc) delta) rt
  | I -> delta

let bind_computational (delta: L.t) (name: Sym.t) (rt: RT.t) : L.t =
  let Computational ((s,bt),rt) = rt in
  let s' = Sym.fresh () in
  let rt' = RT.subst_var_l {before=s;after=S s'} rt in
  let delta' = add (mA name (bt,s')) (add (mL s' (Base bt)) delta) in
  bind_logical delta' rt'
    

let bind (name: Sym.t) (rt: RT.t) : L.t =
  bind_computational L.empty name rt
  
let bind_logically (rt: RT.t) : ((BT.t * Sym.t) * L.t) m =
  let Computational ((s,bt),rt) = rt in
  let s' = Sym.fresh () in
  let rt' = RT.subst_var_l {before=s;after=S s'} rt in
  let delta = add (mL s' (Base bt)) L.empty in
  let delta' = bind_logical delta rt' in
  return ((bt,s'), delta')


(*** pattern matching *********************************************************)

let check_logical_sort (loc: Loc.t) (has: LS.t) (expect: LS.t) : unit m =
  if LS.equal has expect 
  then return () 
  else fail loc (Mismatch {has; expect})

let check_base_type (loc: Loc.t) (has: BT.t) (expect: BT.t) : unit m =
  check_logical_sort loc (LS.Base has) (LS.Base expect)


let pattern_match (loc: Loc.t) (this: IT.t) (pat: pattern) (expect_bt: BT.t) : L.t m =
  let rec aux (local': L.t) (this: IT.t) (pat: pattern) (expect_bt: BT.t) : L.t m = 
    match pat with
    | M_Pattern (annots, M_CaseBase (o_s, has_bt)) ->
       let* () = check_base_type loc has_bt expect_bt in
       let s' = Sym.fresh () in 
       let local' = addL s' (Base has_bt) local' in
       let* local' = match o_s with
         | Some s -> 
            if is_bound s local' 
            then fail loc (Name_bound_twice s)
            else return (add (mA s (has_bt,s')) local')
         | None -> return local'
       in
       let local' = addUC (LC (EQ (this, S s'))) local' in
       return local'
    | M_Pattern (annots, M_CaseCtor (constructor, pats)) ->
       match constructor, expect_bt, pats with
       | M_Cnil item_bt, _, [] ->
          let* () = check_base_type loc (BT.List item_bt) expect_bt in
          return local'
       | M_Cnil item_bt, _, _ ->
          fail loc (Number_arguments {has=List.length pats; expect=0})
       | M_Ccons, List item_bt, [p1;p2] ->
          let* local' = aux local' (Head this) p1 item_bt in
          let* local' = aux local' (Tail this) p2 expect_bt in
          return local'
       | M_Ccons, _, [p1;p2] ->
          let err = !^"cons pattern incompatible with expect type" ^^^ 
                      BT.pp false expect_bt in
          fail loc (Generic err)
       | M_Ccons, _, _ -> 
          fail loc (Number_arguments {has=List.length pats; expect=2})
       | M_Ctuple, Tuple bts, _ ->
          let rec components local' i pats bts =
            match pats, bts with
            | pat :: pats, bt :: bts ->
               let* local' = aux local' (Nth (expect_bt, i, this)) pat bt in
               components local' (i+1) pats bts
            | [], [] -> 
               return local'
            | _, _ ->
               let expect = i+List.length bts in
               let has = i+List.length pats in
               fail loc (Number_arguments {expect; has})
          in
          components local' 0 pats bts
       | M_Ctuple, _, _ ->
          fail loc (Generic (!^"tuple pattern incompatible with expect type" ^^^ 
                               BT.pp false expect_bt))
       | M_Cspecified, _, [pat] ->
          aux local' this pat expect_bt
       | M_Cspecified, _, _ ->
          fail loc (Number_arguments {expect=1;has=List.length pats})
       | M_Carray, _, _ ->
          fail loc (Unsupported !^"todo: array types")
       | M_CivCOMPL, _, _
       | M_CivAND, _, _
       | M_CivOR, _, _
       | M_CivXOR, _, _
       | M_Cfvfromint, _, _
       | M_Civfromfloat, _, _
         ->
          fail loc (Unsupported !^"todo: Civ..")
  in
  aux L.empty this pat expect_bt

  
(* The pattern-matching might de-struct 'bt'. For easily making
   constraints carry over to those values, record (lname,bound) as a
   logical variable and record constraints about how the variables
   introduced in the pattern-matching relate to (name,bound). *)
let pattern_match_rt (loc: Loc.t) (pat: pattern) (rt: RT.t) : L.t m =
  let* ((bt,s'), delta) = bind_logically rt in
  let* delta' = pattern_match loc (S s') pat bt in
  return (delta' ++ delta)



(*** function call typing and subtyping ***************************************)

(* Spine is parameterised by RT_Sig, so it can be used both for
   function and label types (which don't have a return type) *)
module Spine (RT: AT.RT_Sig) = struct

  module FT = AT.Make(RT)
  module NFT = NormalisedArgumentTypes.Make(RT)

  let pp_argslocs =
    pp_list (fun ((bt,lname),(_l:Loc.t)) -> 
        parens (BT.pp false bt ^^^ bar ^^^ Sym.pp lname))

  let pp_unis (unis: (IT.t Uni.t) SymMap.t) : Pp.document = 
    let pp_entry (sym, Uni.{resolved}) =
      match resolved with
      | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ IT.pp res
      | None -> Sym.pp sym ^^^ !^"unresolved"
    in
    pp_list pp_entry (SymMap.bindings unis)

  let spine (loc: Loc.t) 
            {local;global} 
            (arguments: ((BT.t * Sym.t) * Loc.t) list) 
            (ftyp: FT.t)
            (descr: string)
      : (RT.t * L.t) m 
    =

    let open NFT in
    let ftyp = NFT.normalise ftyp in

    let rec check_computational args ftyp = 
      match args, ftyp with
      | ((abt,lname),arg_loc) :: args, Computational ((sname,sbt),ftyp) ->
         if BT.equal abt sbt then 
           let ftyp' = NFT.subst_var {before=sname;after=S lname} ftyp in
           check_computational args ftyp'
         else 
           fail loc (Mismatch {has = Base abt; expect = Base sbt})
      | [], L ftyp -> 
         return ftyp
      | [], Computational (_,_)
      | _ :: _, L _ -> 
         let expect = NFT.count_computational ftyp in
         let has = List.length arguments in
         fail loc (Number_arguments {expect; has})
    in
    let* ftyp = check_computational arguments ftyp in

    let rec delay_logical (unis,lspec) ftyp =
        match ftyp with
        | Logical ((sname,sls),ftyp) ->
           let sym = Sym.fresh () in
           let unis = SymMap.add sym (Uni.{ resolved = None }) unis in
           let ftyp' = NFT.subst_var_l {before=sname;after=S sym} ftyp in
           delay_logical (unis,lspec @ [(sym,sls)]) ftyp'
        | R ftyp -> 
           return ((unis,lspec), ftyp)
    in
    let* ((unis,lspec), ftyp) = delay_logical (SymMap.empty,[]) ftyp in
    
    (* Pp.d 4 (lazy (!^"starting resource inference"));
     * Pp.d 4 (lazy (item "ftyp" (NFT.pp_r ftyp)));
     * Pp.d 4 (lazy (item "unis" (pp_unis unis))); *)

    let rec infer_resources local unis = function
      | Resource (re,ftyp) -> 
         let* () = match Uni.unresolved_var unis (IT.vars_in (RE.pointer re)) with
           | Some var -> fail loc (Unconstrained_logical_variable var)
           | _ -> return ()
         in
         let* matched = Memory.for_fp loc {local;global} (RE.fp re) in
         begin match matched with
         | None -> fail loc (Missing_resource re)
         | Some (r,resource') ->
            match RE.unify_non_pointer re resource' unis with
            | None -> 
               fail loc (Missing_resource re)
            | Some unis ->
               let* local = use_resource loc r [loc] local in
               let (_,new_substs) = Uni.find_resolved local unis in
               let ftyp' = NFT.subst_vars_r new_substs ftyp in
               infer_resources local unis ftyp'
         end
      | C ftyp ->
         return (local,unis,ftyp)
    in
    let* (local,unis,ftyp) = infer_resources local unis ftyp in

    let rec check_logical unis = function
      | (sname,sls) :: lspec ->
         let* Uni.{resolved} = SymMapM.lookup loc unis sname in
         begin match resolved with
         | None -> 
            fail loc (Unconstrained_logical_variable sname)
         | Some sym ->
            let* als = ITT.infer_index_term loc {local;global} sym in
            if LS.equal als sls 
            then check_logical unis lspec
            else fail loc (Mismatch {has = als; expect = sls})
         end
      | [] -> 
         return ()
    in
    let* () = check_logical unis lspec in

    let rec check_constraints = function
      | Constraint (c, ftyp) ->
         let* (holds,_,_) = Solver.constraint_holds loc {local;global} c in
         if holds 
         then check_constraints ftyp 
         else fail loc (Unsat_constraint c)
      | I rt -> 
         return rt
    in
    let* rt = check_constraints ftyp in

    return (rt,local)

end

module Spine_FT = Spine(ReturnTypes)
module Spine_LT = Spine(False)


let calltype_ft loc {local;global} args (ftyp: FT.t) : (RT.t * L.t) m =
  Spine_FT.spine loc {local;global} args ftyp "function call type"

let calltype_lt loc {local;global} args (ltyp: LT.t) : (False.t * L.t) m =
  Spine_LT.spine loc {local;global} args ltyp "label call type"

(* The "subtyping" judgment needs the same resource/lvar/constraint
   inference as the spine judgment. So implement the subtyping
   judgment 'arg <: RT' by type checking 'f(arg)' for 'f: RT -> False'. *)
let subtype (loc: Loc.t) {local;global} arg (rtyp: RT.t) : L.t m =
  let* (False, local) = Spine_LT.spine loc {local;global} [arg] 
                          (Conversions.rt_to_lt rtyp) "subtype" in
  return local
  


(*** pure value inference *****************************************************)

(* these functions return types `{x : bt | phi(x)}` *)
type vt = Sym.t * BT.t * LC.t 

let infer_tuple (loc: Loc.t) {local;global} (asyms: 'a asyms) : vt m = 
  let new_lname = Sym.fresh () in
  let* (bts,constrs,_) = 
    ListM.fold_leftM (fun (bts,constrs,i) (A (a, _, sym)) -> 
        let* (bt,lname) = get_a (Loc.update loc a) sym local in
        return (bts@[bt],constrs @ [(fun tbt -> IT.EQ (Nth (tbt, i, S new_lname), S lname))],i+1)
      ) ([],[], 0) asyms 
  in
  let bt = BT.Tuple bts in
  let constrs = List.map (fun f -> f bt) constrs in
  return (new_lname, bt, LC (And constrs))

let infer_constructor (loc: Loc.t) {local;global} (constructor: ctor) (asyms: 'a asyms) : vt m = 
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
     let new_lname = Sym.fresh () in
     begin match asyms with
     | [A (a,_,sym)] -> 
        let* (bt,lname) = get_a (Loc.update loc a) sym local in
        return (new_lname, bt, LC (EQ (S new_lname, S lname)))
     | _ ->
        fail loc (Number_arguments {has=List.length asyms; expect=1})
     end
  | M_Cnil item_bt -> 
     let new_lname = Sym.fresh () in
     if asyms = [] then
        return (new_lname, BT.List item_bt, LC (EQ (S new_lname, Nil item_bt)))
     else
        fail loc (Number_arguments {has=List.length asyms; expect=0})
  | M_Ccons -> 
     let new_lname = Sym.fresh () in
     begin match asyms with
     | [A (a1,_,sym1);A (a2,_,sym2)] -> 
        let* (bt1,lname1) = get_a (Loc.update loc a1) sym1 local in
        let* (bt2,lname2) = get_a (Loc.update loc a2) sym2 local in
        let* () = check_base_type (Loc.update loc a2) bt2 (List bt1) in
        return (new_lname, bt2, LC (EQ (S new_lname, Cons (S lname1, S lname2))))
     | _ ->
        fail loc (Number_arguments {has=List.length asyms; expect=2})
     end
  | M_Cfvfromint -> fail loc (Unsupported !^"floats")
  | M_Civfromfloat -> fail loc (Unsupported !^"floats")

let infer_ptrval (loc: Loc.t) {local;global} (ptrval: CF.Impl_mem.pointer_value) : vt m = 
  let new_lname = Sym.fresh () in
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let constr = (LC (Null (S new_lname))) in
      return (new_lname, BT.Loc, constr) )
    ( fun sym -> 
      return (new_lname, BT.FunctionPointer sym, LC (Bool true)) )
    ( fun _prov loc -> 
      let constr = LC (EQ (S new_lname, Num loc)) in
      return (new_lname, BT.Loc, constr) )
    ( fun () -> fail loc (unreachable !^"unspecified pointer value") )

let rec infer_mem_value (loc: Loc.t) {local;global} (mem: CF.Impl_mem.mem_value) : vt m = 
  CF.Impl_mem.case_mem_value mem
    ( fun ctyp -> fail loc (Unspecified ctyp) )
    ( fun _ _ -> fail loc (Unsupported !^"infer_mem_value: concurrent read case") )
    ( fun it iv -> 
      let* v = Memory.integer_value_to_num loc iv in
      let s = Sym.fresh () in
      return (s, BT.Integer, LC (EQ (S s, Num v))) )
    ( fun ft fv -> fail loc (Unsupported !^"Floating point") )
    ( fun _ ptrval -> infer_ptrval loc {local;global} ptrval  )
    ( fun mem_values -> infer_array loc {local;global} mem_values )
    ( fun tag fields -> 
      infer_struct loc {local;global} (BT.Tag tag) 
                   (List.map (fun (mem,_,mv) -> (mem,mv)) fields) )
    ( fun tag id mv -> infer_union loc {local;global} (BT.Tag tag) id mv )

and infer_struct (loc: Loc.t) {local;global} (tag: BT.tag) 
                 (fields: (Id.t * CF.Impl_mem.mem_value) list) : vt m =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let* decl = Global.get_struct_decl loc global.struct_decls tag in
  let ret = Sym.fresh () in
  let rec check fields decl =
    match fields, decl with
    | (id,mv) :: fields, (smember,sbt) :: decl when BT.Member (Id.s id) = smember ->
       let* constraints = check fields decl in
       let* (lname,abt,LC lc) = infer_mem_value loc {local;global} mv in
       let* () = check_base_type loc abt sbt in
       let member_constraint = 
         IT.subst_var {before=lname;after=Member (tag, S ret, Member (Id.s id))} lc in
       return (constraints @ [member_constraint])
    | [], [] -> 
       return []
    | (id,mv) :: fields, (smember,sbt) :: decl ->
       fail loc (unreachable !^"mismatch in fields in infer_struct")
    | [], (BT.Member smember,sbt) :: _ ->
       fail loc (Generic (!^"field" ^^^ !^smember ^^^ !^"missing"))
    | (id,_) :: _, [] ->
       fail loc (Generic (!^"supplying unexpected field" ^^^ !^(Id.s id)))
  in
  let* constraints = check fields decl.raw in
  return (ret, BT.Struct tag, LC (And constraints))

and infer_union (loc: Loc.t) {local;global} (tag: BT.tag) (id: Id.t) (mv: CF.Impl_mem.mem_value) : vt m =
  fail loc (Unsupported !^"todo: union types")

and infer_array (loc: Loc.t) {local;global} (mem_values: CF.Impl_mem.mem_value list) = 
  fail loc (Unsupported !^"todo: array types")

let infer_object_value (loc: Loc.t) {local;global} (ov: 'bty object_value) : vt m =
  match ov with
  | M_OVinteger iv ->
     let new_lname = Sym.fresh () in
     let* i = Memory.integer_value_to_num loc iv in
     let constr = LC (EQ (S new_lname, Num i)) in
     return (new_lname, BT.Integer, constr)
  | M_OVpointer p -> 
     infer_ptrval loc {local;global} p
  | M_OVarray items ->
     fail loc (Unsupported !^"todo: array types")
  | M_OVstruct (tag, fields) -> 
     infer_struct loc {local;global} (Tag tag) 
                  (List.map (fun (id,_,mv) -> (id,mv)) fields)
  | M_OVunion (sym,id,mv) -> 
     infer_union loc {local;global} (Tag sym) id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")

let infer_value (loc: Loc.t) {local;global} (v: 'bty value) : vt m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc {local;global} ov
  | M_Vunit ->
     return (Sym.fresh (), BT.Unit, LC (Bool true))
  | M_Vtrue ->
     let new_lname = Sym.fresh () in
     let constr = LC (S new_lname) in
     return (new_lname, BT.Bool, constr)
  | M_Vfalse -> 
     let new_lname = Sym.fresh () in
     let constr = LC (Not (S new_lname)) in
     return (new_lname, BT.Bool, constr)
  | M_Vlist (ibt, asyms) ->
     let new_lname = Sym.fresh () in
     let* lnames = 
       ListM.mapM (fun (A (a,_,sym)) -> 
           let* (ibt',lname) = get_a (Loc.update loc a) sym local in
           let* () = check_base_type loc ibt' ibt in
           return (IT.S lname)
         ) asyms 
     in
     return (new_lname, BT.List ibt, LC (EQ (S new_lname, List (lnames,ibt))))
  | M_Vtuple asyms ->
     infer_tuple loc {local;global} asyms











(* logic around markers in the environment *)

(* pop_return: "pop" the local environment back until last mark and
   add to `rt` *)
let pop_return (rt, local) = 
  let (RT.Computational ((lname,bt),rt)) = rt in
  let (new_local,old_local) = since local in
  let rec aux vbs acc = 
    match vbs with
    | [] -> acc
    | (_, VB.Computational _) :: vbs ->
       aux vbs acc
    | (s, VB.Logical ls) :: vbs ->
       let s' = Sym.fresh () in
       aux vbs (RT.Logical ((s',ls), RT.subst_var_l {before=s;after=S s'} acc))
    | (_, VB.Resource re) :: vbs ->
       aux vbs (RT.Resource (re,acc))
    | (_, VB.UsedResource _) :: vbs ->
       aux vbs acc
    | (_, VB.Constraint lc) :: vbs ->
       aux vbs (RT.Constraint (lc,acc))
  in
  (RT.Computational ((lname,bt), aux new_local rt), old_local)

(* pop_empty: "pop" the local environment back until last mark and
   drop the content, while ensuring that it does not contain unused
   resources *)
(* all_empty: do the same for the whole local environment (without
   supplying a marker) *)
let (pop_empty,all_empty) = 
    let rec aux loc = function
      | (s, VB.Resource resource) :: _ -> 
         fail loc (Unused_resource {resource;is_merge=false})
      | _ :: rest -> aux loc rest
      | [] -> return ()
    in
  let pop_empty loc local = 
    let (new_local,old_local) = since local in
    let* () = aux loc new_local in
    return old_local
  in
  let all_empty loc local = 
    let new_local = all local in
    let* () = aux loc new_local in
    return ()
  in
  (pop_empty,all_empty)





(* `or_false` is used for inferring/checking the type of unreachable
   control-flow positions, including after Goto: Goto has no return
   type (because the control flow does not return there), but instead
   returns `False`. Type checking of pure expressions returns a local
   environment or `False`; type inference of impure expressions
   returns either a return type and a local environment or `False` *)
type 'a or_false = 
  | Normal of 'a
  | False

(* or_false: check if the monadic argument evaluates to `False`; if
   so, the value is `False, otherwise whatever the continuation
   (taking a non-False argument) returns *)
let or_false (m: ('a or_false) m) (c: 'a -> ('b or_false) m) : ('b or_false) m =
  let* aof = m in
  match aof with
  | Normal a -> c a
  | False -> return False

(* special syntax for `or_false` *)
let (let*?) = or_false

let pp_or_false pp = function
  | Normal a -> pp a
  | False -> if !unicode then !^"\u{22A5}" else !^"bot"

let or_false_to_option (aof: 'a or_false) : 'a option =
  match aof with
  | Normal a -> Some a
  | False -> None

let non_false (aofs: ('a or_false) list) : 'a list = 
  List.filter_map or_false_to_option aofs



(* merging information after control-flow join points  *)

let merge_return_types loc (LC c,rt) (LC c2,rt2) = 
  let RT.Computational ((lname,bt),lrt) = rt in
  let RT.Computational ((lname2,bt2),lrt2) = rt2 in
  let* () = check_base_type loc bt2 bt in
  let rec aux lrt lrt2 = 
    match lrt, lrt2 with
    | RT.I, RT.I -> 
       return RT.I
    | RT.Logical ((s,ls),lrt1), _ ->
       let* lrt = aux lrt1 lrt2 in
       return (RT.Logical ((s,ls), lrt))
    | RT.Constraint (LC lc, lrt1), _ ->
       let* lrt = aux lrt1 lrt2 in
       return (RT.Constraint (LC lc, lrt))
    | _, RT.Logical ((s,ls),lrt2) ->
       let s' = Sym.fresh () in
       let* lrt = aux lrt (RT.subst_var_l {before=s; after=S s'} lrt2) in
       return (RT.Logical ((s',ls), lrt))
    | _, Constraint (LC lc,lrt2) ->
       let* lrt = aux lrt lrt2 in
       return (RT.Constraint (LC (Impl (c2, lc)), lrt))
    | Resource _, _
    | _, Resource _ -> 
       fail loc (Generic !^"Cannot infer type of this expression (cannot merge)")
  in
  let lrt2' = RT.subst_var_l {before=lname2; after=S lname} lrt2 in
  let* lrt = aux lrt lrt2' in
  return (LC (Or [c; c2]), RT.Computational ((lname,bt), lrt))


let big_merge_return_types (loc: Loc.t) (rt: LC.t * RT.t) (rts: (LC.t * RT.t) list) : (LC.t * RT.t) m =
  ListM.fold_leftM (merge_return_types loc) rt rts

let merge_locals (loc: Loc.t) (locals_or_false: (L.t or_false) list) : L.t or_false m =
  let locals = non_false locals_or_false in
  match locals with
  | [] -> return False
  | first :: _ -> 
     let* local = L.big_merge loc first locals in 
     return (Normal local)

let merge_locals_and_return_types (loc: Loc.t) (rts_locals_or_false: (((LC.t * RT.t) * L.t) or_false) list) : (RT.t * L.t) or_false m =
  let rts_locals = non_false rts_locals_or_false in
  let rts,locals = List.split rts_locals in
  match rts_locals with
  | [] -> return False
  | (first_rt,first_local) :: _ -> 
     let* (_,rt) = big_merge_return_types loc first_rt rts in 
     let* local = L.big_merge loc first_local locals in 
     return (Normal (rt,local))



(* auxiliary functions *)
let asym_to_arg loc local (A (a,_,sym)) =
  let loc = Loc.update loc a in
  let* (abt,lname) = get_a loc sym local in
  return ((abt,lname),loc)

let asyms_to_args loc local asyms =
  ListM.mapM (asym_to_arg loc local) asyms 

let false_if_unreachable (loc: Loc.t) {local;global} : (unit or_false) m =
  let* is_unreachable = Solver.is_unreachable loc {local;global} in
  if is_unreachable then return False else return (Normal ())  

(* ensure that the control flow point is not unexpectedly unreachable *)
let ensure_reachable (loc: Loc.t) {local;global} : unit m = 
  let* is_unreachable = Solver.is_unreachable loc {local;global} in
  if not is_unreachable then return ()
  else fail loc (unreachable !^"inconsistent environment") 



(*** pure expression inference ************************************************)

(* infer_pexpr: the raw type inference logic for pure expressions;
   returns a return type and a "reduced" local environment *)
(* infer_pexpr_and_pop: place a marker in the local environment, run
   the raw type inference, and return, in addition to what the raw
   inference returns, all logical (logical variables, resources,
   constraints) in the local environment *)

let rec infer_pexpr (loc: Loc.t) {local;global} (pe: 'bty pexpr) : ((RT.t * L.t) or_false) m = 
  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "inferring pure expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_pexpr pe))));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  let*? (rt,local) = match pe_ with
    | M_PEsym sym ->
       let ret = Sym.fresh () in
       let* (bt,lname) = get_a loc sym local in
       let constr = LC (EQ (S ret, S lname)) in
       let rt = RT.Computational ((ret, bt), Constraint (constr, I)) in
       return (Normal (rt, local))
    | M_PEimpl i ->
       let* t = G.get_impl_constant loc global i in
       return (Normal (RT.Computational ((Sym.fresh (), t), I), local))
    | M_PEval v ->
       let* (lname,bt,constr) = infer_value loc {local;global} v in
       return (Normal (RT.Computational ((lname,bt), Constraint (constr, I)),local))
    | M_PEconstrained _ ->
       fail loc (Unsupported !^"todo: PEconstrained")
    | M_PEundef (loc,undef) ->
       fail loc (Undefined_behaviour undef)
    | M_PEerror (err, A (a,_,sym)) ->
       fail (Loc.update loc a) (StaticError (err,sym))
    | M_PEctor (ctor, args) ->
       let* (lname,bt,constr) = infer_constructor loc {local;global} ctor args in
       return (Normal (RT.Computational ((lname,bt), Constraint (constr, I)),local))
    | M_PEarray_shift _ ->
       fail loc (Unsupported !^"todo: PEarray_shift")
    | M_PEmember_shift (A (a,_,sym), tag, id) ->
       let loc = Loc.update loc a in
       let ret = Sym.fresh () in
       let member = BT.Member (Id.s id) in
       let tag = BT.Tag tag in
       let* (bt,lname) = get_a loc sym local in
       let* () = check_base_type loc bt Loc in
       let* decl = Global.get_struct_decl loc global.struct_decls tag in
       let* () = match List.assoc_opt member decl.raw with
         | None -> fail loc (Generic (!^"struct" ^^^ BT.pp_tag tag ^^^ 
                                        !^"does not have field" ^^^ squotes !^(Id.s id)))
         | Some _ -> return ()
       in
       let constr = LC (EQ (S ret, IT.MemberOffset (tag,S lname,member))) in
       let rt = RT.Computational ((ret, Loc), Constraint (constr,I)) in
       return (Normal (rt, local))
    | M_PEnot (A (a,_,sym)) ->
       let* (bt,lname) = get_a (Loc.update loc a) sym local in
       let* () = check_base_type (Loc.update loc a) Bool bt in
       let ret = Sym.fresh () in 
       let constr = (LC (EQ (S ret, Not (S lname)))) in
       let rt = RT.Computational ((ret, Bool), Constraint (constr, I)) in
       return (Normal (rt, local))
    | M_PEop (op,A (a1,_,sym1),A (a2,_,sym2)) ->
       let open CF.Core in
       let binop_typ (op: CF.Core.binop) (v1: IT.t) (v2: IT.t) =
         let open BT in
         match op with
         | OpAdd -> (((Integer, Integer), Integer), IT.Add (v1, v2))
         | OpSub -> (((Integer, Integer), Integer), IT.Sub (v1, v2))
         | OpMul -> (((Integer, Integer), Integer), IT.Mul (v1, v2))
         | OpDiv -> (((Integer, Integer), Integer), IT.Div (v1, v2))
         | OpRem_t -> (((Integer, Integer), Integer), IT.Rem_t (v1, v2))
         | OpRem_f -> (((Integer, Integer), Integer), IT.Rem_f (v1, v2))
         | OpExp -> (((Integer, Integer), Integer), IT.Exp (v1, v2))
         | OpEq -> (((Integer, Integer), Bool), IT.EQ (v1, v2))
         | OpGt -> (((Integer, Integer), Bool), IT.GT (v1, v2))
         | OpLt -> (((Integer, Integer), Bool), IT.LT (v1, v2))
         | OpGe -> (((Integer, Integer), Bool), IT.GE (v1, v2))
         | OpLe -> (((Integer, Integer), Bool), IT.LE (v1, v2))
         | OpAnd -> (((Bool, Bool), Bool), IT.And [v1; v2])
         | OpOr -> (((Bool, Bool), Bool), IT.Or [v1; v2])
       in
       let* (bt1,lname1) = get_a (Loc.update loc a1) sym1 local in
       let* (bt2,lname2) = get_a (Loc.update loc a2) sym2 local in
       let (((ebt1,ebt2),rbt),result_it) = binop_typ op (S lname1) (S lname2) in
       let* () = check_base_type (Loc.update loc a1) bt1 ebt1 in
       let* () = check_base_type (Loc.update loc a2) bt2 ebt2 in
       let ret = Sym.fresh () in
       let constr = LC (EQ (S ret, result_it)) in
       let rt = RT.Computational ((ret, rbt), Constraint (constr, I)) in
       return (Normal (rt, local))
    | M_PEstruct _ ->
       fail loc (Unsupported !^"todo: PEstruct")
    | M_PEunion _ ->
       fail loc (Unsupported !^"todo: PEunion")
    | M_PEmemberof _ ->
       fail loc (Unsupported !^"todo: M_PEmemberof")
    | M_PEcall (called, asyms) ->
       let* decl_typ = match called with
         | CF.Core.Impl impl -> G.get_impl_fun_decl loc global impl 
         | CF.Core.Sym sym -> 
            let* (_,t) = G.get_fun_decl loc global sym in 
            return t
       in
       let* args = asyms_to_args loc local asyms in
       let* (rt, local) = calltype_ft loc {local;global} args decl_typ in
       return (Normal (rt, local))
    | M_PElet (p, e1, e2) ->
       let*? (rt, local) = infer_pexpr loc {local;global} e1 in
       let* delta = match p with
         | M_Symbol sym -> return (bind sym rt)
         | M_Pat pat -> pattern_match_rt loc pat rt
       in
       infer_pexpr_and_pop loc delta {local;global} e2
    | M_PEcase _ -> fail loc (unreachable !^"PEcase in inferring position")
    | M_PEif (A (a,_,csym), e1, e2) ->
       let* (cbt,clname) = get_a (Loc.update loc a) csym local in
       let* () = check_base_type (Loc.update loc a) cbt Bool in
       let* paths =
         ListM.mapM (fun (lc, e) ->
             let delta = addUC lc L.empty in
             let*? () = false_if_unreachable loc {local = delta ++ local;global} in
             let*? (rt,local) = infer_pexpr_and_pop loc delta {local;global} e in
             return (Normal ((lc,rt),local))
           ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
       in
       merge_locals_and_return_types loc paths
  in  
  Pp.d 2 (lazy (item "type" (RT.pp rt)));
  return (Normal (rt,local))

and infer_pexpr_and_pop (loc: Loc.t) delta {local;global} (pe: 'bty pexpr) : ((RT.t * L.t) or_false) m = 
  let local = delta ++ marked ++ local in 
  let*? (rt, local) = infer_pexpr loc {local;global} pe in
  return (Normal (pop_return (rt, local)))


(* check_pexpr: type check the pure expression `e` against return type
   `typ`; returns a "reduced" local environment *)

let rec check_pexpr (loc: Loc.t) {local;global} (e: 'bty pexpr) (typ: RT.t) : (L.t or_false) m = 
  let (M_Pexpr (annots, _, e_)) = e in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "checking pure expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_pexpr e))));
  Pp.d 2 (lazy (item "type" (RT.pp typ)));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  match e_ with
  | M_PEif (A (a,_,csym), e1, e2) ->
     let* (cbt,clname) = get_a (Loc.update loc a) csym local in
     let* () = check_base_type (Loc.update loc a) cbt Bool in
     let* paths =
       ListM.mapM (fun (lc, e) ->
           let delta = addUC lc L.empty in
           let*? () = false_if_unreachable loc {local = delta ++ local;global} in
           check_pexpr_and_pop loc delta {local;global} e typ
         ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
     in
     merge_locals loc paths
  | M_PEcase (A (a,_,sym), pats_es) ->
     let* (bt,lname) = get_a (Loc.update loc a) sym local in
     let* paths = 
       ListM.mapM (fun (pat,pe) ->
           (* TODO: make pattern matching return (in delta)
              constraints corresponding to the pattern *)
           let* delta = pattern_match loc (S lname) pat bt in
           let*? () = false_if_unreachable loc {local = delta ++ local;global} in
           check_pexpr_and_pop loc delta {local;global} e typ
         ) pats_es
     in
     merge_locals loc paths
  | M_PElet (p, e1, e2) ->
     let*? (rt, local) = infer_pexpr loc {local;global} e1 in
     let* delta = match p with
       | M_Symbol sym -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     check_pexpr_and_pop loc delta {local;global} e2 typ
  | _ ->
     let*? (rt, local) = infer_pexpr loc {local;global} e in
     let* ((abt,lname),delta) = bind_logically rt in
     let local = delta ++ marked ++ local in
     let* local = subtype loc {local;global} ((abt,lname),loc) typ in
     let* local = pop_empty loc local in
     return (Normal local)

and check_pexpr_and_pop (loc: Loc.t) delta {local;global} (pe: 'bty pexpr) (typ: RT.t) : (L.t or_false) m =
  let local = delta ++ marked ++ local in 
  let*? local = check_pexpr loc {local;global} pe typ in
  let* local = pop_empty loc local in
  return (Normal local)



(*** impure expression inference **********************************************)


(* type inference of impure expressions; returns either a return type
   and new local environment or False *)
(* infer_expr: the raw type inference for impure expressions. *)
(* infer_expr_and_pop: analogously to infer_pexpr: place a marker, run
   the raw type inference, and additionally return whatever is left in
   the local environment since that marker (except for computational
   variables) *)

let rec infer_expr (loc: Loc.t) {local;labels;global} (e: 'bty expr) : ((RT.t * L.t) or_false) m = 
  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "inferring expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_expr e))));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  let* r = match e_ with
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
       | M_PtrValidForDeref (A (_,_,(dbt,size)), A (a,_,sym)) ->
          let ret = Sym.fresh () in
          let* (bt,lname) = get_a (Loc.update loc a) sym local in
          let* () = check_base_type (Loc.update loc a) bt Loc in
          (* check more things? *)
          let* o_resource = Memory.for_fp loc {local;global} (S lname,size) in
          let constr = LC (EQ (S ret, Bool (Option.is_some o_resource))) in
          let ret = RT.Computational ((ret, Bool), Constraint (constr, I)) in
          return (Normal (ret, local))
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
    | M_Eaction (M_Paction (_pol, M_Action (aloc,action_))) ->
       begin match action_ with
       | M_Create (A (a,_,sym), A (_,_,(bt,size)), _prefix) -> 
          let* (abt,_lname) = get_a (Loc.update loc a) sym local in
          let* () = check_base_type (Loc.update loc a) Integer abt in
          let ret = Sym.fresh () in
          let* rbindings = Memory.store loc {local;global} bt (S ret) size None in
          let rt = RT.Computational ((ret, Loc), rbindings) in
          return (Normal (rt, local))
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (_is_dynamic, A (a,_,sym)) -> 
          let* (abt,lname) = get_a (Loc.update loc a) sym local in
          let* () = check_base_type (Loc.update loc a) Loc abt in
          (* revisit *)
          let* found = 
            filter_rM (fun name t ->
                let* holds = Solver.equal loc {local;global} (S lname) (RE.pointer t) in
                return (if holds then Some (name,t) else None)
              ) local
          in
          begin match found with
          | [(re_name,re)] -> 
             let* local = match re with
             | Uninit _ -> Local.use_resource loc re_name [loc] local
             | Points p -> 
                let* (Base bt) = ITT.infer_index_term loc 
                                   {local;global} p.pointee in
                Memory.remove_owned_subtree loc {local;global} bt 
                  p.pointer p.size Kill None
             in
             let rt = RT.Computational ((Sym.fresh (), Unit), I) in
             return (Normal (rt, local))
          | [] -> fail loc (Generic !^"Cannot deallocate unowned location")
          | _ -> fail loc (Generic !^"Cannot guess type of pointer to de-allocate")
          end
       | M_Store (_is_locking, A(_,_,(s_vbt,size)), A(ap,_,psym), A(av,_,vsym), mo) -> 
          let ploc = Loc.update loc ap in
          let vloc = Loc.update loc av in
          let* (pbt,plname) = get_a ploc psym local in
          let* (vbt,vlname) = get_a vloc vsym local in
          let* () = check_base_type loc vbt s_vbt in
          let* () = check_base_type loc pbt BT.Loc in
          (* The generated Core program will before this already have
             checked whether the store value is representable and done
             the right thing. *)
          let* local = 
            Memory.remove_owned_subtree ploc {local;global} vbt 
              (S plname) size Store None in
          let* bindings = 
            Memory.store loc {local;global} vbt (S plname) 
              size (Some (S vlname)) in
          let rt = RT.Computational ((Sym.fresh (), Unit), bindings) in
          return (Normal (rt,local))
       | M_Load (A (_,_,(bt,size)), A (ap,_,psym), _mo) -> 
          let ploc = Loc.update loc ap in
          let* (pbt,plname) = get_a ploc psym local in
          let* () = check_base_type loc pbt BT.Loc in
          let ret = Sym.fresh () in
          let* constraints = 
            Memory.load loc {local;global} bt (S plname) size (S ret) None in
          let rt = RT.Computational ((ret, bt), constraints) in
          return (Normal (rt,local))
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
       let rt = RT.Computational ((Sym.fresh (), Unit), I) in
       return (Normal (rt, local))
    | M_Eccall (_ctype, A(af,_,fsym), asyms) ->
       let* (bt,_) = get_a (Loc.update loc af) fsym local in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail (Loc.update loc af) (Generic !^"not a function pointer")
       in
       let* (_loc,decl_typ) = G.get_fun_decl loc global fun_sym in
       let* args = asyms_to_args loc local asyms in
       let* (rt,local) = calltype_ft loc {local;global} args decl_typ in
       return (Normal (rt, local))
    | M_Eproc (fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            G.get_impl_fun_decl loc global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ) = G.get_fun_decl loc global sym in
            return decl_typ
       in
       let* args = asyms_to_args loc local asyms in
       let* (rt, local) = calltype_ft loc {local;global} args decl_typ in
       return (Normal (rt, local))
    | M_Ebound (n, e) ->
       infer_expr loc {local;labels;global} e
    | M_End _ ->
       fail loc (Unsupported !^"todo: End")
    | M_Erun (label_sym,asyms) ->
       let* lt = match SymMap.find_opt label_sym labels with
       | None -> fail loc (Generic (!^"undefined label" ^^^ Sym.pp label_sym))
       | Some lt -> return lt
       in
       let* args = asyms_to_args loc local asyms in
       let* (False, local) = calltype_lt loc {local;global} args lt in
       let* () = all_empty loc local in
       return False
    | M_Ecase _ -> fail loc (unreachable !^"Ecase in inferring position")
    | M_Eif _ -> fail loc (unreachable !^"Eif in inferring position")
    | M_Elet (p, e1, e2) ->
       let*? (rt, local) = infer_pexpr loc {local;global} e1 in
       let* delta = match p with
         | M_Symbol sym -> return (bind sym rt)
         | M_Pat pat -> pattern_match_rt loc pat rt
       in
       infer_expr_and_pop loc delta {local;labels;global} e2
    | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
    | M_Esseq (pat, e1, e2) ->
       let*? (rt,local) = infer_expr loc {local;labels;global} e1 in
       let* delta = pattern_match_rt loc pat rt in
       infer_expr_and_pop loc delta {local;labels;global} e2
  in
  Pp.d 2 (lazy (match r with
                    | False -> item "type" (parens !^"no return")
                    | Normal (rt,_) -> item "type" (RT.pp rt)));
  return r

and infer_expr_and_pop (loc: Loc.t) delta {local;labels;global} (e: 'bty expr) : ((RT.t * L.t) or_false) m =
  let local = delta ++ marked ++ local in 
  let*? (rt, local) = infer_expr loc {local;labels;global} e in
  return (Normal (pop_return (rt, local)))

(* check_expr: type checking for impure epressions; type checks `e`
   against `typ`, which is either a return type or `False`; returns
   either an updated environment, or `False` in case of Goto *)
let rec check_expr (loc: Loc.t) {local;labels;global} (e: 'bty expr) (typ: RT.t or_false) = 
  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "checking expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_expr e))));
  Pp.d 2 (lazy (item "type" (pp_or_false RT.pp typ)));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  match e_ with
  | M_Eif (A (a,_,csym), e1, e2) ->
     let* (cbt,clname) = get_a (Loc.update loc a) csym local in
     let* () = check_base_type (Loc.update loc a) cbt Bool in
     let* paths =
       ListM.mapM (fun (lc, e) ->
           let delta = addUC lc L.empty in
           let*? () = false_if_unreachable loc {local = delta ++ local;global} in
           check_expr_and_pop loc delta {local;labels;global} e typ 
         ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
     in
     merge_locals loc paths
  | M_Ecase (A (a,_,sym), pats_es) ->
     let* (bt,lname) = get_a (Loc.update loc a) sym local in
     let* paths = 
       ListM.mapM (fun (pat,pe) ->
           (* TODO: make pattern matching return (in delta)
              constraints corresponding to the pattern *)
           let* delta = pattern_match loc (S lname) pat bt in
           let*? () = false_if_unreachable loc {local = delta ++ local;global} in
           check_expr_and_pop loc delta {local;labels;global} e typ
         ) pats_es
     in
     merge_locals loc paths
  | M_Elet (p, e1, e2) ->
     let*? (rt, local) = infer_pexpr loc {local;global} e1 in
     let* delta = match p with 
       | M_Symbol sym -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     check_expr_and_pop loc delta {local;labels;global} e2 typ
  | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (pat, e1, e2) ->
     let*? (rt, local) = infer_expr loc {local;labels;global} e1 in
     let* delta = pattern_match_rt loc pat rt in
     check_expr_and_pop loc delta {local;labels;global} e2 typ
  | _ ->
     let*? (rt, local) = infer_expr loc {local;labels;global} e in
     let* ((abt,lname),delta) = bind_logically rt in
     let local = delta ++ marked ++ local in
     match typ with
     | Normal typ ->
        let* local = subtype loc {local;global} ((abt,lname),loc) typ in
        let* local = pop_empty loc local in
        return (Normal local)
     | False ->
        fail loc (Generic !^"This expression returns but is expected to have noreturn-type.")

and check_expr_and_pop (loc: Loc.t) delta {labels;local;global} (pe: 'bty expr) (typ: RT.t or_false) : (L.t or_false) m =
  let local = delta ++ marked ++ local in 
  let*? local = check_expr loc {labels;local;global} pe typ in
  let* local = pop_empty loc local in
  return (Normal local)


(* check_and_bind_arguments: typecheck the function/procedure/label
   arguments against its specification; returns
   1. the return type, or False, to type check the body against,
   2. a local environment binding the arguments,
   3. a local environment binding only the computational and logical
      arguments (for use when type checking a procedure, to include those 
      arguments in the environment for type checking the labels),
   4. the substitutions of concrete arguments for the specification's
      type variables (this is used for instantiating those type variables
      in label specifications in the function body when type checking a
      procedure. *)
(* the logic is parameterised by RT_Sig so it can be used uniformly
   for functions and procedures (with return type) and labels with
   no-return (False) type. *)
module CBF (RT: AT.RT_Sig) = struct
  module T = AT.Make(RT)
  let check_and_bind_arguments loc arguments (function_typ: T.t) = 
    let rec check acc_substs local pure_local args (ftyp: T.t) =
      match args, ftyp with
      | (aname,abt) :: args, T.Computational ((lname,sbt),ftyp) 
           when BT.equal abt sbt ->
         let new_lname = Sym.fresh () in
         let subst = Subst.{before=lname;after=IT.S new_lname} in
         let ftyp' = T.subst_var subst ftyp in
         let local = add (mA aname (abt,new_lname)) (add (mL new_lname (Base abt)) local) in
         let pure_local = add (mA aname (abt,new_lname)) (add (mL new_lname (Base abt)) pure_local) in
         check (acc_substs@[subst]) local pure_local args ftyp'
      | (aname,abt) :: args, T.Computational ((sname,sbt),ftyp) ->
         fail loc (Mismatch {has = (Base abt); expect = Base sbt})
      | [], T.Computational (_,_)
      | _ :: _, T.I _ ->
         let expect = T.count_computational function_typ in
         let has = List.length arguments in
         fail loc (Number_arguments {expect;has})
      | args, T.Logical ((sname,sls),ftyp) ->
         let new_lname = Sym.fresh () in
         let subst = Subst.{before=sname;after=IT.S new_lname} in
         let ftyp' = T.subst_var subst ftyp in
         check (acc_substs@[subst]) 
           (add (mL new_lname sls) local) 
           (add (mL new_lname sls) pure_local) args ftyp'
      | args, T.Resource (re,ftyp) ->
         check acc_substs (add (mUR re) local) pure_local args ftyp
      | args, T.Constraint (lc,ftyp) ->
         check acc_substs (add (mUC lc) local) pure_local args ftyp
      | [], T.I rt ->
         return (rt,local,pure_local,acc_substs)
    in
    check [] L.empty L.empty arguments function_typ
end

module CBF_FT = CBF(ReturnTypes)
module CBF_LT = CBF(False)

(* check_function: type check a (pure) function *)
let check_function (loc: Loc.t) 
                   (global: Global.t)
                   (fsym: Sym.t)
                   (arguments: (Sym.t * BT.t) list) 
                   (rbt: BT.t) 
                   (body : 'bty pexpr)
                   (function_typ: FT.t) 
  =
  Pp.p (headline ("checking function " ^ Sym.pp_string fsym));
  let* (rt,delta,_,_substs) = 
    CBF_FT.check_and_bind_arguments loc arguments function_typ in
  (* rbt consistency *)
  let* () = 
    let Computational ((sname,sbt),t) = rt in
    if BT.equal rbt sbt then return ()
    else fail loc (Mismatch {has = (Base rbt); expect = Base sbt})
  in
  let* local_or_false = check_pexpr_and_pop loc delta 
                          {local = L.empty;global} body rt in
  return ()


(* check_procedure: type check an (impure) procedure *)
let check_procedure (loc: Loc.t) 
                    (global: Global.t)
                    (fsym: Sym.t)
                    (arguments: (Sym.t * BT.t) list) 
                    (rbt: BT.t) 
                    (label_defs: 'bty label_defs)
                    (body : 'bty expr)
                    (function_typ: FT.t) 
  =
  Pp.p (headline ("checking procedure " ^ Sym.pp_string fsym));
  let* (rt,delta,pure_delta,substs) = 
    CBF_FT.check_and_bind_arguments loc arguments function_typ in
  (* rbt consistency *)
  let* () = 
    let Computational ((sname,sbt),t) = rt in
    if BT.equal rbt sbt then return ()
    else fail loc (Mismatch {has = (Base rbt); expect = Base sbt})
  in
  let label_defs = 
    Pmap.map (function
        | M_Return lt -> 
           M_Return (LT.subst_vars substs lt)
        | M_Label (lt,args,body,annots) -> 
           M_Label (LT.subst_vars substs lt,args,body,annots)
      ) label_defs 
  in
  let labels = 
    Pmap.fold (fun sym def acc ->
        match def with
        | M_Return lt -> SymMap.add sym lt acc
        | M_Label (lt,_,_,_) -> SymMap.add sym lt acc
      ) label_defs SymMap.empty 
  in
  let check_label lsym def () = 
    match def with
    | M_Return lt ->
       return ()
    | M_Label (lt,args,body,annots) ->
       Pp.p (headline ("checking label " ^ Sym.pp_string lsym));
       let* (rt,delta_label,_,_) = CBF_LT.check_and_bind_arguments loc args lt in
       let* local_or_false = 
         check_expr_and_pop loc (delta_label ++ pure_delta) 
           {local = L.empty;labels;global} body False
       in
       return ()
  in
  let* () = PmapM.foldM check_label label_defs () in
  Pp.p (headline ("checking function body " ^ Sym.pp_string fsym));
  let* local_or_false = 
    check_expr_and_pop loc delta 
      {local = L.empty;labels;global} body (Normal rt)
  in
  return ()







                             
(* TODO: 
  - make call_typ and subtype accept non-A arguments  
  - constrain return type shape, maybe also function type shape
  - fix Ecase "LC (Bool true)"
 *)
