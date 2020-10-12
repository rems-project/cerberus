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
open BT




(*** meta types ***************************************************************)
type pattern = BT.t mu_pattern
type ctor = BT.t mu_ctor
type 'bty pexpr = ((BT.t * RE.size), BT.t, 'bty) mu_pexpr
type 'bty expr = ((BT.t * RE.size), BT.t, 'bty) mu_expr
type 'bty value = ((BT.t * RE.size), BT.t, 'bty) mu_value
type 'bty object_value = ((BT.t * RE.size), 'bty) mu_object_value
type mem_value = CF.Impl_mem.mem_value
type pointer_value = CF.Impl_mem.pointer_value
type 'bty label_defs = (LT.t, (BT.t * RE.size), BT.t, 'bty) mu_label_defs


(*** mucore pp setup **********************************************************)
module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(Pp_typs)
(* let pp_budget () = Some !debug_level *)
let pp_budget () = Some !print_level
let pp_expr e = PP_MUCORE.pp_expr (pp_budget ()) e
let pp_pexpr e = PP_MUCORE.pp_pexpr (pp_budget ()) e



(*** variable binding *********************************************************)

let rec bind_logical (delta : L.t) (lrt : RT.l) : L.t = 
  match lrt with
  | Logical ((s, ls), rt) ->
     let s' = Sym.fresh () in
     let rt' = RT.subst_var_l {before=s; after=s'} rt in
     bind_logical (add_l s' ls delta) rt'
  | Resource (re, rt) -> bind_logical (add_ur re delta) rt
  | Constraint (lc, rt) -> bind_logical (add_uc lc delta) rt
  | I -> delta

let bind_computational (delta : L.t) (name : Sym.t) (rt : RT.t) : L.t =
  let Computational ((s, bt), rt) = rt in
  let s' = Sym.fresh () in
  let rt' = RT.subst_var_l {before = s; after = s'} rt in
  let delta' = add_a name (bt, s') (add_l s' (Base bt) delta) in
  bind_logical delta' rt'
    

let bind (name : Sym.t) (rt : RT.t) : L.t =
  bind_computational L.empty name rt
  
let bind_logically (rt : RT.t) : ((BT.t * Sym.t) * L.t) m =
  let Computational ((s, bt), rt) = rt in
  let s' = Sym.fresh () in
  let rt' = RT.subst_var_l {before = s; after = s'} rt in
  let delta = add_l s' (Base bt) L.empty in
  let delta' = bind_logical delta rt' in
  return ((bt, s'), delta')


(*** pattern matching *********************************************************)

let ensure_logical_sort (loc : Loc.t) ~(expect : LS.t) (has : LS.t) : unit m =
  if LS.equal has expect 
  then return () 
  else fail loc (Mismatch {has; expect})

let ensure_base_type (loc : Loc.t) ~(expect : BT.t) (has : BT.t) : unit m =
  ensure_logical_sort loc ~expect:(LS.Base expect) (LS.Base has)


let pattern_match (loc : Loc.t) (this : IT.t) (pat : pattern) 
                  (expect : BT.t) : L.t m =
  let rec aux (local' : L.t) (this : IT.t) (pat : pattern) 
              (expect_bt : BT.t) : L.t m = 
    match pat with
    | M_Pattern (annots, M_CaseBase (o_s, has_bt)) ->
       let* () = ensure_base_type loc ~expect has_bt in
       let s' = Sym.fresh () in 
       let local' = add_l s' (Base has_bt) local' in
       let* local' = 
         match o_s with
         | Some s when is_bound s local' -> fail loc (Name_bound_twice s)
         | Some s -> return (add_a s (has_bt, s') local')
         | None -> return local'
       in
       let local' = add_uc (LC (EQ (this, S s'))) local' in
       return local'
    | M_Pattern (annots, M_CaseCtor (constructor, pats)) ->
       match constructor, expect_bt, pats with
       | (M_Cnil item_bt), _, [] ->
          let* () = ensure_base_type loc ~expect (List item_bt) in
          return local'
       | (M_Cnil item_bt), _, _ ->
          fail loc (Number_arguments {has = List.length pats; expect = 0})
       | M_Ccons, (List item_bt), [p1; p2] ->
          let* local' = aux local' (Head this) p1 item_bt in
          let* local' = aux local' (Tail this) p2 expect_bt in
          return local'
       | M_Ccons, _, [p1; p2] ->
          let err = 
            !^"cons pattern incompatible with expect type" ^^^ 
              BT.pp false expect_bt 
          in
          fail loc (Generic err)
       | M_Ccons, _, _ -> 
          fail loc (Number_arguments {has = List.length pats; expect = 2})
       | M_Ctuple, (Tuple bts), _ ->
          let rec components local' i pats bts =
            match pats, bts with
            | pat :: pats, bt :: bts ->
               let* local' = aux local' (Nth (expect_bt, i, this)) pat bt in
               components local' (i+1) pats bts
            | [], [] -> 
               return local'
            | _, _ ->
               let expect = i + List.length bts in
               let has = i + List.length pats in
               fail loc (Number_arguments {expect; has})
          in
          components local' 0 pats bts
       | M_Ctuple, _, _ ->
          let err = 
            !^"tuple pattern incompatible with expect type" ^^^ 
              BT.pp false expect_bt
          in
          fail loc (Generic err)
       | M_Cspecified, _, [pat] ->
          aux local' this pat expect_bt
       | M_Cspecified, _, _ ->
          fail loc (Number_arguments {expect = 1; has = List.length pats})
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
  aux L.empty this pat expect

  
(* The pattern-matching might de-struct 'bt'. For easily making
   constraints carry over to those values, record (lname,bound) as a
   logical variable and record constraints about how the variables
   introduced in the pattern-matching relate to (name,bound). *)
let pattern_match_rt (loc : Loc.t) (pat : pattern) (rt : RT.t) : L.t m =
  let* ((bt, s'), delta) = bind_logically rt in
  let* delta' = pattern_match loc (S s') pat bt in
  return (delta' ++ delta)



(*** function call typing and subtyping ***************************************)

(* Spine is parameterised by RT_Sig, so it can be used both for
   function and label types (which don't have a return type) *)

type arg = {lname : Sym.t; bt : BT.t; loc : Loc.t}
type args = arg list

let arg_of_asym (loc : Loc.t) (local : L.t) (A (a, _, s) : 'bty asym) : arg m = 
  let loc = Loc.update loc a in
  let* (bt,lname) = get_a loc s local in
  return {lname; bt; loc}

let args_of_asyms (loc : Loc.t) (local : L.t) (asyms : 'bty asyms) : args m= 
  ListM.mapM (arg_of_asym loc local) asyms


module Spine (RT : AT.I_Sig) = struct

  module FT = AT.Make(RT)
  module NFT = NormalisedArgumentTypes.Make(RT)

  let pp_argslocs =
    pp_list (fun ca -> parens (BT.pp false ca.bt ^^^ bar ^^^ Sym.pp ca.lname))

  let pp_unis (unis : (Sym.t Uni.t) SymMap.t) : Pp.document = 
    let pp_entry (sym, Uni.{resolved}) =
      match resolved with
      | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ Sym.pp res
      | None -> Sym.pp sym ^^^ !^"unresolved"
    in
    pp_list pp_entry (SymMap.bindings unis)


  let spine (loc : Loc.t) {local; global} (arguments : arg list) 
            (ftyp : FT.t) (descr : string) : (RT.t * L.t) m =

    let ftyp = NFT.normalise ftyp in
    let open NFT in

    let* ftyp_l = 
      let rec check_computational args ftyp = 
        match args, ftyp with
        | (arg :: args), (Computational ((s, bt), ftyp))
             when BT.equal arg.bt bt ->
           let ftyp' = NFT.subst_var {before = s; after = arg.lname} ftyp in
           check_computational args ftyp'
        | (arg :: _), (Computational ((_, bt), _))  ->
           fail arg.loc (Mismatch {has = Base arg.bt; expect = Base bt})
        | [], (L ftyp) -> 
           return ftyp
        | _ -> 
           let expect = NFT.count_computational ftyp in
           let has = List.length arguments in
           fail loc (Number_arguments {expect; has})
      in
      check_computational arguments ftyp 
    in

    let* ((unis, lspec), ftyp_r) = 
      let rec delay_logical (unis, lspec) ftyp =
        match ftyp with
        | Logical ((s, ls), ftyp) ->
           let s' = Sym.fresh () in
           let unis = SymMap.add s' Uni.{resolved = None} unis in
           let ftyp' = NFT.subst_var_l {before = s; after = s'} ftyp in
           delay_logical (unis, lspec @ [(s', ls)]) ftyp'
        | R ftyp -> 
           return ((unis, lspec), ftyp)
      in
      delay_logical (SymMap.empty, []) ftyp_l
    in
    
    (* Pp.d 4 (lazy (!^"starting resource inference"));
     * Pp.d 4 (lazy (item "ftyp" (NFT.pp_r ftyp)));
     * Pp.d 4 (lazy (item "unis" (pp_unis unis))); *)

    let* (local, unis, ftyp_c) = 
      let rec infer_resources local unis = function
        | Resource (re, ftyp) -> 
           let* () = 
             match Uni.unresolved_var unis (IT.vars_in (RE.pointer re)) with
             | Some s -> fail loc (Unconstrained_logical_variable s)
             | _ -> return ()
           in
           let* matched = Memory.for_fp loc {local; global} (RE.fp re) in
           begin match matched with
           | None -> fail loc (Missing_resource re)
           | Some (s, re') ->
              match RE.unify_non_pointer re re' unis with
              | None -> fail loc (Missing_resource re)
              | Some unis ->
                 let* local = use_resource loc s [loc] local in
                 let new_substs = Uni.find_resolved local unis in
                 let ftyp' = NFT.subst_vars_r new_substs ftyp in
                 infer_resources local unis ftyp'
           end
        | C ftyp ->
           return (local, unis, ftyp)
      in
      infer_resources local unis ftyp_r
    in

    let* () = 
      let rec check_logical unis = function
        | (s, ls) :: lspec ->
           let* Uni.{resolved} = SymMapM.lookup loc unis s in
           begin match resolved with
           | None -> 
              fail loc (Unconstrained_logical_variable s)
           | Some sym ->
              let* resolved_ls = get_l loc sym local in
              if LS.equal resolved_ls ls 
              then check_logical unis lspec
              else fail loc (Mismatch {has = resolved_ls; expect = ls})
           end
        | [] -> 
           return ()
      in
      check_logical unis lspec 
    in

    let* rt = 
      let rec check_constraints = function
        | Constraint (c, ftyp) ->
           let* (holds, _, s_) = Solver.constraint_holds loc {local; global} c in
           if holds 
           then check_constraints ftyp 
           else fail loc (Unsat_constraint c)
        | I rt -> 
           return rt
      in
      check_constraints ftyp_c
    in

    return (rt, local)

end

module Spine_FT = Spine(ReturnTypes)
module Spine_LT = Spine(False)


let calltype_ft loc {local; global} args (ftyp : FT.t) : (RT.t * L.t) m =
  Spine_FT.spine loc {local; global} args ftyp "function call type"

let calltype_lt loc {local; global} args (ltyp : LT.t) : (False.t * L.t) m =
  Spine_LT.spine loc {local; global} args ltyp "label call type"

(* The "subtyping" judgment needs the same resource/lvar/constraint
   inference as the spine judgment. So implement the subtyping
   judgment 'arg <: RT' by type checking 'f(arg)' for 'f: RT -> False'. *)
let subtype (loc : Loc.t) {local; global} arg (rtyp : RT.t) : L.t m =
  let* (False, local) = 
    Spine_LT.spine loc {local; global} [arg] 
      (LT.of_rt rtyp (LT.I False.False)) "subtype" 
  in
  return local
  


(*** pure value inference *****************************************************)

(* these functions return types `{x : bt | phi(x)}` *)
type vt = Sym.t * BT.t * LC.t 

let rt_of_vt (ret,bt,constr) = 
  RT.Computational ((ret, bt), RT.Constraint (constr, I))


let infer_tuple (loc : Loc.t) {local; global} (args : args) : vt m = 
  let ret = Sym.fresh () in
  let bts = List.map (fun arg -> arg.bt) args in
  let bt = Tuple bts in
  let constrs = 
    List.mapi (fun i arg -> IT.EQ (Nth (bt, i, S ret), S arg.lname)) args 
  in
  return (ret, bt, LC (And constrs))

let infer_constructor (loc : Loc.t) {local; global} (constructor : ctor) 
                      (args : args) : vt m = 
  let ret = Sym.fresh () in
  match constructor, args with
  | M_Ctuple, _ -> 
     infer_tuple loc {local; global} args
  | M_Carray, _ -> 
     fail loc (Unsupported !^"todo: array types")
  | M_CivCOMPL, _
  | M_CivAND, _
  | M_CivOR, _
  | M_CivXOR, _ 
    -> 
     fail loc (Unsupported !^"todo: Civ..")
  | M_Cspecified, [arg] ->
     return (ret, arg.bt, LC (EQ (S ret, S arg.lname)))
  | M_Cspecified, _ ->
     fail loc (Number_arguments {has = List.length args; expect = 1})
  | M_Cnil item_bt, [] -> 
     return (ret, List item_bt, LC (EQ (S ret, Nil item_bt)))
  | M_Cnil item_bt, _ -> 
     fail loc (Number_arguments {has = List.length args; expect=0})
  | M_Ccons, [arg1; arg2] -> 
     let* () = ensure_base_type arg2.loc ~expect:(List arg1.bt) arg2.bt in
     let constr = LC (EQ (S ret, Cons (S arg1.lname, S arg2.lname))) in
     return (ret, arg2.bt, constr)
  | M_Ccons, _ ->
     fail loc (Number_arguments {has = List.length args; expect = 2})
  | M_Cfvfromint, _ -> 
     fail loc (Unsupported !^"floats")
  | M_Civfromfloat, _ -> 
     fail loc (Unsupported !^"floats")

let infer_ptrval (loc : Loc.t) {local; global} (ptrval : pointer_value) : vt m =
  let ret = Sym.fresh () in
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> return (ret, Loc, LC (Null (S ret))) )
    ( fun sym -> return (ret, FunctionPointer sym, LC (Bool true)) )
    ( fun _prov loc -> return (ret, Loc, LC (EQ (S ret, Num loc))) )
    ( fun () -> fail loc (unreachable !^"unspecified pointer value") )

let rec infer_mem_value (loc : Loc.t) {local; global} (mem : mem_value) : vt m =
  let open BT in
  CF.Impl_mem.case_mem_value mem
    ( fun ct -> fail loc (Unspecified ct) )
    ( fun _ _ -> 
      fail loc (Unsupported !^"infer_mem_value: concurrent read case") )
    ( fun it iv -> 
      let ret = Sym.fresh () in
      let* v = Memory.integer_value_to_num loc iv in
      return (ret, Integer, LC (EQ (S ret, Num v))) )
    ( fun ft fv -> fail loc (Unsupported !^"Floating point") )
    ( fun _ ptrval -> infer_ptrval loc {local; global} ptrval  )
    ( fun mem_values -> infer_array loc {local; global} mem_values )
    ( fun tag mvals -> 
      let mvals = List.map (fun (id, _, mv) -> (Member (Id.s id), mv)) mvals in
      infer_struct loc {local; global} (Tag tag) mvals )
    ( fun tag id mv -> infer_union loc {local; global} (Tag tag) id mv )

and infer_struct (loc : Loc.t) {local; global} (tag : tag) 
                 (member_values : (member * mem_value) list) : vt m =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let ret = Sym.fresh () in
  let* spec = Global.get_struct_decl loc global.struct_decls tag in
  let rec check fields spec =
    match fields, spec with
    | ((member, mv) :: fields), ((smember, sbt) :: spec) 
         when member = smember ->
       let* constrs = check fields spec in
       let* (s, bt, LC lc) = infer_mem_value loc {local; global} mv in
       let* () = ensure_base_type loc ~expect:sbt bt in
       let this = IT.Member (tag, S ret, member) in
       let constr = IT.subst_it {before = s; after = this} lc in
       return (constrs @ [constr])
    | [], [] -> 
       return []
    | ((id, mv) :: fields), ((smember, sbt) :: spec) ->
       fail loc (unreachable !^"mismatch in fields in infer_struct")
    | [], ((Member id, _) :: _) ->
       fail loc (Generic (!^"field" ^^^ !^id ^^^ !^"missing"))
    | ((Member id,_) :: _), [] ->
       fail loc (Generic (!^"supplying unexpected field" ^^^ !^id))
  in
  let* constraints = check member_values spec.raw in
  return (ret, Struct tag, LC (And constraints))

and infer_union (loc : Loc.t) {local; global} (tag : tag) (id : Id.t) 
                (mv : mem_value) : vt m =
  fail loc (Unsupported !^"todo: union types")

and infer_array (loc : Loc.t) {local; global} (mem_values : mem_value list) = 
  fail loc (Unsupported !^"todo: array types")

let infer_object_value (loc : Loc.t) {local; global} 
                       (ov : 'bty object_value) : vt m =
  match ov with
  | M_OVinteger iv ->
     let ret = Sym.fresh () in
     let* i = Memory.integer_value_to_num loc iv in
     return (ret, Integer, LC (EQ (S ret, Num i)))
  | M_OVpointer p -> 
     infer_ptrval loc {local; global} p
  | M_OVarray items ->
     fail loc (Unsupported !^"todo: array types")
  | M_OVstruct (tag, fields) -> 
     let mvals = List.map (fun (id,_,mv) -> (Member (Id.s id), mv)) fields in
     infer_struct loc {local; global} (Tag tag) mvals       
  | M_OVunion (sym, id, mv) -> 
     infer_union loc {local; global} (Tag sym) id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")

let infer_value (loc : Loc.t) {local; global} (v : 'bty value) : vt m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) 
    ->
     infer_object_value loc {local; global} ov
  | M_Vunit ->
     return (Sym.fresh (), Unit, LC (Bool true))
  | M_Vtrue ->
     let ret = Sym.fresh () in
     return (ret, Bool, LC (S ret))
  | M_Vfalse -> 
     let ret = Sym.fresh () in
     return (ret, Bool, LC (Not (S ret)))
  | M_Vlist (ibt, asyms) ->
     let ret = Sym.fresh () in
     let* args = args_of_asyms loc local asyms in
     let* () = 
       ListM.iterM (fun arg -> ensure_base_type loc ~expect:ibt arg.bt) args 
     in
     let its = List.map (fun arg -> IT.S arg.lname) args in
     return (ret, List ibt, LC (EQ (S ret, List (its, ibt))))
  | M_Vtuple asyms ->
     let* args = args_of_asyms loc local asyms in
     infer_tuple loc {local; global} args









(* logic around markers in the environment *)

(* pop_return: "pop" the local environment back until last mark and
   add to `rt` *)
let pop_return (rt : RT.t) (local : L.t) : RT.t * L.t = 
  let (RT.Computational (abinding, lrt)) = rt in
  let rec aux vbs acc = 
    match vbs with
    | [] -> acc
    | (_, VB.Computational _) :: vbs ->
       aux vbs acc
    | (s, VB.Logical ls) :: vbs ->
       let s' = Sym.fresh () in
       let acc = RT.subst_var_l {before = s;after = s'} acc in
       aux vbs (RT.Logical ((s', ls), acc))
    | (_, VB.Resource re) :: vbs ->
       aux vbs (RT.Resource (re,acc))
    | (_, VB.UsedResource _) :: vbs ->
       aux vbs acc
    | (_, VB.Constraint lc) :: vbs ->
       aux vbs (RT.Constraint (lc,acc))
  in
  let (new_local, old_local) = since local in
  (RT.Computational (abinding, aux new_local lrt), old_local)

(* pop_empty: "pop" the local environment back until last mark and
   drop the content, while ensuring that it does not contain unused
   resources *)
(* all_empty: do the same for the whole local environment (without
   supplying a marker) *)
let (pop_empty, all_empty) = 
    let rec aux loc = function
      | (s, VB.Resource resource) :: _ -> 
         fail loc (Unused_resource {resource; is_merge = false})
      | _ :: rest -> aux loc rest
      | [] -> return ()
    in
  let pop_empty loc local = 
    let (new_local, old_local) = since local in
    let* () = aux loc new_local in
    return old_local
  in
  let all_empty loc local = 
    let new_local = all local in
    let* () = aux loc new_local in
    return ()
  in
  (pop_empty, all_empty)




module Fallible = struct

  (* `t` is used for inferring/checking the type of unreachable control-flow
     positions, including after Run/Goto: Goto has no return type (because the
     control flow does not return there), but instead returns `False`. Type
     checking of pure expressions returns a local environment or `False`; type
     inference of impure expressions returns either a return type and a local
     environment or `False` *)
  type 'a t = 
    | Normal of 'a
    | False

  type 'a fallible = 'a t

  (* bind: check if the monadic argument evaluates to `False`; if so, the value
     is `False, otherwise whatever the continuation (taking a non-False
     argument) returns *)
  let mbind (m : ('a t) m) (f : 'a -> ('b t) m) : ('b t) m =
    let* aof = m in
    match aof with
    | Normal a -> f a
    | False -> return False

  (* special syntax for `or_false` *)
  let (let*?) = mbind

  let pp (ppf : 'a -> Pp.document) (m : 'a t) : Pp.document = 
    match m with
    | Normal a -> ppf a
    | False -> if !unicode then !^"\u{22A5}" else !^"bot"

  let non_false (ms : ('a t) list) : 'a list = 
    List.filter_map (function
        | Normal a -> Some a
        | False -> None
      ) ms

end

open Fallible

(* merging information after control-flow join points  *)

(* note: first argument is the "summarised" return type so far *)
let merge_return_types loc (LC c, rt) (LC c2, rt2) = 
  let RT.Computational ((lname, bt), lrt) = rt in
  let RT.Computational ((lname2, bt2), lrt2) = rt2 in
  let* () = ensure_base_type loc ~expect:bt bt2 in
  let rec aux lrt lrt2 = 
    match lrt, lrt2 with
    | RT.I, RT.I -> 
       return RT.I
    | RT.Logical ((s, ls), lrt1), _ ->
       let* lrt = aux lrt1 lrt2 in
       return (RT.Logical ((s, ls), lrt))
    | RT.Constraint (LC lc, lrt1), _ ->
       let* lrt = aux lrt1 lrt2 in
       return (RT.Constraint (LC lc, lrt))
    | _, RT.Logical ((s, ls), lrt2) ->
       let s' = Sym.fresh () in
       let* lrt = aux lrt (RT.subst_var_l {before = s; after = s'} lrt2) in
       return (RT.Logical ((s', ls), lrt))
    | _, Constraint (LC lc, lrt2) ->
       let* lrt = aux lrt lrt2 in
       return (RT.Constraint (LC (Impl (c2, lc)), lrt))
    | Resource _, _
    | _, Resource _ -> 
       fail loc (Generic !^"Cannot infer type of this (cannot merge)")
  in
  let lrt2' = RT.subst_var_l {before = lname2; after = lname} lrt2 in
  let* lrt = aux lrt lrt2' in
  return (LC (Or [c; c2]), RT.Computational ((lname, bt), lrt))


let big_merge_return_types (loc : Loc.t) (crt : LC.t * RT.t) 
                           (crts : (LC.t * RT.t) list) : (LC.t * RT.t) m =
  ListM.fold_leftM (merge_return_types loc) crt crts

let merge_paths 
      (loc : Loc.t) 
      (local_or_falses : (L.t fallible) list) : (L.t fallible) m =
  let locals = non_false local_or_falses in
  match locals with
  | [] -> return False
  | first :: _ -> 
     (* for every local environment L: merge L L = L *)
     let* local = L.big_merge loc first locals in 
     return (Normal local)

let merge_return_paths
      (loc : Loc.t)
      (rt_local_or_falses : (((LC.t * RT.t) * L.t) fallible) list) 
    : (RT.t * L.t) fallible m =
  let rts_locals = non_false rt_local_or_falses in
  let rts, locals = List.split rts_locals in
  match rts_locals with
  | [] -> return False
  | (first_rt, first_local) :: _ -> 
     let* (_, rt) = big_merge_return_types loc first_rt rts in 
     let* local = L.big_merge loc first_local locals in 
     return (Normal (rt, local))




let false_if_unreachable (loc : Loc.t) {local; global} : (unit fallible) m =
  let* is_unreachable = Solver.is_unreachable loc {local; global} in
  if is_unreachable then return False else return (Normal ())  


(*** pure expression inference ************************************************)

(* infer_pexpr: the raw type inference logic for pure expressions;
   returns a return type and a "reduced" local environment *)
(* infer_pexpr_pop: place a marker in the local environment, run
   the raw type inference, and return, in addition to what the raw
   inference returns, all logical (logical variables, resources,
   constraints) in the local environment *)

let rec infer_pexpr (loc : Loc.t) {local; global} 
                    (pe : 'bty pexpr) : ((RT.t * L.t) fallible) m = 
  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "inferring pure expression"));
  Pp.d 2 (lazy (item "expr" (pp_pexpr pe)));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  let*? (rt, local) = match pe_ with
    | M_PEsym sym ->
       let ret = Sym.fresh () in
       let* (bt, lname) = get_a loc sym local in
       let constr = LC (EQ (S ret, S lname)) in
       let rt = RT.Computational ((ret, bt), Constraint (constr, I)) in
       return (Normal (rt, local))
    | M_PEimpl i ->
       let* bt = G.get_impl_constant loc global i in
       return (Normal (RT.Computational ((Sym.fresh (), bt), I), local))
    | M_PEval v ->
       let* vt = infer_value loc {local; global} v in
       return (Normal (rt_of_vt vt, local))
    | M_PEconstrained _ ->
       fail loc (Unsupported !^"todo: PEconstrained")
    | M_PEundef (loc, undef) ->
       fail loc (Undefined_behaviour undef)
    | M_PEerror (err, asym) ->
       let* arg = arg_of_asym loc local asym in
       fail arg.loc (StaticError err)
    | M_PEctor (ctor, asyms) ->
       let* args = args_of_asyms loc local asyms in
       let* vt = infer_constructor loc {local; global} ctor args in
       return (Normal (rt_of_vt vt, local))
    | M_PEarray_shift _ ->
       fail loc (Unsupported !^"todo: PEarray_shift")
    | M_PEmember_shift (asym, tag, id) ->
       let* arg = arg_of_asym loc local asym in
       let* () = ensure_base_type arg.loc ~expect:Loc arg.bt in
       let ret = Sym.fresh () in
       let* decl = Global.get_struct_decl loc global.struct_decls (Tag tag) in
       let member = Member (Id.s id) in
       let* () = match List.assoc_opt member decl.raw with
         | Some _ -> return ()
         | None -> 
            let err = 
              !^"struct" ^^^ pp_tag (Tag tag) ^^^ !^"does not have field" ^^^
                squotes !^(Id.s id)
            in
            fail arg.loc (Generic err)
       in
       let shifted_pointer = IT.MemberOffset (Tag tag, S arg.lname, member) in
       let constr = LC (EQ (S ret, shifted_pointer)) in
       let rt = RT.Computational ((ret, Loc), Constraint (constr, I)) in
       return (Normal (rt, local))
    | M_PEnot asym ->
       let* arg = arg_of_asym loc local asym in
       let* () = ensure_base_type arg.loc ~expect:Bool arg.bt in
       let ret = Sym.fresh () in 
       let constr = (LC (EQ (S ret, Not (S arg.lname)))) in
       let rt = RT.Computational ((ret, Bool), Constraint (constr, I)) in
       return (Normal (rt, local))
    | M_PEop (op, asym1, asym2) ->
       let* arg1 = arg_of_asym loc local asym1 in
       let* arg2 = arg_of_asym loc local asym2 in
       let open CF.Core in
       let binop_typ (op : CF.Core.binop) (v1 : IT.t) (v2 : IT.t) =
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
       let (((ebt1, ebt2), rbt), result_it) = 
         binop_typ op (S arg1.lname) (S arg2.lname) 
       in
       let* () = ensure_base_type arg1.loc ~expect:ebt1 arg1.bt in
       let* () = ensure_base_type arg2.loc ~expect:ebt2 arg2.bt in
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
            let* (_, t) = G.get_fun_decl loc global sym in 
            return t
       in
       let* args = args_of_asyms loc local asyms in
       let* (rt, local) = calltype_ft loc {local; global} args decl_typ in
       return (Normal (rt, local))
    | M_PElet (p, e1, e2) ->
       let*? (rt, local) = infer_pexpr loc {local; global} e1 in
       let* delta = match p with
         | M_Symbol sym -> return (bind sym rt)
         | M_Pat pat -> pattern_match_rt loc pat rt
       in
       infer_pexpr_pop loc delta {local; global} e2
    | M_PEcase _ -> fail loc (unreachable !^"PEcase in inferring position")
    | M_PEif (casym, e1, e2) ->
       let* carg = arg_of_asym loc local casym in
       let* () = ensure_base_type carg.loc ~expect:Bool carg.bt in
       let* paths =
         ListM.mapM (fun (lc, e) ->
             let delta = add_uc lc L.empty in
             let*? () = 
               false_if_unreachable loc {local = delta ++ local; global} 
             in
             let*? (rt, local) = infer_pexpr_pop loc delta {local; global} e in
             return (Normal ((lc, rt), local))
           ) [(LC (S carg.lname), e1); (LC (Not (S carg.lname)), e2)]
       in
       merge_return_paths loc paths
  in  
  Pp.d 2 (lazy (item "type" (RT.pp rt)));
  return (Normal (rt, local))

and infer_pexpr_pop (loc : Loc.t) delta {local; global} 
                    (pe : 'bty pexpr) : ((RT.t * L.t) fallible) m = 
  let local = delta ++ marked ++ local in 
  let*? (rt, local) = infer_pexpr loc {local; global} pe in
  return (Normal (pop_return rt local))


(* check_pexpr: type check the pure expression `e` against return type
   `typ`; returns a "reduced" local environment *)

let rec check_pexpr (loc : Loc.t) {local; global} (e : 'bty pexpr) 
                    (typ : RT.t) : (L.t fallible) m = 
  let (M_Pexpr (annots, _, e_)) = e in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "checking pure expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_pexpr e))));
  Pp.d 2 (lazy (item "type" (RT.pp typ)));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  match e_ with
  | M_PEif (casym, e1, e2) ->
     let* carg = arg_of_asym loc local casym in
     let* () = ensure_base_type carg.loc ~expect:Bool carg.bt in
     let* paths =
       ListM.mapM (fun (lc, e) ->
           let delta = add_uc lc L.empty in
           let*? () = 
             false_if_unreachable loc {local = delta ++ local; global} 
           in
           check_pexpr_pop loc delta {local; global} e typ
         ) [(LC (S carg.lname), e1); (LC (Not (S carg.lname)), e2)]
     in
     merge_paths loc paths
  | M_PEcase (asym, pats_es) ->
     let* arg = arg_of_asym loc local asym in
     let* paths = 
       ListM.mapM (fun (pat, pe) ->
           (* TODO: make pattern matching return (in delta)
              constraints corresponding to the pattern *)
           let* delta = pattern_match arg.loc (S arg.lname) pat arg.bt in
           let*? () = 
             false_if_unreachable loc {local = delta ++ local;global} 
           in
           check_pexpr_pop loc delta {local; global} e typ
         ) pats_es
     in
     merge_paths loc paths
  | M_PElet (p, e1, e2) ->
     let*? (rt, local) = infer_pexpr loc {local; global} e1 in
     let* delta = match p with
       | M_Symbol sym -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     check_pexpr_pop loc delta {local; global} e2 typ
  | _ ->
     let*? (rt, local) = infer_pexpr loc {local; global} e in
     let* ((bt, lname), delta) = bind_logically rt in
     let local = delta ++ marked ++ local in
     let* local = subtype loc {local; global} {bt; lname; loc} typ in
     let* local = pop_empty loc local in
     return (Normal local)

and check_pexpr_pop (loc : Loc.t) delta {local; global} (pe : 'bty pexpr) 
                    (typ : RT.t) : (L.t fallible) m =
  let local = delta ++ marked ++ local in 
  let*? local = check_pexpr loc {local; global} pe typ in
  let* local = pop_empty loc local in
  return (Normal local)



(*** impure expression inference **********************************************)


(* type inference of impure expressions; returns either a return type
   and new local environment or False *)
(* infer_expr: the raw type inference for impure expressions. *)
(* infer_expr_pop: analogously to infer_pexpr: place a marker, run
   the raw type inference, and additionally return whatever is left in
   the local environment since that marker (except for computational
   variables) *)

let rec infer_expr (loc : Loc.t) {local; labels; global} 
                   (e : 'bty expr) : ((RT.t * L.t) fallible) m = 
  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "inferring expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_expr e))));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  let* r = match e_ with
    | M_Epure pe -> 
       infer_pexpr loc {local; global} pe
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
         -> 
          fail loc (Unsupported !^"todo: ememop")
       | M_PtrValidForDeref (A (_, _, (dbt, size)), asym) ->
          let* arg = arg_of_asym loc local asym in
          let ret = Sym.fresh () in
          let* () = ensure_base_type arg.loc ~expect:Loc arg.bt in
          (* check more things? *)
          let* o_resource = 
            Memory.for_fp loc {local; global} (S arg.lname, size) 
          in
          let constr = LC (EQ (S ret, Bool (Option.is_some o_resource))) in
          let rt = RT.Computational ((ret, Bool), Constraint (constr, I)) in
          return (Normal (rt, local))
       | M_PtrWellAligned _ (* (actype 'bty * asym 'bty  ) *)
       | M_PtrArrayShift _ (* (asym 'bty * actype 'bty * asym 'bty  ) *)
       | M_Memcpy _ (* (asym 'bty * asym 'bty * asym 'bty) *)
       | M_Memcmp _ (* (asym 'bty * asym 'bty * asym 'bty) *)
       | M_Realloc _ (* (asym 'bty * asym 'bty * asym 'bty) *)
       | M_Va_start _ (* (asym 'bty * asym 'bty) *)
       | M_Va_copy _ (* (asym 'bty) *)
       | M_Va_arg _ (* (asym 'bty * actype 'bty) *)
       | M_Va_end _ (* (asym 'bty) *) 
         -> 
          fail loc (Unsupported !^"todo: ememop")
       end
    | M_Eaction (M_Paction (_pol, M_Action (aloc, action_))) ->
       begin match action_ with
       | M_Create (asym, A (_, _, (bt, size)), _prefix) -> 
          let* arg = arg_of_asym loc local asym in
          let* () = ensure_base_type arg.loc ~expect:Integer arg.bt in
          let ret = Sym.fresh () in
          let* lrt = Memory.store loc {local; global} bt (S ret) size None in
          let rt = RT.Computational ((ret, Loc), lrt) in
          return (Normal (rt, local))
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (M_Dynamic, asym) -> 
          fail loc (Unsupported !^"todo: free")
       | M_Kill (M_Static (bt, size), asym) -> 
          let* arg = arg_of_asym loc local asym in
          let* () = ensure_base_type arg.loc ~expect:Loc arg.bt in
          let* local = Memory.remove_owned_subtree loc {local; global} bt 
                         (S arg.lname) size Kill None in
          let rt = RT.Computational ((Sym.fresh (), Unit), I) in
          return (Normal (rt, local))
       | M_Store (_is_locking, A(_ ,_ ,(s_vbt, size)), pasym, vasym, mo) -> 
          let* parg = arg_of_asym loc local pasym in
          let* varg = arg_of_asym loc local vasym in
          let* () = ensure_base_type loc ~expect:s_vbt varg.bt in
          let* () = ensure_base_type loc ~expect:Loc parg.bt in
          (* The generated Core program will before this already have
             checked whether the store value is representable and done
             the right thing. *)
          let* local = 
            Memory.remove_owned_subtree parg.loc {local; global} varg.bt 
              (S parg.lname) size Store None in
          let* bindings = 
            Memory.store loc {local; global} varg.bt (S parg.lname) 
              size (Some (S varg.lname)) in
          let rt = RT.Computational ((Sym.fresh (), Unit), bindings) in
          return (Normal (rt, local))
       | M_Load (A (_,_,(bt, size)), pasym, _mo) -> 
          let* parg = arg_of_asym loc local pasym in
          let* () = ensure_base_type loc ~expect:Loc parg.bt in
          let ret = Sym.fresh () in
          let* constraints = 
            Memory.load loc {local; global} bt (S parg.lname) size (S ret) None 
          in
          let rt = RT.Computational ((ret, bt), constraints) in
          return (Normal (rt, local))
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
    | M_Eccall (_ctype, A(af, _, fsym), asyms) ->
       let* (bt, _) = get_a (Loc.update loc af) fsym local in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail (Loc.update loc af) (Generic !^"not a function pointer")
       in
       let* (_loc, decl_typ) = G.get_fun_decl loc global fun_sym in
       let* args = args_of_asyms loc local asyms in
       let* (rt, local) = calltype_ft loc {local; global} args decl_typ in
       return (Normal (rt, local))
    | M_Eproc (fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            G.get_impl_fun_decl loc global impl
         | CF.Core.Sym sym ->
            let* (_loc, decl_typ) = G.get_fun_decl loc global sym in
            return decl_typ
       in
       let* args = args_of_asyms loc local asyms in
       let* (rt, local) = calltype_ft loc {local; global} args decl_typ in
       return (Normal (rt, local))
    | M_Ebound (n, e) ->
       infer_expr loc {local; labels; global} e
    | M_End _ ->
       fail loc (Unsupported !^"todo: End")
    | M_Erun (label_sym, asyms) ->
       let* lt = match SymMap.find_opt label_sym labels with
       | None -> fail loc (Generic (!^"undefined label" ^^^ Sym.pp label_sym))
       | Some lt -> return lt
       in
       let* args = args_of_asyms loc local asyms in
       let* (False, local) = calltype_lt loc {local; global} args lt in
       let* () = all_empty loc local in
       return False
    | M_Ecase _ -> fail loc (unreachable !^"Ecase in inferring position")
    | M_Eif _ -> fail loc (unreachable !^"Eif in inferring position")
    | M_Elet (p, e1, e2) ->
       let*? (rt, local) = infer_pexpr loc {local; global} e1 in
       let* delta = match p with
         | M_Symbol sym -> return (bind sym rt)
         | M_Pat pat -> pattern_match_rt loc pat rt
       in
       infer_expr_pop loc delta {local; labels; global} e2
    | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
    | M_Esseq (pat, e1, e2) ->
       let*? (rt, local) = infer_expr loc {local; labels; global} e1 in
       let* delta = pattern_match_rt loc pat rt in
       infer_expr_pop loc delta {local; labels; global} e2
  in
  Pp.d 2 (lazy (match r with
                    | False -> item "type" (parens !^"no return")
                    | Normal (rt,_) -> item "type" (RT.pp rt)));
  return r

and infer_expr_pop (loc : Loc.t) delta {local; labels; global} 
                   (e : 'bty expr) : ((RT.t * L.t) fallible) m =
  let local = delta ++ marked ++ local in 
  let*? (rt, local) = infer_expr loc {local; labels; global} e in
  return (Normal (pop_return rt local))

(* check_expr: type checking for impure epressions; type checks `e`
   against `typ`, which is either a return type or `False`; returns
   either an updated environment, or `False` in case of Goto *)
let rec check_expr (loc : Loc.t) {local; labels; global} (e : 'bty expr) 
                   (typ : RT.t fallible) : (L.t fallible) m = 
  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in
  Pp.d 2 (lazy (action "checking expression"));
  Pp.d 2 (lazy (item "expr" (group (pp_expr e))));
  Pp.d 2 (lazy (item "type" (Fallible.pp RT.pp typ)));
  Pp.d 2 (lazy (item "ctxt" (L.pp local)));
  match e_ with
  | M_Eif (casym, e1, e2) ->
     let* carg = arg_of_asym loc local casym in
     let* () = ensure_base_type carg.loc ~expect:Bool carg.bt in
     let* paths =
       ListM.mapM (fun (lc, e) ->
           let delta = add_uc lc L.empty in
           let*? () = 
             false_if_unreachable loc {local = delta ++ local; global} 
           in
           check_expr_pop loc delta {local; labels; global} e typ 
         ) [(LC (S carg.lname), e1); (LC (Not (S carg.lname)), e2)]
     in
     merge_paths loc paths
  | M_Ecase (asym, pats_es) ->
     let* arg = arg_of_asym loc local asym in
     let* paths = 
       ListM.mapM (fun (pat, pe) ->
           (* TODO: make pattern matching return (in delta)
              constraints corresponding to the pattern *)
           let* delta = pattern_match arg.loc (S arg.lname) pat arg.bt in
           let*? () = 
             false_if_unreachable loc {local = delta ++ local; global} 
           in
           check_expr_pop loc delta {local; labels; global} e typ
         ) pats_es
     in
     merge_paths loc paths
  | M_Elet (p, e1, e2) ->
     let*? (rt, local) = infer_pexpr loc {local; global} e1 in
     let* delta = match p with 
       | M_Symbol sym -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     check_expr_pop loc delta {local; labels; global} e2 typ
  | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (pat, e1, e2) ->
     let*? (rt, local) = infer_expr loc {local; labels; global} e1 in
     let* delta = pattern_match_rt loc pat rt in
     check_expr_pop loc delta {local; labels; global} e2 typ
  | _ ->
     let*? (rt, local) = infer_expr loc {local; labels; global} e in
     let* ((bt, lname), delta) = bind_logically rt in
     let local = delta ++ marked ++ local in
     match typ with
     | Normal typ ->
        let* local = subtype loc {local; global} {bt; lname; loc} typ in
        let* local = pop_empty loc local in
        return (Normal local)
     | False ->
        let err = 
          "This expression returns but is expected " ^
            "to have noreturn-type." 
        in
        fail loc (Generic !^err)

and check_expr_pop (loc : Loc.t) delta {labels; local; global} (pe : 'bty expr) 
                   (typ : RT.t fallible) : (L.t fallible) m =
  let local = delta ++ marked ++ local in 
  let*? local = check_expr loc {labels; local; global} pe typ in
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
module CBF (RT : AT.I_Sig) = struct
  module T = AT.Make(RT)
  let check_and_bind_arguments loc arguments (function_typ : T.t) = 
    let rec check acc_substs local pure_local args (ftyp : T.t) =
      match args, ftyp with
      | ((aname,abt) :: args), (T.Computational ((lname, sbt), ftyp))
           when equal abt sbt ->
         let new_lname = Sym.fresh () in
         let subst = Subst.{before=lname;after=new_lname} in
         Pp.d 6 (lazy (item "subst" (Subst.pp Sym.pp Sym.pp subst)));
         let ftyp' = T.subst_var subst ftyp in
         let local = add_l new_lname (Base abt) local in
         let local = add_a aname (abt,new_lname) local in
         let pure_local = add_l new_lname (Base abt) pure_local in
         let pure_local = add_a aname (abt,new_lname) pure_local in
         check (acc_substs@[subst]) local pure_local args ftyp'
      | ((aname, abt) :: args), (T.Computational ((sname, sbt), ftyp)) ->
         fail loc (Mismatch {has = (Base abt); expect = Base sbt})
      | [], (T.Computational (_,_))
      | (_ :: _), (T.I _) ->
         let expect = T.count_computational function_typ in
         let has = List.length arguments in
         fail loc (Number_arguments {expect; has})
      | args, (T.Logical ((sname, sls), ftyp)) ->
         let new_lname = Sym.fresh () in
         let subst = Subst.{before = sname; after = new_lname} in
         let ftyp' = T.subst_var subst ftyp in
         let local = add_l new_lname sls local in
         let pure_local = add_l new_lname sls pure_local in
         check (acc_substs@[subst]) local pure_local args ftyp'
      | args, (T.Resource (re, ftyp)) ->
         check acc_substs (add_ur re local) pure_local args ftyp
      | args, (T.Constraint (lc, ftyp)) ->
         check acc_substs (add_uc lc local) pure_local args ftyp
      | [], (T.I rt) ->
         return (rt, local, pure_local, acc_substs)
    in
    check [] L.empty L.empty arguments function_typ
end

module CBF_FT = CBF(ReturnTypes)
module CBF_LT = CBF(False)

(* check_function: type check a (pure) function *)
let check_function (loc : Loc.t) (global : Global.t) (fsym : Sym.t) 
                   (arguments : (Sym.t * BT.t) list) (rbt : BT.t) 
                   (body : 'bty pexpr) (function_typ : FT.t) : unit m =
  Pp.p (headline ("checking function " ^ Sym.pp_string fsym));
  let* (rt, delta, _, _substs) = 
    CBF_FT.check_and_bind_arguments loc arguments function_typ 
  in
  (* rbt consistency *)
  let* () = 
    let Computational ((sname, sbt), t) = rt in
    ensure_base_type loc ~expect:sbt rbt
  in
  let* local_or_false = 
    check_pexpr_pop loc delta {local = L.empty; global} body rt 
  in
  return ()


(* check_procedure: type check an (impure) procedure *)
let check_procedure (loc : Loc.t) (global : Global.t) (fsym : Sym.t)
                    (arguments : (Sym.t * BT.t) list) (rbt : BT.t) 
                    (body : 'bty expr) (function_typ : FT.t) (
                    label_defs : 'bty label_defs) : unit m =
  Pp.p (headline ("checking procedure " ^ Sym.pp_string fsym));
  let* (rt, delta, pure_delta, substs) = 
    CBF_FT.check_and_bind_arguments loc arguments function_typ 
  in
  (* rbt consistency *)
  let* () = 
    let Computational ((sname, sbt), t) = rt in
    ensure_base_type loc ~expect:sbt rbt
  in
  let label_defs = 
    Pmap.map (function
        | M_Return lt -> 
           M_Return (LT.subst_vars substs lt)
        | M_Label (lt, args, body, annots) -> 
           M_Label (LT.subst_vars substs lt, args, body, annots)
      ) label_defs 
  in
  let labels = 
    Pmap.fold (fun sym def acc ->
        match def with
        | M_Return lt -> SymMap.add sym lt acc
        | M_Label (lt, _, _, _) -> SymMap.add sym lt acc
      ) label_defs SymMap.empty 
  in
  let check_label lsym def () = 
    match def with
    | M_Return lt ->
       return ()
    | M_Label (lt, args, body, annots) ->
       Pp.p (headline ("checking label " ^ Sym.pp_string lsym));
       Pp.d 2 (lazy (item "type" (LT.pp lt)));
       let* (rt, delta_label, _, _) = 
         CBF_LT.check_and_bind_arguments loc args lt 
       in
       let* local_or_false = 
         check_expr_pop loc (delta_label ++ pure_delta) 
           {local = L.empty; labels; global} body False
       in
       return ()
  in
  let* () = PmapM.foldM check_label label_defs () in
  Pp.p (headline ("checking function body " ^ Sym.pp_string fsym));
  let* local_or_false = 
    check_expr_pop loc delta 
      {local = L.empty; labels; global} body (Normal rt)
  in
  return ()







                             
(* TODO: 
  - make call_typ and subtype accept non-A arguments  
  - constrain return type shape, maybe also function type shape
  - fix Ecase "LC (Bool true)"
 *)
