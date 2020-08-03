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

module E = Environment
module L = Local
module G = Global
module Loc = Locations
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module RT = ReturnTypes
module FT = FunctionTypes
module NRT = NReturnTypes
module NFT = NFunctionTypes
module SymSet = Set.Make(Sym)



type mu_pattern = BT.t CF.Mucore.mu_pattern
type mu_ctor = BT.t CF.Mucore.mu_ctor
type 'bty mu_pexpr = ((BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_pexpr
type 'bty mu_expr = ((BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_expr
type 'bty mu_value = ((BT.t * RE.size),BT.t,'bty) CF.Mucore.mu_value
type 'bty mu_object_value = ((BT.t * RE.size),'bty) CF.Mucore.mu_object_value


module Pp_srt_typ = struct
  type bt = BT.t
  type ct = (BT.t * RE.size)
  type ft = FT.t
  let pp_bt = BT.pp true
  let pp_ct (bt,size) = parens (BT.pp false bt ^^ comma ^^ Num.pp size)
  let pp_funinfo _ = failwith "not implementeed"
  let pp_funinfo_with_attributes _  = failwith "not implementeed"
end

module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(Pp_srt_typ)

let pp_expr e = nocolour PP_MUCORE.pp_expr e
let pp_pexpr e = nocolour PP_MUCORE.pp_pexpr e


type 'bty pexpr_or_expr = 
  | PEXPR of 'bty mu_pexpr
  | EXPR of 'bty mu_expr



let pp_budget = Some 7

let error pp =
  CB.Pipeline.run_pp None 
    (hardline ^^
     hardline ^^ 
     !^(redb "[!] Error") ^/^ pp ^^
     hardline
    );
  exit 1





type 'a asyms = ('a asym) list


let check_logical_sort (loc: Loc.t) (has: LS.t) (expect: LS.t) : unit m =
  if BT.equal has expect then return () else fail loc (Mismatch {has; expect})

let check_base_type (loc: Loc.t) (has: BT.t) (expect: BT.t) : unit m =
  check_logical_sort loc (LS.Base has) (LS.Base expect)






let rec infer_index_term (loc: Loc.t) (env: E.t) (it: IT.t) : LS.t m = 
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
  | And ts | Or ts ->
     let* () = iterM (check_index_term loc env (Base Bool)) ts in
     return (Base Bool)
  | Impl (t,t') ->
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
     let* decl = Global.get_struct_decl loc env.global.struct_decls tag in
     let* bt = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
     return (Base bt)
  | MemberOffset (tag, it', member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc env.global.struct_decls tag in
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

and check_index_term loc env (ls: LS.t) (it: IT.t) : unit m = 
  let* ls' = infer_index_term loc env it in
  if LS.equal ls ls' then return ()
  else fail loc (Illtyped_it it)








let rec bind_logical (delta: L.t) (rt: RT.l) : L.t =
  match rt with
  | Logical ((s,ls),rt) ->
     let s' = fresh () in
     bind_logical (add (mL s' ls) delta) (subst_var_l {s; swith=S s'} rt)
  | Resource (re,rt) -> bind_logical (add (mUR re) delta) rt
  | Constraint (lc,rt) -> bind_logical (add (mUC lc) delta) rt
  | I -> delta

let bind_computational delta name = function
  | Computational ((s,bt),rt) ->
     let s' = fresh () in
     bind_logical 
       (add (mA name (bt,s')) (add (mL s' (Base bt)) delta))
       (subst_var_l {s;swith=S s'} rt)

let bind (name: Sym.t) (rt: RT.t) : L.t =
  bind_computational L.empty name  rt
  
let bind_logically (rt: RT.t) : (L.t * (BT.t * Sym.t)) m =
  let Computational ((s,bt),rt) = rt in
  let s' = fresh () in
  let delta = 
    bind_logical (add (mL s' (Base bt)) L.empty)
                 (subst_var_l {s;swith=S s'} rt) 
  in
  return (delta, (bt,s'))


let pattern_match (loc: Loc.t) (this: IT.t) (pat: mu_pattern) (expect_bt: BT.t) : L.t m =
  let rec aux local' this pat expect_bt = 
    match pat with
    | M_Pattern (annots, M_CaseBase (o_s, has_bt)) ->
       let* () = check_base_type loc has_bt expect_bt in
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
       | M_Cnil item_bt ->
          begin match pats with
          | [] ->
             if BT.equal (List item_bt) expect_bt 
             then return local'
             else fail loc (Mismatch {has=Base (List item_bt);
                                      expect=Base expect_bt})
          | _ -> fail loc (Number_arguments {has=length pats; expect=0})
          end
       | M_Ccons ->
          begin match expect_bt, pats with
          | List item_bt, [p1;p2] ->
             let* local' = aux local' (Head this) p1 item_bt in
             let* local' = aux local' (Tail this) p2 expect_bt in
             return local'
          | _, [p1;p2] ->
             fail loc (Generic (!^"cons pattern incompatible with expect type" ^^^ 
                                  BT.pp false expect_bt))
          | _ -> fail loc (Number_arguments {has=length pats; expect=2})
          end
       | M_Ctuple ->
          begin match expect_bt with 
          | Tuple bts ->
             let rec components local' i pats bts =
               match pats, bts with
               | [], [] -> return local'
               | pat::pats, bt::bts ->
                  let* local' = aux local' (Nth (i, this)) pat bt in
                  components local' (i+1) pats bts
               | _, _ ->
                  fail loc (Number_arguments {expect=i+length bts; has=i+length pats})
             in
             let* local' = components local' 0 pats bts in
             return local'
          | _ ->
             fail loc (Generic (!^"tuple pattern incompatible with expect type" ^^^ 
                                  BT.pp false expect_bt))
          end
       | M_Cspecified ->
          begin match pats with
          | [pat] -> aux local' this pat expect_bt
          | _ -> fail loc (Number_arguments {expect=1;has=length pats})
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
  aux L.empty this pat expect_bt

  


let pattern_match_rt (loc: Loc.t) (pat: mu_pattern) (rt: RT.t) : L.t m =
  (* The pattern-matching might de-struct 'bt'. For easily making
     constraints carry over to those values, record (lname,bound) as a
     logical variable and record constraints about how the variables
     introduced in the pattern-matching relate to (name,bound). *)
  let* (delta, (bt,s')) = bind_logically rt in
  let* delta' = pattern_match loc (S s') pat bt in
  return (delta' ++ delta)






let pp_unis (unis: (IT.t Uni.t) SymMap.t) : Pp.document = 
  let pp_entry (sym, Uni.{resolved}) =
    match resolved with
    | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ IT.pp true res
    | None -> Sym.pp sym ^^^ !^"unresolved"
  in
  pp_list pp_entry (SymMap.bindings unis)





let match_resource (loc: Loc.t) {local;global} shape : ((Sym.t * RE.t) option) m = 
  let* found = 
    Local.filter_rM (fun name t -> 
        if match_shape shape t then
          let* equal = Solver.equal loc {local;global} (shape_pointer shape) (pointer t) in
          return (if equal then Some (name,t) else None)
        else 
          return None
      ) local
  in
  Tools.at_most_one loc !^"multiple matching resources" found


let points_to (loc: Loc.t) {local;global} (loc_it: IT.t) (size: size) 
    : ((Sym.t * RE.points) option) m = 
  let* points = 
    Local.filter_rM (fun name t ->
        match t with
        | RE.Points p when Num.equal p.size size ->
           let* holds = Solver.equal loc {local;global} loc_it p.pointer in
           return (if holds then Some (name,p) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points


let stored_struct_to (loc: Loc.t) {local;global} (loc_it: IT.t) (tag: BT.tag) : ((Sym.t * RE.stored_struct) option) m = 
  let* stored = 
    Local.filter_rM (fun name t ->
        match t with
        | RE.StoredStruct s when s.tag = tag ->
           let* holds = Solver.equal loc {local;global} loc_it s.pointer in
           return (if holds then Some (name,s) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" stored



let match_concrete_resource (loc: Loc.t) {local;global} (resource: RE.t) : ((Sym.t * RE.t) option) m = 
  match_resource loc {local;global} (RE.shape resource)



let rec remove_owned_subtree (loc: Loc.t) {local;global} ((re_name:Sym.t), (re:RE.t)) = 
  match re with
  | StoredStruct s ->
     let* decl = Global.get_struct_decl loc global.struct_decls s.tag in
     fold_leftM (fun local (member,member_pointer) ->
         let bt = List.assoc member decl.raw  in
         let ct = List.assoc member decl.ctypes  in
         let* size = Memory.size_of_ctype loc ct in
         let* local = Local.use_resource loc re_name [loc] local in
         let shape = match bt with
           | Struct tag -> StoredStruct_ (member_pointer, tag)
           | _ -> Points_ (member_pointer,size)
         in
         let* o_member_resource = match_resource loc {local;global} shape in
         match o_member_resource with
         | Some (rname,r) -> remove_owned_subtree loc {local;global} (rname,r)
         | None -> fail loc (Generic !^"missing ownership for de-allocating")
       ) local s.members
  | Points _ ->
     Local.use_resource loc re_name [loc] local


let load_point loc {local;global} pointer size bt path is_field = 
  let* o_resource = points_to loc {local;global} pointer size in
  let* pointee = match o_resource, is_field with
    | None, false -> fail loc (Generic !^"missing ownership of load location")
    | None, true -> fail loc (Generic !^"missing ownership of struct field")
    | Some (_,{pointee = None; _}), false -> fail loc (Generic !^"load location uninitialised")
    | Some (_,{pointee = None; _}), true -> fail loc (Generic !^"load location uninitialised")
    | Some (_,{pointee = Some pointee; _}),_  -> 
       return pointee
  in
  let* vbt = infer_index_term loc {local;global} pointee in
  let* () = check_logical_sort loc vbt (Base bt) in
  return [LC (path %= pointee)]
  
let rec load_struct (loc: Loc.t) {local;global} (tag: BT.tag) (pointer: IT.t) (path: IT.t) =
  let open RT in
  let* o_resource = stored_struct_to loc {local;global} pointer tag in
  let* decl = Global.get_struct_decl loc global.struct_decls tag in
  let* (_,stored) = match o_resource with
    | None -> fail loc (Generic !^"missing ownership for loading the struct")
    | Some s -> return s
  in
  let rec aux = function
    | (member,member_pointer)::members ->
       let member_bt = assoc member decl.raw in
       let member_path = IT.Member (tag, path, member) in
       let* member_size = Memory.size_of_ctype loc (assoc member decl.ctypes) in
       let* constraints = aux members in
       let* constraints2 = match member_bt with
         | Struct tag2 -> load_struct loc {local;global} tag2 member_pointer member_path
         | _ -> load_point loc {local;global} member_pointer member_size member_bt member_path true
       in
       return (constraints2@constraints)
    | [] -> return []
  in  
  aux stored.members



let pp_argslocs =
  pp_list (fun ((bt,lname),(_l:Loc.t)) -> 
      parens (BT.pp false bt ^^^ bar ^^^ Sym.pp lname))







let subtype_new (loc: Loc.t)
            {local;global}
            (arg: (BT.t * Sym.t) * Loc.t)
            (rtyp: RT.t)
            ppdescr 
    : L.t m 
  =

  let rtyp = RT.normalise rtyp in
  let open NRT in

  let check_computational ((abt,lname),arg_loc) (Computational ((sname,sbt),rtyp)) = 
    if BT.equal abt sbt 
    then return (NRT.subst_var_l {s=sname;swith=S lname} rtyp)
    else fail loc (Mismatch {has = Base abt; expect = Base sbt})
  in
  let* rtyp = check_computational arg rtyp in
  
  let rec delay_logical (unis,lspec) rtyp = 
    match rtyp with
    | Logical ((sname,sls),rtyp) ->
       let sym = Sym.fresh () in
       let unis = SymMap.add sym (Uni.{ resolved = None }) unis in
       delay_logical (unis,lspec @ [(sym,sls)]) 
                     (NRT.subst_var_l {s=sname;swith=S sym} rtyp)
    | R rtyp -> return ((unis,lspec), rtyp)
  in
  let* ((unis,lspec), rtyp) = delay_logical (SymMap.empty,[]) rtyp in

  let rec infer_resources local unis rtyp = 
    match rtyp with
    | Resource (re,rtyp) -> 
       let* matched = match_concrete_resource loc {local;global} re in
       begin match matched with
       | None -> fail loc (Missing_resource re)
       | Some (r,resource') ->
          match RE.unify_non_pointer re resource' unis with
          | None -> fail loc (Missing_resource re)
          | Some unis ->
             let* local = use_resource loc r [loc] local in
             let (_,new_substs) = Uni.find_resolved local unis in
             infer_resources local unis (NRT.subst_vars_r new_substs rtyp)
       end
    | C rtyp ->
       return (local,unis,rtyp)
  in
  let* (local,unis,rtyp) = infer_resources local unis rtyp in

  let rec check_logical unis lspec = 
    match lspec with
    | (sname,sls) :: lvars ->
       let* found = symmap_lookup loc unis sname in
       begin match found with
       | Uni.{resolved = None} -> 
          fail loc (Unconstrained_logical_variable sname)
       | Uni.{resolved = Some it} ->
          let* als = infer_index_term loc {local;global} it in
          if LS.equal als sls 
          then check_logical unis lspec
          else fail loc (Mismatch {has = als; expect = sls})
       end
    | [] -> return ()
  in
  let* () = check_logical unis lspec in

  let rec check_constraints rtyp =
    match rtyp with
    | Constraint (c, rtyp) ->
       let* (holds,_,_) = Solver.constraint_holds loc {local;global} c in
       if holds then check_constraints rtyp else fail loc (Unsat_constraint c)
    | I -> return ()
  in
  let* () = check_constraints rtyp in

  return local



let calltyp_new (loc: Loc.t) 
            {local;global} 
            (arguments: ((BT.t * Sym.t) * Loc.t) list) 
            (ftyp: FT.t)
    : (RT.t * L.t) m 
  =


  let ftyp = FT.normalise ftyp in
  let open NFT in

  let rec check_computational args ftyp = 
    match args, ftyp with
    | ((abt,lname),arg_loc) :: args, Computational ((sname,sbt),ftyp) ->
       if BT.equal abt sbt 
       then check_computational args 
              (NFT.subst_var {s=sname;swith=S lname} ftyp)
       else fail loc (Mismatch {has = Base abt; expect = Base sbt})
    | [], L ftyp -> 
       return ftyp
    | [], Computational (_,_)
    | _ :: _, L _ -> 
       let expect = NFT.count_computational ftyp in
       let has = length arguments in
       fail loc (Number_arguments {expect; has})
  in
  let* ftyp = check_computational arguments ftyp in

  let rec delay_logical (unis,lspec) ftyp = 
    match ftyp with
    | Logical ((sname,sls),ftyp) ->
       let sym = Sym.fresh () in
       let unis = SymMap.add sym (Uni.{ resolved = None }) unis in
       delay_logical (unis,lspec @ [(sym,sls)]) 
                     (NFT.subst_var_l {s=sname;swith=S sym} ftyp)
    | R ftyp -> return ((unis,lspec), ftyp)
  in
  let* ((unis,lspec), ftyp) = delay_logical (SymMap.empty,[]) ftyp in

  let rec infer_resources local unis ftyp = 
    match ftyp with
    | Resource (re,ftyp) -> 
       let* matched = match_concrete_resource loc {local;global} re in
       begin match matched with
       | None -> fail loc (Missing_resource re)
       | Some (r,resource') ->
          match RE.unify_non_pointer re resource' unis with
          | None -> fail loc (Missing_resource re)
          | Some unis ->
             let* local = use_resource loc r [loc] local in
             let (_,new_substs) = Uni.find_resolved local unis in
             infer_resources local unis (NFT.subst_vars_r new_substs ftyp)
       end
    | C ftyp ->
       return (local,unis,ftyp)
  in
  let* (local,unis,ftyp) = infer_resources local unis ftyp in

  let rec check_logical unis lspec = 
    match lspec with
    | (sname,sls) :: lvars ->
       let* found = symmap_lookup loc unis sname in
       begin match found with
       | Uni.{resolved = None} -> 
          fail loc (Unconstrained_logical_variable sname)
       | Uni.{resolved = Some it} ->
          let* als = infer_index_term loc {local;global} it in
          if LS.equal als sls 
          then check_logical unis lspec
          else fail loc (Mismatch {has = als; expect = sls})
       end
    | [] -> return ()
  in
  let* () = check_logical unis lspec in

  let rec check_constraints ftyp =
    match ftyp with
    | Constraint (c, ftyp) ->
       let* (holds,_,_) = Solver.constraint_holds loc {local;global} c in
       if holds then check_constraints ftyp else fail loc (Unsat_constraint c)
    | Return rt -> return rt
  in
  let* rt = check_constraints ftyp in

  return (RT.unnormalise rt,local)




let subtype (loc: Loc.t)
            {local;global}
            (arg: (BT.t * Sym.t) * Loc.t)
            (rtyp: RT.t)
            ppdescr 
    : L.t m 
  =

  let module STS = struct

    type t = 
      { typ: RT.l;
        lvars: (Sym.t * LS.t) list;
        constraints: LC.t list }

    let subst_var s spec = 
      { spec with 
        typ = RT.subst_var_l s spec.typ;
        constraints = List.map (LC.subst_var s) spec.constraints }

    let subst_vars = Subst.make_substs subst_var

  end in


  let ((abt,lname),arg_loc) = arg in
  let Computational ((sname,sbt),rtyp) = rtyp in

  let* () = 
    if BT.equal abt sbt then return ()
    else fail loc (Mismatch {has = Base abt; expect = Base sbt})
  in

  let spec = STS.{ typ = rtyp ; lvars = []; constraints = []} in
  let spec = STS.subst_var {s=sname;swith=S lname} spec in

  let* () = debug_print 1 (action ppdescr) in
  let* () = debug_print 2 PPrint.empty in

  let* () = debug_print 2 (blank 3 ^^ item "value" (pp_argslocs [arg])) in
  let* () = debug_print 2 (blank 3 ^^ item "specification" (RT.pp_l spec.STS.typ)) in


  let rec aux local (unis: (IT.t Uni.t) SymMap.t) spec = 
    let* () = debug_print 2 (blank 3 ^^ item "specification" (RT.pp_l spec.STS.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (L.pp local)) in
    match spec.typ with
    | I -> 
       begin match spec.lvars, spec.constraints with
       | (sname,sls) :: lvars, _ ->
          let* found = symmap_lookup loc unis sname in
          begin match found with
          | Uni.{resolved = None} -> 
             fail loc (Unconstrained_logical_variable sname)
          | Uni.{resolved = Some it} ->
             let* als = infer_index_term loc {local;global} it in
             if LS.equal als sls then
               let spec = STS.{ spec with lvars } in
               let spec = STS.subst_var {s=sname;swith=it} spec in
               aux local unis spec
             else
               fail loc (Mismatch {has = als; expect = sls})
          end
       | [], (c :: constraints) -> 
          let spec = STS.{ spec with constraints } in
          let* (holds,_,_) = Solver.constraint_holds loc {local;global} c in
          if holds then aux local unis spec
          else fail loc (Unsat_constraint c)
       | [], [] ->
          return local
       end
    | Logical ((sname,sls),rtyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = STS.{ spec with lvars = spec.lvars @ [(sym,sls)]; typ = rtyp } in
       let spec = STS.subst_var {s=sname;swith=S sym} spec in
       aux local unis spec
    | Resource (re,rtyp) -> 
       let* matched = match_concrete_resource loc {local;global} re in
       begin match matched with
       | None -> fail loc (Missing_resource re)
       | Some (r,resource') ->
          let* () = debug_print 3 (blank 3 ^^ item "unis" (pp_unis unis)) in
          match RE.unify_non_pointer re resource' unis with
          | None -> fail loc (Missing_resource re)
          | Some unis ->
             let* () = debug_print 3 (blank 3 ^^ item "unis" (pp_unis unis)) in
             let* local = use_resource loc r [loc] local in
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




let calltyp (loc: Loc.t) 
            {local;global} 
            (arguments: ((BT.t * Sym.t) * Loc.t) list) 
            (ftyp: FT.t)
    : (RT.t * L.t) m 
  =

  let module CTS = struct

    type calltyp_spec = 
      { typ: FT.t; 
        lvars: (Sym.t * LS.t) list;
        constraints: LC.t list }

    let subst_var s spec = 
      { spec with typ = FT.subst_var s spec.typ;
                  constraints = List.map (LC.subst_var s) spec.constraints }

    let subst_vars = Subst.make_substs subst_var

  end in

  let open FT in
  let open CTS in

  let* () = debug_print 1 (action "function call type") in
  let* () = debug_print 2 PPrint.empty in

  let rec aux local args unis (spec: calltyp_spec) = 
    let* () = debug_print 2 (blank 3 ^^ item "arguments" (pp_argslocs args)) in
    let* () = debug_print 2 (blank 3 ^^ item "specification" (FT.pp spec.typ)) in
    let* () = debug_print 2 (blank 3 ^^ item "environment" (L.pp local)) in
    match args, spec.typ with
    | [], Return rt -> 
       begin match spec.lvars, spec.constraints with
       | (sname,sls) :: lvars, _ ->
          let* found = symmap_lookup loc unis sname in
          begin match found with
          | Uni.{resolved = None} -> 
             fail loc (Unconstrained_logical_variable sname)
          | Uni.{resolved = Some it} ->
             let* als = infer_index_term loc {local;global} it in
             if LS.equal als sls then
               let spec = CTS.{ spec with lvars } in
               let spec = CTS.subst_var {s=sname;swith=it} spec in
               aux local args unis spec
             else
               fail loc (Mismatch {has = als; expect = sls})
          end
       | [], (c :: constraints) -> 
          let spec = CTS.{ spec with constraints } in
          let* (holds,_,_) = Solver.constraint_holds loc {local;global} c in
          if holds then aux local args unis spec
          else fail loc (Unsat_constraint c)
       | [], [] ->
          return (rt,local)
       end
    | [], Computational (_,_)
      | _ :: _, Return _ -> 
       let expect = FT.count_computational ftyp in
       let has = length arguments in
       fail loc (Number_arguments {expect; has})
    | ((abt,lname),arg_loc) :: args, Computational ((sname,sbt),ftyp) ->
       if BT.equal abt sbt then
         let spec = CTS.{ spec with typ = ftyp} in
         let spec = CTS.subst_var {s=sname;swith=S lname} spec in
         aux local args unis spec
       else
         fail loc (Mismatch {has = Base abt; expect = Base sbt})
    | _, Logical ((sname,sls),ftyp) ->
       let sym = Sym.fresh () in
       let uni = Uni.{ resolved = None } in
       let unis = SymMap.add sym uni unis in
       let spec = CTS.{ spec with lvars = spec.lvars @ [(sym,sls)]; typ = ftyp} in
       let spec = CTS.subst_var {s=sname;swith=S sym} spec in
       aux local args unis spec
    | _, Resource (re,ftyp) -> 
       let* matched = match_concrete_resource loc {local;global} re in
       begin match matched with
       | None -> fail loc (Missing_resource re)
       | Some (r,resource') ->
          let* () = debug_print 3 (action ("trying resource " ^ plain (RE.pp false resource'))) in
          let* () = debug_print 3 (blank 3 ^^ item "unis" (pp_unis unis)) in
          match RE.unify_non_pointer re resource' unis with
          | None -> fail loc (Missing_resource re)
          | Some unis ->
             let* () = debug_print 3 (blank 3 ^^ item "unis" (pp_unis unis)) in
             let* local = use_resource loc r [loc] local in
             let (_,new_substs) = Uni.find_resolved local unis in
             let spec = CTS.{ spec with typ = ftyp } in
             let spec = CTS.subst_vars new_substs spec in
             aux local args unis spec
       end
    | _, Constraint (constr,ftyp) ->
       let spec = { spec with constraints = spec.constraints @ [constr]; typ = ftyp} in
       aux local args unis spec  
  in

  aux local arguments SymMap.empty { typ = ftyp ; lvars = []; constraints = []}






type vt = Sym.t * BT.t * LC.t 



let infer_tuple (loc: Loc.t) {local;global} (asyms: 'a asyms) : vt m = 
  let new_lname = fresh () in
  let* (bts,constrs,_) = 
    fold_leftM (fun (bts,constrs,i) (A (a, _, sym)) -> 
        let* (bt,lname) = get_a (Loc.update loc a) sym local in
        return (bts@[bt],constrs @ [(Nth (i, S new_lname) %= S lname)],i+1)
      ) ([],[], 0) asyms 
  in
  let bt = Tuple bts in
  return (new_lname, bt, LC (And constrs))


let infer_constructor (loc: Loc.t) {local;global} (constructor: mu_ctor) (asyms: 'a asyms) : vt m = 
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
     | [A (a,_,sym)] -> 
        let* (bt,lname) = get_a (Loc.update loc a) sym local in
        return (new_lname, bt, LC (S new_lname %= S lname))
     | _ ->
        fail loc (Number_arguments {has=length asyms; expect=1})
     end
  | M_Cnil item_bt -> 
     let new_lname = fresh () in
     if asyms = [] then
        return (new_lname, List item_bt, LC (S new_lname %= Nil item_bt))
     else
        fail loc (Number_arguments {has=length asyms; expect=0})
  | M_Ccons -> 
     let new_lname = fresh () in
     begin match asyms with
     | [A (a1,_,sym1);A (a2,_,sym2)] -> 
        let* (bt1,lname1) = get_a (Loc.update loc a1) sym1 local in
        let* (bt2,lname2) = get_a (Loc.update loc a2) sym2 local in
        let* () = check_base_type (Loc.update loc a2) bt2 (List bt1) in
        return (new_lname, bt2, LC (S new_lname %= Cons (S lname1, S lname2)))
     | _ ->
        fail loc (Number_arguments {has=length asyms; expect=2})
     end
  | M_Cfvfromint -> fail loc (Unsupported !^"floats")
  | M_Civfromfloat -> fail loc (Unsupported !^"floats")




let infer_ptrval (loc: Loc.t) {local;global} (ptrval: CF.Impl_mem.pointer_value) : vt m = 
  let new_lname = fresh () in
  CF.Impl_mem.case_ptrval ptrval
    ( fun _cbt -> 
      let constr = (LC (Null (S new_lname))) in
      return (new_lname, Loc, constr) )
    ( fun sym -> 
      return (new_lname, FunctionPointer sym, LC (Bool true)) )
    ( fun _prov loc ->      
      let constr = LC (S new_lname %= Num loc) in
      return (new_lname, Loc, constr) )
    ( fun () -> fail loc (Unreachable !^"unspecified pointer value") )



let rec infer_mem_value (loc: Loc.t) {local;global} (mem: CF.Impl_mem.mem_value) : vt m = 
  CF.Impl_mem.case_mem_value mem
    ( fun ctyp -> fail loc (Unspecified ctyp) )
    ( fun _ _ -> fail loc (Unsupported !^"infer_mem_value: concurrent read case") )
    ( fun it iv -> 
      let* v = Memory.integer_value_to_num loc iv in
      let s = fresh () in
      return (s, Int, LC (S s %= Num v) )
    )
    ( fun ft fv -> fail loc (Unsupported !^"Floating point") )
    ( fun _ ptrval -> infer_ptrval loc {local;global} ptrval  )
    ( fun mem_values -> infer_array loc {local;global} mem_values )
    ( fun tag fields -> 
      infer_struct loc {local;global} (Tag tag) 
                   (map (fun (mem,_,mv) -> (mem,mv)) fields) )
    ( fun tag id mv -> infer_union loc {local;global} (Tag tag) id mv )

and infer_struct (loc: Loc.t) {local;global} (tag: tag)
(fields: (Id.t * CF.Impl_mem.mem_value) list) : vt m =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let* decl = Global.get_struct_decl loc global.struct_decls tag in
  let ret = fresh () in
  let rec check fields decl =
    match fields, decl with
    | (id,mv)::fields, (smember,sbt)::decl when Member (Id.s id) = smember ->
       let* constraints = check fields decl in
       let* (lname,abt,LC lc) = infer_mem_value loc {local;global} mv in
       let* () = check_base_type loc abt sbt in
       let member_constraint = IT.subst_var {s=lname;swith = Member (tag, S ret, Member (Id.s id))} lc in
       return (constraints @ [member_constraint])
    | [], [] -> 
       return []
    | (id,mv)::fields, (smember,sbt)::decl ->
       fail loc (Unreachable !^"mismatch in fields in infer_struct")
    | [], (Member smember,sbt)::_ ->
       fail loc (Generic (!^"field" ^^^ !^smember ^^^ !^"missing"))
    | (id,_)::_, [] ->
       fail loc (Generic (!^"supplying unexpected field" ^^^ !^(Id.s id)))
  in
  let* constraints = check fields decl.raw in
  return (ret, Struct tag, LC (IT.And constraints))



and infer_union (loc: Loc.t) {local;global} (tag: tag) (id: Id.t) (mv: CF.Impl_mem.mem_value) : vt m =
  fail loc (Unsupported !^"todo: union types")

and infer_array (loc: Loc.t) {local;global} (mem_values: CF.Impl_mem.mem_value list) = 
  fail loc (Unsupported !^"todo: array types")

let infer_object_value (loc: Loc.t) {local;global} (ov: 'bty mu_object_value) : vt m =
  match ov with
  | M_OVinteger iv ->
     let new_lname = fresh () in
     let* i = Memory.integer_value_to_num loc iv in
     let constr = LC (S new_lname %= Num i) in
     return (new_lname, Int, constr)
  | M_OVpointer p -> 
     infer_ptrval loc {local;global} p
  | M_OVarray items ->
     fail loc (Unsupported !^"todo: array types")
  | M_OVstruct (tag, fields) -> 
     infer_struct loc {local;global} (Tag tag) 
                  (map (fun (id,_,mv) -> (id,mv)) fields)
  | M_OVunion (sym,id,mv) -> 
     infer_union loc {local;global} (Tag sym) id mv
  | M_OVfloating iv ->
     fail loc (Unsupported !^"floats")


let infer_value (loc: Loc.t) {local;global} (v: 'bty mu_value) : vt m = 
  match v with
  | M_Vobject ov
  | M_Vloaded (M_LVspecified ov) ->
     infer_object_value loc {local;global} ov
  | M_Vunit ->
     return (fresh (), Unit, LC (IT.Bool true))
  | M_Vtrue ->
     let new_lname = fresh () in
     let constr = LC (S new_lname) in
     return (new_lname, Bool, constr)
  | M_Vfalse -> 
     let new_lname = fresh () in
     let constr = LC (Not (S new_lname)) in
     return (new_lname, Bool, constr)
  | M_Vlist (ibt, asyms) ->
     let new_lname = fresh () in
     let* lnames = 
       mapM (fun (A (a,_,sym)) -> 
           let* (ibt',lname) = get_a (Loc.update loc a) sym local in
           let* () = check_base_type loc ibt' ibt in
           return (S lname)
         ) asyms 
     in
     return (new_lname, List ibt, LC (S new_lname %= List (lnames,ibt)))
  | M_Vtuple asyms ->
     infer_tuple loc {local;global} asyms



let binop_typ (op: CF.Core.binop) (v1: IT.t) (v2: IT.t): (((BT.t * BT.t) * BT.t) * IT.t) = 
  let open CF.Core in
  match op with
  | OpAdd -> (((Int, Int), Int), Add (v1, v2))
  | OpSub -> (((Int, Int), Int), Sub (v1, v2))
  | OpMul -> (((Int, Int), Int), Mul (v1, v2))
  | OpDiv -> (((Int, Int), Int), Div (v1, v2))
  | OpRem_t -> (((Int, Int), Int), Rem_t (v1, v2))
  | OpRem_f -> (((Int, Int), Int), Rem_f (v1, v2))
  | OpExp -> (((Int, Int), Int), Exp (v1, v2))
  | OpEq -> (((Int, Int), Bool), EQ (v1, v2))
  | OpGt -> (((Int, Int), Bool), GT (v1, v2))
  | OpLt -> (((Int, Int), Bool), LT (v1, v2))
  | OpGe -> (((Int, Int), Bool), GE (v1, v2))
  | OpLe -> (((Int, Int), Bool), LE (v1, v2))
  | OpAnd -> (((Bool, Bool), Bool), And [v1; v2])
  | OpOr -> (((Bool, Bool), Bool), Or [v1; v2])


  


let get_a_loc_asym loc local (A (a,_,sym)) =
  let loc = Loc.update loc a in
  let* (abt,lname) = get_a loc sym local in
  return ((abt,lname),loc)

let get_a_loc_asyms loc local asyms =
  mapM (get_a_loc_asym loc local) asyms 




let merge_local_environments (loc: Loc.t) (new_locals: L.t list) : L.t m =
  let* () = debug_print 1 (action "merging environments at control-flow join point") in
  match new_locals with
  | [] -> fail loc (Unreachable !^"no reachable control-flow path")
  | first::others -> fold_leftM (Local.merge loc) first new_locals


let ensure_reachable (loc: Loc.t) {local;global} : unit m = 
  let* unreachable = Solver.is_unreachable loc {local;global} in
  if not unreachable then return ()
  else fail loc (Unreachable !^"inconsistent environment") 



let rt_pop (Computational ((lname,bt),rt), local) = 
  let (new_local,old_local) = new_old local in
  let rec aux vbs acc = 
    match vbs with
    | [] -> acc
    | (_, VB.Computational _) :: vbs ->
       aux vbs acc
    | (s, VB.Logical ls) :: vbs ->
       let s' = fresh () in
       aux vbs (RT.Logical ((s',ls), RT.subst_var_l {s;swith=S s'} acc))
    | (_, VB.Resource re) :: vbs ->
       aux vbs (RT.Resource (re,acc))
    | (_, VB.UsedResource _) :: vbs ->
       aux vbs acc
    | (_, VB.Constraint lc) :: vbs ->
       aux vbs (RT.Constraint (lc,acc))
       
  in
  (RT.Computational ((lname,bt), aux new_local rt), old_local)

let empty_pop loc local = 
  let (new_local,old_local) = new_old local in
  let rec aux = function
    | (s, VB.Resource resource) :: _ -> 
       fail loc (Unused_resource {resource;is_merge=false})
    | _ :: rest -> aux rest
    | [] -> return ()
  in
  let* () = aux new_local in
  return old_local


let rec infer_pexpr_pop (loc: Loc.t) {local;global} (pe: 'bty mu_pexpr) : (RT.t * L.t) m = 
  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Loc.update loc annots in
  match pe_ with
  | M_PElet (p, e1, e2) ->
     let* (rt, local) = infer_pexpr_pop loc {local = mark ++ local;global} e1 in
     let* local' = match p with
       | M_Symbol (A (_,_,sym)) -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     let local = local' ++ local in
     infer_pexpr_pop loc {local;global} e2
  | _ ->
     let* (rt, local) = infer_pexpr_pure loc {local;global} pe in
     return (rt_pop (rt, local))

and infer_pexpr_pure (loc: Loc.t) {local;global} (pe: 'bty mu_pexpr) : (RT.t * L.t) m = 

  let* () = debug_print 1 (action "inferring pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (L.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget pe)) in

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Loc.update loc annots in

  let* (rt,local) = match pe_ with
    | M_PEsym sym ->
       let ret = fresh () in
       let* (bt,lname) = get_a loc sym local in
       let constr = LC (S ret %= S lname) in
       let rt = Computational ((ret, bt), Constraint (constr, I)) in
       return (rt, local)
    | M_PEimpl i ->
       let* t = get_impl_constant loc global i in
       return (Computational ((fresh (), t), I), local)
    | M_PEval v ->
       let* (lname,bt,constr) = infer_value loc {local;global} v in
       return (Computational ((lname,bt), Constraint (constr, I)),local)
    | M_PEconstrained _ ->
       fail loc (Unsupported !^"todo: PEconstrained")
    | M_PEundef (loc,undef) ->
       fail loc (Undefined_behaviour undef)
    | M_PEerror (err, A (a,_,sym)) ->
       fail (Loc.update loc a) (StaticError (err,sym))
    | M_PEctor (ctor, args) ->
       let* (lname,bt,constr) = infer_constructor loc {local;global} ctor args in
       return (Computational ((lname,bt), Constraint (constr, I)),local)
    | M_PEarray_shift _ ->
       fail loc (Unsupported !^"todo: PEarray_shift")
    | M_PEmember_shift (A (a,_,sym), tag, id) ->
       let loc = Loc.update loc a in
       let ret = fresh () in
       let member = Member (Id.s id) in
       let tag = Tag tag in
       let* (bt,lname) = get_a loc sym local in
       let* () = check_base_type loc bt Loc in
       let* stored_struct = stored_struct_to loc {local;global} (S lname) tag in
       let* members = match stored_struct with
         | Some (_,{members; _}) -> return members
         | _ -> fail loc (Generic (!^"this location does not contain a struct with tag" ^^^ pp_tag tag))
       in
       let* faddr = assoc_err loc member members (Unreachable !^"check store field access") in
       let constr = LC (S ret %= faddr) in
       let rt = Computational ((ret, Loc), Constraint (constr,I)) in
       return (rt, local)
    | M_PEnot (A (a,_,sym)) ->
       let* (bt,lname) = get_a (Loc.update loc a) sym local in
       let* () = check_base_type (Loc.update loc a) Bool bt in
       let ret = fresh () in 
       let constr = (LC (S ret %= Not (S lname))) in
       let rt = Computational ((sym, Bool), Constraint (constr, I)) in
       return (rt, local)
    | M_PEop (op,A (a1,_,sym1),A (a2,_,sym2)) ->
       let* (bt1,lname1) = get_a (Loc.update loc a1) sym1 local in
       let* (bt2,lname2) = get_a (Loc.update loc a2) sym2 local in
       let (((ebt1,ebt2),rbt),result_it) = binop_typ op (S lname1) (S lname2) in
       let* () = check_base_type (Loc.update loc a1) bt1 ebt1 in
       let* () = check_base_type (Loc.update loc a2) bt2 ebt2 in
       let ret = fresh () in
       let constr = LC (S ret %= result_it) in
       let rt = Computational ((ret, rbt), Constraint (constr, I)) in
       return (rt, local)
    | M_PEstruct _ ->
       fail loc (Unsupported !^"todo: PEstruct")
    | M_PEunion _ ->
       fail loc (Unsupported !^"todo: PEunion")
    | M_PEmemberof _ ->
       fail loc (Unsupported !^"todo: M_PEmemberof")
    | M_PEcall (CF.Core.Impl impl, asyms) ->
       let* decl_typ = get_impl_fun_decl loc global impl in
       let* args = get_a_loc_asyms loc local asyms in
       let* (rt, local) = calltyp loc {local;global} args decl_typ in
       return (rt, local)
    | M_PEcall (CF.Core.Sym sym, asyms) ->
       let* (_loc,decl_typ) = get_fun_decl loc global sym in
       let* args = get_a_loc_asyms loc local asyms in
       let* (rt, local) = calltyp loc {local;global} args decl_typ in
       return (rt, local)
    | M_PElet (p, e1, e2) ->
       let* (rt, local) = infer_pexpr_pop loc {local = mark ++ local;global} e1 in
       let* local' = match p with
         | M_Symbol (A (_,_,sym)) -> return (bind sym rt)
         | M_Pat pat -> pattern_match_rt loc pat rt
       in
       let local = local' ++ local in
       infer_pexpr_pure loc {local;global} e2
    | M_PEcase _ -> fail loc (Unreachable !^"PEcase in inferring position")
    | M_PEif (casym, e1, e2) -> fail loc (Unreachable !^"PEif in inferring position")
  in
  
  let* () = debug_print 3 (blank 3 ^^ item "inferred" (RT.pp rt)) in
  let* () = debug_print 1 PPrint.empty in
  return (rt,local)




let rec check_pexpr (loc: Loc.t) {local;global} (e: 'bty mu_pexpr) (typ: RT.t) : L.t m = 

  let* () = debug_print 1 (action "checking pure expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (L.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_pexpr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = Loc.update loc annots in
  
  let* () = ensure_reachable loc {local;global} in

  match e_ with
  | M_PEif (A (a,_,csym), e1, e2) ->
     let* (cbt,clname) = get_a (Loc.update loc a) csym local in
     let* () = check_base_type (Loc.update loc a) cbt Bool in
     let* paths =
       filter_mapM (fun (lc, e) ->
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_pexpr loc {local;global} e typ in
             return (Some (local))
         ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
     in
     merge_local_environments loc paths
  | M_PEcase (A (a,_,sym), pats_es) ->
     let* (bt,lname) = get_a (Loc.update loc a) sym local in
     let* paths = 
       filter_mapM (fun (pat,pe) ->
           let* local' = pattern_match loc (S lname) pat bt in
           let local = local' ++ local in
           (* fix *)
           let lc = LC (Bool true) in
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_pexpr loc {local;global} e typ in
             return (Some (local))
         ) pats_es
     in
     merge_local_environments loc paths
  | M_PElet (p, e1, e2) ->
     let* (rt, local) = infer_pexpr_pop loc {local = mark ++ local;global} e1 in
     let* local' = match p with
       | M_Symbol (A (_,_,sym)) -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     let local = local' ++ local in
     check_pexpr loc {local;global} e2 typ
  | _ ->
     let* (rt, local) = infer_pexpr_pure loc {local;global} e in
     let* (local',(abt,lname)) = bind_logically rt in
     let local = local' ++ local in
     let* local = subtype loc {local;global} ((abt,lname),loc)
                  typ "function return type" in
     empty_pop loc local



let rec infer_expr_pop (loc: Loc.t) {local;global} (e: 'bty mu_expr) : (RT.t * L.t) m =
  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in
  match e_ with
  | M_Elet (p, e1, e2) ->
     let* (rt, local) = infer_pexpr_pop loc {local = mark ++ local;global} e1 in
     let* local' = match p with
       | M_Symbol (A (_,_,sym)) -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     let local = local' ++ local in
     infer_expr_pure loc {local;global} e2
  | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (pat, e1, e2) ->
     let* (rt, local) = infer_expr_pop loc {local = mark ++ local;global} e1 in
     let* local' = pattern_match_rt loc pat rt in
     let local = local' ++ local in
     infer_expr_pop loc {local;global} e2
  | _ ->
     let* (rt, local) = infer_expr_pure loc {local;global} e in
     return (rt_pop (rt, local))
  


and infer_expr_pure (loc: Loc.t) {local;global} (e: 'bty mu_expr) : (RT.t * L.t) m = 

  let* () = debug_print 1 (action "inferring expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (L.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in

  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in

  let* (typ,local) : RT.t * L.t = match e_ with
    | M_Epure pe -> 
       infer_pexpr_pure loc {local;global} pe
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
       | M_PtrValidForDeref (A (_,_,(_,size)), A (a,_,sym)) ->
          let ret = fresh () in
          let* (bt,lname) = get_a (Loc.update loc a) sym local in
          let* () = check_base_type (Loc.update loc a) bt Loc in
          (* check more things? *)
          let shape = match bt with
            | Struct tag -> StoredStruct_ (S lname, tag)
            | _ -> Points_ (S lname,size)
          in
          let* o_resource = match_resource loc {local;global} shape in
          let constr = LC (S ret %= Bool (is_some o_resource)) in
          let ret = Computational ((ret, Bool), Constraint (constr, I)) in
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
    | M_Eaction (M_Paction (_pol, M_Action (aloc,action_))) ->
       begin match action_ with
       | M_Create (A (a,_,sym), A (_,_,(bt,size)), _prefix) -> 
          let* (abt,_lname) = get_a (Loc.update loc a) sym local in
          let* () = check_base_type (Loc.update loc a) Int abt in
          let ret = fresh () in
          let* rt = match bt with
            | Struct tag -> 
               let* (stored,lbindings,rbindings) = 
                 Memory.store_struct loc global.struct_decls tag (S ret) None in
               return (Computational ((ret, Loc), lbindings @@
                       Resource (StoredStruct stored, rbindings)))
            | _ ->
               let r = Points {pointer = S ret; pointee = None; size} in
               return (Computational ((ret, Loc), Resource (r, I)))
          in
          return (rt, local)
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          fail loc (Unsupported !^"todo: CreateReadOnly")
       | M_Alloc (ct, sym, _prefix) -> 
          fail loc (Unsupported !^"todo: Alloc")
       | M_Kill (_is_dynamic, A (a,_,sym)) -> 
          (* have remove resources of location instead? *)
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
          | [] -> 
             fail loc (Generic !^"cannot deallocate unowned location")
          | _ :: _ :: _ -> 
             fail loc (Generic !^"cannot guess type of pointer to de-allocate" )
          | [(re_name,re)] -> 
             let* local = remove_owned_subtree loc {local;global} (re_name,re) in
             let rt = Computational ((Sym.fresh (), Unit), I) in
             return (rt, local)
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
          let resource_shape = match vbt with
            | Struct tag -> StoredStruct_ (S plname, tag)
            | _ -> Points_ (S plname,size)
          in
          let* o_resource = match_resource loc {local;global} resource_shape in
          let* local = match o_resource with
            | Some (rname,r) -> remove_owned_subtree loc {local;global} (rname,r)
            | None -> fail loc (Generic !^"missing ownership for store")
          in
          let* bindings = match vbt with
          | Struct tag -> 
             let* (stored,lbindings,rbindings) = 
               Memory.store_struct loc global.struct_decls tag (S plname) (Some (S vlname)) in
             return (lbindings @@ Resource (StoredStruct stored, rbindings))
           | _ -> 
             let resource = Points {pointer = S plname; pointee = Some (S vlname); size} in
             return (Resource (resource, I))
          in
          let rt = Computational ((fresh (), Unit), bindings) in
          return (rt,local)
       | M_Load (A (_,_,(bt,size)), A (ap,_,psym), _mo) -> 
          let ploc = Loc.update loc ap in
          let* (pbt,plname) = get_a ploc psym local in
          let* () = check_base_type loc pbt BT.Loc in
          let ret = fresh () in
          let* lcs = match bt with
            | Struct tag -> load_struct loc {local;global} tag (S plname) (S ret)
            | _ -> load_point loc {local;global} (S plname) size bt (S ret) false
          in
          let constraints = fold_right RT.mconstraint lcs RT.I in
          let rt = Computational ((ret, bt), constraints) in
          return (rt,local)
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
       let rt = Computational ((fresh (), Unit), I) in
       return (rt, local)
    | M_Eccall (_ctype, A(af,_,fsym), asyms) ->
       let* (bt,_) = get_a (Loc.update loc af) fsym local in
       let* fun_sym = match bt with
         | FunctionPointer sym -> return sym
         | _ -> fail (Loc.update loc af) (Generic !^"not a function pointer")
       in
       let* (_loc,decl_typ) = get_fun_decl loc global fun_sym in
       let* args = get_a_loc_asyms loc local asyms in
       let* (rt,local) = calltyp loc {local;global} args decl_typ in
       return (rt, local)
    | M_Eproc (fname, asyms) ->
       let* decl_typ = match fname with
         | CF.Core.Impl impl -> 
            get_impl_fun_decl loc global impl
         | CF.Core.Sym sym ->
            let* (_loc,decl_typ) = get_fun_decl loc global sym in
            return decl_typ
       in
       let* args = get_a_loc_asyms loc local asyms in
       let* (rt, local) = calltyp loc {local;global} args decl_typ in
       return (rt, local)
    | M_Ebound (n, e) ->
       infer_expr_pure loc {local;global} e
    | M_End _ ->
       fail loc (Unsupported !^"todo: End")
    | M_Esave _ ->
       fail loc (Unsupported !^"todo: Esave")
    | M_Erun _ ->
       fail loc (Unsupported !^"todo: Erun")
    | M_Ecase _ -> fail loc (Unreachable !^"Ecase in inferring position")
    | M_Eif _ -> fail loc (Unreachable !^"Eif in inferring position")
    | M_Elet (p, e1, e2) ->
       let* (rt, local) = infer_pexpr_pop loc {local = mark ++ local;global} e1 in
       let* local' = match p with
         | M_Symbol (A (_,_,sym)) -> return (bind sym rt)
         | M_Pat pat -> pattern_match_rt loc pat rt
       in
       let local = local' ++ local in
       infer_expr_pure loc {local;global} e2
    | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
    | M_Esseq (pat, e1, e2) ->
       let* (rt, local) = infer_expr_pop loc {local = mark ++ local;global} e1 in
       let* local' = pattern_match_rt loc pat rt in
       let local = local' ++ local in
       infer_expr_pure loc {local;global} e2
  in

  let* () = debug_print 3 (blank 3 ^^ item "inferred" (RT.pp typ)) in
  let* () = debug_print 1 PPrint.empty in
  return (typ,local)


let rec check_expr (loc: Loc.t) {local;global} (e: 'bty mu_expr) (typ: RT.t) = 

  let* () = debug_print 1 (action "checking expression type") in
  let* () = debug_print 1 (blank 3 ^^ item "type" (RT.pp typ)) in
  let* () = debug_print 1 (blank 3 ^^ item "environment" (L.pp local)) in
  let* () = debug_print 3 (blank 3 ^^ item "expression" (pp_expr pp_budget e)) in
  let* () = debug_print 1 PPrint.empty in

  let* () = ensure_reachable loc {local;global} in

  let (M_Expr (annots, e_)) = e in
  let loc = Loc.update loc annots in
  match e_ with
  | M_Eif (A (a,_,csym), e1, e2) ->
     let* (cbt,clname) = get_a (Loc.update loc a) csym local in
     let* () = check_base_type (Loc.update loc a) cbt Bool in
     let* paths =
       filter_mapM (fun (lc, e) ->
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_expr loc {local;global} e typ in
             return (Some (local))
         ) [(LC (S clname), e1); (LC (Not (S clname)), e2)]
     in
     merge_local_environments loc paths
  | M_Ecase (A (a,_,sym), pats_es) ->
     let* (bt,lname) = get_a (Loc.update loc a) sym local in
     let* paths = 
       filter_mapM (fun (pat,pe) ->
           let* local' = pattern_match loc (S lname) pat bt in
           let local = local' ++ local in
           (* fix *)
           let lc = LC (Bool true) in
           let local = add (mUC lc) local in
           let* unreachable = Solver.is_unreachable loc {local;global} in
           if unreachable then return None else 
             let* local = check_expr loc {local;global} e typ in
             return (Some (local))
         ) pats_es
     in
     merge_local_environments loc paths
  | M_Epure pe -> 
     check_pexpr loc {local;global} pe typ
  | M_Elet (p, e1, e2) ->
     let* (rt, local) = infer_pexpr_pop loc {local = mark ++ local;global} e1 in
     let* local' = match p with 
       | M_Symbol (A (_,_,sym)) -> return (bind sym rt)
       | M_Pat pat -> pattern_match_rt loc pat rt
     in
     let local = local' ++ local in
     check_expr loc {local;global} e2 typ
  | M_Ewseq (pat, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (pat, e1, e2) ->
     let* (rt, local) = infer_expr_pop loc {local = mark ++ local;global} e1 in
     let* local' = pattern_match_rt loc pat rt in
     let local = local' ++ local in
     check_expr loc {local;global} e2 typ
  | M_Esave (_ret, args, body) ->
     let* {local;global} = 
       fold_leftM (fun {local;global} (sym, (_, A (a,_,vsym))) ->
           let new_lname = fresh () in
           let* (bt,lname) = get_a (Loc.update loc a) vsym local in
           let local = add (mL new_lname (Base bt)) local in
           let local = add (mA sym (bt,new_lname)) local in
           let local = add (mUC (LC (S new_lname %= S lname))) local in
           return {local;global}
         ) {local;global} args
     in
     check_expr loc {local;global} body typ
  | _ ->
     let* (rt, local) = infer_expr_pure loc {local;global} e in
     let* (local',(abt,lname)) = bind_logically rt in
     let local = local' ++ local in
     let* local = subtype loc {local;global} ((abt,lname),loc) typ "function return type" in
     empty_pop loc local
     



let check_function (loc: Loc.t) 
                   (global: Global.t)
                   (fsym: Sym.t)
                   (arguments: (Sym.t * BT.t) list) 
                   (rbt: BT.t) 
                   (body : 'bty pexpr_or_expr)
                   (function_typ: FT.t) =
  
  let* () = match body with
    | EXPR body -> debug_print 1 (h1 ("Checking procedure " ^ (plain (Sym.pp fsym)))) 
    | PEXPR body -> debug_print 1 (h1 ("Checking function " ^ (plain (Sym.pp fsym)))) 
  in

  let rt_consistent rbt (Computational ((sname,sbt),t)) =
    if BT.equal rbt sbt then return ()
    else fail loc (Mismatch {has = (Base rbt); expect = Base sbt})
  in

  let rec check local args rbt body ftyp =
    match args, ftyp with
    | (aname,abt)::args, FT.Computational ((lname,sbt),ftyp) 
         when BT.equal abt sbt ->
       let new_lname = fresh () in
       let ftyp' = FT.subst_var {s=lname;swith=S new_lname} ftyp in
       let local = add (mL new_lname (Base abt)) local in
       let local = add (mA aname (abt,new_lname)) local in
       check local args rbt body ftyp'
    | (aname,abt)::args, FT.Computational ((sname,sbt),ftyp) ->
       fail loc (Mismatch {has = (Base abt); expect = Base sbt})
    | [], FT.Computational (_,_)
    | _::_, FT.Return _ ->
       let expect = FT.count_computational function_typ in
       let has = length arguments in
       fail loc (Number_arguments {expect;has})
    | args, FT.Logical ((sname,sls),ftyp) ->
       let new_lname = fresh () in
       let ftyp' = FT.subst_var {s=sname;swith=S new_lname} ftyp in
       check (add (mL new_lname sls) local) args rbt body ftyp'       
    | args, FT.Resource (re,ftyp) ->
       check (add (mUR re) local) args rbt body ftyp
    | args, FT.Constraint (lc,ftyp) ->
       check (add (mUC lc) local) args rbt body ftyp
    | [], FT.Return rt ->
       let* () = rt_consistent rbt rt in
       begin match body with
         | EXPR body -> check_expr loc {local;global} body rt
         | PEXPR body -> check_pexpr loc {local;global} body rt
       end
  in
  (* check environment has no resources? *)
  let* local = check L.empty arguments rbt body function_typ in
  let* () = debug_print 1 hardline in
  let* () = debug_print 2 (blank 3 ^^ item "environment" (L.pp local)) in
  let* () = debug_print 1 (!^(greenb "...checked ok")) in

  return ()



                             
(* TODO: 
  - make call_typ and subtype accept non-A arguments  
  - constrain return type shape, maybe also function type shape
 *)
