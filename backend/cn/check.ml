module CF=Cerb_frontend
module RE = Resources.RE
module RER = Resources.Requests
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LFT = ArgumentTypes.Make(LogicalReturnTypes)
module FT = ArgumentTypes.Make(ReturnTypes)
module LT = ArgumentTypes.Make(False)
module PackingFT = ArgumentTypes.Make(OutputDef)
module TE = TypeErrors
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module L = Local

open Subst
open IT
open Locations
open TypeErrors
open Resultat
module Mu = Retype.New
open CF.Mucore
open Mu
open Binding

open Pp
open BT
open Resources
open Resources.RE
open Predicates
open LogicalConstraints




(* some of this is informed by impl_mem *)



(*** mucore pp setup **********************************************************)

module PP_TYPS = struct
  module T = Retype.SR_Types
  let pp_bt = BT.pp 
  let pp_ct ct = Sctypes.pp ct
  let pp_ft = FT.pp
  let pp_gt = pp_ct
  let pp_lt = LT.pp
  let pp_ut _ = Pp.string "todo: implement union type printer"
  let pp_st _ = Pp.string "todo: implement struct type printer"
end

module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(PP_TYPS)
(* let pp_budget () = Some !debug_level *)
let pp_budget () = Some (!print_level*5)
let pp_pexpr e = PP_MUCORE.pp_pexpr e
let pp_tpexpr e = PP_MUCORE.pp_tpexpr (pp_budget ()) e
let pp_expr e = PP_MUCORE.pp_expr e
let pp_texpr e = PP_MUCORE.pp_texpr (pp_budget ()) e


module Make (G : sig val global : Global.t end) = struct
  module Solver = Solver.Make(G)
  module WT = WellTyped.Make(G)
  module Explain = Explain.Make(G)
  open L



  (*** meta types ***************************************************************)
  type mem_value = CF.Impl_mem.mem_value
  type pointer_value = CF.Impl_mem.pointer_value


  (*** auxiliaries **************************************************************)

  let ensure_logical_sort (loc : loc) ~(expect : LS.t) (has : LS.t) : (unit, type_error) m =
    if LS.equal has expect 
    then return () 
    else fail loc (Mismatch {has; expect})

  let ensure_base_type (loc : loc) ~(expect : BT.t) (has : BT.t) : (unit, type_error) m =
    ensure_logical_sort loc ~expect has


  let check_computational_bound loc s local = 
    if L.bound s KComputational local then return ()
    else fail loc (Unbound_name (Sym s))

  let get_struct_decl loc tag = 
    let open Global in
    match SymMap.find_opt tag G.global.struct_decls with
      | Some decl -> return decl
      | None -> fail loc (Missing_struct tag)

  let get_member_type loc tag member layout = 
    match List.assoc_opt Id.equal member (Memory.member_types layout) with
    | Some membertyp -> return membertyp
    | None -> fail loc (Missing_member (tag, member))






  (*** pattern matching *********************************************************)


  let pattern_match = 

    let rec aux (local' : L.t) pat : (L.t * IT.t, type_error) m = 
      let (M_Pattern (loc, _, pattern) : mu_pattern) = pat in
      match pattern with
      | M_CaseBase (o_s, has_bt) ->
         let lsym = Sym.fresh () in 
         let local' = add_l lsym has_bt local' in
         begin match o_s with
         | Some s when L.bound s KComputational local' -> 
            fail loc (Name_bound_twice (Sym s))
         | Some s -> 
            let local' = add_a s (has_bt, lsym) local' in
            return (local', sym_ (lsym, has_bt))
         | None -> 
            return (local', sym_ (lsym, has_bt))
         end
      | M_CaseCtor (constructor, pats) ->
         match constructor, pats with
         | M_Cnil item_bt, [] ->
            return (local', IT.nil_ ~item_bt)
         | M_Cnil item_bt, _ ->
            fail loc (Number_arguments {has = List.length pats; expect = 0})
         | M_Ccons, [p1; p2] ->
            let@ (local', it1) = aux local' p1 in
            let@ (local', it2) = aux local' p2 in
            let@ () = ensure_base_type loc ~expect:(List (IT.bt it1)) (IT.bt it2) in
            return (local', cons_ (it1, it2))
         | M_Ccons, _ -> 
            fail loc (Number_arguments {has = List.length pats; expect = 2})
         | M_Ctuple, pats ->
            let@ (local', its) = 
              ListM.fold_rightM (fun pat (local', its) ->
                  let@ (local', it) = aux local' pat in
                  return (local', it :: its)
                ) pats (local', [])
            in
            return (local', tuple_ its)
         | M_Cspecified, [pat] ->
            aux local' pat
         | M_Cspecified, _ ->
            fail loc (Number_arguments {expect = 1; has = List.length pats})
         | M_Carray, _ ->
            Debug_ocaml.error "todo: array types"
    in
    
    fun (sym, bt) (pat : mu_pattern) ->
    let@ (local, it) = aux L.empty pat in
    let@ () = 
      let (M_Pattern (loc, _, _) : mu_pattern) = pat in
      ensure_base_type loc ~expect:bt (IT.bt it) 
    in
    let local' = add_c (t_ (eq_ (it, sym_ (sym, bt)))) local in
    return local'
    


  (* The pattern-matching might de-struct 'bt'. For easily making
     constraints carry over to those values, record (lname,bound) as a
     logical variable and record constraints about how the variables
     introduced in the pattern-matching relate to (name,bound). *)
  let pattern_match_rt (pat : mu_pattern) (rt : RT.t) : (L.t, type_error) m =
    let ((bt, s'), delta) = bind_logically rt in
    let@ delta' = pattern_match (s', bt) pat in
    return (delta' ++ delta)





  (*** function call typing and subtyping ***************************************)

  (* Spine is parameterised by RT_Sig, so it can be used both for
     function and label types (which don't have a return type) *)


  type arg = {lname : Sym.t; bt : BT.t; loc : loc}
  type args = arg list

  let arg_of_sym (loc : loc) (local : L.t) (sym : Sym.t) : (arg, type_error) m = 
    let@ () = check_computational_bound loc sym local in
    let (bt,lname) = get_a sym local in
    return {lname; bt; loc}

  let arg_of_asym (local : L.t) (asym : 'bty asym) : (arg, type_error) m = 
    arg_of_sym asym.loc local asym.sym

  let args_of_asyms (local : L.t) (asyms : 'bty asyms) : (args, type_error) m = 
    ListM.mapM (arg_of_asym local) asyms


  let pp_unis (unis : IT.t Uni.t) : Pp.document = 
   let pp_entry (sym, Uni.{resolved}) =
     match resolved with
     | Some res -> Sym.pp sym ^^^ !^"resolved as" ^^^ IT.pp res
     | None -> Sym.pp sym ^^^ !^"unresolved"
   in
   Pp.list pp_entry (SymMap.bindings unis)






  module type Naming = sig val names : Explain.naming end
  module Checker (Names : Naming) = struct

    open Names

    module Prompt = struct

      type request_ui_info = { 
          original_local : L.t;
          extra_names : Explain.naming;
          loc: loc;
          situation: situation 
        }

      type resource_request = { 
          local : L.t;
          resource : RER.t;
          ui_info : request_ui_info;
        }

      type packing_request = { 
          local : L.t;
          packing_function : PackingFT.t;
          ui_info : request_ui_info;
        }

      type err = loc * Tools.stacktrace option * type_error Lazy.t

      type 'a m = 
        | Done : 'a -> 'a m
        | Prompt : 'r prompt * ('r -> 'a m) -> 'a m

      and 'r prompt = 
        | R_Resource : resource_request -> (RE.t * L.t) prompt
        | R_Packing : packing_request -> (OutputDef.t * L.t) prompt
        | R_Try : (('r m) Lazy.t) List1.t -> 'r prompt
        | R_Error : err -> 'r prompt


      module Operators = struct

        let return a = 
          Done a

        let fail loc err = 
          let r = R_Error (loc, Tools.do_stack_trace (),  err) in
          Prompt (r, fun r -> Done r)

        let prompt r = 
          Prompt (r, fun reply -> Done reply)

        let try_choices choices = 
          let r = R_Try choices in
          Prompt (r, fun reply -> Done reply)


        let rec bind m f = 
          match m with
          | Done a -> f a
          | Prompt (r, c) -> Prompt (r, fun r -> bind (c r) f)

        let (let@) = bind

        module ListM = struct  
          let fold_leftM (f : 'a -> 'b -> 'c m) (a : 'a) (bs : 'b list) =
            Stdlib.List.fold_left (fun aM b -> let@ a = aM in f a b) (return a) bs

          (* maybe from Exception.lem *)
          let fold_rightM (f : 'b -> 'a -> 'c m) (bs : 'b list) (a : 'a) =
            Stdlib.List.fold_right (fun b aM -> let@ a = aM in f b a) bs (return a)

        end

      end

    end




  (* requires equality on inputs *)
  let match_resources loc local error r1 r2 res =
    let open Prompt.Operators in
    let aux (res, constrs) (c, c') = 
      match IT.unify c c' res with
      | Some res -> return (res, constrs)
      | None -> return (res, (c, c') :: constrs)
    in
    let auxs (res, constrs) cs cs' =
      ListM.fold_leftM aux (res, []) (List.combine cs cs')
    in
    match r1, r2 with
    | Point b, Point b' 
         when IT.equal b.pointer b'.pointer &&
              Z.equal b.size b'.size &&
              IT.equal b.permission b'.permission ->
       let@ (res, constrs) = auxs (res, []) [b.value;b.init] [b'.value; b'.init] in
       if Solver.holds local (t_ (and_ (List.map eq_ constrs)))
       then return res
       else fail loc error
    | QPoint b, QPoint b' 
         when Sym.equal b.qpointer b'.qpointer &&
              Z.equal b.size b'.size &&
              IT.equal b.permission b'.permission ->
       let b' = { b' with value = eta_expand (b.qpointer, Loc) b'.value;
                          init = eta_expand (b.qpointer, Loc) b'.init; } in
       let@ (res,constrs) = auxs (res, []) [b.value; b.init] [b'.value; b'.init] in
       if Solver.holds local 
            (forall_ (b.qpointer, BT.Loc)
               None
               (impl_ (gt_ (b.permission, q_ (0, 1)), 
                       and_ (List.map eq_ constrs))))
       then return res 
       else fail loc error
    | Predicate p, Predicate p' 
         when 
           predicate_name_equal p.name p'.name &&
             IT.equal p.pointer p'.pointer &&
               List.equal IT.equal p.iargs p'.iargs &&
                 p.unused = p'.unused ->
       let@ (res, constrs) = auxs (res, []) p.oargs p'.oargs in
       if Solver.holds local 
            (t_ (impl_ (bool_ p'.unused, 
                        and_ (List.map eq_ constrs))))
       then return res 
       else fail loc error
    | QPredicate p, QPredicate p' 
         when 
           IT.equal p.pointer p'.pointer &&
              IT.equal p.element_size p'.element_size &&
              IT.equal p.istart p'.istart &&
              IT.equal p.iend p'.iend &&
              List.equal IT.equal p.moved p'.moved &&
              p.unused = p'.unused &&
              predicate_name_equal p.name p'.name &&
              Sym.equal p.i p'.i &&
              List.equal IT.equal p.iargs p'.iargs ->
       let p' = { p' with oargs = List.map (eta_expand (p.i, Integer)) p'.oargs } in
       let@ (res, constrs) = auxs (res, []) p.oargs p'.oargs in
       if Solver.holds local 
            (forall_ (p.i, BT.Integer)
             None
               (impl_ (and_ [bool_ p.unused; 
                             is_qpredicate_instance_index p (sym_ (p.i, Integer))],
                       and_ (List.map eq_ constrs))))
       then return res 
       else fail loc error
    | _ -> 
       fail loc error


    module Spine (I : AT.I_Sig) = struct

      module FT = AT.Make(I)
      module NFT = NormalisedArgumentTypes.Make(I)

      let pp_argslocs =
        Pp.list (fun ca -> parens (BT.pp ca.bt ^/^ bar ^/^ Sym.pp ca.lname))

      open Prompt
      open Prompt.Operators


      let spine 
            ui_info
            local
            (arguments : arg list) 
            (ftyp : FT.t) : (I.t * L.t) m =

        let open NFT in

        let loc = ui_info.loc in
        let original_local = ui_info.original_local in
        let situation = ui_info.situation in
        let names = names @ ui_info.extra_names in

        let ftyp = NFT.normalise ftyp in
        let unis = SymMap.empty in

        debug 6 (lazy (checking_situation situation));
        debug 6 (lazy (item "local" (L.pp local)));
        debug 6 (lazy (item "spec" (NFT.pp ftyp)));

        let@ ftyp_l = 
          let rec check_computational args ftyp = 
            match args, ftyp with
            | (arg :: args), (Computational ((s, bt), ftyp))
                 when BT.equal arg.bt bt ->
               let ftyp' = NFT.subst_var {before = s; after = arg.lname} ftyp in
               check_computational args ftyp'
            | (arg :: _), (Computational ((_, bt), _))  ->
               fail arg.loc (lazy (Mismatch {has = arg.bt; expect = bt}))
            | [], (L ftyp) -> 
               return ftyp
            | _ -> 
               let expect = NFT.count_computational ftyp in
               let has = List.length arguments in
               fail loc (lazy (Number_arguments {expect; has}))
          in
          check_computational arguments ftyp 
        in

        let@ ((unis, lspec), ftyp_r) = 
          let rec delay_logical (unis, lspec) ftyp =
            debug 6 (lazy (item "local" (L.pp local)));
            debug 6 (lazy (item "spec" (NFT.pp_l ftyp)));
            match ftyp with
            | Logical ((s, ls), ftyp) ->
               let s' = Sym.fresh () in
               let unis = SymMap.add s' Uni.{resolved = None} unis in
               let ftyp' = NFT.subst_var_l {before = s; after = s'} ftyp in
               delay_logical (unis, lspec @ [(s', ls)]) ftyp'
            | R ftyp -> 
               return ((unis, lspec), ftyp)
          in
          delay_logical (unis, []) ftyp_l
        in

        let@ (local, unis, ftyp_c) = 
          let rec infer_resources local unis ftyp = 
            debug 6 (lazy (item "local" (L.pp local)));
            debug 6 (lazy (item "spec" (NFT.pp_r ftyp)));
            debug 6 (lazy (item "unis" (pp_unis unis)));
            match ftyp with
            | Resource (resource, ftyp) -> 
               let rr = { ui_info; local; resource = RE.request resource; } in
               let@ (resource', local) = prompt (R_Resource rr) in
               let mismatch = 
                 lazy begin
                     let ((expect,has), state) = 
                       Explain.resources names original_local (resource, resource') in
                     (Resource_mismatch {expect; has; state; situation})
                   end
               in
               let@ unis = match_resources loc local mismatch resource resource' unis in
               let new_substs = Uni.find_resolved local unis in
               let ftyp' = NFT.subst_its_r new_substs ftyp in
               infer_resources local unis ftyp'
            | C ftyp ->
               return (local, unis, ftyp)
          in
          infer_resources local unis ftyp_r
        in

        let@ () = 
          let rec check_logical_variables = function
            | [] -> return ()
            | (s, expect) :: lspec ->
               let Uni.{resolved} = SymMap.find s unis in
               match resolved with
               | Some solution ->
                  if LS.equal (IT.bt solution) expect 
                  then check_logical_variables lspec
                  else fail loc (lazy (Mismatch { has = IT.bt solution; expect }))
               | None -> 
                  Debug_ocaml.error ("Unconstrained_logical_variable " ^ Sym.pp_string s)
          in
          check_logical_variables lspec
        in

        let@ rt = 
          let rec check_logical_constraints = function
            | Constraint (c, ftyp) -> 
               if Solver.holds local c then 
                 check_logical_constraints ftyp
               else
                 let err = 
                   lazy begin
                       let (constr,state) = 
                         Explain.unsatisfied_constraint names original_local c
                       in
                       (Unsat_constraint {constr; hint = None; state})
                     end
                 in
                 fail loc err
            | I rt ->
               return rt
          in
          check_logical_constraints ftyp_c
        in
        return (rt, local)

    end

    module Spine_FT = Spine(ReturnTypes)
    module Spine_LFT = Spine(LogicalReturnTypes)
    module Spine_LT = Spine(False)
    module Spine_Packing = Spine(OutputDef)




    (*** resource inference *******************************************************)



    let is_global local it = 
      SymSet.exists (fun s ->
        Solver.holds local (t_ (eq_ (it, IT.sym_ (s, BT.Loc))))
      ) local.global



    let resource_request_missing ui_info request =
      let open Prompt in
      let open Prompt.Operators in
      let err = 
        lazy begin 
            let (resource, state) = 
              Explain.resource_request (names @ ui_info.extra_names) 
                ui_info.original_local request 
            in
            Missing_resource {resource; used = None; state; 
                              situation = ui_info.situation}
          end
      in
      fail ui_info.loc err
    




    let unpack_predicate local (p : predicate) = 

      let def = Option.get (Global.get_predicate_def G.global p.name) in
      let substs = 
        {before = def.pointer; after= p.pointer} ::
        List.map2 (fun (before, _) after -> {before; after}) 
          def.iargs p.iargs
      in
      let possible_unpackings = 
        List.filter_map (fun (_, clause) ->
            let clause = PackingFT.subst_its substs clause in 
            let condition, outputs = PackingFT.logical_arguments_and_return clause in
            let lc = and_ (List.map2 (fun it (_, it') -> eq__ it it') p.oargs outputs) in
            let spec = LRT.concat condition (Constraint (t_ lc, I)) in
            let lrt = LRT.subst_its substs spec in
            (* remove resource before binding the return
               type 'condition', so as not to unsoundly
               introduce extra disjointness constraints *)
            let test_local = L.remove_resource (Predicate p) local in
            let test_local = bind_logical test_local lrt in
            if not (Solver.is_inconsistent test_local)
            then Some test_local else None
          ) def.clauses
      in
      begin match possible_unpackings with
      | [] -> Debug_ocaml.error "inconsistent state in every possible resource unpacking"
      | [new_local] -> (new_local, true)
      | _ -> (local, false)
      end


    let unpack_resources local = 
      let rec aux local = 
        let (local, changed) = 
          List.fold_left (fun (local, changed) resource ->
              match resource with
              | RE.Predicate p when p.unused ->
                 let (local, changed') = unpack_predicate local p in
                 (local, changed || changed')
              | _ ->
                 (local, changed)
            ) (local, false) (L.all_resources local)
        in
        if changed then aux local else local
      in
      aux local


    let unpack_resources_for local pointer = 
      let rec aux local = 
        let (local, changed) = 
          List.fold_left (fun (local, changed) resource ->
              match resource with
              | RE.Predicate p when p.unused ->
                 let (local, changed') = unpack_predicate local p in
                 (local, changed || changed')
              | RE.QPredicate p when p.unused && Solver.holds local (t_ (RE.is_qpredicate_instance_pointer p pointer)) ->
                 let p_inst = 
                   let index = qpredicate_pointer_to_index p p.pointer in
                   let iargs = List.map (IT.subst_it {before=p.i; after=index}) p.iargs in
                   let oargs = List.map (IT.subst_it {before=p.i; after=index}) p.oargs in
                   {name = p.name; pointer; iargs; oargs; unused = true} 
                 in
                 let local = L.remove_resource (QPredicate p) local in
                 let local = L.add_r (QPredicate {p with moved = pointer :: p.moved}) local in
                 let local = L.add_r (Predicate p_inst) local in
                 (local, true)
              | _ ->
                 (local, changed)
            ) (local, false) (L.all_resources local)
        in
        if changed then aux local else local
      in
      aux local
      


    let point_request_prompt ui_info local (requested : Resources.Requests.point) = 
      let open Prompt.Operators in
      let needed = requested.permission in 
      let local, (needed, value, init) =
        L.map_and_fold_resources (fun re (needed, value, init) ->
            match re with
            | Point p' 
                 when Z.equal requested.size p'.size &&
                      BT.equal requested.value (IT.bt p'.value) &&
                      Solver.holds local (t_ (eq_ (requested.pointer, p'.pointer))) ->
               let can_take = min_ (p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let value = ite_ (took, p'.value, value) in
               let init = ite_ (took, p'.init, init) in
               let needed = sub_ (needed, can_take) in
               let permission' = sub_ (p'.permission, can_take) in
               (Point {p' with permission = permission'}, (needed, value, init))
            | QPoint p' 
                 when Z.equal requested.size p'.size &&
                      BT.equal requested.value (IT.bt p'.value) ->
               let subst = {before=p'.qpointer; after = requested.pointer} in
               let can_take = min_ (IT.subst_it subst p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let value =  ite_ (took, IT.subst_it subst p'.value, value) in
               let init = ite_ (took, IT.subst_it subst p'.init, init) in
               let needed = sub_ (needed, can_take) in
               let permission' =
                 ite_ (eq_ (sym_ (p'.qpointer, BT.Loc), requested.pointer),
                       sub_ (IT.subst_it subst p'.permission, can_take),
                       p'.permission)
               in
               (QPoint {p' with permission = permission'}, (needed, value, init))
            | re ->
               (re, (needed, value, init))
          ) local (needed, default_ requested.value, default_ BT.Bool)
      in
      if Solver.holds local (t_ (eq_ (needed, q_ (0, 1)))) 
      then 
        let r = 
          { pointer = requested.pointer;
            size = requested.size;
            value = Simplify.simp local.constraints value;
            init = Simplify.simp local.constraints init;
            permission = requested.permission }
        in
        return (r, local)
      else resource_request_missing ui_info (Point requested)

    let qpoint_request_prompt ui_info local (requested : Resources.Requests.qpoint) = 
      let open Prompt.Operators in
      let needed = requested.permission in
      let local, (needed, value, init) =
        L.map_and_fold_resources (fun re (needed, value, init) ->
            match re with
            | Point p' 
                 when Z.equal requested.size p'.size &&
                      BT.equal requested.value (IT.bt p'.value) ->
               let subst = {before=requested.qpointer; after = p'.pointer} in
               let can_take = min_ (p'.permission, IT.subst_it subst needed) in
               let pmatch = eq_ (sym_ (requested.qpointer, BT.Loc), p'.pointer) in
               let needed = ite_ (pmatch, sub_ (IT.subst_it subst needed, can_take), needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let value = ite_ (and_ [pmatch;took], p'.value, value) in
               let init = ite_ (and_ [pmatch;took], p'.init, init) in
               let permission' = sub_ (p'.permission, can_take) in
               (Point {p' with permission = permission'}, (needed, value, init))
            | QPoint p' 
                 when Z.equal requested.size p'.size &&
                      BT.equal requested.value (IT.bt p'.value) ->
               let subst = {before=p'.qpointer; after = requested.qpointer} in
               let can_take = min_ (IT.subst_var subst p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let needed = sub_ (needed, can_take) in
               let value = ite_ (took, IT.subst_var subst p'.value, value) in
               let init = ite_ (took, IT.subst_var subst p'.init, init) in
               let permission' = 
                 sub_ (p'.permission, 
                       IT.subst_var {before=requested.qpointer; after = p'.qpointer} 
                         can_take)
               in
               (QPoint {p' with permission = permission'}, (needed, value, init))
            | re ->
               (re, (needed, value, init))
          ) local (needed, default_ requested.value, default_ BT.Bool)
      in
      if Solver.holds local 
           (forall_ (requested.qpointer, BT.Loc) None
              (eq_ (needed, q_ (0, 1))))
      then 
        let r = 
          { qpointer = requested.qpointer;
            size = requested.size;
            value = Simplify.simp local.constraints value; 
            init = Simplify.simp local.constraints init;
            permission = requested.permission;
          } 
        in
        return (r, local)
      else 
        resource_request_missing ui_info (QPoint requested)


    let predicate_request_prompt ui_info local (p : Resources.Requests.predicate) = 
      let open Prompt.Operators in
      if p.unused = false then
        let oargs = List.map (fun oa_bt -> default_ oa_bt) p.oargs in
        let r = 
          { name = p.name;
            pointer = p.pointer;
            iargs = p.iargs;
            oargs = oargs;
            unused = p.unused;
          }
        in
        return (r, local)
      else
        let local, found =
          L.map_and_fold_resources (fun re found ->
              match re, found with
              | Predicate p', None ->
                 if predicate_name_equal p.name p'.name &&
                    p'.unused && 
                    Solver.holds local (t_ (
                        and_ (IT.eq__ p.pointer p'.pointer ::
                              List.map2 eq__ p.iargs p'.iargs)
                      ))
                 then (Predicate {p' with unused = false}, Some p'.oargs)
                 else (re, found)
              | QPredicate p', None ->
                 let index = qpredicate_pointer_to_index p' p.pointer in
                 if predicate_name_equal p.name p'.name &&
                    p'.unused && 
                    Solver.holds local (
                        let iargs' = List.map (IT.subst_it {before=p'.i; after=index}) p'.iargs in
                        t_ (and_ (is_qpredicate_instance_pointer p' p.pointer ::
                                    List.map2 eq__ p.iargs iargs'))
                      )
                 then
                   let oargs = List.map (IT.subst_it {before=p'.i; after=index}) p'.oargs in
                   let moved = p.pointer :: p'.moved in
                   (QPredicate {p' with moved}, Some oargs)
                 else
                   (re, found)
              | _ ->
                 (re, found)
            ) local None
        in
        begin match found with
        (* we've already got the right resource *)
        | Some oargs ->
           let r = 
             { name = p.name;
               pointer = p.pointer;
               iargs = p.iargs;
               oargs = oargs;
               unused = p.unused;
             }
           in
           return (r, local)
        | None ->
           (* we haven't and will try to get it by packing *)
           (* (we've eagerly unpacked, so no need to try to get it by unpacking) *)
           let def = Option.get (Global.get_predicate_def G.global p.name) in
           let substs = 
             (* only input arguments! *)
             {before = def.pointer; after = p.pointer} ::
               List.map2 (fun (before, _) after -> {before; after}) 
                 def.iargs p.iargs 
           in
           let attempt_prompts = 
             List.map (fun (_, clause) ->
                 lazy begin
                     let packing_function = subst_its_clause substs clause in
                     prompt (R_Packing {ui_info; local; packing_function})
                   end
               ) def.clauses
           in
           let choices = 
             attempt_prompts @ 
               [lazy (resource_request_missing ui_info (Predicate p))] 
           in
           let choices1 = List1.make (List.hd choices, List.tl choices) in
           let@ (assignment, local) = try_choices choices1 in
           let r = 
             { pointer = p.pointer;
               name = p.name;
               iargs = p.iargs;
               oargs = List.map snd assignment;
               unused = p.unused;
             }
           in
           return (r, local)
        end

    let qpredicate_request_prompt ui_info local (p : Resources.Requests.qpredicate) = 
      let open Prompt.Operators in
      assert ([] = p.moved); (* todo? *)
      if p.unused = false then
        let oargs = List.map (fun oa_bt -> default_ oa_bt) p.oargs in
        let r = 
          { name = p.name;
            element_size = p.element_size;
            istart = p.istart;
            iend = p.iend;
            i = p.i;
            pointer = p.pointer;
            iargs = p.iargs;
            oargs = oargs;
            unused = p.unused;
            moved = p.moved;
          }
        in
        return (r, local)
      else
        let local, found =
          L.map_and_fold_resources (fun re found ->
              match re, found with
              | QPredicate p', None ->
                 if predicate_name_equal p.name p'.name &&
                    p.unused = p'.unused &&
                    Solver.holds local 
                      (t_ (and_ [eq_ (p.pointer, p'.pointer);
                                 eq_ (p.element_size, p'.element_size);
                                 eq_ (p.istart, p'.istart);
                                 eq_ (p.iend, p'.iend)])) &&
                      Solver.holds local 
                        (forall_ (p.i, BT.Integer) None
                           (impl_ 
                              (RER.is_qpredicate_instance_index {p with moved = p'.moved} (sym_ (p.i, Integer)),
                               let iargs' = List.map (IT.subst_var {before=p'.i;after=p.i}) p'.iargs in
                               and_ (List.map2 eq__ p.iargs iargs')))
                        )
                 then 
                   let oargs' = List.map (IT.subst_var {before=p'.i;after=p.i}) p'.oargs in
                   (QPredicate {p' with unused = false}, Some (oargs', p'.moved))
                 else 
                   (re, found)
              | _ ->
                 (re, found)
            ) local None
        in
        match found with
        | Some (oargs, moved) ->
           (* fill in moved ownership *)
           let@ (oargs, local) = 
             ListM.fold_leftM (fun (oargs, local) moved_pointer ->
                 (* moved_pointer assumed to satisfy
                    pointer-start-element_size-length condition *)
                 let index = RER.qpredicate_pointer_to_index p moved_pointer in
                 let request = RER.{
                     name = p.name; 
                     pointer = moved_pointer;
                     iargs = List.map (IT.subst_it{before=p.i;after=index}) p.iargs;
                     oargs = p.oargs; 
                     unused = true
                   }
                 in
                 let@ (packed, local) = 
                   predicate_request_prompt ui_info local request
                 in
                 let oargs = 
                   List.map2 (fun oa oa' ->
                       ite_ (eq_ (sym_ (p.i, Integer), index), oa', oa)
                     ) oargs packed.oargs
                 in
                 return (oargs, local)
               ) (oargs, local) moved
           in
           let r = 
             { pointer = p.pointer;
               element_size = p.element_size;
               istart = p.istart;
               iend = p.iend;
               moved = []; 
               unused = p.unused;
               name = p.name;
               i = p.i;
               iargs = p.iargs;
               oargs = oargs 
             }
           in
           return (r, local)
        | None ->
           resource_request_missing ui_info (QPredicate p)

    let resource_request_prompt ui_info local (request : Resources.Requests.t) : (RE.t * L.t) Prompt.m = 
      let open Prompt.Operators in
      match request with
      | Point requested ->
         let@ point, local = point_request_prompt ui_info local requested in
         return (Point point, local)
      | QPoint requested ->
         let@ qpoint, local = qpoint_request_prompt ui_info local requested in
         return (QPoint qpoint, local)
      | Predicate requested ->
         let@ predicate, local = predicate_request_prompt ui_info local requested in
         return (Predicate predicate, local)
      | QPredicate requested ->
         let@ qpredicate, local = qpredicate_request_prompt ui_info local requested in
         return (QPredicate qpredicate, local)


    let handle_prompt : 'a. 'a Prompt.m -> ('a, type_error) m =
      let rec aux  : 'a. 'a Prompt.m -> ('a, (loc * Tools.stacktrace option * type_error) Lazy.t) result = function
        | Prompt.Done a -> 
           Ok a
        | Prompt.Prompt (r, c) ->
           begin match r with
           | Prompt.R_Error (loc,tr,error) -> 
              Error (lazy (loc,tr, Lazy.force error))
           | R_Resource {ui_info; local; resource} ->
              let prompt = 
                resource_request_prompt ui_info local resource in
              let@ (unis, local) = aux prompt in
              aux (c (unis, local))
           | R_Packing {ui_info; local; packing_function} ->
              let prompt = Spine_Packing.spine ui_info local [] packing_function in
              let@ (assignment, local) = aux prompt in
              aux (c (assignment, local))
           | R_Try choices ->
              let rec first_success list1 =
                let (hd, tl) = List1.dest list1 in
                let hd_run = aux (Lazy.force hd) in
                match tl with
                | [] -> hd_run
                | hd' :: tl' -> msum hd_run (lazy (first_success (List1.make (hd', tl'))))
              in
              let@ reply = first_success choices in
              aux (c reply)
           end
      in
      fun prompt ->
      match aux prompt with
      | Ok a -> Ok a
      | Error e -> Error (Lazy.force e)





    let calltype_ft loc local args (ftyp : FT.t) : (RT.t * L.t, type_error) m =
      let extra_names = 
        List.mapi (fun i arg ->
            let v = "ARG" ^ string_of_int i in
            (arg.lname, Ast.Addr v)
          ) args
      in
      let open Prompt in
      let ui_info = { loc; extra_names; situation = FunctionCall; original_local = local } in
      let prompt = Spine_FT.spine ui_info local args ftyp in
      let@ (rt, local) = handle_prompt prompt in
      return (rt, local)

    let calltype_lt loc extra_names local args ((ltyp : LT.t), label_kind) : (False.t * L.t, type_error) m =
      let open Prompt in
      let ui_info = { loc; extra_names; situation = LabelCall label_kind; original_local = local } in
      let prompt = Spine_LT.spine ui_info local args ltyp in
      let@ (rt, local) = handle_prompt prompt in
      return (rt, local)

    (* The "subtyping" judgment needs the same resource/lvar/constraint
       inference as the spine judgment. So implement the subtyping
       judgment 'arg <: RT' by type checking 'f(arg)' for 'f: RT -> False'. *)
    let subtype (loc : loc) local arg (rtyp : RT.t) : (L.t, type_error) m =
      let extra_names = [(arg.lname, Ast.Var {label = None; v ="return"})] in
      let open Prompt in
      let ui_info = { loc; extra_names; situation = Subtyping; original_local = local } in
      let lt = LT.of_rt rtyp (LT.I False.False) in
      let prompt = Spine_LT.spine ui_info local [arg] lt in
      let@ (False.False, local) = handle_prompt prompt in
      return local




    let resource_request (loc: loc) situation local (request : RER.t) : (RE.t * L.t, type_error) m = 
      let open Prompt in
      let ui_info = { loc; extra_names = []; situation; original_local = local } in
      let prompt = resource_request_prompt ui_info local request in
      handle_prompt prompt


    let predicate_request (loc: loc) situation local (request : RER.predicate) : (RE.predicate * L.t, type_error) m = 
      let open Prompt in
      let ui_info = { loc; extra_names = []; situation; original_local = local } in
      let prompt = predicate_request_prompt ui_info local request in
      handle_prompt prompt



    (*** pure value inference *****************************************************)

    type vt = BT.t * IT.t
    let it_of_arg arg = sym_ (arg.lname, arg.bt)
    let vt_of_arg arg = (arg.bt, it_of_arg arg)

    let rt_of_vt (bt,it) = 
      let s = Sym.fresh () in 
      RT.Computational ((s, bt), 
      LRT.Constraint (t_ (def_ s it),
      LRT.I))


    let infer_tuple (loc : loc) (vts : vt list) : (vt, type_error) m = 
      let bts, its = List.split vts in
      return (Tuple bts, IT.tuple_ its)

    let infer_array (loc : loc) (vts : vt list) = 
      let item_bt = match vts with
        | [] -> Debug_ocaml.error "todo: empty arrays"
        | (i_bt, _) :: _ -> i_bt
      in
      let@ (_, it) = 
        ListM.fold_leftM (fun (index,it) (arg_bt, arg_it) -> 
            let@ () = ensure_base_type loc ~expect:item_bt arg_bt in
            return (index + 1, mod_ (it, int_ index, arg_it))
             ) (0, const_ (default_ item_bt)) vts
      in
      return (BT.Param (Integer, item_bt), it)


    let infer_constructor (loc : loc) local (constructor : mu_ctor) 
                          (args : arg list) : (vt, type_error) m = 
      match constructor, args with
      | M_Ctuple, _ -> 
         infer_tuple loc (List.map vt_of_arg args)
      | M_Carray, args -> 
         infer_array loc (List.map vt_of_arg args)
      | M_Cspecified, [arg] ->
         return (vt_of_arg arg)
      | M_Cspecified, _ ->
         fail loc (Number_arguments {has = List.length args; expect = 1})
      | M_Cnil item_bt, [] -> 
         let bt = List item_bt in
         return (bt, nil_ ~item_bt)
      | M_Cnil item_bt, _ -> 
         fail loc (Number_arguments {has = List.length args; expect=0})
      | M_Ccons, [arg1; arg2] -> 
         let bt = List arg1.bt in
         let@ () = ensure_base_type arg2.loc ~expect:bt arg2.bt in
         let list_it = cons_ (it_of_arg arg1, it_of_arg arg2) in
         return (arg2.bt, list_it)
      | M_Ccons, _ ->
         fail loc (Number_arguments {has = List.length args; expect = 2})



    let infer_ptrval (loc : loc) (ptrval : pointer_value) : (vt, type_error) m =
      CF.Impl_mem.case_ptrval ptrval
        ( fun ct -> 
          return (Loc, IT.null_) )
        ( fun sym -> 
          return (Loc, sym_ (sym, BT.Loc)) )
        ( fun _prov loc -> 
          return (Loc, pointer_ loc) )
        ( fun () -> 
          Debug_ocaml.error "unspecified pointer value" )

    let rec infer_mem_value (loc : loc) (mem : mem_value) : (vt, type_error) m =
      let open BT in
      CF.Impl_mem.case_mem_value mem
        ( fun ct -> 
          fail loc (Unspecified ct) )
        ( fun _ _ -> 
          unsupported loc !^"infer_mem_value: concurrent read case" )
        ( fun it iv -> 
          return (Integer, z_ (Memory.integer_value_to_num iv)) )
        ( fun ft fv -> 
          unsupported loc !^"floats" )
        ( fun _ ptrval -> 
          infer_ptrval loc ptrval  )
        ( fun mem_values -> 
          let@ vts = ListM.mapM (infer_mem_value loc) mem_values in
          infer_array loc vts )
        ( fun tag mvals -> 
          let mvals = List.map (fun (member, _, mv) -> (member, mv)) mvals in
          infer_struct loc tag mvals )
        ( fun tag id mv -> 
          infer_union loc tag id mv )

    and infer_struct (loc : loc) (tag : tag) 
                     (member_values : (member * mem_value) list) : (vt, type_error) m =
      (* might have to make sure the fields are ordered in the same way as
         in the struct declaration *)
      let@ layout = get_struct_decl loc tag in
      let rec check fields spec =
        match fields, spec with
        | ((member, mv) :: fields), ((smember, sct) :: spec) 
             when member = smember ->
           let@ (member_bt, member_it) = infer_mem_value loc mv in
           let@ () = ensure_base_type loc ~expect:(BT.of_sct sct) member_bt in
           let@ member_its = check fields spec in
           return ((member, member_it) :: member_its)
        | [], [] -> 
           return []
        | ((id, mv) :: fields), ((smember, sbt) :: spec) ->
           Debug_ocaml.error "mismatch in fields in infer_struct"
        | [], ((member, _) :: _) ->
           fail loc (Generic (!^"field" ^/^ Id.pp member ^^^ !^"missing"))
        | ((member,_) :: _), [] ->
           fail loc (Generic (!^"supplying unexpected field" ^^^ Id.pp member))
      in
      let@ it = check member_values (Memory.member_types layout) in
      return (BT.Struct tag, IT.struct_ (tag, it))

    and infer_union (loc : loc) (tag : tag) (id : Id.t) 
                    (mv : mem_value) : (vt, type_error) m =
      Debug_ocaml.error "todo: union types"
    
    let rec infer_object_value (loc : loc)
                           (ov : 'bty mu_object_value) : (vt, type_error) m =
      match ov with
      | M_OVinteger iv ->
         let i = Memory.integer_value_to_num iv in
         return (Integer, z_ i)
      | M_OVpointer p -> 
         infer_ptrval loc p
      | M_OVarray items ->
         let@ vts = ListM.mapM (infer_loaded_value loc) items in
         infer_array loc vts
      | M_OVstruct (tag, fields) -> 
         let mvals = List.map (fun (member,_,mv) -> (member, mv)) fields in
         infer_struct loc tag mvals       
      | M_OVunion (tag, id, mv) -> 
         infer_union loc tag id mv
      | M_OVfloating iv ->
         unsupported loc !^"floats"

    and infer_loaded_value loc (M_LVspecified ov) =
      infer_object_value loc ov

    let rec infer_value (loc : loc) (v : 'bty mu_value) : (vt, type_error) m = 
      match v with
      | M_Vobject ov ->
         infer_object_value loc ov
      | M_Vloaded lv ->
         infer_loaded_value loc lv
      | M_Vunit ->
         return (Unit, IT.unit_)
      | M_Vtrue ->
         return (Bool, IT.bool_ true)
      | M_Vfalse -> 
         return (Bool, IT.bool_ false)
      | M_Vlist (bt, vals) ->
         let@ its = 
           ListM.mapM (fun v -> 
               let@ (i_bt, i_it) = infer_value loc v in
               let@ () = ensure_base_type loc ~expect:bt i_bt in
               return i_it
             ) vals
         in
         return (BT.List bt, list_ ~item_bt:bt its)
      | M_Vtuple vals ->
         let@ vts = ListM.mapM (infer_value loc) vals in
         let bts, its = List.split vts in
         return (Tuple bts, tuple_ its)



    (*** pure expression inference ************************************************)

    (* infer_pexpr: the raw type inference logic for pure expressions;
       returns a return type and a local environment *)
    (* infer_pexpr_pop: place a marker in the local environment, run
       the raw type inference, and return, in addition to what the raw
       inference returns, all logical (logical variables, resources,
       constraints) in the local environment *)

    let infer_array_shift local asym1 ct asym2 =
      let@ arg1 = arg_of_asym local asym1 in
      let@ arg2 = arg_of_asym local asym2 in
      let@ () = ensure_base_type arg1.loc ~expect:Loc arg1.bt in
      let@ () = ensure_base_type arg2.loc ~expect:Integer arg2.bt in
      let element_size = Memory.size_of_ctype ct in
      let v = 
        addPointer_ (it_of_arg arg1, 
                     mul_ (z_ element_size, it_of_arg arg2))
      in
      return (Loc, v)

    let infer_wrapI local ct asym =
      match ct with
      | Sctypes.Sctype (_, Integer ty) ->
         let@ arg = arg_of_asym local asym in
         let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
         (* try to follow wrapI from runtime/libcore/std.core *)
         let dlt = add_ (sub_ (maxInteger_ ty, minInteger_ ty), int_ 1) in
         let r = rem_f___ (it_of_arg arg, dlt) in
         let result_it = ite_  (le_ (r, maxInteger_ ty), r,sub_ (r, dlt)) in
         return (rt_of_vt (Integer, result_it), local)
      | _ ->
         Debug_ocaml.error "wrapI applied to non-integer type"



    let infer_pexpr local (pe : 'bty mu_pexpr) : ((RT.t * L.t), type_error) m = 
      let (M_Pexpr (loc, _annots, _bty, pe_)) = pe in
      debug 3 (lazy (action "inferring pure expression"));
      debug 3 (lazy (item "expr" (pp_pexpr pe)));
      debug 3 (lazy (item "ctxt" (L.pp local)));
      let@ (rt, local) = match pe_ with
        | M_PEsym sym ->
           let@ arg = arg_of_sym loc local sym in
           return ((rt_of_vt (vt_of_arg arg), local))
        | M_PEimpl i ->
           let rt = Global.get_impl_constant G.global i in
           return (rt, local)
        | M_PEval v ->
           let@ vt = infer_value loc v in
           return (rt_of_vt vt, local)
        | M_PEconstrained _ ->
           Debug_ocaml.error "todo: PEconstrained"
        | M_PEerror (err, asym) ->
           let@ arg = arg_of_asym local asym in
           fail arg.loc (StaticError err)
        | M_PEctor (ctor, asyms) ->
           let@ args = args_of_asyms local asyms in
           let@ vt = infer_constructor loc (local, G.global) ctor args in
           return (rt_of_vt vt, local)
        | M_CivCOMPL _
          | M_CivAND _
          | M_CivOR _
          | M_CivXOR _ 
          -> 
           Debug_ocaml.error "todo: Civ..."
        | M_Cfvfromint _ -> 
           unsupported loc !^"floats"
        | M_Civfromfloat _ -> 
           unsupported loc !^"floats"
        | M_PEarray_shift (asym1, ct, asym2) ->
           let@ vt = infer_array_shift local asym1 ct asym2 in
           return (rt_of_vt vt, local)
        | M_PEmember_shift (asym, tag, member) ->
           let@ arg = arg_of_asym local asym in
           let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
           let local = unpack_resources_for local (it_of_arg arg) in
           let@ (predicate, local) = 
             predicate_request loc (Access (Load None)) local 
               { name = Ctype (Sctype ([], Struct tag)) ;
                 pointer = it_of_arg arg;
                 iargs = [];
                 oargs = [Struct tag ; BT.Bool];
                 unused = true;
               }
           in
           let@ layout = get_struct_decl loc tag in
           let@ _member_bt = get_member_type loc tag member layout in
           let@ offset = match Memory.member_offset layout member with
             | Some offset -> return offset
             | None -> fail loc (Missing_member (tag, member))
           in
           let vt = (Loc, IT.addPointer_ (it_of_arg arg, z_ offset)) in
           return (RT.concat (rt_of_vt vt) (Resource (Predicate predicate, LRT.I)), local)
        | M_PEnot asym ->
           let@ arg = arg_of_asym local asym in
           let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
           let vt = (Bool, not_ (it_of_arg arg)) in
           return (rt_of_vt vt, local)
        | M_PEop (op, asym1, asym2) ->
           let@ arg1 = arg_of_asym local asym1 in
           let@ arg2 = arg_of_asym local asym2 in
           let v1 = it_of_arg arg1 in
           let v2 = it_of_arg arg2 in
           let (((ebt1, ebt2), rbt), result_it) =
             match op with
             | OpAdd ->   (((Integer, Integer), Integer), IT.add_ (v1, v2))
             | OpSub ->   (((Integer, Integer), Integer), IT.sub_ (v1, v2))
             | OpMul ->   (((Integer, Integer), Integer), IT.mul_ (v1, v2))
             | OpDiv ->   (((Integer, Integer), Integer), IT.div_ (v1, v2))
             | OpRem_t -> (((Integer, Integer), Integer), IT.rem_t___ (v1, v2))
             | OpRem_f -> (((Integer, Integer), Integer), IT.rem_f___ (v1, v2))
             | OpExp ->   (((Integer, Integer), Integer), IT.exp_ (v1, v2))
             | OpEq ->    (((Integer, Integer), Bool), IT.eq_ (v1, v2))
             | OpGt ->    (((Integer, Integer), Bool), IT.gt_ (v1, v2))
             | OpLt ->    (((Integer, Integer), Bool), IT.lt_ (v1, v2))
             | OpGe ->    (((Integer, Integer), Bool), IT.ge_ (v1, v2))
             | OpLe ->    (((Integer, Integer), Bool), IT.le_ (v1, v2))
             | OpAnd ->   (((Bool, Bool), Bool), IT.and_ [v1; v2])
             | OpOr ->    (((Bool, Bool), Bool), IT.or_ [v1; v2])
           in
           let@ () = ensure_base_type arg1.loc ~expect:ebt1 arg1.bt in
           let@ () = ensure_base_type arg2.loc ~expect:ebt2 arg2.bt in
           return (rt_of_vt (rbt, result_it), local)
        | M_PEstruct _ ->
           Debug_ocaml.error "todo: PEstruct"
        | M_PEunion _ ->
           Debug_ocaml.error "todo: PEunion"
        | M_PEmemberof _ ->
           Debug_ocaml.error "todo: M_PEmemberof"
        | M_PEcall (called, asyms) ->
           let@ decl_typ = match called with
             | CF.Core.Impl impl -> 
                return (Global.get_impl_fun_decl G.global impl )
             | CF.Core.Sym sym -> 
                let@ (_, t) = match Global.get_fun_decl G.global sym with
                  | Some t -> return t
                  | None -> fail loc (Missing_function sym)
                in
                return t
           in
           let@ args = args_of_asyms local asyms in
           calltype_ft loc local args decl_typ
        | M_PEassert_undef (asym, _uloc, undef) ->
           let@ arg = arg_of_asym local asym in
           let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
           if Solver.holds local (t_ (it_of_arg arg)) then
             return (rt_of_vt (Unit, unit_), local)
           else
             let expl = Explain.undefined_behaviour names local in
             fail loc (Undefined_behaviour (undef, expl))
        | M_PEbool_to_integer asym ->
           let@ arg = arg_of_asym local asym in
           let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
           let vt = (Integer, (ite_ (it_of_arg arg, int_ 1, int_ 0))) in
           return (rt_of_vt vt, local)
        | M_PEconv_int (act, asym) ->
           let@ arg = arg_of_asym local asym in
           let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
           (* try to follow conv_int from runtime/libcore/std.core *)
           let arg_it = it_of_arg arg in
           begin match act.ct with
           | Sctype (_, Integer Bool) ->
              let vt = (Integer, ite_ (eq_ (arg_it, int_ 0), int_ 0, int_ 1)) in
              return (rt_of_vt vt, local)
           | _ 
                when Solver.holds local (t_ (representable_ (act.ct, arg_it))) ->
              return (rt_of_vt (Integer, arg_it), local)
           | Sctype (_, Integer ty) 
                when Sctypes.is_unsigned_integer_type act.ct ->
              infer_wrapI local act.ct asym
           | _ ->
              let (it_pp, state_pp) = 
                Explain.implementation_defined_behaviour names local 
                  arg_it
              in
              fail loc (Implementation_defined_behaviour 
                          (it_pp ^^^ !^"outside representable range for" ^^^ 
                             Sctypes.pp act.ct, state_pp))
           end
        | M_PEwrapI (act, asym) ->
           infer_wrapI local act.ct asym
      in  
      debug 3 (lazy (item "type" (RT.pp rt)));
      return (rt, local)


    (* check_pexpr: type check the pure expression `e` against return type
       `typ`; returns a "reduced" local environment *)






    let rec check_tpexpr local (e : 'bty mu_tpexpr) (typ : RT.t) : (unit, type_error) m = 
      let (M_TPexpr (loc, _annots, _, e_)) = e in
      debug 3 (lazy (action "checking pure expression"));
      debug 3 (lazy (item "expr" (group (pp_tpexpr e))));
      debug 3 (lazy (item "type" (RT.pp typ)));
      debug 3 (lazy (item "ctxt" (L.pp local)));
      match e_ with
      | M_PEif (casym, e1, e2) ->
         let@ carg = arg_of_asym local casym in
         let@ () = ensure_base_type carg.loc ~expect:Bool carg.bt in
         ListM.iterM (fun (lc, e) ->
             let local = add_c (t_ lc) local in
             if Solver.is_inconsistent local then return ()
             else check_tpexpr local e typ
           ) [(it_of_arg carg, e1); (not_ (it_of_arg carg), e2)]
      | M_PEcase (asym, pats_es) ->
         let@ arg = arg_of_asym local asym in
         ListM.iterM (fun (pat, pe) ->
             let@ delta = pattern_match (arg.lname, arg.bt) pat in
             let local = delta ++ local in
             if Solver.is_inconsistent local then return ()
             else check_tpexpr local e typ
           ) pats_es
      | M_PElet (p, e1, e2) ->
         let@ (rt, local) = infer_pexpr local e1 in
         let@ delta = match p with
           | M_Symbol sym -> return (bind sym rt)
           | M_Pat pat -> pattern_match_rt pat rt
         in
         check_tpexpr (delta ++ local) e2 typ
      | M_PEdone asym ->
         let@ arg = arg_of_asym local asym in
         let@ local = subtype loc local arg typ in
         return ()
      | M_PEundef (_loc, undef) ->
         let expl = Explain.undefined_behaviour names local in
         fail loc (Undefined_behaviour (undef, expl))


    (*** impure expression inference **********************************************)


    (* type inference of impure expressions; returns either a return type
       and new local environment or False *)
    (* infer_expr: the raw type inference for impure expressions. *)
    (* infer_expr_pop: analogously to infer_pexpr: place a marker, run
       the raw type inference, and additionally return whatever is left in
       the local environment since that marker (except for computational
       variables) *)

    (* `t` is used for the type of Run/Goto: Goto has no return type
       (because the control flow does not return there), but instead
       returns `False`. Type inference of impure expressions returns
       either a return type and a local environment or `False` *)
    type 'a t = 
      | Normal of 'a
      | False

    type 'a orFalse = 'a t

    let pp_or_false (ppf : 'a -> Pp.document) (m : 'a t) : Pp.document = 
      match m with
      | Normal a -> ppf a
      | False -> parens !^"no return"


    (*** auxiliary ****************************************************************)
    let json_local loc names local : Yojson.Safe.t = 
      `Assoc [("loc", json_loc loc);
              ("context", `Variant ("context", Some (Explain.json_state names local)))]

    let json_false loc : Yojson.Safe.t = 
      `Assoc [("loc", json_loc loc);
              ("context", `Variant ("unreachable", None))]

    let json_local_or_false loc names = function
      | Normal local -> json_local loc names local
      | False -> json_false loc



    let all_empty loc extra_names local = 
      let bad = 
        List.find_opt (fun resource ->
            match resource with
            | Point p ->
               not (Solver.holds local (t_ (le_ (p.permission, q_ (0, 1)))))
            | QPoint p ->
               not (Solver.holds local 
                      (forall_ (p.qpointer, BT.Loc) None
                         (le_ (p.permission, q_ (0, 1)))))
            | Predicate p ->
               not p.unused
            | QPredicate p ->
               not p.unused &&
                 not (Solver.holds local (t_ (eq_ (p.istart, p.iend))))
          ) local.resources
      in
      match bad with
      | None -> return ()
      | Some resource ->
         let names = names @ extra_names in
         let (resource, state) = Explain.resource names local resource in
         fail loc (Unused_resource {resource; state})


    type labels = (LT.t * label_kind) SymMap.t


    let infer_expr (local, labels) (e : 'bty mu_expr) 
            : ((RT.t * L.t), type_error) m = 
      let (M_Expr (loc, _annots, e_)) = e in
      debug 3 (lazy (action "inferring expression"));
      debug 3 (lazy (item "expr" (group (pp_expr e))));
      debug 3 (lazy (item "ctxt" (L.pp local)));
      let@ result = match e_ with
        | M_Epure pe -> 
           infer_pexpr local pe
        | M_Ememop memop ->
           let pointer_op op asym1 asym2 = 
             let@ arg1 = arg_of_asym local asym1 in
             let@ arg2 = arg_of_asym local asym2 in
             let@ () = ensure_base_type arg1.loc ~expect:Loc arg1.bt in
             let@ () = ensure_base_type arg2.loc ~expect:Loc arg2.bt in
             let vt = (Bool, op (it_of_arg arg1, it_of_arg arg2)) in
             return (rt_of_vt vt, local)
           in
           begin match memop with
           | M_PtrEq (asym1, asym2) -> 
              pointer_op eq_ asym1 asym2
           | M_PtrNe (asym1, asym2) -> 
              pointer_op ne_ asym1 asym2
           | M_PtrLt (asym1, asym2) -> 
              pointer_op ltPointer_ asym1 asym2
           | M_PtrGt (asym1, asym2) -> 
              pointer_op gtPointer_ asym1 asym2
           | M_PtrLe (asym1, asym2) -> 
              pointer_op lePointer_ asym1 asym2
           | M_PtrGe (asym1, asym2) -> 
              pointer_op gePointer_ asym1 asym2
           | M_Ptrdiff (act, asym1, asym2) -> 
              Debug_ocaml.error "todo: M_Ptrdiff"
           | M_IntFromPtr (act_from, act2_to, asym) ->
              let@ arg = arg_of_asym local asym in
              let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
              let vt = (Integer, pointerToIntegerCast_ (it_of_arg arg)) in
              return (rt_of_vt vt, local)            
           | M_PtrFromInt (act_from, act2_to, asym) ->
              let@ arg = arg_of_asym local asym in
              let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
              let vt = (Loc, integerToPointerCast_ (it_of_arg arg)) in
              return (rt_of_vt vt, local)            
           | M_PtrValidForDeref (act, asym) ->
              (* check *)
              let@ arg = arg_of_asym local asym in
              let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
              let local = unpack_resources local in
              let request = 
                RER.Predicate {
                    name = Ctype act.ct; 
                    pointer = it_of_arg arg;
                    iargs = [];
                    oargs = [BT.of_sct act.ct; BT.Bool];
                    unused = true;
                  }
              in
              let@ _ = resource_request loc (Access Deref) local request in
              let vt = (Bool, aligned_ (it_of_arg arg, act.ct)) in
              return (rt_of_vt vt, local)
           | M_PtrWellAligned (act, asym) ->
              let@ arg = arg_of_asym local asym in
              let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
              let vt = (Bool, aligned_ (it_of_arg arg, act.ct)) in
              return (rt_of_vt vt, local)
           | M_PtrArrayShift (asym1, act, asym2) ->
              let@ vt = infer_array_shift local asym1 act.ct asym2 in
              return (rt_of_vt vt, local)
           | M_Memcpy _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
              Debug_ocaml.error "todo: M_Memcpy"
           | M_Memcmp _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
              Debug_ocaml.error "todo: M_Memcmp"
           | M_Realloc _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
              Debug_ocaml.error "todo: M_Realloc"
           | M_Va_start _ (* (asym 'bty * asym 'bty) *) ->
              Debug_ocaml.error "todo: M_Va_start"
           | M_Va_copy _ (* (asym 'bty) *) ->
              Debug_ocaml.error "todo: M_Va_copy"
           | M_Va_arg _ (* (asym 'bty * actype 'bty) *) ->
              Debug_ocaml.error "todo: M_Va_arg"
           | M_Va_end _ (* (asym 'bty) *) ->
              Debug_ocaml.error "todo: M_Va_end"
           end
        | M_Eaction (M_Paction (_pol, M_Action (aloc, action_))) ->
           let local = unpack_resources local in
           begin match action_ with
           | M_Create (asym, act, _prefix) -> 
              let@ arg = arg_of_asym local asym in
              let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
              let ret = Sym.fresh () in
              let value_s, value_t = IT.fresh (BT.of_sct act.ct) in
              let resource = 
                RE.Predicate {
                    name = Ctype act.ct; 
                    pointer = sym_ (ret, Loc);
                    iargs = [];
                    oargs = [value_t; (bool_ false)];
                    unused = true;
                  }
              in
              let rt = 
                RT.Computational ((ret, Loc), 
                LRT.Constraint (t_ (representable_ (Sctypes.pointer_sct act.ct, sym_ (ret, Loc))), 
                LRT.Constraint (t_ (alignedI_ ~align:(it_of_arg arg) ~t:(sym_ (ret, Loc))), 
                LRT.Logical ((value_s, BT.of_sct act.ct),
                LRT.Resource (resource, LRT.I)))))
              in
              return (rt, local)
           | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
              Debug_ocaml.error "todo: CreateReadOnly"
           | M_Alloc (ct, sym, _prefix) -> 
              Debug_ocaml.error "todo: Alloc"
           | M_Kill (M_Dynamic, asym) -> 
              Debug_ocaml.error "todo: free"
           | M_Kill (M_Static ct, asym) -> 
              let@ arg = arg_of_asym local asym in
              let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
              let local = unpack_resources_for local (it_of_arg arg) in
              let@ (_, local) = 
                resource_request loc (Access Kill) local 
                  (RER.Predicate {
                       name = Ctype ct;
                       pointer = it_of_arg arg;
                       iargs = [];
                       oargs = [BT.of_sct ct; BT.Bool];
                       unused = true;
                     }
                  )
              in
              let rt = RT.Computational ((Sym.fresh (), Unit), I) in
              return (rt, local)
           | M_Store (_is_locking, act, pasym, vasym, mo) -> 
              let@ parg = arg_of_asym local pasym in
              let@ varg = arg_of_asym local vasym in
              let@ () = ensure_base_type loc ~expect:(BT.of_sct act.ct) varg.bt in
              let@ () = ensure_base_type loc ~expect:Loc parg.bt in
              (* The generated Core program will in most cases before this
                 already have checked whether the store value is
                 representable and done the right thing. Pointers, as I
                 understand, are an exception. *)
              let@ () = 
                let in_range_lc = representable_ (act.ct, it_of_arg varg) in
                if Solver.holds local (t_ in_range_lc) then return () else 
                  let (constr,state) = 
                    Explain.unsatisfied_constraint names local (t_ in_range_lc)
                  in
                  fail loc (Unsat_constraint {constr; state; hint = Some !^"write value unrepresentable"})
              in
              let local = unpack_resources_for local (it_of_arg parg) in
              let@ (_, local) = 
                resource_request loc (Access (Store None)) local 
                  (RER.Predicate {
                       name = Ctype act.ct; 
                       pointer = it_of_arg parg;
                       iargs = [];
                       oargs = [BT.of_sct act.ct; BT.Bool];
                       unused = true;
                  })
              in
              let resource = 
                RE.Predicate {
                    name = Ctype act.ct;
                    pointer = it_of_arg parg;
                    iargs = [];
                    oargs = [(it_of_arg varg); (bool_ true)];
                    unused = true;
                  }
              in
              let rt = RT.Computational ((Sym.fresh (), Unit), Resource (resource, LRT.I)) in
              return (rt, local)
           | M_Load (act, pasym, _mo) -> 
              let@ parg = arg_of_asym local pasym in
              let@ () = ensure_base_type parg.loc ~expect:Loc parg.bt in
              let local = unpack_resources_for local (it_of_arg parg) in
              let@ (predicate, _) = 
                predicate_request loc (Access (Load None)) local 
                  { name = Ctype act.ct ;
                    pointer = it_of_arg parg;
                    iargs = [];
                    oargs = [BT.of_sct act.ct ; BT.Bool];
                    unused = true;
                  }
              in
              let value, init = List.hd predicate.oargs, List.hd (List.tl predicate.oargs) in
              let@ () = 
                if Solver.holds local (t_ init) then return () else
                 let state = Explain.state names local in
                 fail loc (Uninitialised_read {is_member = None; state})
              in
              let ret = Sym.fresh () in
              let constr = def_ ret value in
              let rt = RT.Computational ((ret, IT.bt value), 
                       Constraint (t_ constr, LRT.I)) 
              in
              return (rt, local)
           | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) -> 
              Debug_ocaml.error "todo: RMW"
           | M_Fence mo -> 
              Debug_ocaml.error "todo: Fence"
           | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) -> 
              Debug_ocaml.error "todo: CompareExchangeStrong"
           | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) -> 
              Debug_ocaml.error "todo: CompareExchangeWeak"
           | M_LinuxFence mo -> 
              Debug_ocaml.error "todo: LinuxFemce"
           | M_LinuxLoad (ct, sym1, mo) -> 
              Debug_ocaml.error "todo: LinuxLoad"
           | M_LinuxStore (ct, sym1, sym2, mo) -> 
              Debug_ocaml.error "todo: LinuxStore"
           | M_LinuxRMW (ct, sym1, sym2, mo) -> 
              Debug_ocaml.error "todo: LinuxRMW"
           end
        | M_Eskip -> 
           let rt = RT.Computational ((Sym.fresh (), Unit), I) in
           return (rt, local)
        | M_Eccall (_ctype, afsym, asyms) ->
           let local = unpack_resources local in
           let@ args = args_of_asyms local asyms in
           let@ (_loc, ft) = match Global.get_fun_decl G.global afsym.sym with
             | Some (loc, ft) -> return (loc, ft)
             | None -> fail loc (Missing_function afsym.sym)
           in
           calltype_ft loc local args ft
        | M_Eproc (fname, asyms) ->
           let local = unpack_resources local in
           let@ decl_typ = match fname with
             | CF.Core.Impl impl -> 
                return (Global.get_impl_fun_decl G.global impl)
             | CF.Core.Sym sym ->
                match Global.get_fun_decl G.global sym with
                | Some (loc, ft) -> return ft
                | None -> fail loc (Missing_function sym)
           in
           let@ args = args_of_asyms local asyms in
           calltype_ft loc local args decl_typ
      in
      debug 3 (lazy (RT.pp (fst result)));
      return result

    (* check_expr: type checking for impure epressions; type checks `e`
       against `typ`, which is either a return type or `False`; returns
       either an updated environment, or `False` in case of Goto *)
    let rec check_texpr (local, labels) (e : 'bty mu_texpr) (typ : RT.t orFalse) 
            : (unit, type_error) m = 

      let (M_TExpr (loc, _annots, e_)) = e in
      debug 3 (lazy (action "checking expression"));
      debug 3 (lazy (item "expr" (group (pp_texpr e))));
      debug 3 (lazy (item "type" (pp_or_false RT.pp typ)));
      debug 3 (lazy (item "ctxt" (L.pp local)));
      let@ result = match e_ with
        | M_Eif (casym, e1, e2) ->
           let@ carg = arg_of_asym local casym in
           let@ () = ensure_base_type carg.loc ~expect:Bool carg.bt in
           ListM.iterM (fun (lc, e) ->
               let local = add_c (t_ lc) local in
               if Solver.is_inconsistent local then return ()
               else check_texpr (local, labels) e typ 
             ) [(it_of_arg carg, e1); (not_ (it_of_arg carg), e2)]
        | M_Ebound (_, e) ->
           check_texpr (local, labels) e typ 
        | M_End _ ->
           Debug_ocaml.error "todo: End"
        | M_Ecase (asym, pats_es) ->
           let@ arg = arg_of_asym local asym in
           ListM.iterM (fun (pat, pe) ->
               let@ delta = pattern_match (arg.lname, arg.bt) pat in
               let local = delta ++ local in
               if Solver.is_inconsistent local then return ()
               else check_texpr (local, labels) e typ
             ) pats_es
        | M_Elet (p, e1, e2) ->
           let@ (rt, local) = infer_pexpr local e1 in
           let@ delta = match p with 
             | M_Symbol sym -> return (bind sym rt)
             | M_Pat pat -> pattern_match_rt pat rt
           in
           check_texpr (delta ++ local, labels) e2 typ
        | M_Ewseq (pat, e1, e2) ->
           let@ (rt, local) = infer_expr (local, labels) e1 in
           let@ delta = pattern_match_rt pat rt in
           check_texpr (delta ++ local, labels) e2 typ
        | M_Esseq (pat, e1, e2) ->
           let@ (rt, local) = infer_expr (local, labels) e1 in
           let@ delta = match pat with
             | M_Symbol sym -> return (bind sym rt)
             | M_Pat pat -> pattern_match_rt pat rt
           in
           check_texpr (delta ++ local, labels) e2 typ
        | M_Edone asym ->
           begin match typ with
           | Normal typ ->
              let@ arg = arg_of_asym local asym in
              let@ local = subtype loc local arg typ in
              all_empty loc [] local
           | False ->
              let err = 
                "This expression returns but is expected "^
                  "to have non-return type."
              in
              fail loc (Generic !^err)
           end
        | M_Eundef (_loc, undef) ->
           let expl = Explain.undefined_behaviour names local in
           fail loc (Undefined_behaviour (undef, expl))
        | M_Erun (label_sym, asyms) ->
           let local = unpack_resources local in
           let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
             | None -> fail loc (Generic (!^"undefined label" ^/^ Sym.pp label_sym))
             | Some (lt,lkind) -> return (lt,lkind)
           in
           let@ args = args_of_asyms local asyms in
           let extra_names = match args, lkind with
             | [arg], Return -> [arg.lname, Ast.Var {label = None; v = "return"}]
             | _ -> []
           in
           let@ (False, local) = calltype_lt loc extra_names local args (lt,lkind) in
           let@ () = all_empty loc extra_names local in
           return ()

      in
      return result


  end (* Checker *)



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
  module CBF (I : AT.I_Sig) = struct
    module T = AT.Make(I)
    let check_and_bind_arguments loc arguments (function_typ : T.t) = 
      let rec check acc_substs local pure_local args (ftyp : T.t) =
        match args, ftyp with
        | ((aname,abt) :: args), (T.Computational ((lname, sbt), ftyp))
             when BT.equal abt sbt ->
           let new_lname = Sym.fresh () in
           let subst = {before=lname;after=new_lname} in
           let ftyp' = T.subst_var subst ftyp in
           let local = add_l new_lname abt local in
           let local = add_a aname (abt,new_lname) local in
           let pure_local = add_l new_lname abt pure_local in
           let pure_local = add_a aname (abt,new_lname) pure_local in
           check (acc_substs@[subst]) local pure_local args ftyp'
        | ((aname, abt) :: args), (T.Computational ((sname, sbt), ftyp)) ->
           fail loc (Mismatch {has = abt; expect = sbt})
        | [], (T.Computational (_,_))
        | (_ :: _), (T.I _) ->
           let expect = T.count_computational function_typ in
           let has = List.length arguments in
           fail loc (Number_arguments {expect; has})
        | args, (T.Logical ((sname, sls), ftyp)) ->
           let new_lname = Sym.fresh_same sname in
           let subst = {before = sname; after = new_lname} in
           let ftyp' = T.subst_var subst ftyp in
           let local = add_l new_lname sls local in
           let pure_local = add_l new_lname sls pure_local in
           check (acc_substs@[subst]) local pure_local args ftyp'
        | args, (T.Resource (re, ftyp)) ->
           check acc_substs (add_r re local) pure_local args ftyp
        | args, (T.Constraint (lc, ftyp)) ->
           let local = add_c lc local in
           let pure_local = add_c lc pure_local in
           check acc_substs local pure_local args ftyp
        | [], (T.I rt) ->
           return (rt, local, pure_local, acc_substs)
      in
      check [] L.empty L.empty arguments function_typ
  end

  module CBF_FT = CBF(ReturnTypes)
  module CBF_LT = CBF(False)

  
  let check_initial_environment_consistent loc info local = 
    match Solver.is_inconsistent local, info with
    | true, `Label -> 
       fail loc (Generic (!^"this label makes inconsistent assumptions"))
    | true, `Fun -> 
       fail loc (Generic (!^"this function makes inconsistent assumptions"))
    | _ -> 
       return ()


  (* check_function: type check a (pure) function *)
  let check_function 
        (loc : loc) 
        (local : Local.t)
        mapping (info : string) 
        (arguments : (Sym.t * BT.t) list) (rbt : BT.t) 
        (body : 'bty mu_tpexpr) (function_typ : FT.t) : (unit, type_error) m =
    debug 2 (lazy (headline ("checking function " ^ info)));
    let@ (rt, delta, _, substs) = 
      CBF_FT.check_and_bind_arguments loc arguments function_typ 
    in
    let local = delta ++ local in
    let@ () = check_initial_environment_consistent loc `Fun local in
    (* rbt consistency *)
    let@ () = 
      let Computational ((sname, sbt), t) = rt in
      ensure_base_type loc ~expect:sbt rbt
    in
    let@ local_or_false =
      let names = 
        Explain.naming_substs substs 
          (Explain.naming_of_mapping mapping)
      in
      let module C = Checker(struct let names = names end) in
      C.check_tpexpr local body rt 
    in
    return ()


  (* check_procedure: type check an (impure) procedure *)
  let check_procedure 
        (loc : loc) (local : Local.t)
        mapping (fsym : Sym.t)
        (arguments : (Sym.t * BT.t) list) (rbt : BT.t) 
        (body : 'bty mu_texpr) (function_typ : FT.t) 
        (label_defs : 'bty mu_label_defs) : (unit, type_error) m =
    print stdout (!^("checking function " ^ Sym.pp_string fsym));
    debug 2 (lazy (headline ("checking procedure " ^ Sym.pp_string fsym)));
    debug 2 (lazy (item "type" (FT.pp function_typ)));

    (* check and bind the function arguments *)
    let@ (rt, delta, pure_delta, substs) = 
      CBF_FT.check_and_bind_arguments loc arguments function_typ 
    in
    (* prepare name mapping *)
    let fnames = 
      Explain.naming_substs substs (Explain.naming_of_mapping mapping) 
    in

    (* check that the function does not make inconsistent assumptions *)
    let@ () = check_initial_environment_consistent loc `Fun (delta ++ local) in

    (* rbt consistency *)
    let@ () = 
      let Computational ((sname, sbt), t) = rt in
      ensure_base_type loc ~expect:sbt rbt
    in

    (* apply argument substitutions to label types *)
    let label_defs = 
      Pmap.map (fun def ->
          match def with
          | M_Return (loc, lt) -> 
             M_Return (loc, LT.subst_vars substs lt)
          | M_Label (loc, lt, args, body, annots, mapping) -> 
             M_Label (loc, LT.subst_vars substs lt, args, body, annots, mapping)
        ) label_defs 
    in

    (* check well-typedness of labels and record their types *)
    let@ labels = 
      PmapM.foldM (fun sym def acc ->
          match def with
          | M_Return (loc, lt) ->
             let@ () = WT.WLT.welltyped loc fnames (pure_delta ++ local) lt in
             return (SymMap.add sym (lt, Return) acc)
          | M_Label (loc, lt, _, _, annots, mapping) -> 
             let label_kind = match CF.Annot.get_label_annot annots with
               | Some (LAloop_body loop_id) -> Loop
               | Some (LAloop_continue loop_id) -> Loop
               | _ -> Other
             in
             let@ () = WT.WLT.welltyped loc fnames (pure_delta ++ local) lt in
             return (SymMap.add sym (lt, label_kind) acc)
        ) label_defs SymMap.empty 
    in

    (* check each label *)
    let check_label lsym def () = 
      match def with
      | M_Return (loc, lt) ->
         return ()
      | M_Label (loc, lt, args, body, annots, mapping) ->
         debug 2 (lazy (headline ("checking label " ^ Sym.pp_string lsym)));
         debug 2 (lazy (item "type" (LT.pp lt)));
         let@ (rt, delta_label, _, lsubsts) = 
           CBF_LT.check_and_bind_arguments loc args lt 
         in
         let@ () = check_initial_environment_consistent loc 
                     `Label (delta_label ++ pure_delta ++ local) in
         let@ local_or_false = 
           let names = 
             Explain.naming_substs (lsubsts @ substs)
               (Explain.naming_of_mapping mapping)  
           in
           let module C = Checker(struct let names = names end) in
           C.check_texpr (delta_label ++ pure_delta ++ local, labels) body False
         in
         return ()
    in
    let@ () = PmapM.foldM check_label label_defs () in

    (* check the function body *)
    debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
    let@ local_or_false = 
      let module C = Checker(struct let names = fnames end) in
      C.check_texpr (delta ++ local, labels) body (Normal rt)
    in
    return ()


end
 





(* TODO: do this when we've added the machinery for user-defined predicates *)
let check_predicate_definition def = return ()


let check_and_record_tagDefs (global: Global.t) tagDefs = 
  let open Memory in
  PmapM.foldM (fun tag def (global: Global.t) ->
      match def with
      | M_UnionDef _ -> 
         unsupported Loc.unknown !^"todo: union types"
      | M_StructDef layout -> 
         let@ () =
           ListM.iterM (fun piece ->
               match piece.member_or_padding with
               | Some (_, Sctypes.Sctype (_, Sctypes.Struct sym2)) ->
                  begin match SymMap.find_opt sym2 global.struct_decls with
                  | Some _ -> return ()
                  | None -> fail Loc.unknown (Missing_struct sym2)
                  end
               | _ -> return ()
             ) layout
         in
         let struct_decls = SymMap.add tag layout global.struct_decls in
         return { global with struct_decls }
    ) tagDefs global




let record_funinfo (global, local) funinfo =
  let module WT = WellTyped.Make(struct let global = global end) in
  let module Explain = Explain.Make(struct let global = global end) in
  PmapM.foldM
    (fun fsym (M_funinfo (loc, Attrs attrs, ftyp, has_proto, mapping)) 
         (global, local) ->
      let () = debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym))) in
      let () = debug 2 (lazy (item "type" (FT.pp ftyp))) in
      let names = Explain.naming_of_mapping mapping in
      let@ () = WT.WFT.welltyped loc names local ftyp in
      let fun_decls = SymMap.add fsym (loc, ftyp) global.Global.fun_decls in
      let local = 
        let voidstar = Sctypes.pointer_sct (Sctype ([], Void)) in
        let lc = representable_ (voidstar, sym_ (fsym, Loc)) in
        Local.add_c (t_ lc) local
      in
      return ({global with fun_decls}, local)
    ) funinfo (global, local)


let print_initial_environment genv = 
  debug 1 (lazy (headline "initial environment"));
  debug 1 (lazy (Global.pp genv));
  return ()


let check_functions (global, local) fns =
  let module C = Make(struct let global = global end) in
  PmapM.iterM (fun fsym fn -> 
      match fn with
      | M_Fun (rbt, args, body) ->
         let@ (loc, ftyp) = match Global.get_fun_decl global fsym with
           | Some t -> return t
           | None -> fail Loc.unknown (TypeErrors.Missing_function fsym)
         in
         C.check_function loc local Mapping.empty 
           (Sym.pp_string fsym) args rbt body ftyp
      | M_Proc (loc, rbt, args, body, labels, mapping) ->
         let@ (loc', ftyp) = match Global.get_fun_decl global fsym with
           | Some t -> return t
           | None -> fail loc (TypeErrors.Missing_function fsym)
         in
         C.check_procedure loc' local mapping 
           fsym args rbt body ftyp labels
      | M_ProcDecl _
      | M_BuiltinDecl _ -> 
         return ()
    ) fns



let check_and_record_impls (global, local) impls = 
  let open Global in
  PmapM.foldM (fun impl impl_decl global ->
      let module G = struct let global = global end in
      let module C = Make(G) in
      let module WT = WellTyped.Make(G) in
      let descr = CF.Implementation.string_of_implementation_constant impl in
      match impl_decl with
      | M_Def (rt, rbt, pexpr) -> 
         let@ () = WT.WRT.welltyped Loc.unknown [] local rt in
         let@ () = 
           C.check_function Loc.unknown local
             [] descr [] rbt pexpr (FT.I rt) in
         let global = 
           { global with impl_constants = 
                           ImplMap.add impl rt global.impl_constants}
         in
         return global
      | M_IFun (ft, rbt, args, pexpr) ->
         let@ () = WT.WFT.welltyped Loc.unknown [] local ft in
         let@ () = 
           C.check_function Loc.unknown local [] 
             (CF.Implementation.string_of_implementation_constant impl)
             args rbt pexpr ft
         in
         let impl_fun_decls = ImplMap.add impl ft global.impl_fun_decls in
         return { global with impl_fun_decls }
    ) impls global




(* TODO: check the expressions *)
let record_globals local globs = 
  let open Global in
  ListM.fold_leftM (fun local (sym, def) ->
      match def with
      | M_GlobalDef (lsym, (_, ct), _)
      | M_GlobalDecl (lsym, (_, ct)) ->
         let bt = Loc in
         let local = Local.add_l lsym bt local in
         let local = Local.add_a sym (bt, lsym) local in
         let local = Local.add_c (t_ (IT.good_pointer (sym_ (lsym, bt)) ct)) local in
         let global = SymSet.add lsym local.global in
         return {local with global}
    ) local globs







let check mu_file = 
  let open Global in
  let global = Global.empty in
  let local = Local.empty in
  let@ global = check_and_record_impls (global, local) mu_file.mu_impl in
  let@ global = check_and_record_tagDefs global mu_file.mu_tagDefs in
  let@ local = record_globals local mu_file.mu_globs in
  let@ global = 
    ListM.fold_leftM (fun global (name,def) -> 
        let module WT = WellTyped.Make(struct let global = global end) in
        let@ () = WT.WPD.welltyped [] local def in
        let resource_predicates =
          StringMap.add name def global.resource_predicates in
        return {global with resource_predicates}
      ) global mu_file.mu_predicates
  in
  (* has to be after globals: the functions can refer to globals *)
  let@ (global, local) = record_funinfo (global, local) mu_file.mu_funinfo in
  let@ () = print_initial_environment global in
  let@ result = check_functions (global, local) mu_file.mu_stdlib in
  let@ result = check_functions (global, local) mu_file.mu_funs in
  return result





(* TODO: 
   - when resources are missing because of BT mismatches, report that correctly
   - be more careful about which counter-model to use in Explain
   - rem_t vs rem_f
   - check resource definition well-formedness
   - check globals with expressions
 *)
