open Pp
open Resultat
module CF=Cerb_frontend
open CF.Mucore
open ReturnTypes


module SymMap = Map.Make(Sym)
module RE = Resources
module LT = ArgumentTypes.Make(False)
module FT = ArgumentTypes.Make(ReturnTypes)





let record_tagDefs (global: Global.t) tagDefs = 
  PmapM.foldM (fun sym def (global: Global.t) ->
      match def with
      | M_UnionDef _ -> 
         fail Loc.unknown (TypeErrors.Unsupported !^"todo: union types")
      | M_StructDef (_ct, decl) -> 
         let struct_decls = SymMap.add sym decl global.struct_decls in
         return { global with struct_decls }
    ) tagDefs global


let record_funinfo global funinfo =
  let module WT = WellTyped.Make(struct let global = global end) in
  let module Explain = Explain.Make(struct let global = global end) in
  PmapM.foldM
    (fun fsym (M_funinfo (loc, Attrs attrs, ftyp, is_variadic, has_proto, mapping)) global ->
      if is_variadic then 
        let err = !^"Variadic function" ^^^ Sym.pp fsym ^^^ !^"unsupported" in
        fail loc (TypeErrors.Unsupported err)
      else
        let () = debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym))) in
        let () = debug 2 (lazy (item "type" (FT.pp ftyp))) in
        let names =Explain.naming_of_mapping mapping in
        let@ () = WT.WFT.welltyped loc names WT.L.empty ftyp in
        let fun_decls = SymMap.add fsym (loc, ftyp) global.Global.fun_decls in
        return {global with fun_decls}
    ) funinfo global


(* check the types? *)
let record_impl genv impls = 
  let open Global in
  Pmap.fold (fun impl impl_decl genv ->
      match impl_decl with
      | M_Def (bt, _p) -> 
         { genv with impl_constants = ImplMap.add impl bt genv.impl_constants}
      | M_IFun (rbt, args, _body) ->
         let args_ts = List.map FT.mComputational args in
         let rt = FT.I (Computational ((Sym.fresh (), rbt), I)) in
         let ftyp = (Tools.comps args_ts) rt in
         let impl_fun_decls = ImplMap.add impl ftyp genv.impl_fun_decls in
         { genv with impl_fun_decls }
    ) impls genv


let print_initial_environment genv = 
  debug 1 (lazy (headline "initial environment"));
  debug 1 (lazy (Global.pp genv));
  return ()


let process_functions genv fns =
  let module C = Check.Make(struct let global = genv end) in
  PmapM.iterM (fun fsym fn -> 
      match fn with
      | M_Fun (rbt, args, body) ->
         let@ (loc, ftyp) = match Global.get_fun_decl genv fsym with
           | Some t -> return t
           | None -> fail Loc.unknown (TypeErrors.Missing_function fsym)
         in
         C.check_function loc Mapping.empty fsym args rbt body ftyp
      | M_Proc (loc, rbt, args, body, labels, mapping) ->
         let@ (loc', ftyp) = match Global.get_fun_decl genv fsym with
           | Some t -> return t
           | None -> fail loc (TypeErrors.Missing_function fsym)
         in
         C.check_procedure loc' mapping fsym args rbt body ftyp labels
      | M_ProcDecl _
      | M_BuiltinDecl _ -> 
         return ()
    ) fns






let process mu_file =
  let@ mu_file = PreProcess.retype_file mu_file in
  let solver_context = SolverInitialContext.context in
  let global = Global.empty solver_context in
  let stdlib_funs = SymSet.of_list (Pset.elements (Pmap.domain mu_file.mu_stdlib)) in
  let global = { global with stdlib_funs } in
  let global = record_impl global mu_file.mu_impl in
  let@ global = record_tagDefs global mu_file.mu_tagDefs in
  let@ global = 
    let open Global in
    let open PreProcess in
    ListM.fold_leftM (fun global (sym, def) ->
        match def with
        | M_GlobalDef (lsym, (_, cti), e) ->
           (* let module C1 = Check.Make(struct let global = global end) in
            * let module C2 = C1.Checker(struct let names = Mapping.empty end) in
            * let@ local_or_false = 
            *   C2.check_expr_pop ~print:true C1.L.empty (C1.L.empty, SymMap.empty) 
            *     e (Check.Fallible.Normal rt)
            * in            *)
           let logical = (lsym, LS.Base Loc) :: global.logical in
           let computational = (sym, (lsym, BT.Loc)) :: global.computational in
           let it = IT.good_pointer lsym cti.ct in
           let sc = SolverConstraints.of_index_term global it in
           let constraints = (LC.LC it,sc) :: global.constraints in
           return {global with logical; computational; constraints}
        | M_GlobalDecl (lsym, (_, cti)) ->
           let logical = (lsym, LS.Base Loc) :: global.logical in
           let computational = (sym, (lsym, BT.Loc)) :: global.computational in
           let it = IT.good_pointer lsym cti.ct in
           let sc = SolverConstraints.of_index_term global it in
           let constraints = (LC.LC it,sc) :: global.constraints in
           return {global with logical; computational; constraints}
      ) global mu_file.mu_globs
  in
  let@ global = record_funinfo global mu_file.mu_funinfo in
  let@ () = print_initial_environment global in
  let@ result = process_functions global mu_file.mu_funs in

  return result



