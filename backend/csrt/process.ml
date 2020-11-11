open Pp
open Resultat
module CF=Cerb_frontend
open CF.Mucore
open Check
open TypeErrors
open ReturnTypes


module SymMap = Map.Make(Sym)
module RE = Resources
module LT = ArgumentTypes.Make(False)
module FT = ArgumentTypes.Make(ReturnTypes)





let record_tagDefs (global: Global.t) tagDefs = 
  PmapM.foldM (fun sym def (global: Global.t) ->
      match def with
      | M_UnionDef _ -> 
         fail Loc.unknown (Unsupported !^"todo: union types")
      | M_StructDef (_ct, decl) -> 
         let struct_decls = SymMap.add sym decl global.struct_decls in
         return { global with struct_decls }
    ) tagDefs global


let record_funinfo global funinfo =
  PmapM.foldM
    (fun fsym (M_funinfo (loc, attrs, ftyp, is_variadic, has_proto)) global ->
      let loc' = Loc.update Loc.unknown loc in
      if is_variadic then 
        let err = !^"Variadic function" ^^^ Sym.pp fsym ^^^ !^"unsupported" in
        fail loc' (Unsupported err)
      else
        let () = debug 2 (lazy (item "recording function type" (FT.pp ftyp))) in
        (* let* () = WellTyped.WFT.welltyped loc {local = L.empty; global} ftyp in *)
        let fun_decls = SymMap.add fsym (loc', ftyp) global.Global.fun_decls in
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
  PmapM.iterM (fun fsym fn -> 
      match fn with
      | M_Fun (rbt, args, body) ->
         let* (loc,ftyp) = Global.get_fun_decl Loc.unknown genv fsym in
         check_function loc genv fsym args rbt body ftyp
      | M_Proc (loc, rbt, args, body, labels) ->
         let loc' = Loc.update Loc.unknown loc in
         let* (loc,ftyp) = Global.get_fun_decl loc' genv fsym in
         check_procedure loc genv fsym args rbt body ftyp labels
      | M_ProcDecl _
      | M_BuiltinDecl _ -> 
         return ()
    ) fns



let process mu_file =
  let* mu_file = PreProcess.retype_file Loc.unknown mu_file in
  let global = Global.empty in
  let* global = record_tagDefs global mu_file.mu_tagDefs in
  let global = record_impl global mu_file.mu_impl in
  let* global = record_funinfo global mu_file.mu_funinfo in
  let stdlib_funs = SymSet.of_list (Pset.elements (Pmap.domain mu_file.mu_stdlib)) in
  let global = { global with stdlib_funs } in
  let* () = print_initial_environment global in
  process_functions global mu_file.mu_funs


let process_and_report mu_file = 
  if !print_level > 0 then Printexc.record_backtrace true else ();
  match process mu_file with
  | Ok () -> ()
  | Error (loc,ostacktrace,err) -> 
     TypeErrors.type_error loc ostacktrace err
