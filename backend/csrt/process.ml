open Pp
open Result
module CF=Cerb_frontend
open CF.Mucore
open Check
open TypeErrors
open ReturnTypes
open BaseTypes

module RE = Resources
module LT = ArgumentTypes.Make(NoReturn)
module FT = ArgumentTypes.Make(ReturnTypes)





let record_tagDefs (global: Global.t) tagDefs = 
  PmapM.foldM (fun sym def (global: Global.t) ->
      match def with
      | M_UnionDef _ -> fail Loc.unknown (Unsupported !^"todo: union types")
      | M_StructDef decl -> 
         let struct_decls = SymMap.add sym decl global.struct_decls in
         return { global with struct_decls }
    ) tagDefs global


let record_funinfo global funinfo =
  PmapM.foldM
    (fun fsym (M_funinfo (loc,attrs,ftyp,is_variadic,has_proto)) global ->
      if is_variadic then fail loc (Variadic_function fsym) else
        let fun_decls = SymMap.add fsym (loc,ftyp) global.Global.fun_decls in
        return {global with fun_decls}
    ) funinfo global


(* check the types? *)
let record_impl genv impls = 
  let open Global in
  Pmap.fold (fun impl impl_decl genv ->
      match impl_decl with
      | M_Def (bt, _p) -> 
         { genv with impl_constants = ImplMap.add impl bt genv.impl_constants}
      | M_IFun (bt, args, _body) ->
         let args_ts = List.map (fun (sym,a_bt) -> FT.mcomputational sym a_bt) args in
         let ftyp = (Tools.comps args_ts) (FT.I (Computational ((Sym.fresh (), bt), I))) in
         { genv with impl_fun_decls = ImplMap.add impl ftyp genv.impl_fun_decls }
    ) impls genv


let print_initial_environment genv = 
  let* () = dprintM 1 (h1 "initial environment") in
  let* () = dprintM 1 (Global.pp genv) in
  return ()


let process_functions genv fns =
  PmapM.iterM (fun fsym fn -> 
      match fn with
      | M_Fun (rbt, args, body) ->
         let* (loc,ftyp) = Global.get_fun_decl Loc.unknown genv fsym in
         check_function loc genv fsym args rbt body ftyp
      | M_Proc (loc, rbt, args, body, labels) ->
         let* (loc,ftyp) = Global.get_fun_decl loc genv fsym in
         check_procedure loc genv fsym args rbt labels body ftyp
      | M_ProcDecl _
      | M_BuiltinDecl _ -> 
         return ()
    ) fns

(* let pp_fun_map_decl funinfo = 
 *   let pp = CF.Pp_core.All.pp_funinfo_with_attributes funinfo in
 *   print_string (plain pp) *)



let process mu_file =
  let* mu_file : (FT.t, LT.t, (BT.t * RE.size), BT.t, Global.struct_decl, unit, 'bty) mu_file =
    PreProcess.retype_file Loc.unknown mu_file in
  (* pp_fun_map_decl mu_file.mu_funinfo; *)
  let global = Global.empty in
  let* global = record_tagDefs global mu_file.mu_tagDefs in
  let global = record_impl global mu_file.mu_impl in
  let* global = record_funinfo global mu_file.mu_funinfo in
  let* () = print_initial_environment global in
  process_functions global mu_file.mu_funs


let process_and_report mu_file = 
  if !debug_level > 0 then Printexc.record_backtrace true else ();
  match process mu_file with
  | Ok () -> ()
  | Error (loc,err) -> Pp.error (TypeErrors.pp loc err); exit 1
