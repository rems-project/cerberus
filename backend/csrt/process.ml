open Pp
open Except
module CF=Cerb_frontend
open CF.Mucore
open Check
open TypeErrors
open FunctionTypes
open ReturnTypes
open Subst






let record_functions genv funinfo : (Global.t, Locations.t * 'e) Except.t  = 
  pmap_foldM 
    (fun fsym ((loc,attrs,ret_ctype,args,is_variadic,_has_proto) : CF.Mucore.mu_funinfo) genv ->
      if is_variadic 
      then fail loc (Variadic_function fsym) 
      else
        let* ftyp = Conversions.make_fun_spec loc genv attrs args ret_ctype in
        return { genv with fun_decls = SymMap.add fsym (loc,ftyp) genv.fun_decls }
    ) funinfo genv


(* check the types? *)
let record_impl genv impls = 
  let open Global in
  pmap_foldM 
    (fun impl impl_decl genv ->
      match impl_decl with
      | M_Def (bt, _p) -> 
         let* bt = Conversions.bt_of_core_base_type Loc.unknown bt in
         return { genv with impl_constants = ImplMap.add impl bt genv.impl_constants}
      | M_IFun (bt, args, _body) ->
         let* args_ts = 
           mapM (fun (sym,a_bt) -> 
               let* a_bt = Conversions.bt_of_core_base_type Loc.unknown a_bt in
               return (FT.mcomputational sym a_bt)) args
         in
         let* bt = Conversions.bt_of_core_base_type Loc.unknown bt in
         let ftyp = (Tools.comps args_ts) (Return (Computational (Sym.fresh (), bt, I))) in

         return { genv with impl_fun_decls = ImplMap.add impl ftyp genv.impl_fun_decls }
    ) impls genv


let struct_decl loc tag fields genv = 
  let open Sym in
  let open BaseTypes in

  let rec aux thisstruct loc (acc_members,acc_sopen,acc_sclosed,acc_cts) member ct =
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update loc annots in
    match ct_ with
    | Void -> 
       return ((member,Unit)::acc_members, 
               acc_sopen, 
               acc_sclosed, 
               (member,ct)::acc_cts)
    | Basic (Integer it) -> 
       let* lc1 = Conversions.integerType_constraint loc 
                    (Member (tag, S thisstruct, member)) it in
       let spec_name = fresh () in
       let* lc2 = Conversions.integerType_constraint loc (S spec_name) it in
       return ((member,Int)::acc_members, 
               Constraint (lc1,acc_sopen), 
               Constraint (lc1,acc_sclosed),
               (member,ct)::acc_cts)
    | Array (ct, _maybe_integer) -> 
       return ((member,Array)::acc_members, 
               acc_sopen, 
               acc_sclosed, 
               (member,ct):: acc_cts)
    | Pointer (_qualifiers, ct) -> 
       return ((member,Loc)::acc_members, 
               acc_sopen, 
               acc_sclosed, 
               (member,ct)::acc_cts)
    (* fix *)
    | Atomic ct -> 
       aux thisstruct loc (acc_members,acc_sopen,acc_sclosed,acc_cts) member ct
    | Struct tag2 -> 
       let* decl = Global.get_struct_decl loc genv (Tag tag2) in
       let sopen = 
         let subst = {s=decl.open_type.sbinder; 
                      swith=IT.Member (tag, S thisstruct, member)} in
         RT.subst_var_l subst decl.open_type.souter
       in
       let sclosed = 
         let subst = {s=decl.closed_type.sbinder; 
                      swith=IT.Member (tag, S thisstruct, member)} in
         RT.subst_var_l subst decl.closed_type.souter
       in
       return ((member, Struct (Tag tag2))::acc_members, 
               sopen@@acc_sopen, 
               sclosed@@acc_sclosed,
               (member, ct)::acc_cts)
    | Basic (Floating _) -> 
       fail loc (Unsupported !^"todo: union types")
    | Union sym -> 
       fail loc (Unsupported !^"todo: union types")
    | Function _ -> 
       fail loc (Unsupported !^"function pointers")
  in
  let thisstruct = fresh () in
  let* (raw,sopen,sclosed,ctypes) = 
    List.fold_right (fun (id, (_attributes, _qualifier, ct)) acc ->
        let* acc = acc in
        aux thisstruct loc acc (Member (Id.s id)) ct
      ) fields (return ([],I,I,[])) 
  in
  let open Global in
  let open_type = {sbinder = thisstruct; souter=sopen } in
  let closed_type = {sbinder = thisstruct; souter=sclosed } in
  return { raw; open_type; closed_type; ctypes }
  


let record_tagDef file sym def genv =
  match def with
  | CF.Ctype.UnionDef _ -> 
     fail Loc.unknown (Unsupported !^"todo: union types")
  | CF.Ctype.StructDef (fields, _) ->
     let* decl = struct_decl Loc.unknown (Tag sym) fields genv in
let genv = { genv with struct_decls = SymMap.add sym decl genv.struct_decls } in
     return genv


let record_tagDefs file genv tagDefs = 
  pmap_foldM (record_tagDef file) tagDefs genv



let print_initial_environment genv = 
  let* () = debug_print 1 (h1 "initial environment") in
  let* () = debug_print 1 (Global.pp genv) in
  return ()

let pp_fun_map_decl funinfo = 
  let pp = CF.Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (plain pp)


let process_functions genv fns =

  let convert_arg loc (name,mbt) = 
    let* bt = Conversions.bt_of_core_base_type loc mbt in
    return (name,bt)
  in

  pmap_iterM (fun fsym fn -> 
      match fn with
      | M_Fun (ret, args, body) ->
         let* (loc,ftyp) = Global.get_fun_decl Loc.unknown genv fsym in
         let* args = mapM (convert_arg loc) args in
         let* rbt = Conversions.bt_of_core_base_type Loc.unknown ret in
         check_function loc genv fsym args rbt (`PEXPR body) ftyp
      | M_Proc (loc, ret, args, body) ->
         let* (loc,ftyp) = Global.get_fun_decl loc genv fsym in
         let* args = mapM (convert_arg loc) args in
         let* rbt = Conversions.bt_of_core_base_type Loc.unknown ret in
         check_function loc genv fsym args rbt (`EXPR body) ftyp
      | M_ProcDecl _
      | M_BuiltinDecl _ -> 
         return ()
    ) fns





let process mu_file =
  pp_fun_map_decl mu_file.mu_funinfo;
  let genv = Global.empty in
  let* genv = record_tagDefs mu_file genv mu_file.mu_tagDefs in
  let* genv = record_functions genv mu_file.mu_funinfo in
  let* () = print_initial_environment genv in
  process_functions genv mu_file.mu_funs


let process_and_report core_file = 
  match process core_file with
  | Result () -> ()
  | Exception (loc,err) -> 
     let pped = TypeErrors.pp loc err in
     error pped
