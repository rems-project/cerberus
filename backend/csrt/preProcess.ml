(* open Pp *)
open Except
module CF=Cerb_frontend
module Symbol=CF.Symbol
module Loc=Locations
module RT=ReturnTypes
module FT=FunctionTypes
open CF.Mucore
open TypeErrors
open Pp

let retype_ctor loc = function
  | M_Cnil cbt -> 
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     return (M_Cnil bt)
  | M_Ccons -> return M_Ccons
  | M_Ctuple -> return M_Ctuple
  | M_Carray -> return M_Carray
  | M_CivCOMPL -> return M_CivCOMPL
  | M_CivAND -> return M_CivAND
  | M_CivOR -> return M_CivOR
  | M_CivXOR -> return M_CivXOR
  | M_Cspecified -> return M_Cspecified
  | M_Cfvfromint -> return M_Cfvfromint
  | M_Civfromfloat -> return M_Civfromfloat


let rec retype_pattern loc (M_Pattern (annots,pattern_)) =
  match pattern_ with
  | M_CaseBase (msym, cbt) -> 
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     return (M_Pattern (annots,M_CaseBase (msym,bt)))
  | M_CaseCtor (ctor, pats) ->
     let* ctor = retype_ctor loc ctor in
     let* pats = mapM (retype_pattern loc) pats in
     return (M_Pattern (annots,M_CaseCtor (ctor,pats)))

let retype_sym_or_pattern loc = function
  | M_Symbol s -> 
     return (M_Symbol s)
  | M_Pat pat -> 
     let* pat = retype_pattern loc pat in
     return (M_Pat pat)



let retype_object_value loc = function
  | M_OVinteger iv -> return (M_OVinteger iv)
  | M_OVfloating fv -> return (M_OVfloating fv)
  | M_OVpointer pv -> return (M_OVpointer pv)
  | M_OVarray asyms -> return (M_OVarray asyms)
  | M_OVstruct (s, members) ->
     let* members = 
       mapM (fun (id,ct,mv) ->
           let* bt = Conversions.bt_of_ctype loc ct in
           let* size = Memory.size_of_ctype loc ct in
           return (id,(bt,size),mv)
         ) members
     in
     return (M_OVstruct (s, members))
  | M_OVunion (s,id,mv) ->
     return (M_OVunion (s,id,mv))


let retype_loaded_value loc = function
  | M_LVspecified ov ->
     let* ov = retype_object_value loc ov in
     return (M_LVspecified ov)

let retype_value loc = function 
 | M_Vobject ov -> 
    let* ov = retype_object_value loc ov in
    return (M_Vobject ov)
 | M_Vloaded lv -> 
    let* lv = retype_loaded_value loc lv in
    return (M_Vloaded lv)
 | M_Vunit -> return (M_Vunit)
 | M_Vtrue -> return (M_Vtrue)
 | M_Vfalse -> return (M_Vfalse)
 (* | M_Vctype of ctype (\* C type as value *\) *)
 | M_Vlist (cbt,asyms) -> 
    let* bt = Conversions.bt_of_core_base_type loc cbt in
    return (M_Vlist (bt,asyms))
 | M_Vtuple asyms -> return (M_Vtuple asyms)

let rec retype_pexpr loc (M_Pexpr (annots,bty,pexpr_)) = 
  let loc = Loc.update loc annots in
  let* pexpr_ = match pexpr_ with
    | M_PEsym sym -> 
       return (M_PEsym sym)
    | M_PEimpl impl -> 
       return (M_PEimpl impl)
    | M_PEval v -> 
       let* v = retype_value loc v in
       return (M_PEval v)
    | M_PEconstrained cs -> 
       return (M_PEconstrained cs)
    | M_PEundef (loc,undef) -> 
       return (M_PEundef (loc,undef))
    | M_PEerror (err,asym) -> 
       return (M_PEerror (err,asym))
    | M_PEctor (ctor,asyms) -> 
       let* ctor = retype_ctor loc ctor in
       return (M_PEctor (ctor,asyms))
    | M_PEcase (asym,pats_pes) ->
       let* pats_pes = 
         mapM (fun (pat,pexpr) ->
             let* pat = retype_pattern loc pat in
             let* pexpr = retype_pexpr loc pexpr in
             return (pat,pexpr)
           ) pats_pes
       in
       return (M_PEcase (asym,pats_pes))
    | M_PEarray_shift (asym,ct,asym') ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_PEarray_shift (asym,(bt,size),asym'))
    | M_PEmember_shift (asym,sym,id) ->
       return (M_PEmember_shift (asym,sym,id))
    | M_PEnot asym -> 
       return (M_PEnot asym)
    | M_PEop (op,asym1,asym2) ->
       return (M_PEop (op,asym1,asym2))
    | M_PEstruct (sym,members) ->
       return (M_PEstruct (sym,members))
    | M_PEunion (sym,id,asym) ->
       return (M_PEunion (sym,id,asym))
    (* | M_PEcfunction of asym 'bty (\* C function pointer expression *\) *)
    | M_PEmemberof (sym,id,asym) ->
       return (M_PEmemberof (sym,id,asym))
    | M_PEcall (name,asyms) ->
       return (M_PEcall (name,asyms))
    | M_PElet (sym_or_pattern,pexpr,pexpr') ->
       let* sym_or_pattern = retype_sym_or_pattern loc sym_or_pattern in
       let* pexpr = retype_pexpr loc pexpr in
       let* pexpr' = retype_pexpr loc pexpr' in
       return (M_PElet (sym_or_pattern,pexpr,pexpr'))
    | M_PEif (asym,pexpr1,pexpr2) ->
       let* pexpr1 = retype_pexpr loc pexpr1 in
       let* pexpr2 = retype_pexpr loc pexpr2 in
       return (M_PEif (asym,pexpr1,pexpr2))
    (* | M_PEis_scalar of asym 'bty
     * | M_PEis_integer of asym 'bty
     * | M_PEis_signed of asym 'bty
     * | M_PEbmc_assume of asym 'bty
     * | M_PEis_unsigned of asym 'bty
     * | M_PEare_compatible of asym 'bty * asym 'bty *)
  in
  return (M_Pexpr (annots,bty,pexpr_))

let retype_memop loc = function
  | M_PtrEq (asym1,asym2) -> return (M_PtrEq (asym1,asym2))
  | M_PtrNe (asym1,asym2) -> return (M_PtrNe (asym1,asym2))
  | M_PtrLt (asym1,asym2) -> return (M_PtrLt (asym1,asym2))
  | M_PtrGt (asym1,asym2) -> return (M_PtrGt (asym1,asym2))
  | M_PtrLe (asym1,asym2) -> return (M_PtrLe (asym1,asym2))
  | M_PtrGe (asym1,asym2) -> return (M_PtrGe (asym1,asym2))
  | M_Ptrdiff (A (annots,bty,ct), asym1, asym2) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_Ptrdiff (A (annots,bty,(bt,size)), asym1, asym2))
  | M_IntFromPtr (A (annots,bty,ct), asym) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_IntFromPtr (A (annots,bty,(bt,size)), asym))
  | M_PtrFromInt (A (annots,bty,ct), asym) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_PtrFromInt (A (annots,bty,(bt,size)), asym))
  | M_PtrValidForDeref (A (annots,bty,ct), asym) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_PtrValidForDeref (A (annots,bty,(bt,size)), asym))
  | M_PtrWellAligned (A (annots,bty,ct), asym) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_PtrWellAligned (A (annots,bty,(bt,size)), asym))
  | M_PtrArrayShift (asym1, A (annots,bty,ct), asym2) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_PtrArrayShift (asym1, A (annots,bty,(bt,size)), asym2))
  | M_Memcpy (asym1,asym2,asym3) -> return (M_Memcpy (asym1,asym2,asym3))
  | M_Memcmp (asym1,asym2,asym3) -> return (M_Memcmp (asym1,asym2,asym3))
  | M_Realloc (asym1,asym2,asym3) -> return (M_Realloc (asym1,asym2,asym3))
  | M_Va_start (asym1,asym2) -> return (M_Va_start (asym1,asym2))
  | M_Va_copy asym -> return (M_Va_copy asym)
  | M_Va_arg (asym, A (annots,bty,ct)) ->
     let* bt = Conversions.bt_of_ctype loc ct in
     let* size = Memory.size_of_ctype loc ct in
     return (M_Va_arg (asym, A (annots,bty,(bt,size))))
  | M_Va_end asym -> return (M_Va_end asym)

let retype_action loc (M_Action (loc,action_)) =
  let* action_ = match action_ with
    | M_Create (asym, A (annots,bty,ct), prefix) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_Create (asym, A (annots,bty,(bt,size)), prefix))
    | M_CreateReadOnly (asym1, A (annots,bty,ct), asym2, prefix) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_CreateReadOnly (asym1, A (annots,bty,(bt,size)), asym2, prefix))
    | M_Alloc (A (annots,bty,ct), asym, prefix) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_Alloc (A (annots,bty,(bt,size)), asym, prefix))
    | M_Kill (b, asym) -> 
       return (M_Kill (b, asym))
    | M_Store (m, A (annots,bty,ct), asym1, asym2, mo) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_Store (m, A (annots,bty,(bt,size)), asym1, asym2, mo))
    | M_Load (A (annots,bty,ct), asym, mo) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_Load (A (annots,bty,(bt,size)), asym, mo))
    | M_RMW (A (annots,bty,ct), asym1, asym2, asym3, mo1, mo2) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_RMW (A (annots,bty,(bt,size)), asym1, asym2, asym3, mo1, mo2))
    | M_Fence mo ->
       return (M_Fence mo)
    | M_CompareExchangeStrong (A (annots,bty,ct), asym1, asym2, asym3, mo1, mo2) -> 
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_CompareExchangeStrong (A (annots,bty,(bt,size)), asym1, asym2, asym3, mo1, mo2))
    | M_CompareExchangeWeak (A (annots,bty,ct), asym1, asym2, asym3, mo1, mo2) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_CompareExchangeWeak (A (annots,bty,(bt,size)), asym1, asym2, asym3, mo1, mo2))
    | M_LinuxFence mo ->
       return (M_LinuxFence mo)
    | M_LinuxLoad (A (annots,bty,ct), asym, mo) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_LinuxLoad (A (annots,bty,(bt,size)), asym, mo))
    | M_LinuxStore (A (annots,bty,ct), asym1, asym2, mo) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_LinuxStore (A (annots,bty,(bt,size)), asym1, asym2, mo))
    | M_LinuxRMW (A (annots,bty,ct), asym1, asym2, mo) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_LinuxRMW (A (annots,bty,(bt,size)), asym1, asym2, mo))
  in
  return (M_Action (loc,action_))


let retype_paction loc = function
 | M_Paction (pol,action) ->
    let* action = retype_action loc action in
    return (M_Paction (pol,action))



let rec retype_expr loc struct_decls oftyp (M_Expr (annots,expr_)) = 
  let retype_expr loc = retype_expr loc struct_decls oftyp in
  let* expr_ = match expr_ with
    | M_Epure pexpr -> 
       let* pexpr = retype_pexpr loc pexpr in
       return (M_Epure pexpr)
    | M_Ememop memop ->
       let* memop = retype_memop loc memop in
       return (M_Ememop memop)
    | M_Eaction paction ->
       let* paction = retype_paction loc paction in
       return (M_Eaction paction)
    | M_Ecase (asym,pats_es) ->
       let* pats_es = 
         mapM (fun (pat,e) ->
             let* pat = retype_pattern loc pat in
             let* e = retype_expr loc e in
             return (pat,e)
           ) pats_es
       in
       return (M_Ecase (asym,pats_es))
    | M_Elet (sym_or_pattern,pexpr,expr) ->
       let* sym_or_pattern = retype_sym_or_pattern loc sym_or_pattern in
       let* pexpr = retype_pexpr loc pexpr in
       let* expr = retype_expr loc expr in
       return (M_Elet (sym_or_pattern,pexpr,expr))
    | M_Eif (asym,expr1,expr2) ->
       let* expr1 = retype_expr loc expr1 in
       let* expr2 = retype_expr loc expr2 in
       return (M_Eif (asym,expr1,expr2))
    | M_Eskip ->
       return (M_Eskip)
    | M_Eccall (A (annots,bty,ct),asym,asyms) ->
       let* bt = Conversions.bt_of_ctype loc ct in
       let* size = Memory.size_of_ctype loc ct in
       return (M_Eccall (A (annots,bty,(bt,size)),asym,asyms))
    | M_Eproc (name,asyms) ->
       return (M_Eproc (name,asyms))
    (* | M_Eunseq of list (mu_expr 'DBTY 'bty) (\* unsequenced expressions *\) *)
    | M_Ewseq (pat,expr1,expr2) ->
       let* pat = retype_pattern loc pat in
       let* expr1 = retype_expr loc expr1 in
       let* expr2 = retype_expr loc expr2 in
       return (M_Ewseq (pat,expr1,expr2))
    | M_Esseq (pat,expr1,expr2) ->
       let* pat = retype_pattern loc pat in
       let* expr1 = retype_expr loc expr1 in
       let* expr2 = retype_expr loc expr2 in
       return (M_Esseq (pat,expr1,expr2))
    (* | M_Easeq of (symbol * 'DBTY) * (mu_action 'bty) * (mu_paction 'bty) (\* atomic sequencing *\) *)
    (* | M_Eindet of nat * (mu_expr 'DBTY 'bty) (\* indeterminately sequenced expr *)
    | M_Ebound (n,expr) ->
       let* expr = retype_expr loc expr in
       return (M_Ebound (n,expr))
    | M_End es ->
       let* es = mapM (retype_expr loc) es in
       return (M_End es)
    | M_Esave (ft,(sym,(cbt,ct)),args,expr) ->
       let* size = try Memory.size_of_ctype loc ct with _ -> return Num.zero in
       let* bt = Conversions.bt_of_core_base_type loc cbt in
       let* ft = 
         match is_return annots, oftyp with
         | true, Some ftyp -> 
            let RT.Computational ((s,bt),f_lrt) = FT.get_return ftyp in
            let rt = RT.Computational ((Sym.fresh (), BT.Unit), RT.I) in
            let ft = FT.Computational ((s,bt), Conversions.logical_returnType_to_argumentType f_lrt (FT.Return rt)) in
            return ft
         | true, None -> fail loc (unreachable !^"Esave in expression without ftyp")
         | false, _ ->
           Conversions.make_esave_spec loc struct_decls 
             (CF.Annot.get_attrs annots) 
             (List.map (fun (sym,((_,ct),_)) -> (Some sym,ct)) args) ct 
       in
       let* args = 
         mapM (fun (sym,((acbt,act),asym)) ->
             let* size = try Memory.size_of_ctype loc ct with _ -> return Num.zero in
             let* abt = Conversions.bt_of_core_base_type loc acbt in
             return (sym,((abt,(abt,size)),asym))
           ) args
       in
       let* expr = retype_expr loc expr in
       return (M_Esave (ft,(sym,(bt,(bt,size))),args,expr))
    | M_Erun (sym,asyms) ->
       return (M_Erun (sym,asyms))
    (* | M_Epar of list (mu_expr 'DBTY 'bty) (\* cppmem-like thread creation *\) *)
    (* | M_Ewait of Mem_common.thread_id (\* wait for thread termination *\) *)
  in
  return (M_Expr (annots,expr_))


let retype_impl_decl loc = function
  | M_Def (cbt,pexpr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* pexpr = retype_pexpr loc pexpr in
     return (M_Def (bt,pexpr))
  | M_IFun (cbt,args,pexpr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = 
       mapM (fun (sym,acbt) ->
           let* abt = Conversions.bt_of_core_base_type loc acbt in
           return (sym,abt)
         ) args
     in
     let* pexpr = retype_pexpr loc pexpr in
     return (M_IFun (bt,args,pexpr))


let retype_impls loc impls = 
  pmap_mapM (fun _ decl -> retype_impl_decl loc decl) 
            impls CF.Implementation.implementation_constant_compare


let retype_fun_map_decl loc structs funinfo fsym = function
  | M_Fun (cbt,args,pexpr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = 
       mapM (fun (sym,acbt) ->
           let* abt = Conversions.bt_of_core_base_type loc acbt in
           return (sym,abt)
         ) args
     in
     let* pexpr = retype_pexpr loc pexpr in
     return (M_Fun (bt,args,pexpr))
  | M_Proc (loc,cbt,args,expr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = 
       mapM (fun (sym,acbt) ->
           let* abt = Conversions.bt_of_core_base_type loc acbt in
           return (sym,abt)
         ) args
     in
     let* ftyp = match Pmap.lookup fsym funinfo with
       | Some (M_funinfo (_,_,ftyp,_,_)) -> return ftyp 
       | None -> fail loc (unreachable (Sym.pp fsym ^^^ !^"not found in funinfo"))
     in
     let* expr = retype_expr loc structs (Some ftyp) expr in
     return (M_Proc (loc,bt,args,expr))
  | M_ProcDecl (loc,cbt,args) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = mapM (Conversions.bt_of_core_base_type loc) args in
     return (M_ProcDecl (loc,bt,args))
  | M_BuiltinDecl (loc,cbt,args) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = mapM (Conversions.bt_of_core_base_type loc) args in
     return (M_BuiltinDecl (loc,bt,args))

let retype_fun_map loc structs funinfo fun_map = 
  pmap_mapM (fun fsym decl -> 
      retype_fun_map_decl loc structs funinfo fsym decl
    ) fun_map Symbol.symbol_compare


let retype_globs loc struct_decls = function
  | M_GlobalDef (cbt,expr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* expr = retype_expr loc struct_decls None expr in
     return (M_GlobalDef (bt,expr))
  | M_GlobalDecl cbt ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     return (M_GlobalDecl bt)


let retype_globs_map loc struct_decls funinfo globs_map = 
  pmap_mapM (fun _ globs -> retype_globs loc struct_decls globs) 
            globs_map Symbol.symbol_compare








let retype_tagDefs loc tagDefs = 
  let open Pp in
  pmap_foldM 
    (fun sym def (acc,acc_structs,acc_unions) -> 
      match def with
      | M_UnionDef _ -> 
         fail Loc.unknown (Unsupported !^"todo: union types")
      | M_StructDef (fields, _f) ->
         let* decl = Conversions.struct_decl Loc.unknown (Tag sym) fields acc_structs in
         let acc = Pmap.add sym (M_StructDef decl) acc in
         let acc_structs = SymMap.add sym decl acc_structs in
         return (acc,acc_structs,acc_unions)
    ) 
    tagDefs (Pmap.empty Symbol.symbol_compare,SymMap.empty,SymMap.empty)


let retype_funinfo struct_decls funinfo =
  pmap_mapM
    (fun fsym (M_funinfo (loc,attrs,(ret_ctype,args),is_variadic,has_proto)) ->
      if is_variadic then fail loc (Variadic_function fsym) else
        let* ftyp = Conversions.make_fun_spec loc struct_decls attrs args ret_ctype in
        return (M_funinfo (loc,attrs,ftyp,is_variadic,has_proto))
    ) funinfo Symbol.symbol_compare


let retype_file loc file 
    : ((FT.t, (BT.t * RE.size), BT.t, Global.struct_decl, unit, 'bty) mu_file) m =

  let* (tagDefs,structs,unions) = retype_tagDefs loc file.mu_tagDefs in
  let* funinfo = retype_funinfo structs file.mu_funinfo in
  let* stdlib = retype_fun_map loc structs funinfo file.mu_stdlib in
  let* funs = retype_fun_map loc structs funinfo file.mu_funs in


  let* impls = retype_impls loc file.mu_impl in
  let* globs = 
    mapM (fun (sym, glob) -> 
        let* glob = retype_globs loc structs glob in
        return (sym,glob)
      ) file.mu_globs 
  in
  return { mu_main = file.mu_main;
           mu_tagDefs = tagDefs;
           mu_stdlib = stdlib;
           mu_impl = impls;
           mu_globs = globs;
           mu_funs = funs;
           mu_extern = file.mu_extern;
           mu_funinfo = funinfo; }
    
