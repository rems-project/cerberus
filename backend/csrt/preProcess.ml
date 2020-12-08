(* open Pp *)
open Resultat
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)
module CF=Cerb_frontend
module Symbol=CF.Symbol
module Loc=Locations
module RT=ReturnTypes
module LRT=LogicalReturnTypes
module FT=ArgumentTypes.Make(ReturnTypes)
module LT=ArgumentTypes.Make(False)
module CA=CF.Core_anormalise
module LC=LogicalConstraints
open CF.Mucore
open TypeErrors
open Pp

open Debug_ocaml

open ListM

open Assertions



module StringSet = Set.Make(String)

let specially_typed = 
  StringSet.of_list []
    (*   "free_proxy";
     *   "malloc_proxy";
     * ] *)



let get_loc_ annots = Cerb_frontend.Annot.get_loc_ annots


let mapM_a f a =
  let* item = f a.item in
  return {a with item}

type ctype_information = {
    bt : BT.t;
    ct : Sctypes.t
  }


let ct_of_ct loc ct = 
  match Sctypes.of_ctype ct with
  | Some ct -> return ct
  | None -> fail loc (Unsupported (!^"ctype" ^^^ CF.Pp_core_ctype.pp_ctype ct))


(* for convenience *)
let ctype_information (loc : Loc.t) ct = 
  let* ct = ct_of_ct loc ct in
  let bt = BT.of_sct ct in
  return {bt; ct}


let retype_ctor (loc : Loc.t) = function
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


let rec retype_pattern (loc : Loc.t) (M_Pattern (annots,pattern_)) =
  match pattern_ with
  | M_CaseBase (msym, cbt) -> 
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     return (M_Pattern (annots,M_CaseBase (msym,bt)))
  | M_CaseCtor (ctor, pats) ->
     let* ctor = retype_ctor loc ctor in
     let* pats = mapM (retype_pattern loc) pats in
     return (M_Pattern (annots,M_CaseCtor (ctor,pats)))

let retype_sym_or_pattern (loc : Loc.t) = function
  | M_Symbol s -> 
     return (M_Symbol s)
  | M_Pat pat -> 
     let* pat = retype_pattern loc pat in
     return (M_Pat pat)



let retype_object_value (loc : Loc.t) = function
  | M_OVinteger iv -> return (M_OVinteger iv)
  | M_OVfloating fv -> return (M_OVfloating fv)
  | M_OVpointer pv -> return (M_OVpointer pv)
  | M_OVarray asyms -> return (M_OVarray asyms)
  | M_OVstruct (s, members) ->
     let* members = 
       mapM (fun (id, ct, mv) ->
           let* ict = ctype_information loc ct in
           return (id, ict, mv)
         ) members
     in
     return (M_OVstruct (s, members))
  | M_OVunion (s,id,mv) ->
     return (M_OVunion (s,id,mv))


let retype_loaded_value (loc : Loc.t) = function
  | M_LVspecified ov ->
     let* ov = retype_object_value loc ov in
     return (M_LVspecified ov)

let retype_value (loc : Loc.t) = function 
 | M_Vobject ov -> 
    let* ov = retype_object_value loc ov in
    return (M_Vobject ov)
 | M_Vloaded lv -> 
    let* lv = retype_loaded_value loc lv in
    return (M_Vloaded lv)
 | M_Vunit -> return (M_Vunit)
 | M_Vtrue -> return (M_Vtrue)
 | M_Vfalse -> return (M_Vfalse)
 | M_Vlist (cbt,asyms) -> 
    let* bt = Conversions.bt_of_core_base_type loc cbt in
    return (M_Vlist (bt,asyms))
 | M_Vtuple asyms -> return (M_Vtuple asyms)

let rec retype_pexpr (loc : Loc.t) (M_Pexpr (annots,bty,pexpr_)) = 
  let loc = Loc.update loc (get_loc_ annots) in
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
       let* ict = ctype_information loc ct in
       return (M_PEarray_shift (asym,ict,asym'))
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
  in
  return (M_Pexpr (annots,bty,pexpr_))

let retype_memop (loc : Loc.t) = function
  | M_PtrEq (asym1,asym2) -> return (M_PtrEq (asym1,asym2))
  | M_PtrNe (asym1,asym2) -> return (M_PtrNe (asym1,asym2))
  | M_PtrLt (asym1,asym2) -> return (M_PtrLt (asym1,asym2))
  | M_PtrGt (asym1,asym2) -> return (M_PtrGt (asym1,asym2))
  | M_PtrLe (asym1,asym2) -> return (M_PtrLe (asym1,asym2))
  | M_PtrGe (asym1,asym2) -> return (M_PtrGe (asym1,asym2))
  | M_Ptrdiff (act, asym1, asym2) ->
     let* act = mapM_a (ctype_information loc) act in
     return (M_Ptrdiff (act, asym1, asym2))
  | M_IntFromPtr (act, asym) ->
     let* act = mapM_a (ctype_information loc) act in
     return (M_IntFromPtr (act, asym))
  | M_PtrFromInt (act1, act2, asym) ->
     let* act1 = mapM_a (ctype_information loc) act1 in
     let* act2 = mapM_a (ctype_information loc) act2 in
     return (M_PtrFromInt (act1, act2, asym))
  | M_PtrValidForDeref (act, asym) ->
     let* act = mapM_a (ctype_information loc) act in
     return (M_PtrValidForDeref (act, asym))
  | M_PtrWellAligned (act, asym) ->
     let* act = mapM_a (ctype_information loc) act in
     return (M_PtrWellAligned (act, asym))
  | M_PtrArrayShift (asym1, act, asym2) ->
     let* act = mapM_a (ctype_information loc) act in
     return (M_PtrArrayShift (asym1, act, asym2))
  | M_Memcpy (asym1,asym2,asym3) -> 
     return (M_Memcpy (asym1,asym2,asym3))
  | M_Memcmp (asym1,asym2,asym3) -> 
     return (M_Memcmp (asym1,asym2,asym3))
  | M_Realloc (asym1,asym2,asym3) -> 
     return (M_Realloc (asym1,asym2,asym3))
  | M_Va_start (asym1,asym2) -> 
     return (M_Va_start (asym1,asym2))
  | M_Va_copy asym -> return (M_Va_copy asym)
  | M_Va_arg (asym, act) ->
     let* act = mapM_a (ctype_information loc) act in
     return (M_Va_arg (asym, act))
  | M_Va_end asym -> return (M_Va_end asym)

let retype_action (loc : Loc.t) (M_Action (loc2,action_)) =
  let loc = Loc.update loc loc2 in
  let* action_ = match action_ with
    | M_Create (asym, act, prefix) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_Create (asym, act, prefix))
    | M_CreateReadOnly (asym1, act, asym2, prefix) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_CreateReadOnly (asym1, act, asym2, prefix))
    | M_Alloc (asym1, asym2, prefix) ->
       return (M_Alloc (asym1, asym2, prefix))
    | M_Kill (M_Dynamic, asym) -> 
       return (M_Kill (M_Dynamic, asym))
    | M_Kill (M_Static ct, asym) -> 
       let* ict = ctype_information loc ct in
       return (M_Kill (M_Static ict, asym))
    | M_Store (m, act, asym1, asym2, mo) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_Store (m, act, asym1, asym2, mo))
    | M_Load (act, asym, mo) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_Load (act, asym, mo))
    | M_RMW (act, asym1, asym2, asym3, mo1, mo2) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_RMW (act, asym1, asym2, asym3, mo1, mo2))
    | M_Fence mo ->
       return (M_Fence mo)
    | M_CompareExchangeStrong (act, asym1, asym2, asym3, mo1, mo2) -> 
       let* act = mapM_a (ctype_information loc) act in
       return (M_CompareExchangeStrong (act, asym1, asym2, asym3, mo1, mo2))
    | M_CompareExchangeWeak (act, asym1, asym2, asym3, mo1, mo2) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_CompareExchangeWeak (act, asym1, asym2, asym3, mo1, mo2))
    | M_LinuxFence mo ->
       return (M_LinuxFence mo)
    | M_LinuxLoad (act, asym, mo) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_LinuxLoad (act, asym, mo))
    | M_LinuxStore (act, asym1, asym2, mo) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_LinuxStore (act, asym1, asym2, mo))
    | M_LinuxRMW (act, asym1, asym2, mo) ->
       let* act = mapM_a (ctype_information loc) act in
       return (M_LinuxRMW (act, asym1, asym2, mo))
  in
  return (M_Action (loc2,action_))


let retype_paction (loc : Loc.t) = function
 | M_Paction (pol,action) ->
    let* action = retype_action loc action in
    return (M_Paction (pol,action))


let rec retype_expr (loc : Loc.t) (M_Expr (annots,expr_)) = 
  let retype_expr loc = retype_expr loc in
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
    | M_Eccall (act,asym,asyms) ->
       (* let* act = mapM_a (ctype_information loc) act in *)
       return (M_Eccall (act,asym,asyms))
    | M_Eproc (name,asyms) ->
       return (M_Eproc (name,asyms))
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
    | M_Ebound (n,expr) ->
       let* expr = retype_expr loc expr in
       return (M_Ebound (n,expr))
    | M_End es ->
       let* es = mapM (retype_expr loc) es in
       return (M_End es)
    | M_Erun (sym,asyms) ->
       return (M_Erun (sym,asyms))
  in
  return (M_Expr (annots,expr_))


let retype_arg (loc : Loc.t) (sym,acbt) = 
  let* abt = Conversions.bt_of_core_base_type loc acbt in
  return (sym,abt)

let retype_impl_decl (loc : Loc.t) = function
  | M_Def (cbt,pexpr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* pexpr = retype_pexpr loc pexpr in
     return (M_Def (bt,pexpr))
  | M_IFun (cbt,args,pexpr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = mapM (retype_arg loc) args in
     let* pexpr = retype_pexpr loc pexpr in
     return (M_IFun (bt,args,pexpr))


let retype_impls (loc : Loc.t) impls = 
  PmapM.mapM (fun _ decl -> retype_impl_decl loc decl) 
    impls CF.Implementation.implementation_constant_compare



open Parse_ast
type funinfos = FT.t mu_funinfos
type mapping = Object.mapping
type funinfo_extra = (Sym.t, mapping * Parse_ast.aarg list) Pmap.map





let retype_label (loc : Loc.t) ~funinfo ~(funinfo_extra:funinfo_extra) ~loop_attributes ~structs ~fsym lsym def = 
  let ftyp = match Pmap.lookup fsym funinfo with
    | Some (M_funinfo (_,_,ftyp,_,_)) -> ftyp 
    | None -> error (Sym.pp_string fsym^" not found in funinfo")
  in
  let (mapping, fargs) = match Pmap.lookup fsym funinfo_extra with
    | Some (mapping, fargs) -> (mapping, fargs)
    | None -> error (Sym.pp_string fsym^" not found in funinfo")
  in
  match def with
  | M_Return _ ->
     let lt = LT.of_rt (FT.get_return ftyp) (LT.I False.False) in
     return (M_Return lt)
  | M_Label (argtyps,args,e,annots) -> 
     let loc = Loc.update loc (get_loc_ annots) in
     let* args = mapM (retype_arg loc) args in
     let* argtyps = 
       ListM.mapM (fun (msym, (ct,by_pointer)) ->
           let () = if not by_pointer then error "label argument passed as value" in
           let* ct = ct_of_ct loc ct in
           return (msym,ct) 
         ) argtyps
     in
     begin match CF.Annot.get_label_annot annots with
     | Some (LAloop_body loop_id)
     | Some (LAloop_continue loop_id)
       ->
        let this_attrs = match Pmap.lookup loop_id loop_attributes with
          | Some attrs -> attrs 
          | None -> CF.Annot.no_attributes
        in
        let* (lt,_) = 
          Conversions.make_label_spec loc lsym mapping
            structs fargs argtyps this_attrs
        in
        let* e = retype_expr loc e in
        return (M_Label (lt,args,e,annots))
     | Some (LAloop_break loop_id) ->
        error "break label has not been inlined"
     | Some LAreturn -> 
        error "return label has not been inlined"
     | Some LAswitch -> 
        error "switch labels"
     | None -> 
        error "non-loop labels"
     end



let retype_fun_map_decl (loc : Loc.t) ~funinfo ~(funinfo_extra:funinfo_extra) ~loop_attributes ~structs
                        fsym (decl: (CA.lt, CA.ct, CA.bt, 'bty) mu_fun_map_decl) = 
  match decl with
  | M_Fun (cbt,args,pexpr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* args = mapM (retype_arg loc) args in
     let* pexpr = retype_pexpr loc pexpr in
     return (M_Fun (bt,args,pexpr))
  | M_Proc (loc2,cbt,args,expr,(labels : (CA.lt, CA.ct, CA.bt, 'bty) mu_label_defs)) ->
     let loc' = Loc.update loc loc2 in
     let* bt = Conversions.bt_of_core_base_type loc' cbt in
     let* args = mapM (retype_arg loc) args in
     let* expr = retype_expr loc expr in
     let* labels = 
       PmapM.mapM (
           retype_label loc ~funinfo ~funinfo_extra 
             ~loop_attributes ~structs ~fsym
         ) labels Sym.compare
     in
     return (M_Proc (loc2,bt,args,expr,labels))
  | M_ProcDecl (loc2,cbt,args) ->
     let loc' = Loc.update loc loc2 in
     let* bt = Conversions.bt_of_core_base_type loc' cbt in
     let* args = mapM (Conversions.bt_of_core_base_type loc') args in
     return (M_ProcDecl (loc2,bt,args))
  | M_BuiltinDecl (loc2,cbt,args) ->
     let loc' = Loc.update loc loc2 in
     let* bt = Conversions.bt_of_core_base_type loc' cbt in
     let* args = mapM (Conversions.bt_of_core_base_type loc') args in
     return (M_BuiltinDecl (loc2,bt,args))

let retype_fun_map (loc : Loc.t) ~funinfo ~funinfo_extra ~loop_attributes ~structs
                   (fun_map : (CA.lt, CA.ct, CA.bt, 'bty) mu_fun_map) = 
  PmapM.mapM (fun fsym decl ->
      retype_fun_map_decl loc ~funinfo ~funinfo_extra 
        ~loop_attributes ~structs fsym decl
    ) fun_map Sym.compare


let retype_globs loc struct_decls (sym, glob) =
  match glob with
  | M_GlobalDef (cbt,expr) ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     let* expr = retype_expr loc expr in
     return (sym, M_GlobalDef (bt,expr))
  | M_GlobalDecl cbt ->
     let* bt = Conversions.bt_of_core_base_type loc cbt in
     return (sym, M_GlobalDecl bt)


let retype_globs_map loc struct_decls funinfo globs_map = 
  PmapM.mapM (fun _ globs -> retype_globs loc struct_decls globs) 
            globs_map Sym.compare





let retype_tagDefs 
      (loc : Loc.t) 
      (tagDefs : (CA.st, CA.ut) mu_tag_definitions) 
    : ((CA.ct mu_struct_def * Global.struct_decl, 
        CA.ct mu_union_def) mu_tag_definitions *
         Global.struct_decl SymMap.t * 
           unit SymMap.t,
      type_error) m
  = 
  PmapM.foldM 
    (fun tag def (acc,acc_structs,acc_unions) -> 
      match def with
      | M_UnionDef _ -> 
         Debug_ocaml.error "todo: union types"
      | M_StructDef (fields, f) ->
         let* decl = Conversions.struct_decl loc tagDefs fields tag in
         let acc = Pmap.add tag (M_StructDef ((fields, f), decl)) acc in
         let acc_structs = SymMap.add tag decl acc_structs in
         return (acc,acc_structs,acc_unions)
    ) 
    tagDefs (Pmap.empty Sym.compare,SymMap.empty,SymMap.empty)




let retype_funinfo struct_decls funinfo stdlib_fsyms : (funinfos * funinfo_extra, type_error) m =
  Debug_ocaml.begin_csv_timing "preprocess";
  let* result = 
    PmapM.foldM
      (fun fsym (M_funinfo (loc,attrs,(ret_ctype,args),is_variadic,has_proto)) (funinfo, funinfo_extra) ->
        let special_type = match Sym.name fsym with
          | Some name -> StringSet.mem name specially_typed
          | None -> false
        in
        if special_type then 
          return (funinfo, funinfo_extra)
        else
          let loc' = Loc.update Loc.unknown loc in
          if is_variadic then 
            let err = !^"Variadic function" ^^^ Sym.pp fsym ^^^ !^"unsupported" in
            fail loc' (Unsupported err) 
          else
            let* ret_ctype = ct_of_ct loc' ret_ctype in
            let* args = 
              ListM.mapM (fun (msym, ct) ->
                  let* ct = ct_of_ct loc' ct in
                  return (msym, ct)
                ) args
            in
            let* (ftyp, mapping, args) = 
              Conversions.make_fun_spec loc' struct_decls args ret_ctype attrs in
            return (Pmap.add fsym (M_funinfo (loc,attrs,ftyp,is_variadic,has_proto)) funinfo,
                    Pmap.add fsym (mapping, args) funinfo_extra)
      ) funinfo (Pmap.empty Sym.compare, Pmap.empty Sym.compare)
  in
  Debug_ocaml.end_csv_timing ();
  return result




let retype_file loc (file : (CA.ft, CA.lt, CA.ct, CA.bt, CA.ct mu_struct_def, CA.ct mu_union_def, 'bty) mu_file)
    : ((FT.t, LT.t, ctype_information, BT.t, 
        CA.ct mu_struct_def * Global.struct_decl, 
        CA.ct mu_union_def, 'bty) mu_file,
      type_error) m =

  let stdlib_fsyms = Pmap.domain file.mu_stdlib in

  let loop_attributes = file.mu_loop_attributes in
  let* (tagDefs,structs,unions) = retype_tagDefs loc file.mu_tagDefs in
  let* (funinfo,funinfo_extra) = retype_funinfo structs file.mu_funinfo stdlib_fsyms in
  let* stdlib = 
    retype_fun_map loc ~loop_attributes ~structs 
      ~funinfo ~funinfo_extra file.mu_stdlib 
  in
  let* funs = 
    retype_fun_map loc ~loop_attributes ~structs 
      ~funinfo ~funinfo_extra file.mu_funs 
  in
  let* impls = retype_impls loc file.mu_impl in
  let* globs = mapM (retype_globs loc structs) file.mu_globs in
  let file = 
    { mu_main = file.mu_main;
      mu_tagDefs = tagDefs;
      mu_stdlib = stdlib;
      mu_impl = impls;
      mu_globs = globs;
      mu_funs = funs;
      mu_extern = file.mu_extern;
      mu_funinfo = funinfo; 
      mu_loop_attributes = file.mu_loop_attributes;
    }
  in
  return file
    
