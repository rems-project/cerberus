(* open Pp *)
open Resultat
open Effectful.Make(Resultat)
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)
module CF=Cerb_frontend
module Symbol=CF.Symbol
module Loc=Locations
module RT=ReturnTypes
module LRT=LogicalReturnTypes
module AT = ArgumentTypes
module CA=CF.Core_anormalise
module LC=LogicalConstraints
module StringSet = Set.Make(String)
module IT = IndexTerms
module BT = BaseTypes
(* open TypeErrors *)
open Pp
open Debug_ocaml
open ListM
open TypeErrors
open Tools



module SR_Types = struct
  type ct = Sctypes.t
  type bt = BT.t
  type ift = AT.ft
  type ict = RT.t
  type ft = AT.ft
  type lt = AT.lt
  type st = Memory.struct_layout
  type gt = ct
  type ut = unit
  type mapping = Mapping.t
  type resource_predicates = (string * ResourcePredicates.definition) list
  type logical_predicates = (string * LogicalPredicates.definition) list
end

module Old = CF.Mucore.Make(CF.Mucore.SimpleTypes)
module New = CF.Mucore.Make(SR_Types)


type funinfos = New.mu_funinfos
type funinfo_extras = (Sym.t, Ast.function_spec * Mapping.t) Pmap.map



let mapM_act f (a : 'TY Old.act) : ('TY New.act, type_error) m =
  let@ ct = f a.ct in
  let act = New.{ 
      loc = a.loc;
      annot = a.annot;
      type_annot = a.type_annot;
      ct = ct 
    }
  in
  return act



type ctype_information = {
    bt : BT.t;
    ct : Sctypes.t
  }


let ct_of_ct loc ct = 
  match Sctypes.of_ctype ct with
  | Some ct -> return ct
  | None -> return (unsupported loc (!^"ctype" ^^^ CF.Pp_core_ctype.pp_ctype ct))


(* for convenience *)
let ctype_information (loc : Loc.t) ct = 
  let@ ct = ct_of_ct loc ct in
  let bt = BT.of_sct ct in
  return {bt; ct}




  




let retype_ctor (loc : Loc.t) (ctor : Old.mu_ctor) : (New.mu_ctor, type_error) m =
  match ctor with
  | Old.M_Cnil cbt -> 
     let@ bt = Conversions.bt_of_core_base_type loc cbt in
     return (New.M_Cnil bt)
  | Old.M_Ccons -> return New.M_Ccons
  | Old.M_Ctuple -> return New.M_Ctuple
  | Old.M_Carray -> return New.M_Carray
  | Old.M_Cspecified -> return New.M_Cspecified


let rec retype_pattern (pattern : Old.mu_pattern) : (New.mu_pattern, type_error) m =
  let (M_Pattern (loc, annots,pattern_)) = pattern in
  match pattern_ with
  | Old.M_CaseBase (msym, cbt) -> 
     let@ bt = Conversions.bt_of_core_base_type loc cbt in
     return (New.M_Pattern (loc, annots, M_CaseBase (msym,bt)))
  | Old.M_CaseCtor (ctor, pats) ->
     let@ ctor = retype_ctor loc ctor in
     let@ pats = mapM retype_pattern pats in
     return (New.M_Pattern (loc, annots,M_CaseCtor (ctor,pats)))


let retype_sym_or_pattern = function
  | Old.M_Symbol s -> 
     return (New.M_Symbol s)
  | Old.M_Pat pat -> 
     let@ pat = retype_pattern pat in
     return (New.M_Pat pat)


let rec retype_object_value (loc : Loc.t) = function
  | Old.M_OVinteger iv -> return (New.M_OVinteger iv)
  | Old.M_OVfloating fv -> return (New.M_OVfloating fv)
  | Old.M_OVpointer pv -> return (New.M_OVpointer pv)
  | Old.M_OVarray lvs -> 
     let@ lvs = ListM.mapM (retype_loaded_value loc) lvs in
     return (New.M_OVarray lvs)
  | Old.M_OVstruct (s, members) ->
     let@ members = 
       mapM (fun (id, ct, mv) ->
           let@ ct = ct_of_ct loc ct in
           return (id, ct, mv)
         ) members
     in
     return (New.M_OVstruct (s, members))
  | Old.M_OVunion (s,id,mv) ->
     return (New.M_OVunion (s,id,mv))


and retype_loaded_value (loc : Loc.t) = function
  | Old.M_LVspecified ov ->
     let@ ov = retype_object_value loc ov in
     return (New.M_LVspecified ov)

and retype_value (loc : Loc.t) = function 
 | Old.M_Vobject ov -> 
    let@ ov = retype_object_value loc ov in
    return (New.M_Vobject ov)
 | Old.M_Vloaded lv -> 
    let@ lv = retype_loaded_value loc lv in
    return (New.M_Vloaded lv)
 | Old.M_Vunit -> return (New.M_Vunit)
 | Old.M_Vtrue -> return (New.M_Vtrue)
 | Old.M_Vfalse -> return (New.M_Vfalse)
 | Old.M_Vlist (cbt,vs) -> 
    let@ bt = Conversions.bt_of_core_base_type loc cbt in
    let@ vs = ListM.mapM (retype_value loc) vs in
    return (New.M_Vlist (bt,vs))
 | Old.M_Vtuple vs -> 
    let@ vs = ListM.mapM (retype_value loc) vs in
    return (New.M_Vtuple vs)

let retype_pexpr (Old.M_Pexpr (loc, annots,bty,pexpr_)) =
  let@ pexpr_ = match pexpr_ with
    | M_PEsym sym -> 
       return (New.M_PEsym sym)
    | M_PEimpl impl -> 
       return (New.M_PEimpl impl)
    | M_PEval v -> 
       let@ v = retype_value loc v in
       return (New.M_PEval v)
    | M_PEconstrained cs -> 
       return (New.M_PEconstrained cs)
    | M_PEerror (err,asym) -> 
       return (New.M_PEerror (err,asym))
    | M_PEctor (ctor,asyms) -> 
       let@ ctor = retype_ctor loc ctor in
       return (New.M_PEctor (ctor,asyms))
    | M_CivCOMPL (act, asym) -> 
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CivCOMPL (act, asym))
    | M_CivAND (act, asym1, asym2) -> 
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CivAND (act, asym1, asym2))
    | M_CivOR (act, asym1, asym2) -> 
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CivOR (act, asym1, asym2))
    | M_CivXOR (act, asym1, asym2) -> 
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CivXOR (act, asym1, asym2))
    | M_Cfvfromint asym -> 
       return (New.M_Cfvfromint asym)
    | M_Civfromfloat (act, asym) -> 
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_Civfromfloat (act, asym))
    | M_PEarray_shift (asym,ct,asym') ->
       let@ ict = ct_of_ct loc ct in
       return (New.M_PEarray_shift (asym,ict,asym'))
    | M_PEmember_shift (asym,sym,id) ->
       return (New.M_PEmember_shift (asym,sym,id))
    | M_PEnot asym -> 
       return (New.M_PEnot asym)
    | M_PEop (op,asym1,asym2) ->
       return (New.M_PEop (op,asym1,asym2))
    | M_PEstruct (sym,members) ->
       return (New.M_PEstruct (sym,members))
    | M_PEunion (sym,id,asym) ->
       return (New.M_PEunion (sym,id,asym))
    | M_PEmemberof (sym,id,asym) ->
       return (New.M_PEmemberof (sym,id,asym))
    | M_PEcall (name,asyms) ->
       return (New.M_PEcall (name,asyms))
    | M_PEassert_undef (asym, loc, undef) ->
       return (New.M_PEassert_undef (asym, loc, undef))
    | M_PEbool_to_integer asym ->
       return (New.M_PEbool_to_integer asym)
    | M_PEconv_int (act, asym) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_PEconv_int (act, asym))
    | M_PEwrapI (act, asym) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_PEwrapI (act, asym))
  in
  return (New.M_Pexpr (loc, annots,bty,pexpr_))


let rec retype_tpexpr (Old.M_TPexpr (loc, annots,bty,pexpr_)) = 
  let@ pexpr_ = match pexpr_ with
    | M_PEcase (asym,pats_pes) ->
       let@ pats_pes = 
         mapM (fun (pat,pexpr) ->
             let@ pat = retype_pattern pat in
             let@ pexpr = retype_tpexpr pexpr in
             return (pat,pexpr)
           ) pats_pes
       in
       return (New.M_PEcase (asym,pats_pes))
    | M_PElet (sym_or_pattern,pexpr,pexpr') ->
       let@ sym_or_pattern = retype_sym_or_pattern sym_or_pattern in
       let@ pexpr = retype_pexpr pexpr in
       let@ pexpr' = retype_tpexpr pexpr' in
       return (New.M_PElet (sym_or_pattern,pexpr,pexpr'))
    | M_PEif (asym,pexpr1,pexpr2) ->
       let@ pexpr1 = retype_tpexpr pexpr1 in
       let@ pexpr2 = retype_tpexpr pexpr2 in
       return (New.M_PEif (asym,pexpr1,pexpr2))
    | M_PEdone asym ->
       return (New.M_PEdone asym)
    | M_PEundef (loc,undef) -> 
       return (New.M_PEundef (loc,undef))
       
  in
  return (New.M_TPexpr (loc, annots,bty,pexpr_))


let retype_memop (loc : Loc.t) = function
  | Old.M_PtrEq (asym1,asym2) -> return (New.M_PtrEq (asym1,asym2))
  | Old.M_PtrNe (asym1,asym2) -> return (New.M_PtrNe (asym1,asym2))
  | Old.M_PtrLt (asym1,asym2) -> return (New.M_PtrLt (asym1,asym2))
  | Old.M_PtrGt (asym1,asym2) -> return (New.M_PtrGt (asym1,asym2))
  | Old.M_PtrLe (asym1,asym2) -> return (New.M_PtrLe (asym1,asym2))
  | Old.M_PtrGe (asym1,asym2) -> return (New.M_PtrGe (asym1,asym2))
  | Old.M_Ptrdiff (act, asym1, asym2) ->
     let@ act = mapM_act (ct_of_ct loc) act in
     return (New.M_Ptrdiff (act, asym1, asym2))
  | Old.M_IntFromPtr (act1, act2, asym) ->
     let@ act1 = mapM_act (ct_of_ct loc) act1 in
     let@ act2 = mapM_act (ct_of_ct loc) act2 in
     return (New.M_IntFromPtr (act1, act2, asym))
  | Old.M_PtrFromInt (act1, act2, asym) ->
     let@ act1 = mapM_act (ct_of_ct loc) act1 in
     let@ act2 = mapM_act (ct_of_ct loc) act2 in
     return (New.M_PtrFromInt (act1, act2, asym))
  | Old.M_PtrValidForDeref (act, asym) ->
     let@ act = mapM_act (ct_of_ct loc) act in
     return (New.M_PtrValidForDeref (act, asym))
  | Old.M_PtrWellAligned (act, asym) ->
     let@ act = mapM_act (ct_of_ct loc) act in
     return (New.M_PtrWellAligned (act, asym))
  | Old.M_PtrArrayShift (asym1, act, asym2) ->
     let@ act = mapM_act (ct_of_ct loc) act in
     return (New.M_PtrArrayShift (asym1, act, asym2))
  | Old.M_Memcpy (asym1,asym2,asym3) -> 
     return (New.M_Memcpy (asym1,asym2,asym3))
  | Old.M_Memcmp (asym1,asym2,asym3) -> 
     return (New.M_Memcmp (asym1,asym2,asym3))
  | Old.M_Realloc (asym1,asym2,asym3) -> 
     return (New.M_Realloc (asym1,asym2,asym3))
  | Old.M_Va_start (asym1,asym2) -> 
     return (New.M_Va_start (asym1,asym2))
  | Old.M_Va_copy asym -> return (New.M_Va_copy asym)
  | Old.M_Va_arg (asym, act) ->
     let@ act = mapM_act (ct_of_ct loc) act in
     return (New.M_Va_arg (asym, act))
  | Old.M_Va_end asym -> return (New.M_Va_end asym)


let retype_action (Old.M_Action (loc,action_)) =
  let@ action_ = match action_ with
    | M_Create (asym, act, prefix) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_Create (asym, act, prefix))
    | M_CreateReadOnly (asym1, act, asym2, prefix) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CreateReadOnly (asym1, act, asym2, prefix))
    | M_Alloc (asym1, asym2, prefix) ->
       return (New.M_Alloc (asym1, asym2, prefix))
    | M_Kill (M_Dynamic, asym) -> 
       return (New.M_Kill (M_Dynamic, asym))
    | M_Kill (M_Static ct, asym) -> 
       let@ ict = ct_of_ct loc ct in
       return (New.M_Kill (M_Static ict, asym))
    | M_Store (m, act, asym1, asym2, mo) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_Store (m, act, asym1, asym2, mo))
    | M_Load (act, asym, mo) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_Load (act, asym, mo))
    | M_RMW (act, asym1, asym2, asym3, mo1, mo2) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_RMW (act, asym1, asym2, asym3, mo1, mo2))
    | M_Fence mo ->
       return (New.M_Fence mo)
    | M_CompareExchangeStrong (act, asym1, asym2, asym3, mo1, mo2) -> 
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CompareExchangeStrong (act, asym1, asym2, asym3, mo1, mo2))
    | M_CompareExchangeWeak (act, asym1, asym2, asym3, mo1, mo2) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_CompareExchangeWeak (act, asym1, asym2, asym3, mo1, mo2))
    | M_LinuxFence mo ->
       return (New.M_LinuxFence mo)
    | M_LinuxLoad (act, asym, mo) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_LinuxLoad (act, asym, mo))
    | M_LinuxStore (act, asym1, asym2, mo) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_LinuxStore (act, asym1, asym2, mo))
    | M_LinuxRMW (act, asym1, asym2, mo) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_LinuxRMW (act, asym1, asym2, mo))
  in
  return (New.M_Action (loc,action_))


let retype_paction = function
 | Old.M_Paction (pol,action) ->
    let@ action = retype_action action in
    return (New.M_Paction (pol,action))


let retype_expr (Old.M_Expr (loc, annots, expr_)) =
  let@ expr_ = match expr_ with
    | M_Epure pexpr -> 
       let@ pexpr = retype_pexpr pexpr in
       return (New.M_Epure pexpr)
    | M_Ememop memop ->
       let@ memop = retype_memop loc memop in
       return (New.M_Ememop memop)
    | M_Eaction paction ->
       let@ paction = retype_paction paction in
       return (New.M_Eaction paction)
    | M_Eskip ->
       return (New.M_Eskip)
    | M_Eccall (act,asym,asyms) ->
       let@ act = mapM_act (ct_of_ct loc) act in
       return (New.M_Eccall (act,asym,asyms))
    | M_Eproc (name,asyms) ->
       return (New.M_Eproc (name,asyms))
    | M_Erpredicate (pack_unpack, name, asyms) ->
       let pack_unpack = match pack_unpack with
         | Pack -> New.Pack
         | Unpack -> New.Unpack
       in
       return (New.M_Erpredicate (pack_unpack, name, asyms))
    | M_Elpredicate (have_show, name, asyms) ->
       let have_show = match have_show with
         | Have -> New.Have
         | Show -> New.Show
       in
       return (New.M_Elpredicate (have_show, name, asyms))
  in

  return (New.M_Expr (loc, annots,expr_))

let rec retype_texpr (Old.M_TExpr (loc, annots, expr_)) = 
  let@ expr_ = match expr_ with
    | M_Ecase (asym,pats_es) ->
       let@ pats_es = 
         mapM (fun (pat,e) ->
             let@ pat = retype_pattern pat in
             let@ e = retype_texpr e in
             return (pat,e)
           ) pats_es
       in
       return (New.M_Ecase (asym,pats_es))
    | M_Elet (sym_or_pattern,pexpr,expr) ->
       let@ sym_or_pattern = retype_sym_or_pattern sym_or_pattern in
       let@ pexpr = retype_pexpr pexpr in
       let@ expr = retype_texpr expr in
       return (New.M_Elet (sym_or_pattern,pexpr,expr))
    | M_Eif (asym,expr1,expr2) ->
       let@ expr1 = retype_texpr expr1 in
       let@ expr2 = retype_texpr expr2 in
       return (New.M_Eif (asym,expr1,expr2))
    | M_Ewseq (pat,expr1,expr2) ->
       let@ pat = retype_pattern pat in
       let@ expr1 = retype_expr expr1 in
       let@ expr2 = retype_texpr expr2 in
       return (New.M_Ewseq (pat,expr1,expr2))
    | M_Esseq (pat,expr1,expr2) ->
       let@ pat = retype_sym_or_pattern pat in
       let@ expr1 = retype_expr expr1 in
       let@ expr2 = retype_texpr expr2 in
       return (New.M_Esseq (pat,expr1,expr2))
    | M_Ebound (n,expr) ->
       let@ expr = retype_texpr expr in
       return (New.M_Ebound (n,expr))
    | M_End es ->
       let@ es = mapM retype_texpr es in
       return (New.M_End es)
    | M_Edone asym ->
       return (New.M_Edone asym)
    | M_Erun (sym,asyms) ->
       return (New.M_Erun (sym,asyms))
    | M_Eundef (loc,undef) -> 
       return (New.M_Eundef (loc,undef))
  in
  return (New.M_TExpr (loc, annots,expr_))


let retype_arg (loc : Loc.t) (sym,acbt) = 
  let@ abt = Conversions.bt_of_core_base_type loc acbt in
  return (sym,abt)






let retype_file (file : 'TY Old.mu_file) : ('TY New.mu_file, type_error) m =

  let@ tagDefs =
    let retype_tagDef tag def =
      match def with
      | Old.M_UnionDef _ -> 
         Debug_ocaml.error "todo: union types"
      | Old.M_StructDef (fields, f) ->
         let@ decl = Conversions.struct_decl Loc.unknown fields tag in
         return (New.M_StructDef decl)
    in
    PmapM.mapM retype_tagDef file.mu_tagDefs Sym.compare
  in

  let struct_decls =
    Pmap.fold (fun sym def decls ->
        match def with
        | New.M_StructDef def ->
           SymMap.add sym def decls
        | _ -> decls
      ) tagDefs SymMap.empty
  in


  let resource_predicates = ResourcePredicates.predicate_list struct_decls in
  let logical_predicates = LogicalPredicates.predicate_list struct_decls in


  let@ (globs, glob_typs) = 
    let retype_globs (sym, glob) (globs, glob_typs) =
      let loc = Loc.unknown in
      match glob with
      | Old.M_GlobalDef (lsym, (bt,ct),expr) ->
         let@ ct = ct_of_ct loc ct in
         let bt = BT.of_sct ct in
         let@ expr = retype_texpr expr in
         let globs = (sym, New.M_GlobalDef (lsym, (bt,ct),expr)) :: globs in
         let glob_typs = (sym, lsym, ct) :: glob_typs in
         return (globs, glob_typs)
      | M_GlobalDecl (lsym, (bt,ct)) ->
         let@ ct = ct_of_ct loc ct in
         let bt = BT.of_sct ct in
         let globs = (sym, New.M_GlobalDecl (lsym, (bt,ct))) :: globs in
         let glob_typs = (sym, lsym, ct) :: glob_typs in
         return (globs, glob_typs)
    in
    ListM.fold_rightM retype_globs file.mu_globs ([], [])
  in


  let@ impls = 
    let retype_impl_decl impl def = 
      match def with
      | Old.M_Def (ict,cbt,pexpr) ->
         let@ ict = 
           let@ bt = Conversions.bt_of_core_base_type Loc.unknown ict in
           return (RT.Computational ((Sym.fresh (), bt), (Loc.unknown, None), LRT.I))
         in
         let@ bt = Conversions.bt_of_core_base_type Loc.unknown cbt in
         let@ pexpr = retype_tpexpr pexpr in
         return (New.M_Def (ict,bt,pexpr))
      | Old.M_IFun (ift,cbt,args,pexpr) ->
         let@ ift = 
           let (rbt, argbts) = ift in
           let@ rbt = Conversions.bt_of_core_base_type Loc.unknown rbt in
           let@ args = 
             ListM.mapM (fun bt -> 
                 let@ bt = Conversions.bt_of_core_base_type Loc.unknown bt in
                 return (Sym.fresh (), bt, (Loc.unknown, None))
               ) argbts 
           in
           let ft = (AT.mComputationals args) 
                      (AT.I (RT.Computational ((Sym.fresh (), rbt), (Loc.unknown, None), LRT.I)))
           in
           return ft
         in
         let@ bt = Conversions.bt_of_core_base_type Loc.unknown cbt in
         let@ args = mapM (retype_arg Loc.unknown) args in
         let@ pexpr = retype_tpexpr pexpr in
         return (New.M_IFun (ift,bt,args,pexpr))
    in
    PmapM.mapM retype_impl_decl file.mu_impl 
      CF.Implementation.implementation_constant_compare
  in


  
  let@ ((funinfo : funinfos), 
        (funinfo_extra : funinfo_extras)) =
    let retype_funinfo fsym funinfo_entry (funinfo, funinfo_extra) =
      let (Old.M_funinfo (floc,attrs,(ret_ctype,args,is_variadic), trusted, has_proto)) = 
        funinfo_entry in
      let loc = Loc.update Loc.unknown floc in
      if is_variadic then 
        let err = !^"Variadic function" ^^^ Sym.pp fsym ^^^ !^"unsupported" in
        unsupported loc err
      else
        let@ ret_ctype = ct_of_ct loc ret_ctype in
        let@ args = 
          ListM.mapM (fun (msym, ct) ->
              let@ ct = ct_of_ct loc ct in
              return (msym, ct)
            ) args
        in
        let@ fspec = Parse.parse_function glob_typs trusted args ret_ctype attrs in
        let@ (ftyp, trusted, mappings) = 
          Conversions.make_fun_spec loc struct_decls resource_predicates 
            logical_predicates fsym fspec 
        in
        let funinfo_entry = New.M_funinfo (floc,attrs,ftyp, trusted, has_proto) in
        let funinfo = Pmap.add fsym funinfo_entry funinfo in
        let funinfo_extra = Pmap.add fsym (fspec, mappings) funinfo_extra in
        return (funinfo, funinfo_extra)
    in
    PmapM.foldM retype_funinfo file.mu_funinfo (Pmap.empty Sym.compare, Pmap.empty Sym.compare)
  in
  


  let retype_label ~fsym (lsym : Sym.t) def = 
    let ftyp = match Pmap.lookup fsym funinfo with
      | Some (New.M_funinfo (_,_,ftyp, _trusted, _)) -> ftyp 
      | None -> error (Sym.pp_string fsym^" not found in funinfo")
    in
    let (fspec, start_mapping) = match Pmap.lookup fsym funinfo_extra with
      | Some extra -> extra
      | None -> error (Sym.pp_string fsym^" not found in funinfo")
    in
    match def with
    | Old.M_Return (loc, _) ->
       let lt = AT.of_rt (AT.get_return ftyp) (AT.I False.False) in
       return (New.M_Return (loc, lt))
    | Old.M_Label (loc, argtyps, args, e, annots) -> 
       let@ args = mapM (retype_arg loc) args in
       let@ argtyps = 
         ListM.mapM (fun (msym, (ct,by_pointer)) ->
             let sym = Option.value (Sym.fresh ()) msym in
             let () = if not by_pointer then error "label argument passed as value" in
             let@ ct = ct_of_ct loc ct in
             return (sym,ct) 
           ) argtyps
       in
       begin match CF.Annot.get_label_annot annots with
       | Some (LAloop_prebody loop_id)
         ->
          let this_attrs = match Pmap.lookup loop_id file.mu_loop_attributes with
            | Some attrs -> attrs 
            | None -> CF.Annot.no_attributes
          in
          let lname = match Sym.description lsym with
            | Sym.SD_Id lname -> lname
            | _ -> failwith "label without name"
          in
          let@ lspec = Parse.parse_label lname argtyps fspec this_attrs in
          let@ (lt,mapping) = 
            Conversions.make_label_spec loc struct_decls resource_predicates 
              logical_predicates lname start_mapping lspec
          in
          let@ e = retype_texpr e in
          return (New.M_Label (loc, lt,args,e,annots))
       | Some (LAloop_body loop_id) ->
          error "body label has not been inlined"
       | Some (LAloop_continue loop_id) ->
          error "continue label has not been inlined"
       | Some (LAloop_break loop_id) ->
          error "break label has not been inlined"
       | Some LAreturn -> 
          error "return label has not been inlined"
       | Some LAswitch -> 
          error "switch labels"
       | None -> 
          error "non-loop labels"
       end
  in


 let retype_fun_map_decl fsym decl = 
   match decl with
   | Old.M_Fun (cbt,args,pexpr) ->
      let@ bt = Conversions.bt_of_core_base_type Loc.unknown cbt in
      let@ args = mapM (retype_arg Loc.unknown) args in
      let@ pexpr = retype_tpexpr pexpr in
      return (New.M_Fun (bt,args,pexpr))
   | Old.M_Proc (loc,cbt,args,expr,labels) ->
      let@ bt = Conversions.bt_of_core_base_type loc cbt in
      let@ args = mapM (retype_arg loc) args in
      let@ expr = retype_texpr expr in
      let@ labels = PmapM.mapM (retype_label ~fsym) labels Sym.compare in
      return (New.M_Proc (loc,bt,args,expr,labels))
   | Old.M_ProcDecl (loc,cbt,args) ->
      let@ bt = Conversions.bt_of_core_base_type loc cbt in
      let@ args = mapM (Conversions.bt_of_core_base_type loc) args in
      return (New.M_ProcDecl (loc,bt,args))
   | Old.M_BuiltinDecl (loc,cbt,args) ->
      let@ bt = Conversions.bt_of_core_base_type loc cbt in
      let@ args = mapM (Conversions.bt_of_core_base_type loc) args in
      return (New.M_BuiltinDecl (loc,bt,args))
 in

  let@ stdlib = 
    PmapM.mapM (fun fsym decl -> retype_fun_map_decl fsym decl
      ) file.mu_stdlib Sym.compare
  in

  let@ funs = 
    let number_entries = List.length (Pmap.bindings_list file.mu_funs) in
    let ping = Pp.progress "processing specs" number_entries in
    PmapM.mapM (fun fsym decl -> 
        let@ () = return (ping (Sym.pp_string fsym)) in
        let@ result = retype_fun_map_decl fsym decl in
        return result
      ) file.mu_funs Sym.compare
  in

  let file = 
    New.{ mu_main = file.mu_main;
          mu_tagDefs = tagDefs;
          mu_stdlib = stdlib;
          mu_impl = impls;
          mu_globs = globs;
          mu_funs = funs;
          mu_extern = file.mu_extern;
          mu_funinfo = funinfo; 
          mu_loop_attributes = file.mu_loop_attributes;
          mu_resource_predicates = resource_predicates;
          mu_logical_predicates = logical_predicates;
    }
  in
  return file
    
