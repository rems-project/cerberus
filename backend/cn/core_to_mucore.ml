module Print = Pp
open Cerb_frontend
open Lem_pervasives
open Ctype
open Milicore


module Pmap = struct
  include Pmap
  let filter_map compare f map = 
    Pmap.fold (fun key value acc ->
        match f key value with
        | Some value' -> Pmap.add key value' acc
        | None -> acc
      ) map (Pmap.empty compare)
end



module SymSet = 
  Set.Make(struct
      let compare = Symbol.symbol_compare
      type t = Symbol.sym
    end)


open Core
open Annot
module BT = BaseTypes
module SBT = SurfaceBaseTypes
module Mu = Mucore
open Mu
module Loc = Locations
module C = Compile
module SymMap = Map.Make(Sym)
module IdMap = Map.Make(Id)
open Print
open TypeErrors
open Cn


(* This rewrite should happen after some partial evaluation and
   rewrites that remove expressions passing ctypes and function
   pointers as values. The embedding into mucore then is partial in
   those places. *)


(* type bty = core_base_type *)
(* type 'bty pexpr = ('bty, Symbol.sym) generic_pexpr *)
(* type 'bty pexprs = ('bty pexpr) list *)
(* type ('a, 'bty) expr = ('a, 'bty, Symbol.sym) generic_expr *)
(* type annot = Annot.annot *)
(* type annots = annot list *)

type symbol = Symbol.sym
type mu_pexpr = unit Mu.mu_pexpr
type mu_pexprs = mu_pexpr list
type mu_expr = unit Mu.mu_expr








let assert_error loc msg = 
  Print.error loc msg []; 
  exit 2

let assertl loc b msg = 
  if b then () 
  else assert_error loc msg

let convert_ct loc ct = Sctypes.of_ctype_unsafe loc ct

let convert_bt loc =

  let rec bt_of_core_object_type = function
    | OTy_integer -> BT.Integer
    | OTy_pointer -> BT.Loc
    | OTy_array t -> BT.Map (Integer, bt_of_core_object_type t)
    | OTy_struct tag -> BT.Struct tag
    | OTy_union _tag -> Tools.unsupported loc !^"union types"
    | OTy_floating -> Tools.unsupported loc !^"floats"
  in

  let rec bt_of_core_base_type = function
    | BTy_unit -> BT.Unit
    | BTy_boolean -> BT.Bool
    | BTy_object ot -> bt_of_core_object_type ot
    | BTy_loaded ot -> bt_of_core_object_type ot
    | BTy_list bt -> BT.List (bt_of_core_base_type bt)
    | BTy_tuple bts -> BT.Tuple (List.map bt_of_core_base_type bts)
    | BTy_storable -> assert_error loc (!^"BTy_storable")
    | BTy_ctype -> assert_error loc (!^"BTy_ctype")
  in

  fun cbt -> bt_of_core_base_type cbt



let ensure_pexpr_ctype loc err pe : 'TY act = 
  match pe with
  | Pexpr (annot, bty, PEval (Vctype ct)) -> 
     {loc; annot; type_annot = bty; ct = convert_ct loc ct}
  | _ ->
     assert_error loc (err)



(* ... (originally) adapting the algorithm from
   http://matt.might.net/articles/a-normalization/ for core *)





let ensure_ctype__pexpr loc = function
  | Core.Pexpr (annot, bty, Core.PEval (Core.Vctype ct)) -> 
     Some ({loc; annot; type_annot = bty; ct = convert_ct loc ct})
  | _ -> None


let loc_error loc msg = 
  Print.error loc !^msg []; 
  assert false

let loc_error_pp loc msg = 
  Print.error loc msg [];
  assert false

let fensure_ctype__pexpr loc err pe : 'TY act = 
  match ensure_ctype__pexpr loc pe with
  | Some ctype -> ctype
  | None -> loc_error loc err










let rec core_to_mu__pattern loc (Pattern (annots, pat_)) = 
  let loc = Loc.update loc (Annot.get_loc_ annots) in

  let wrap pat_ = M_Pattern(loc, annots, pat_) in
  match pat_ with
  | CaseBase (msym, bt1) -> 
     wrap (M_CaseBase (msym, convert_bt loc bt1))
  | CaseCtor(ctor, pats) -> 
     let pats = map (core_to_mu__pattern loc) pats in
     match ctor with
     | Cnil bt1 -> wrap (M_CaseCtor (M_Cnil (convert_bt loc bt1), pats))
     | Ccons -> wrap (M_CaseCtor (M_Ccons, pats))
     | Ctuple -> wrap (M_CaseCtor (M_Ctuple, pats))
     | Carray -> wrap (M_CaseCtor (M_Carray, pats))
     | Cspecified -> List.hd pats
     | _ -> assert_error loc (!^"core_to_mucore: unsupported pattern")


let rec n_ov loc = function
  | OVinteger iv -> 
     M_OVinteger iv
  | OVfloating fv -> 
     M_OVfloating fv
  | OVpointer pv -> 
     M_OVpointer pv
  | OVarray is -> 
     M_OVarray (List.map (n_lv loc) is)
  | OVstruct (sym1, is) -> 
     M_OVstruct (sym1, List.map (fun (id,ct,mv) -> (id,convert_ct loc ct,mv)) is)
  | OVunion (sym1, id1, mv) -> 
     M_OVunion (sym1, id1, mv)

and n_lv loc v =
  match v with
  | LVspecified ov -> 
     n_ov loc ov
  | LVunspecified ct1 -> 
     assert_error loc (!^"core_anormalisation: LVunspecified")


and n_val loc = function
  | Vobject ov -> M_Vobject (n_ov loc ov)
  | Vloaded lv -> M_Vobject (n_lv loc lv)
  | Vunit -> M_Vunit
  | Vtrue -> M_Vtrue
  | Vfalse -> M_Vfalse
  | Vctype _ct -> assert_error loc (!^"core_anormalisation: Vctype")
  | Vlist (cbt, vs) -> M_Vlist (convert_bt loc cbt, List.map (n_val loc) vs)
  | Vtuple vs -> M_Vtuple (List.map (n_val loc) vs)


let unit_pat loc annots = 
  M_Pattern (loc, annots, M_CaseBase (None, BT.Unit))



let rec n_pexpr loc (Pexpr (annots, bty, pe)) : mu_pexpr =
  let loc = Loc.update loc (get_loc_ annots) in
  let annotate pe = M_Pexpr (loc, annots, bty, pe) in
  match pe with
  | PEsym sym1 -> 
     annotate (M_PEsym sym1)
  | PEimpl i -> 
     assert_error loc (!^"PEimpl not inlined")
  | PEval v -> 
     annotate (M_PEval (n_val loc v))
  | PEconstrained l -> 
     let l = List.map (fun (c, e) -> (c, n_pexpr loc e)) l in
     annotate (M_PEconstrained l)
  | PEundef(l, u) -> 
     annotate (M_PEundef (l, u))
  | PEerror(err, e') ->
     annotate (M_PEerror (err, n_pexpr loc e'))
  | PEctor(ctor, args) ->
     begin match ctor, args with
     | Core.CivCOMPL, [ct; arg1] -> 
        let ct = ensure_pexpr_ctype loc !^"CivCOMPL: first argument not a ctype" ct in
        let arg1 = n_pexpr loc arg1 in
        annotate (M_CivCOMPL (ct, arg1))
     | Core.CivCOMPL, _ -> 
        assert_error loc !^"CivCOMPL applied to wrong number of arguments"
     | Core.CivAND, [ct; arg1; arg2] -> 
        let ct = ensure_pexpr_ctype loc !^"CivAND: first argument not a ctype" ct in
        let arg1 = n_pexpr loc arg1 in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_CivAND (ct, arg1, arg2))
     | Core.CivAND, _ ->
        assert_error loc !^"CivAND applied to wrong number of arguments"
     | Core.CivOR, [ct; arg1; arg2] -> 
        let ct = ensure_pexpr_ctype loc !^"CivOR: first argument not a ctype" ct in
        let arg1 = n_pexpr loc arg1 in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_CivOR (ct, arg1, arg2))
     | Core.CivOR, _ ->
        assert_error loc !^"CivOR applied to wrong number of arguments"
     | Core.CivXOR, [ct; arg1; arg2] -> 
        let ct = ensure_pexpr_ctype loc !^"CivXOR: first argument not a ctype" ct in
        let arg1 = n_pexpr loc arg1 in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_CivXOR (ct, arg1, arg2))
     | Core.CivXOR, _ ->
        assert_error loc !^"CivXOR applied to wrong number of arguments"
     | Core.Cfvfromint, [arg1] -> 
        let arg1 = n_pexpr loc arg1 in
        annotate (M_Cfvfromint arg1)
     | Core.Cfvfromint, _ ->
        assert_error loc !^"Cfvfromint applied to wrong number of arguments"
     | Core.Civfromfloat, [ct; arg1] -> 
        let ct = ensure_pexpr_ctype loc !^"Civfromfloat: first argument not a ctype" ct in
        let arg1 = n_pexpr loc arg1 in
        annotate (M_Civfromfloat(ct, arg1))
     | Core.Civfromfloat, _ ->
        assert_error loc !^"Civfromfloat applied to wrong number of arguments"
     | Core.Cnil bt1, _ -> 
        annotate (M_PEctor (M_Cnil (convert_bt loc bt1), 
                            List.map (n_pexpr loc) args))
     | Core.Ccons, _ ->
        annotate (M_PEctor (M_Ccons, List.map (n_pexpr loc) args))
     | Core.Ctuple, _ -> 
        annotate (M_PEctor (M_Ctuple, List.map (n_pexpr loc) args))
     | Core.Carray, _ -> 
        annotate (M_PEctor (M_Carray, List.map (n_pexpr loc) args))
     | Core.Cspecified, _ -> 
        n_pexpr loc (List.hd args)
     | _ -> 
        assert_error loc (!^"core_to_mucore: unsupported ctor application")
     end
  | PEcase(e', pats_pes) ->
     assert_error loc !^"PEcase"
  | PEarray_shift(e', ct, e'') ->
     let e' = n_pexpr loc e' in
     let e'' = n_pexpr loc e'' in
     annotate (M_PEarray_shift(e', convert_ct loc ct, e''))
  | PEmember_shift(e', sym1, id1) ->
     let e' = n_pexpr loc e' in
     annotate (M_PEmember_shift(e', sym1, id1))
  | PEnot e' -> 
     let e' = n_pexpr loc e' in
     annotate (M_PEnot e')
  | PEop(binop1, e', e'') ->
     let e' = n_pexpr loc e' in
     let e'' = n_pexpr loc e'' in
     annotate (M_PEop(binop1, e', e''))
  | PEstruct(sym1, fields) ->
     let fields = List.map (fun (m, e) -> (m, n_pexpr loc e)) fields in
     annotate (M_PEstruct(sym1, fields))
  | PEunion(sym1, id1, e') ->
     let e' = n_pexpr loc e' in
     annotate (M_PEunion(sym1, id1, e'))
  | PEcfunction e' ->
     let e' = n_pexpr loc e' in
     annotate (M_PEcfunction e')
     (* let err = Errors.UNSUPPORTED "function pointers" in *)
     (*   Pp_errors.fatal (Pp_errors.to_string (loc, err));  *)
  | PEmemberof(sym1, id1, e') ->
     let e' = n_pexpr loc e' in
     annotate (M_PEmemberof(sym1, id1, e'))
  | PEcall(sym1, args) ->
     begin match sym1, args with
     | Sym (Symbol (_, _, SD_Id "conv_int")), 
       [arg1;arg2] ->
        let ct = (ensure_pexpr_ctype loc !^"PEcall(conv_int,_): not a ctype" arg1) in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_PEconv_int(ct, arg2))
     | Sym (Symbol (_, _, SD_Id "conv_loaded_int")), 
       [arg1;arg2] ->
        let ct = (ensure_pexpr_ctype loc !^"PEcall(conv_loaded_int,_): not a ctype" arg1) in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_PEconv_loaded_int(ct, arg2))
     | Sym (Symbol (_, _, SD_Id "wrapI")), 
       [arg1;arg2] ->
        let ct = (ensure_pexpr_ctype loc !^"PEcall(wrapI,_): not a ctype" arg1) in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_PEwrapI(ct, arg2))
     | Sym (Symbol (_, _, SD_Id "catch_exceptional_condition")),
       [arg1; arg2] ->
        let ct = ensure_pexpr_ctype loc !^"PEcall(catch_exceptional_condition,_): not a ctype" arg1 in
        let arg2 = n_pexpr loc arg2 in
        annotate (M_PEcatch_exceptional_condition(ct, arg2))
     | Sym (Symbol (_, _, SD_Id "is_representable_integer")),
       [arg1; arg2] ->
        let arg1 = n_pexpr loc arg1 in
        let ct = ensure_pexpr_ctype loc !^"PEcall(is_representable_integer,_): not a ctype" arg2 in
        annotate (M_PEis_representable_integer(arg1, ct))
     | Sym sym, _ ->
        assert_error loc (!^"PEcall not inlined:" ^^^ Sym.pp sym)
     | Impl impl, _ ->
        assert_error loc (!^"PEcall not inlined:" ^^^ !^(Implementation.string_of_implementation_constant impl))
     end
  | PElet(pat, e', e'') ->
     begin match pat, e' with
     | Pattern (annots, CaseBase (Some sym, _)), 
       Pexpr (annots2, _, PEsym sym2) 
     | Pattern (annots, CaseCtor (Cspecified, [Pattern (_, CaseBase (Some sym, _))])), 
       Pexpr (annots2, _, PEsym sym2) 
       ->
        let e'' = Core_peval.subst_sym_pexpr2 sym 
                    (get_loc annots2, `SYM sym2) e'' in
        n_pexpr loc e''


     | Pattern (annots, CaseCtor (Ctuple, [Pattern (_, CaseBase (Some sym, _));
                                           Pattern (_, CaseBase (Some sym', _))])), 
       Pexpr (annots2, _, PEctor (Ctuple, [Pexpr (_, _, PEsym sym2);
                                           Pexpr (_, _, PEsym sym2')]))
     | Pattern (annots, CaseCtor (Ctuple, [Pattern (_, CaseCtor (Cspecified, [Pattern (_, CaseBase (Some sym, _))]));
                                           Pattern (_, CaseCtor (Cspecified, [Pattern (_, CaseBase (Some sym', _))]))])), 
       Pexpr (annots2, _, PEctor (Ctuple, [Pexpr (_, _, PEsym sym2);
                                           Pexpr (_, _, PEsym sym2')]))
       (* pairwise disjoint *)
       when (List.length (List.sort_uniq Sym.compare [sym; sym'; sym2; sym2']) = 4) ->
        let e'' = Core_peval.subst_sym_pexpr2 sym 
                   (get_loc annots2, `SYM sym2) e'' in
        let e'' = Core_peval.subst_sym_pexpr2 sym' 
                   (get_loc annots2, `SYM sym2') e'' in
        n_pexpr loc e''



     | _ ->
        let pat = core_to_mu__pattern loc pat in
        let e' = n_pexpr loc e' in
        let e'' = n_pexpr loc e'' in
        annotate (M_PElet (M_Pat pat, e', e''))
     end
  | PEif(e1, e2, e3) ->
     begin match e2, e3 with
     | Pexpr (_, _, PEval (Vloaded (LVspecified (OVinteger iv1)))), 
       Pexpr (_, _, PEval (Vloaded (LVspecified (OVinteger iv2))))
          when Option.equal Z.equal (Mem.eval_integer_value iv1) (Some Z.one) &&
               Option.equal Z.equal (Mem.eval_integer_value iv2) (Some Z.zero)
       ->
        let e1 = n_pexpr loc e1 in
        annotate (M_PEbool_to_integer e1)
     (* this should go away *)
     | Pexpr (_, _, PEval Vtrue), Pexpr (_, _, PEval Vfalse) ->
        n_pexpr loc e1
     | _ ->
        let e1 = n_pexpr loc e1 in
        let e2 = n_pexpr loc e2 in
        let e3 = n_pexpr loc e3 in
        annotate (M_PEif (e1, e2, e3))
     end
  | PEis_scalar e' ->
     assert_error loc !^"core_anormalisation: PEis_scalar"
  | PEis_integer e' ->
     assert_error loc !^"core_anormalisation: PEis_integer"
  | PEis_signed e' ->
     assert_error loc !^"core_anormalisation: PEis_signed"
  | PEis_unsigned e' ->
     assert_error loc !^"core_anormalisation: PEis_unsigned"
  | PEbmc_assume e' ->
     assert_error loc !^"core_anormalisation: PEbmc_assume"
  | PEare_compatible(e', e'') ->
     assert_error loc !^"core_anormalisation: PEare_compatible"




let n_kill_kind loc = function
  | Dynamic -> M_Dynamic
  | Static0 ct -> M_Static (convert_ct loc ct)


let n_action loc action =
  let (Action (loc', _, a1)) = action in
  let loc = Loc.update loc loc' in
  let wrap a1 = M_Action(loc, a1) in
  match a1 with
  | Create(e1, e2, sym1) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"Create: not a ctype" e2) in
     let e1 = n_pexpr loc e1 in
     wrap (M_Create(e1, ctype1, sym1))
  | CreateReadOnly(e1, e2, e3, sym1) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"CreateReadOnly: not a ctype" e1) in
     let e1 = n_pexpr loc e1 in
     let e3 = n_pexpr loc e3 in
     wrap (M_CreateReadOnly(e1, ctype1, e3, sym1))
  | Alloc0(e1, e2, sym1) ->
     let e1 = n_pexpr loc e1 in
     let e2 = n_pexpr loc e2 in
     wrap (M_Alloc(e1, e2, sym1))
  | Kill(kind, e1) ->
     let e1 = n_pexpr loc e1 in
     wrap (M_Kill((n_kill_kind loc kind), e1))
  | Store0(b, e1, e2, e3, mo1) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"Store: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     let e3 = n_pexpr loc e3 in
     wrap (M_Store(b, ctype1, e2, e3, mo1))
  | Load0(e1, e2, mo1) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"Load: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     wrap (M_Load(ctype1, e2, mo1))
  | SeqRMW (b, e1, e2, sym, e3) ->
      assert_error loc !^"TODO: SeqRMW"
(*
     let ctype1 = (ensure_pexpr_ctype loc !^"SeqRMW: not a ctype" e1) in
     n_pexpr_in_expr_name e2 (fun e2 ->
     n_pexpr_in_expr_name e3 (fun e3 ->
     k (wrap (M_SeqRMW(ctype1, e2, sym, e3)))))
*)
  | RMW0(e1, e2, e3, e4, mo1, mo2) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"RMW: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     let e3 = n_pexpr loc e3 in
     let e4 = n_pexpr loc e4 in
     wrap (M_RMW(ctype1, e2, e3, e4, mo1, mo2))
  | Fence0 mo1 -> 
     wrap (M_Fence mo1)
  | CompareExchangeStrong(e1, e2, e3, e4, mo1, mo2) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"CompareExchangeStrong: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     let e3 = n_pexpr loc e3 in
     let e4 = n_pexpr loc e4 in
     wrap (M_CompareExchangeStrong(ctype1, e2, e3, e4, mo1, mo2))
  | CompareExchangeWeak(e1, e2, e3, e4, mo1, mo2) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"CompareExchangeWeak: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     let e3 = n_pexpr loc e3 in
     let e4 = n_pexpr loc e4 in
     wrap (M_CompareExchangeWeak(ctype1, e2, e3, e4, mo1, mo2))
  | LinuxFence lmo ->
     wrap (M_LinuxFence lmo)
  | LinuxLoad(e1, e2, lmo) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"LinuxLoad: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     wrap (M_LinuxLoad(ctype1, e2, lmo))
  | LinuxStore(e1, e2, e3, lmo) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"LinuxStore: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     let e3 = n_pexpr loc e3 in
     wrap (M_LinuxStore(ctype1, e2, e3, lmo))
  | LinuxRMW(e1, e2, e3, lmo) ->
     let ctype1 = (ensure_pexpr_ctype loc !^"LinuxRMW: not a ctype" e1) in
     let e2 = n_pexpr loc e2 in
     let e3 = n_pexpr loc e3 in
     wrap (M_LinuxRMW(ctype1, e2, e3, lmo))

     

let n_paction loc (Paction(pol, a)) = 
  M_Paction (pol, n_action loc a)





let show_n_memop = 
  Mem_common.instance_Show_Show_Mem_common_memop_dict.show_method

let n_memop loc memop pexprs =
  match (memop, pexprs) with
  | (Mem_common.PtrEq, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrEq (pe1, pe2)
  | (Mem_common.PtrNe, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrNe (pe1, pe2)
  | (Mem_common.PtrLt, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrLt (pe1, pe2)
  | (Mem_common.PtrGt, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrGt (pe1, pe2)
  | (Mem_common.PtrLe, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrLe (pe1, pe2)
  | (Mem_common.PtrGe, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrGe (pe1, pe2)
  | (Mem_common.Ptrdiff, [ct1;pe1;pe2]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"Ptrdiff: not a ctype" ct1) in
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_Ptrdiff (ct1, pe1, pe2)
  | (Mem_common.IntFromPtr, [ct1;ct2;pe]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"IntFromPtr: not a ctype" ct1) in
     let ct2 = (ensure_pexpr_ctype loc !^"IntFromPtr: not a ctype" ct2) in
     let pe = n_pexpr loc pe in
     M_IntFromPtr (ct1, ct2, pe)
  | (Mem_common.PtrFromInt, [ct1;ct2;pe]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"PtrFromInt: not a ctype" ct1) in
     let ct2 = (ensure_pexpr_ctype loc !^"PtrFromInt: not a ctype" ct2) in
     let pe = n_pexpr loc pe in
     M_PtrFromInt (ct1, ct2, pe)
  | (Mem_common.PtrValidForDeref, [ct1;pe]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"PtrValidForDeref: not a ctype" ct1) in
     let pe = n_pexpr loc pe in
     M_PtrValidForDeref (ct1, pe)
  | (Mem_common.PtrWellAligned, [ct1;pe]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"PtrWellAligned: not a ctype" ct1) in
     let pe = n_pexpr loc pe in
     M_PtrWellAligned (ct1, pe)
  | (Mem_common.PtrArrayShift, [pe1;ct1;pe2]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"PtrArrayShift: not a ctype" ct1) in
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_PtrArrayShift (pe1 ,ct1, pe2)
  | (Mem_common.Memcpy, [pe1;pe2;pe3]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     let pe3 = n_pexpr loc pe3 in
     M_Memcpy (pe1 ,pe2, pe3)
  | (Mem_common.Memcmp, [pe1;pe2;pe3]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     let pe3 = n_pexpr loc pe3 in
     M_Memcmp (pe1 ,pe2, pe3)
  | (Mem_common.Realloc, [pe1;pe2;pe3]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     let pe3 = n_pexpr loc pe3 in
     M_Realloc (pe1 ,pe2, pe3)
  | (Mem_common.Va_start, [pe1;pe2]) ->
     let pe1 = n_pexpr loc pe1 in
     let pe2 = n_pexpr loc pe2 in
     M_Va_start (pe1 ,pe2)
  | (Mem_common.Va_copy, [pe]) ->
     let pe = n_pexpr loc pe in
     M_Va_copy pe
  | (Mem_common.Va_arg, [pe;ct1]) ->
     let ct1 = (ensure_pexpr_ctype loc !^"Va_arg: not a ctype" ct1) in
     let pe = n_pexpr loc pe in
     M_Va_arg (pe ,ct1)
  | (Mem_common.Va_end, [pe]) ->
     let pe = n_pexpr loc pe in
     M_Va_end pe
  | (memop, pexprs1) ->
     let err = 
       !^(show_n_memop memop)
       ^^^ !^"applied to" 
       ^^^ Print.int (List.length pexprs1) 
       ^^^ !^"arguments"
     in
     assert_error loc err



let rec n_expr (loc : Loc.t) e : mu_expr = 
  let (Expr (annots, pe)) = e in
  let loc = Loc.update loc (get_loc_ annots) in
  let wrap pe = M_Expr (loc, annots, pe) in
  let n_pexpr = n_pexpr loc in
  let n_paction = (n_paction loc) in
  let n_memop = (n_memop loc) in
  let n_expr = (n_expr loc) in
  match pe with
  | Epure pexpr2 -> 
     wrap (M_Epure (n_pexpr pexpr2))
  | Ememop(memop1, pexprs1) -> 
     wrap (M_Ememop (n_memop memop1 pexprs1))
  | Eaction paction2 ->
     wrap (M_Eaction (n_paction paction2))
  | Ecase(pexpr, pats_es) ->
     assert_error loc !^"Ecase"
     (* let pexpr = n_pexpr pexpr in *)
     (* let pats_es =  *)
     (*   (map (fun (pat,e) ->  *)
     (*       let pat = core_to_mu__pattern loc pat in *)
     (*       let pe = (n_expr e k) in *)
     (*       (pat, pe) *)
     (*    )  *)
     (*     pats_es)  *)
     (* in *)
     (* twrap (M_Ecase(pexpr, pats_es)) *)
  | Elet(pat, e1, e2) ->
     begin match pat, e1 with
     | Pattern (annots, CaseBase (Some sym, _)),
       Pexpr (annots2, _, PEsym sym2) 
     | Pattern (annots, CaseCtor (Cspecified, [Pattern (_, CaseBase (Some sym, _))])), 
       Pexpr (annots2, _, PEsym sym2) 
       ->
        let e2 = Core_peval.subst_sym_expr2 sym 
                   (get_loc annots2, `SYM sym2) e2 in
        n_expr e2
     | Pattern (annots, CaseCtor (Ctuple, [Pattern (_, CaseBase (Some sym, _));
                                           Pattern (_, CaseBase (Some sym', _))])), 
       Pexpr (annots2, _, PEctor (Ctuple, [Pexpr (_, _, PEsym sym2);
                                           Pexpr (_, _, PEsym sym2')]))
     | Pattern (annots, CaseCtor (Ctuple, [Pattern (_, CaseCtor (Cspecified, [Pattern (_, CaseBase (Some sym, _))]));
                                           Pattern (_, CaseCtor (Cspecified, [Pattern (_, CaseBase (Some sym', _))]))])), 
       Pexpr (annots2, _, PEctor (Ctuple, [Pexpr (_, _, PEsym sym2);
                                           Pexpr (_, _, PEsym sym2')]))
       (* pairwise disjoint *)
       when (List.length (List.sort_uniq Sym.compare [sym; sym'; sym2; sym2']) = 4) ->
        let e2 = Core_peval.subst_sym_expr2 sym 
                   (get_loc annots2, `SYM sym2) e2 in
        let e2 = Core_peval.subst_sym_expr2 sym' 
                   (get_loc annots2, `SYM sym2') e2 in
        n_expr e2

     | _ ->
        let e1 = n_pexpr e1 in
        let pat = core_to_mu__pattern loc pat in
        let e2 = n_expr e2 in
        wrap (M_Elet(M_Pat pat, e1, e2))
     end
  | Eif(e1, e2, e3) ->
     begin match e2, e3 with
     | Expr (_, Epure (Pexpr (_, _, PEval (Vloaded (LVspecified (OVinteger iv1)))))), 
       Expr (_, Epure (Pexpr (_, _, PEval (Vloaded (LVspecified (OVinteger iv2))))))
          when Option.equal Z.equal (Mem.eval_integer_value iv1) (Some Z.one) &&
                 Option.equal Z.equal (Mem.eval_integer_value iv2) (Some Z.zero)
       ->
        let e1 = n_pexpr e1 in
        wrap (M_Epure (M_Pexpr (loc, [], (), M_PEbool_to_integer e1)))
     | Expr (_, Epure (Pexpr (_, _, PEval Vtrue))), 
       Expr (_, Epure (Pexpr (_, _, PEval Vfalse))) ->
        let e1 = n_pexpr e1 in
        wrap (M_Epure e1)
     | _ ->
        let e1 = n_pexpr e1 in
        let e2 = n_expr e2 in
        let e3 = n_expr e3 in
        wrap (M_Eif(e1, e2, e3))
     end
  | Eccall(_a, ct1, e2, es) ->
     let ct1 = match ct1 with
       | Core.Pexpr(annot, bty, Core.PEval (Core.Vctype ct1)) -> 
          let loc = Loc.update loc (get_loc_ annots) in
          {loc; annot; type_annot = bty; ct = convert_ct loc ct1}
       | _ -> 
          assert_error loc !^"core_anormalisation: Eccall with non-ctype first argument"
     in
     let e2 = 
       let err () = Tools.unsupported loc !^"function pointers" in
       match e2 with
       | Core.Pexpr(annots, bty, Core.PEval v) ->
          begin match v with
          | Vobject (OVpointer ptrval)
          | Vloaded (LVspecified (OVpointer ptrval)) ->
             Impl_mem.case_ptrval ptrval
               ( fun ct -> err ())
               ( fun sym -> M_Pexpr (loc, annots, bty, (M_PEsym sym)) )
               ( fun _prov _ -> err () )
          | _ -> err ()
          end
       | _ -> err ()
     in
     let es = List.map n_pexpr es in
     wrap (M_Eccall(ct1, e2, es))
  | Eproc(_a, name1, es) ->
     assert_error loc !^"Eproc"
  | Eunseq es ->
     let es = List.map n_expr es in
     wrap (M_Eunseq es)
  | Ewseq(pat, e1, e2) ->
     let e1 = n_expr e1 in
     let pat = core_to_mu__pattern loc pat in
     let e2 = n_expr e2 in
     wrap (M_Ewseq(pat, e1, e2))
  | Esseq(pat, e1, e2) ->
     let e1 = n_expr e1 in
     let pat = core_to_mu__pattern loc pat in
     let e2 = n_expr e2 in
     wrap (M_Esseq(pat, e1, e2))
  | Ebound e ->
     wrap (M_Ebound (n_expr e))
  | End es ->
     let es = List.map n_expr es in
     wrap (M_End es)
  | Esave((sym1,bt1), syms_typs_pes, e) ->  
     assert_error loc !^"core_anormalisation: Esave"
  | Erun(_a, sym1, pes) ->
     let pes = List.map n_pexpr pes in
     wrap (M_Erun(sym1, pes))
  | Epar es -> 
     assert_error loc !^"core_anormalisation: Epar"
  | Ewait tid1 ->
     assert_error loc !^"core_anormalisation: Ewait"
  | Epack(id, pes) ->
     let pes = List.map n_pexpr pes in
     wrap (M_Erpredicate(Pack, id, pes))
  | Eunpack(id, pes) ->
     let pes = List.map n_pexpr pes in
     wrap (M_Erpredicate(Unpack, id, pes))
  | Ehave(id, pes) ->
     let pes = List.map n_pexpr pes in
     wrap (M_Elpredicate(Have, id, pes))
  | Eshow(id, pes) ->
     let pes = List.map n_pexpr pes in
     wrap (M_Elpredicate(Show, id, pes))
  | Einstantiate (id, pe) ->
     let pe = n_pexpr pe in
     wrap (M_Einstantiate (id, pe))
  | Eannot _ ->
      assert_error loc !^"core_anormalisation: Eannot"
  | Eexcluded _ ->
      assert_error loc !^"core_anormalisation: Eexcluded"







module RT = ReturnTypes
module AT = ArgumentTypes
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes

let rec lat_of_arguments f_i = function
  | M_Define (bound, info, l) ->
     LAT.Define (bound, info, lat_of_arguments f_i l)
  | M_Resource (bound, info, l) ->
     LAT.Resource (bound, info, lat_of_arguments f_i l)
  | M_Constraint (lc, info, l) ->
     LAT.Constraint (lc, info, lat_of_arguments f_i l)
  | M_I i ->
     LAT.I (f_i i)

let rec at_of_arguments f_i = function
  | M_Computational (bound, info, a) ->
     AT.Computational (bound, info, at_of_arguments f_i a)
  | M_L l ->
     AT.L (lat_of_arguments f_i l)





open Resultat
open Effectful.Make(Resultat)
open AilSyntax
module IT = IndexTerms



(* copying and adjusting variously compile.ml logic *)

let fetch_ail_env_id (ail_env : AilSyntax.identifier_env) loc x =
  match Pmap.lookup x ail_env with
  | Some (Some (_, sym)) -> return sym
  | Some None -> fail {loc; msg = Generic
    (Print.item "C identifier has null details" (Id.pp x))}
  | None -> fail {loc; msg = Generic
    (Print.item "C identifier unknown" (Id.pp x))}

let desugar_access ail_env globs (loc, id) =
  let@ s = fetch_ail_env_id ail_env loc id in
  let@ ct = match List.assoc_opt Sym.equal s globs with
    | Some (M_GlobalDef ((_, ct), _)) -> return ct
    | Some (M_GlobalDecl ((_, ct))) -> return ct
    | None -> fail {loc; msg = Generic (Sym.pp s ^^^ !^"is not a global") }
  in
  let ct = Sctypes.to_ctype ct in
  return (loc, (s, ct))

let ownership (loc, (addr_s, ct)) env =
  let name = match Sym.description addr_s with
    | SD_ObjectAddress obj_name -> 
       Sym.fresh_make_uniq ("O_"^obj_name)
    | _ -> assert false
  in
  let resource = CN_pred (loc, CN_owned (Some ct), [CNExpr (loc, CNExpr_var addr_s)]) in

  let@ (pt_ret, oa_bt), lcs = 
    C.translate_cn_let_resource env (loc, name, resource) in
  let value = 
    let ct = convert_ct loc ct in
    IT.recordMember_ 
      ~member_bt:(SBT.of_sct ct)
      (IT.sym_ (name, oa_bt), Resources.value_sym)
  in
  return (name, ((pt_ret, oa_bt), lcs), value)



  (* Cn.CN_cletResource (loc, os, pred)) *)

(* let translate_accesses ail_env globs accesses requires ensures = *)
(*   let@ ownerships = ListM.mapM (fun (loc, id) -> *)
(*        return (ownership loc s ct) *)
(*   ) accesses in *)
(*   let (var_vals, preds) = List.split ownerships in *)
(*   return (var_vals, preds @ requires, preds @ ensures) *)




let rec make_lrt env = function
  | ((loc, (addr_s, ct)) :: accesses, ensures) ->
     let@ (name, ((pt_ret, oa_bt), lcs), value) = ownership (loc, (addr_s, ct)) env in
     let env = C.add_logical name oa_bt env in
     let env = C.add_c_variable_state addr_s (CVS_Pointer_pointing_to value) env in
     let@ lrt = make_lrt env (accesses, ensures) in
     return (LRT.mResource ((name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None)) 
            (LRT.mConstraints lcs lrt))
  | ([], Cn.CN_cletResource (loc, name, resource) :: ensures) -> 
     let@ (pt_ret, oa_bt), lcs = 
       C.translate_cn_let_resource env (loc, name, resource) in
     let env = C.add_logical name oa_bt env in
     let@ lrt = make_lrt env ([], ensures) in
     return (LRT.mResource ((name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None)) 
            (LRT.mConstraints lcs lrt))
  | ([], Cn.CN_cletExpr (loc, name, expr) :: ensures) ->
     let@ expr = C.translate_cn_expr env expr in
     let@ lrt = make_lrt (C.add_logical name (IT.bt expr) env) ([], ensures) in
     return (LRT.mDefine (name, IT.term_of_sterm expr, (loc, None)) lrt)
  | ([], Cn.CN_cconstr (loc, constr) :: ensures) ->
     let@ lc = C.translate_cn_assrt env (loc, constr) in
     let@ lrt = make_lrt env ([], ensures) in
     return (LRT.mConstraint (lc, (loc, None)) lrt)
  | ([], []) -> 
     return LRT.I

let make_rt (loc : loc) (env : C.env) (s, ct) (accesses, ensures) =
  let ct = convert_ct loc ct in
  let sbt = SBT.of_sct ct in
  let bt = SBT.to_basetype sbt in
  let@ lrt = make_lrt (C.add_computational s sbt env) (accesses, ensures) in
  let info = (loc, Some "return value good") in
  let lrt = LRT.mConstraint (LC.t_ (IT.good_ (ct, IT.sym_ (s, bt))), info) lrt in
  return (RT.mComputational ((s, bt), (loc, None)) lrt)


let make_largs f_i =
  let rec aux env = function
    | ((loc, (addr_s, ct)) :: accesses, requires) ->
       let@ (name, ((pt_ret, oa_bt), lcs), value) = ownership (loc, (addr_s, ct)) env in
       let env = C.add_logical name oa_bt env in
       let env = C.add_c_variable_state addr_s (CVS_Pointer_pointing_to value) env in
       let@ lat = aux env (accesses, requires) in
       return (Mu.mResource ((name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None)) 
              (Mu.mConstraints lcs lat))
    | ([], Cn.CN_cletResource (loc, name, resource) :: requires) -> 
       let@ (pt_ret, oa_bt), lcs = 
         C.translate_cn_let_resource env (loc, name, resource) in
       let env = C.add_logical name oa_bt env in
       let@ lat = aux env ([], requires) in
       return (Mu.mResource ((name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None)) 
                 (Mu.mConstraints lcs lat))
    | ([], Cn.CN_cletExpr (loc, name, expr) :: requires) ->
       let@ expr = C.translate_cn_expr env expr in
       let@ lat = aux (C.add_logical name (IT.bt expr) env) ([], requires) in
       return (Mu.mDefine ((name, IT.term_of_sterm expr), (loc, None)) lat)
    | ([], Cn.CN_cconstr (loc, constr) :: requires) ->
       let@ lc = C.translate_cn_assrt env (loc, constr) in
       let@ lat = aux env ([], requires) in
       return (Mu.mConstraint (lc, (loc, None)) lat)
    | ([], []) ->
       let@ i = f_i env in
       return (M_I i)
  in
  aux


let is_pass_by_pointer = function
  | By_pointer -> true
  | By_value -> false


let make_label_args f_i loc env args (accesses, inv) =
  let rec aux (resources, good_lcs) env = function
    | ((o_s, (ct, pass_by_value_or_pointer)), (s, bt)) :: rest ->
       assert (Option.equal Sym.equal o_s (Some s));
       assert (BT.equal (convert_bt loc bt) Loc);
       assert (is_pass_by_pointer pass_by_value_or_pointer);
       (* now interesting only: s, ct, rest *)
       let sct = convert_ct loc ct in
       let p_sbt = SBT.Loc (Some sct) in
       let env = C.add_computational s p_sbt env in
       let good_pointer_lc = 
         let info = (loc, Some (Sym.pp_string s ^ " good")) in
         (LC.t_ (IT.good_ (Pointer sct, IT.sym_ (s, BT.Loc))), info)
       in
       let@ (oa_name, ((pt_ret, oa_bt), lcs), value) = ownership (loc, (s, ct)) env in
       let env = C.add_logical oa_name oa_bt env in
       let env = C.add_c_variable_state s (CVS_Pointer_pointing_to value) env in
       let resource = ((oa_name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None)) in
       let@ at = 
         aux (resources @ [resource], 
              good_lcs @ good_pointer_lc :: lcs) 
           env rest 
       in
       return (Mu.mComputational ((s, Loc), (loc, None)) at)
    | [] -> 
       let@ lat = make_largs f_i env (accesses, inv) in
       let at = Mu.mResources resources (Mu.mConstraints good_lcs lat) in
       return (M_L at)
  in
  aux ([],[]) env args




let make_function_args f_i loc env args (accesses, requires) =
  let rec aux good_lcs env = function
    | ((mut_arg, (mut_arg', ct)), (pure_arg, bt)) :: rest ->
       assert (Option.equal Sym.equal (Some mut_arg) mut_arg');
       let ct = convert_ct loc ct in
       let sbt = SBT.of_sct ct in
       let bt = convert_bt loc bt in
       assert (BT.equal bt (SBT.to_basetype sbt));
       let env = C.add_computational pure_arg sbt env in
       let env = C.add_c_variable_state mut_arg 
                   (CVS_Value (IT.sym_ (pure_arg, sbt))) env in
       let good_lc = 
         let info = (loc, Some (Sym.pp_string pure_arg ^ " good")) in
         (LC.t_ (IT.good_ (ct, IT.sym_ (pure_arg, bt))), info)
       in
       let@ at = aux (good_lc :: good_lcs) env rest in
       return (Mu.mComputational ((pure_arg, bt), (loc, None)) at)
    | [] -> 
       let@ lat = make_largs f_i env (accesses, requires) in
       return (M_L (Mu.mConstraints (List.rev good_lcs) lat))
  in
  aux [] env args


let do_ail_desugar_op desugar_state f =
  match f desugar_state with
    | Exception.Result (x, st2) -> return (x, st2)
    | Exception.Exception (loc, msg) ->
      fail {loc; msg = Generic (Print.item "desugaring exception"
          (Print.string (Pp_errors.short_message msg)))}

let do_ail_desugar_rdonly desugar_state f =
  let@ (x, _) = do_ail_desugar_op desugar_state f in
  return x

let register_new_cn_local id d_st =
  do_ail_desugar_op d_st (Cabs_to_ail.register_additional_cn_var id)

let desugar_cond d_st = function
  | Cn.CN_cletResource (loc, id, res) ->
    Print.debug 6 (lazy (Print.typ (Print.string "desugaring a let-resource at") (Locations.pp loc)));
    let@ res = do_ail_desugar_rdonly d_st (Cabs_to_ail.desugar_cn_resource res) in
    let@ (sym, d_st) = register_new_cn_local id d_st in
    return (Cn.CN_cletResource (loc, sym, res), d_st)
  | Cn.CN_cletExpr (loc, id, expr) ->
    Print.debug 6 (lazy (Print.typ (Print.string "desugaring a let-expr at") (Locations.pp loc)));
    let@ expr = do_ail_desugar_rdonly d_st (Cabs_to_ail.desugar_cn_expr expr) in
    let@ (sym, d_st) = register_new_cn_local id d_st in
    return (Cn.CN_cletExpr (loc, sym, expr), d_st)
  | Cn.CN_cconstr (loc, constr) ->
    Print.debug 6 (lazy (Print.typ (Print.string "desugaring a constraint at") (Locations.pp loc)));
    let@ constr = do_ail_desugar_rdonly d_st (Cabs_to_ail.desugar_cn_assertion constr) in
    return (Cn.CN_cconstr (loc, constr), d_st)

let desugar_conds d_st conds =
  let@ (conds, d_st) = ListM.fold_leftM (fun (conds, d_st) cond ->
    let@ (cond, d_st) = desugar_cond d_st cond in
    return (cond :: conds, d_st)) ([], d_st) conds in
  return (List.rev conds, d_st)



let normalise_label (accesses, loop_attributes) (env : C.env) d_st label_name label =
  match label with
  | Mi_Return loc -> 
     return (M_Return loc)
  | Mi_Label (loc, lt, label_args, label_body, annots) ->
     let env = C.remove_c_variable_state env in
     begin match Cerb_frontend.Annot.get_label_annot annots with
     | Some (LAloop_prebody loop_id) ->
        let@ inv = match Pmap.lookup loop_id loop_attributes with
          | Some (_, attrs) -> Parse.parse_inv_spec attrs 
          | None -> return []
        in
        (* Print.debug 6 (lazy (Print.string ("normalising loop invs"))); *)
        (* FIXME: find correct marker and set the appropriate c env *)
        let@ (inv, _) = desugar_conds d_st inv in
        let@ label_args_and_body =
          make_label_args (fun env ->
              return (n_expr loc label_body)
            ) 
            loc 
            env 
            (List.combine lt label_args) 
            (accesses, inv)
        in
        let lt = 
          at_of_arguments (fun _body ->
              False.False
            ) label_args_and_body 
        in
        return (M_Label (loc, label_args_and_body, lt, annots))
     | Some (LAloop_body loop_id) ->
        assert_error loc !^"body label has not been inlined"
     | Some (LAloop_continue loop_id) ->
        assert_error loc !^"continue label has not been inlined"
     | Some (LAloop_break loop_id) ->
        assert_error loc !^"break label has not been inlined"
     | Some LAreturn -> 
        assert_error loc !^"return label has not been inlined"
     | Some LAswitch -> 
        assert_error loc !^"switch labels"
     | Some LAcase -> 
        assert_error loc !^"case label has not been inlined"
     | Some LAdefault -> 
        assert_error loc !^"default label has not been inlined"
     | None -> 
        assert_error loc !^"non-loop labels"
     end





let normalise_fun_map_decl ail_prog env globals d_st (funinfo: mi_funinfo) loop_attributes fname decl =
  match Pmap.lookup fname funinfo with
  | None -> return None
  | Some (loc, attrs, ret_ct, arg_cts, variadic, _) ->
  if variadic then Tools.unsupported loc !^"variadic functions";
  match decl with
  | Mi_Fun (bt, args, pe) -> 
     assert false
  | Mi_Proc (loc, _mrk, ret_bt, args, body, labels) -> 
     Print.debug 2 (lazy (Print.item ("normalising procedure") (Sym.pp fname)));
     let (_, ail_marker, _, ail_args, _) = List.assoc
         Sym.equal fname ail_prog.function_definitions in
     let ail_env = Pmap.find ail_marker ail_prog.markers_env in
     let d_st = Cerb_frontend.Cabs_to_ail_effect.set_cn_c_identifier_env ail_env d_st in
     let@ trusted, accesses, requires, ensures = Parse.parse_function_spec attrs in
     Print.debug 6 (lazy (Print.string "parsed spec attrs"));
     let@ accesses = ListM.mapM (desugar_access ail_env globals) accesses in
     let@ (requires, d_st) = desugar_conds d_st (List.map snd requires) in
     Print.debug 6 (lazy (Print.string "desugared requires conds"));
     let@ (ret_s, ret_d_st) = register_new_cn_local (Id.id "return") d_st in
     assertl loc (BT.equal (convert_bt loc ret_bt) 
                    (BT.of_sct (convert_ct loc ret_ct))) 
       !^"function return type mismatch";
     let@ (ensures, _) = desugar_conds ret_d_st (List.map snd ensures) in
     Print.debug 6 (lazy (Print.string "desugared ensures conds"));
     let@ args_and_body = 
       make_function_args (fun env ->
           (* Print.debug 6 (lazy (Print.string "normalising body")); *)
           let body = n_expr loc body in
           (* Print.debug 6 (lazy (Print.string "normalising labels")); *)
           let@ labels = 
             PmapM.mapM (normalise_label (accesses, loop_attributes) env d_st)
               labels Sym.compare in
           let@ returned = make_rt loc env (ret_s, ret_ct) (accesses, ensures) in
           (* Print.debug 6 (lazy (Print.string "made return-type")); *)
           return (body, labels, returned)
         ) 
         loc 
         env 
         (List.combine (List.combine ail_args arg_cts) args) 
         (accesses, requires)
     in
     let ft = at_of_arguments (fun (_body, _labels, rt) -> rt) args_and_body in
     (* Print.debug 6 (lazy (Print.item "normalised function-type" (AT.pp RT.pp ft))); *)
     return (Some (M_Proc(loc, args_and_body, ft, trusted)))
  | Mi_ProcDecl(loc, ret_bt, bts) -> 
     return None
     (* let@ trusted, accesses, requires, ensures = Parse.parse_function_spec attrs in *)
     (* let@ (requires, d_st2) = desugar_conds d_st (List.map snd requires) in *)
     (* let@ (ret, ret_d_st) = declare_return loc ret_ct ret_bt d_st2 in *)
     (* let@ (ensures, _) = desugar_conds ret_d_st (List.map snd ensures) in *)
     (* let arg_protos = List.mapi (fun i -> function *)
     (*    | (Some sym, ct) -> (sym, ct) *)
     (*    | (None, ct) -> (Sym.fresh_named ("default_" ^ Int.to_string i), ct)) arg_cts in *)
     (* let@ args_and_rt = *)
     (*   make_args (fun env -> *)
     (*       make_rt loc env ret ensures *)
     (*     ) loc env arg_protos requires *)
     (* in *)
     (* let ft = at_of_arguments Tools.id args_and_rt in *)
     (* return (Some (M_ProcDecl(loc, ft))) *)
  | Mi_BuiltinDecl(loc, bt, bts) -> 
     assert false
     (* M_BuiltinDecl(loc, convert_bt loc bt, List.map (convert_bt loc) bts) *)

let normalise_fun_map ail_prog env globals d_st funinfo loop_attributes fmap =
  let@ m1 = PmapM.mapM (normalise_fun_map_decl ail_prog env globals d_st funinfo loop_attributes)
    fmap Sym.compare in
  return (Pmap.filter_map Sym.compare (fun _ x -> x) m1)

  



let normalise_globs sym g =
  let loc = Loc.unknown in
  match g with
  | GlobalDef ((bt, ct), e) -> 
     let e = n_expr loc e in
     M_GlobalDef ((convert_bt loc bt, convert_ct loc ct), e)
  | GlobalDecl (bt, ct) -> 
     M_GlobalDecl (convert_bt loc bt, convert_ct loc ct)


let normalise_globs_list gs = 
   List.map (fun (sym,g) -> (sym, normalise_globs sym g)) gs



let make_struct_decl loc fields (tag : BT.tag) = 

  let open Memory in
  let tagDefs = CF.Tags.tagDefs () in

  let member_offset member = 
    Memory.int_of_ival (CF.Impl_mem.offsetof_ival tagDefs tag member)
  in
  let final_position = Memory.size_of_struct tag in

  let rec aux members position =
    match members with
    | [] -> 
       if position < final_position 
       then [{offset = position; size = final_position - position; member_or_padding = None}]
       else []
    | (member, (attrs, _(*align_opt*), qualifiers, ct)) :: members ->
       (* TODO: support for any alignment specifier *)
       let sct = convert_ct loc ct in
       let offset = member_offset member in
       let size = Memory.size_of_ctype sct in
       let to_pad = offset - position in
       let padding = 
         if to_pad > 0
         then [{offset = position; size = to_pad; member_or_padding = None}] 
         else [] 
       in
       let member = [{offset; size; member_or_padding = Some (member, sct)}] in
       let rest = aux members (offset + size) in
       (padding @ member @ rest)
  in

  aux fields 0



let normalise_tag_definition tag def = 
  let loc = Loc.unknown in
  match def with
  | StructDef(fields, Some flexible_array_member) -> 
     Tools.unsupported loc !^"flexible array member"
  | StructDef (fields, None) -> 
     M_StructDef (make_struct_decl loc fields tag)
  | UnionDef l -> 
     Tools.unsupported loc !^"union types"


let normalise_tag_definitions tagDefs =
   Pmap.mapi normalise_tag_definition tagDefs



let register_glob env (sym, glob) = 
  match glob with
  | M_GlobalDef ((bt, ct), e) ->
     assert (BT.equal bt Loc);
     C.add_computational sym (SBT.Loc (Some ct)) env
     (* |> C.add_c_var_value sym (IT.sym_ (sym, bt)) *)
  | M_GlobalDecl (bt, ct) ->
     assert (BT.equal bt Loc);
     C.add_computational sym (SBT.Loc (Some ct)) env
     (* |> C.add_c_var_value sym (IT.sym_ (sym, bt)) *)
     



let normalise_file ail_prog file = 

  let tagDefs = normalise_tag_definitions file.mi_tagDefs in

  let env = C.empty tagDefs in
  let@ env = C.add_datatype_infos env ail_prog.cn_datatypes in
  let@ env = C.register_cn_functions env ail_prog.cn_functions in
  let@ lfuns = ListM.mapM (C.translate_cn_function env) ail_prog.cn_functions in
  let env = C.register_cn_predicates env ail_prog.cn_predicates in
  let@ preds = ListM.mapM (C.translate_cn_predicate env) ail_prog.cn_predicates in

  let globs = normalise_globs_list file.mi_globs in

  let env = List.fold_left register_glob env globs in

  let desugar_state = Cerb_frontend.Cabs_to_ail_effect.further_cn_desugaring_state
        ail_prog.cn_idents ail_prog.translation_tag_definitions in

  let@ funs = normalise_fun_map ail_prog env globs desugar_state
        file.mi_funinfo file.mi_loop_attributes file.mi_funs in
  let file = {
      mu_main = file.mi_main;
      mu_tagDefs = tagDefs;
      mu_globs = globs;
      mu_funs = funs;
      mu_extern = file.mi_extern;
      mu_resource_predicates = preds;
      mu_logical_predicates = lfuns;
      mu_datatypes = SymMap.bindings (SymMap.map fst env.datatypes);
      mu_constructors = SymMap.bindings env.datatype_constrs;
    }
  in
  return file





