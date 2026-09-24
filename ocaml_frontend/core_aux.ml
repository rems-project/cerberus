open Lem_pervasives
open Utils
open Core
open Ctype
open Annot
open Cerb_symbol


let rec core_object_type_of_ctype (Ctype (_, ty)) =
  match ty with
  | Void -> None
  | Basic (Integer _) -> Some OTy_integer
  | Basic (Floating _) -> Some OTy_floating
  | Array (elem_ty, _) -> (
      match core_object_type_of_ctype elem_ty with
      | Some oTy -> Some (OTy_array oTy)
      | None ->
          Cerb_debug.error
            "Core_aux.core_object_type_of_ctype: Array found a Nothing")
  | Function _ ->
      Cerb_debug.error "core_object_type_of_ctype: not core function object"
  | FunctionNoParams _ ->
      Cerb_debug.error
        "core_object_type_of_ctype: not core function (no params) object"
  | Pointer _ -> Some OTy_pointer
  | Atomic atom_ty -> core_object_type_of_ctype atom_ty
  | Struct tag_sym -> Some (OTy_struct tag_sym)
  | Union tag_sym -> Some (OTy_union tag_sym)
  | Byte ->
      (* May need to revisit based on CN *)
      Some OTy_integer

let rec loadedValueFromMemValue mem_val =
  Cerb_debug.print_debug 6 [] (fun () ->
      "loadedValueFromMemValue ==> " ^ Impl_mem.string_of_mem_value mem_val
  );
  Impl_mem.case_mem_value mem_val
    (fun ty ->
      ( fromJust "loadedValueFromMemValue" (core_object_type_of_ctype ty),
        LVunspecified ty ))
    (fun _ _ ->
      Cerb_debug.error "[Core_aux.loadedValueFromMemValue] concurrency read")
    (fun _ ival -> (OTy_integer, LVspecified (OVinteger ival)))
    (fun _ fval -> (OTy_floating, LVspecified (OVfloating fval)))
    (fun _ ptr_val -> (OTy_pointer, LVspecified (OVpointer ptr_val)))
    (fun mem_vals ->
      match List.map loadedValueFromMemValue mem_vals with
      | [] -> Cerb_debug.error "[Core_aux.loadedValueFromMemValue] empty array"
      | (oTy, lval) :: oTy_lvals ->
          if
            List.exists
              (fun (oTy', _) ->
                (fun x y -> not (eq_core_object_type x y)) oTy oTy')
              oTy_lvals
          then
            Cerb_debug.error
              "[Core_aux.loadedValueFromMemValue] heterogenous array"
          else
            ( OTy_array oTy,
              LVspecified (OVarray (lval :: List.map snd oTy_lvals)) ))
    (fun sym xs -> (OTy_struct sym, LVspecified (OVstruct (sym, xs))))
    (fun sym ident mem_val ->
      (OTy_union sym, LVspecified (OVunion (sym, ident, mem_val))))


let valueFromMemValue mem_val =
  Cerb_debug.print_debug 6 [] (fun () ->
      "valueFromMemValue ==> " ^ Impl_mem.string_of_mem_value mem_val
  );
  Impl_mem.case_mem_value mem_val
    (fun ty ->
      ( fromJust "Core_aux.valueFromMemValue" (core_object_type_of_ctype ty),
        Bloaded (LVunspecified ty) ))
    (fun _ _ ->
      Cerb_debug.error "[Core_aux.valueFromMemValue] concurrency read")
    (fun _ ival -> (OTy_integer, Bloaded (LVspecified (OVinteger ival))))
    (fun _ fval -> (OTy_floating, Bloaded (LVspecified (OVfloating fval))))
    (fun _ ptr_val -> (OTy_pointer, Bloaded (LVspecified (OVpointer ptr_val))))
    (fun mem_vals ->
      let oTys, lvals =
        List.split (List.map loadedValueFromMemValue mem_vals)
      in
      let oTy =
        match oTys with
        | [] ->
            (* Something went wrong in the MLM *)
            Cerb_debug.error "Core_aux.valueFromMemValue ==> empty array"
        | oTy :: _ -> oTy
      in
      (OTy_array oTy, Bloaded (LVspecified (OVarray lvals))))
    (fun sym xs ->
      (OTy_struct sym, Bloaded (LVspecified (OVstruct (sym, xs)))))
    (fun sym ident mem_val ->
      (OTy_union sym, Bloaded (LVspecified (OVunion (sym, ident, mem_val)))))

let rec memValueFromValue ty cval =
  let (Ctype (_, ty_)) = unatomic ty in
  match (ty_, cval) with
  | _, Bunit
  | _, Btrue
  | _, Bfalse
  | _, Blist _
  | _, Btuple _
  | _, Bctype _ -> None
  | _, Bloaded (LVunspecified ty') ->
      Some (Impl_mem.unspecified_mval ty') (* TODO: check ty = ty'? *)
  | Basic (Integer ity), Bobject (OVinteger ival)
  | Basic (Integer ity), Bloaded (LVspecified (OVinteger ival)) ->
      Some (Impl_mem.integer_value_mval ity ival)
  | Byte, Bobject (OVinteger ival)
  | Byte, Bloaded (LVspecified (OVinteger ival)) ->
      Some (Impl_mem.integer_value_mval (Unsigned Ichar) ival)
  | Basic (Floating fty), Bloaded (LVspecified (OVfloating fval))
  | Basic (Floating fty), Bobject (OVfloating fval) ->
      Some (Impl_mem.floating_value_mval fty fval)
  | Pointer (_, ref_ty), Bobject (OVpointer ptr_val) (* TODO: not sure about this *)
  | Pointer (_, ref_ty), Bloaded (LVspecified (OVpointer ptr_val)) ->
      Some (Impl_mem.pointer_mval ref_ty ptr_val)
  | Array (elem_ty, _), Bloaded (LVspecified (OVarray lvals)) ->
      (* TODO: check that the sizes match? *)
      Lem.option_case None
        (fun z -> Some (Impl_mem.array_mval z))
        (List.fold_right
           (fun lval acc_opt ->
             match (memValueFromValue elem_ty (Bloaded lval), acc_opt) with
             | Some mem_val, Some acc -> Some (mem_val :: acc)
             | _ -> None)
           lvals (Some []))
  | Struct tag_sym1, Bloaded (LVspecified (OVstruct (tag_sym2, xs))) ->
      let () =
        Cerb_debug.print_debug 2 [] (fun () ->
            "Comparing struct tag symbols: " ^ Sym.show_raw tag_sym1 ^ " = "
            ^ Sym.show_raw tag_sym2)
      in
      if
        Ctype_aux.are_compatible0
          (no_qualifiers, Ctype ([], Struct tag_sym1))
          (no_qualifiers, Ctype ([], Struct tag_sym2))
      then Some (Impl_mem.struct_mval tag_sym1 xs)
      else None
  | Union tag_sym1, Bloaded (LVspecified (OVunion (tag_sym2, ident, mem_val)))
    ->
      if Sym.equal tag_sym1 tag_sym2
      then Some (Impl_mem.union_mval tag_sym1 ident mem_val)
      else None
  | _ ->
      let () =
        Cerb_debug.print_debug 5 [] (fun () ->
            "memValueFromValue("
            ^ String_core_ctype.string_of_ctype ty
            ^ ", "
            ^ String_core.string_of_value cval
            ^ ")")
      in
      None


let valueFromPexpr = function
  | Pexpr (_, _, PEbase cval) -> Some cval
  | _ -> None

let valueFromPexprs pes =
  List.fold_right
    (fun pe acc_opt ->
      match (valueFromPexpr pe, acc_opt) with
      | Some cval, Some acc -> Some (cval :: acc)
      | _ -> None)
    pes (Some [])


(* Core pattern builders **************************************************** *)
module Pattern = struct
  let mk ?(annots = []) desc = Pattern (annots, desc)
end


let mk_empty_pat bTy = Pattern.mk (CaseBase (None, bTy))
let mk_sym_pat_ annots msym bTy = Pattern.mk ~annots (CaseBase (msym, bTy))
let mk_sym_pat sym bty = mk_sym_pat_ [] (Some sym) bty

let mk_tuple_pat = function
  | [] -> Cerb_debug.error "[Core_aux.mk_tuple_pat] called with |pats| = 0"
  | [ pat ] -> pat
  | pats -> Pattern.mk (CaseDtor (Dtuple, pats))

let mk_specified_pat_ annots pat =
  Pattern.mk ~annots (CaseDtor (Dspecified, [ pat ]))
let mk_specified_pat pat = mk_specified_pat_ [] pat
let mk_unspecified_pat_ annots pat =
  Pattern.mk ~annots (CaseDtor (Dunspecified, [ pat ]))
let mk_unspecified_pat pat = mk_unspecified_pat_ [] pat

(* Core pexpr builders  ***************************************************** *)
module Pexpr = struct
  let mk desc = Pexpr ([], None, desc)
  let ctor0 ctor = mk (PEctor (ctor, []))
  let ctor1 ctor pe = mk (PEctor (ctor, [ pe ]))
  let ctor2 ctor pe1 pe2 = mk (PEctor (ctor, [ pe1; pe2 ]))
  let ctor3 ctor pe1 pe2 pe3 = mk (PEctor (ctor, [ pe1; pe2; pe3 ]))
  let ctorN ctor pes = mk (PEctor (ctor, pes))
  let map f (Pexpr (annots, bTy, desc)) = Pexpr (annots, bTy, f desc)

  let add_annot annot (Pexpr (annots, bTy, desc)) =
    Pexpr (annot :: annots, bTy, desc)
end

let annotate_integer_type_pexpr ity = Pexpr.add_annot (Avalue (Ainteger ity))

let maybe_annotate_integer_type_pexpr (Ctype (_, ty_)) pe =
  match ty_ with
  | Basic (Integer ity) -> annotate_integer_type_pexpr ity pe
  | _ -> pe


let mk_sym_pe sym1 = Pexpr.mk (PEsym sym1)

let mk_integer_pe n =
  Pexpr.mk (PEbase (Bobject (OVinteger (Impl_mem.integer_ival n))))

let mk_floating_pe fval = Pexpr.mk (PEbase (Bobject (OVfloating fval)))

let mk_nullptr_pe ref_ty =
  Pexpr.mk (PEbase (Bobject (OVpointer (Impl_mem.null_ptrval ref_ty))))

let mk_specified_pe = Pexpr.ctor1 Cspecified
let mk_unspecified_pe ty = Pexpr.mk (PEbase (Bloaded (LVunspecified ty)))
let mk_array_pe = Pexpr.ctorN Carray
let mk_unit_pe = Pexpr.mk (PEbase Bunit)
let mk_boolean_pe b = Pexpr.mk (PEbase (if b then Btrue else Bfalse))
let mk_ail_ctype_pe ty = Pexpr.mk (PEbase (Bctype ty))
let mk_ctype_pe ty = Pexpr.mk (PEbase (Bctype ty))

let rec mk_list_pe bTy = function
  | [] -> Pexpr.ctor0 (Cnil bTy)
  | pe :: pes' -> Pexpr.ctor2 Ccons pe (mk_list_pe bTy pes')

let mk_tuple_pe = function
  | [] -> Cerb_debug.error "Core_aux.mk_tuple_pe []"
  | [ pe ] -> pe
  | pes -> Pexpr.ctorN Ctuple pes

let mk_ivmax_pe = Pexpr.ctor1 Civmax
let mk_sizeof_pe = Pexpr.ctor1 Civsizeof
let mk_alignof_pe = Pexpr.ctor1 Civalignof
let mk_nullcap_pe is_signed = Pexpr.ctor0 (CivNULLcap is_signed)
let mk_undef_pe loc ub = Pexpr.mk (PEundef (loc, ub))
let mk_error_pe str pe = Pexpr.mk (PEerror (str, pe))
let mk_not_pe pe = Pexpr.mk (PEnot pe)
let mk_op_pe bop pe1 pe2 = Pexpr.mk (PEop (bop, pe1, pe2))
let mk_conv_int_pe ity pe = Pexpr.mk (PEconv_int (ity, pe))
let mk_wrapI_pe ity iop pe1 pe2 = Pexpr.mk (PEwrapI (ity, iop, pe1, pe2))

let mk_catch_exceptional_condition_pe ity iop1 pe1 pe2 =
  Pexpr.mk (PEcatch_exceptional_condition (ity, iop1, pe1, pe2))

let mk_let_pe pat pe1 pe2 = Pexpr.mk (PElet (pat, pe1, pe2))
let mk_if_pe pe1 pe2 pe3 = Pexpr.mk (PEif (pe1, pe2, pe3))

let mk_array_shift pe1 ty1 pe2 = Pexpr.mk (PEarray_shift (pe1, ty1, pe2))
let mk_member_shift_pe pe1 tag_sym member_ident =
  Pexpr.mk (PEmember_shift (pe1, tag_sym, member_ident))

let mk_memop_pe mop pes = Pexpr.mk (PEmemop (mop, pes))

let mk_case_pe pe pat_pes = Pexpr.mk (PEcase (pe, pat_pes))

(* integerType is the type annotation placed on the 0 literal *)
(* TODO: in the move to OCaml, have mk_integer_pe take an optional integerType
 * instead of doing something special here
 *)
let mk_neg_pe ity pe =
  Pexpr.mk
    (PEop
       ( OpSub,
         annotate_integer_type_pexpr ity (mk_integer_pe (Nat_big_num.of_int 0)),
         pe ))

let mk_struct_pe tag_sym xs = Pexpr.mk (PEstruct (tag_sym, xs))

let mk_union_pe tag_sym memb_ident pe =
  Pexpr.mk (PEunion (tag_sym, memb_ident, pe))

let mk_memberof_pe tag_sym memb_ident pe =
  Pexpr.mk (PEmemberof (tag_sym, memb_ident, pe))

let mk_value_pe cval = Pexpr.mk (PEbase cval)

let mk_cfunction_pe pe = Pexpr.mk (PEcfunction pe)

let mk_std_pe std pexpr =
  Pexpr.add_annot (Astd std) pexpr

let mk_std_undef_pe loc1 std ub = mk_std_pe std (mk_undef_pe loc1 ub)

let mk_std_pair_pe std (pe1, pe2) = (mk_std_pe std pe1, mk_std_pe std pe2)

let mk_call_pe nm pes = Pexpr.mk (PEcall (nm, pes))

let mk_are_compatible pe1 pe2 = Pexpr.mk (PEare_compatible (pe1, pe2))

(* Common undef *)
let mk_undef_exceptional_condition loc1 =
  mk_std_undef_pe loc1 "§6.5#5" Undefined.UB036_exceptional_condition

let bitwise_complement_pe = Pexpr.ctor2 CivCOMPL
let bitwise_AND_pe = Pexpr.ctor3 CivAND
let bitwise_OR_pe = Pexpr.ctor3 CivOR
let bitwise_XOR_pe = Pexpr.ctor3 CivXOR

let mk_ivfromfloat_pe = Pexpr.ctor2 Civfromfloat
let mk_fvfromint_pe = Pexpr.ctor1 Cfvfromint

(* Core expr builders ****************************************************** *)
module Expr = struct
  let mk ?(annots = []) desc = Expr (annots, desc)
  let map f (Expr (annots, desc)) = Expr (annots, f desc)
end

let maybe_annotate_integer_type (Ctype (_, ty_)) (Expr (annots, desc)) =
  let annots =
    match ty_ with
    | Basic (Integer ity) -> Avalue (Ainteger ity) :: annots
    | _ -> annots
  in
  Expr (annots, desc)


let mk_pure_e pe = Expr.mk (Epure pe)
let mk_value_e cval = mk_pure_e (mk_value_pe cval)
let mk_skip_e = mk_value_e Bunit

let mk_memop_e mop pes = Expr.mk (Ememop (mop, pes))
let mk_case_e pe pat_es = Expr.mk (Ecase (pe, pat_es))
let mk_let_e pat pe e = Expr.mk (Elet (pat, pe, e))
let mk_if_e_ annots pe e1 e2 = Expr.mk ~annots (Eif (pe, e1, e2))
let mk_if_e pe e1 e2 = Expr.mk (Eif (pe, e1, e2))
let mk_ccall_e_ annots cty pe pes = Expr.mk ~annots (Eccall ((), cty, pe, pes))
let mk_unseq_e es = Expr.mk (Eunseq es)
let mk_wseq_e pat e1 e2 = Expr.mk (Ewseq (pat, e1, e2))
let mk_sseq_e pat e1 e2 = Expr.mk (Esseq (pat, e1, e2))
let mk_nd_e es = Expr.mk (End es)
let mk_save_e_ annots sym_ty sym_ty_pes e =
  Expr.mk ~annots (Esave (sym_ty, sym_ty_pes, e))
let mk_run_e sym pes = Expr.mk (Erun ((), sym, pes))
let mk_wait_e tid = Expr.mk (Ewait tid)

(* Core expr "smart" builders ************************************************)
let mk_unseq = function
  | [] -> mk_value_e Bunit
  | [ e ] -> e
  | es -> mk_unseq_e es

let rec mk_unit_sseq es =
 fun z ->
  match es with
  | [] -> z
  | e :: es' -> mk_sseq_e (mk_empty_pat BTy_unit) e (mk_unit_sseq es' z)

let rec mk_sseqs pat_es =
 fun z ->
  match pat_es with
  | [] -> z
  | (pat, e) :: pat_es' -> mk_sseq_e pat e (mk_sseqs pat_es' z)

let rec concat_sseq (Expr (annots, e_) as e) e' =
  match e_ with
  | Esseq (pat, e1, e2) -> Expr.mk ~annots (Esseq (pat, e1, concat_sseq e2 e'))
  | Epure (Pexpr (_, _, PEbase Bunit)) -> e'
  | _ -> mk_sseq_e (mk_empty_pat BTy_unit) e e'

(* Core (positive) memory action builders **************************************)
let pcreate loc al ty pref =
  Expr.mk (Eaction (Paction (Pos, Action (loc, (), Create (al, ty, pref)))))

let pcreate_readonly loc al ty init pref =
  Expr.mk
    (Eaction
      (Paction
        (Pos, Action (loc, (), CreateReadOnly (al, ty, init, pref)))))

let pkill loc1 kind1 x =
  Expr.mk (Eaction (Paction (Pos, Action (loc1, (), Kill (kind1, x)))))

let pstore loc ty x n mo =
  Expr.mk
    (Eaction (Paction (Pos, Action (loc, (), Store (false, ty, x, n, mo)))))

let pstore_lock loc ty x n mo =
  Expr.mk
    (Eaction (Paction (Pos, Action (loc, (), Store (true, ty, x, n, mo)))))

let pload loc ty x mo =
  Expr.mk (Eaction (Paction (Pos, Action (loc, (), Load (ty, x, mo)))))

let pcompare_exchange_strong loc ty x n1 n2 mo1 mo2 =
  Expr
    ( [],
      Eaction
        (Paction
           ( Pos,
             Action (loc, (), CompareExchangeStrong (ty, x, n1, n2, mo1, mo2))
           )) )

let pcompare_exchange_weak loc ty x n1 n2 mo1 mo2 =
  Expr
    ( [],
      Eaction
        (Paction
           ( Pos,
             Action (loc, (), CompareExchangeWeak (ty, x, n1, n2, mo1, mo2))
           )) )

let plinux_load loc ty x mo =
  Expr.mk (Eaction (Paction (Pos, Action (loc, (), LinuxLoad (ty, x, mo)))))

let plinux_store loc ty x n mo =
  Expr.mk
    (Eaction (Paction (Pos, Action (loc, (), LinuxStore (ty, x, n, mo)))))

let plinux_rmw loc ty x n mo =
  Expr.mk
    (Eaction (Paction (Pos, Action (loc, (), LinuxRMW (ty, x, n, mo)))))

let seq_rmw loc with_forward ty oTy x sym upd =
  let backend = Cerb_global.backend_name () in
  if String.equal backend "Cn" || String.equal backend "Bmc" then
    (* TODO: compatibility mode for Cn, until SeqRMW is supported *)
    if with_forward then
      Cerb_debug.error "TODO: Core_aux.seq_rmw (comptability mode) with_forward"
    else
      Expr.mk
        ( Ewseq
            ( mk_sym_pat sym (*TODO*) (BTy_loaded oTy),
              pload loc ty x Atomics.NA,
              Expr
                ( [],
                  Ewseq
                    ( mk_empty_pat BTy_unit,
                      pstore loc ty x upd Atomics.NA,
                      Expr.mk (Epure (mk_sym_pe sym)) ) ) ) )
  else
    Expr.mk
      ( Eaction
          (Paction
             (Pos, Action (loc, (), SeqRMW (with_forward, ty, x, sym, upd)))) )


(* check if a symbolic names is part of a pattern *)
let rec in_pattern sym (Pattern (_, pat)) =
  match pat with
  | CaseBase (sym_opt, _) ->
      Option.fold ~none:false ~some:(Sym.equal sym) sym_opt
  | CaseDtor (_, pats') -> List.exists (in_pattern sym) pats'

let rec subst_sym_pexpr sym cval =
  let self x = subst_sym_pexpr sym cval x [@@inline] in
  Pexpr.map (function
  | PEsym sym' as pexpr_ ->
      if Sym.equal sym sym' then PEbase cval else pexpr_
  | (PEimpl _ | PEbase _ | PEundef _) as pexpr_ -> pexpr_
  | PEerror (str, pe) -> PEerror (str, self pe)
  | PEctor (ctor, pes) ->
      PEctor (ctor, List.map (self) pes)
  | PEcase (pe, xs) ->
      PEcase
        ( self pe,
          List.map
            (fun (pat, pe) ->
              ( pat,
                if in_pattern sym pat then pe
                else self pe ))
            xs )
  | PEarray_shift (pe1, ty1, pe2) ->
      PEarray_shift
        (self pe1, ty1, self pe2)
  | PEmember_shift (pe, tag_sym, memb_ident) ->
      PEmember_shift (self pe, tag_sym, memb_ident)
  | PEmemop (mop, pes) ->
      PEmemop (mop, List.map (self) pes)
  | PEnot pe -> PEnot (self pe)
  | PEop (bop, pe1, pe2) ->
      PEop
        (bop, self pe1, self pe2)
  | PEconv_int (ty1, pe) -> PEconv_int (ty1, self pe)
  | PEwrapI (ty1, iop1, pe1, pe2) ->
      PEwrapI
        ( ty1,
          iop1,
          self pe1,
          self pe2 )
  | PEcatch_exceptional_condition (ty1, iop1, pe1, pe2) ->
      PEcatch_exceptional_condition
        ( ty1,
          iop1,
          self pe1,
          self pe2 )
  | PEstruct (tag_sym, xs) ->
      PEstruct
        ( tag_sym,
          List.map
            (fun (ident, pe) -> (ident, self pe))
            xs )
  | PEunion (tag_sym, ident, pe) ->
      PEunion (tag_sym, ident, self pe)
  | PEcfunction pe -> PEcfunction (self pe)
  | PEmemberof (tag_sym, memb_ident, pe) ->
      PEmemberof (tag_sym, memb_ident, self pe)
  | PEcall (nm, pes) ->
      PEcall (nm, List.map (self) pes)
  | PElet (pat, pe1, pe2) ->
      PElet
        ( pat,
          self pe1,
          if in_pattern sym pat then pe2 else self pe2
        )
  | PEif (pe1, pe2, pe3) ->
      PEif
        ( self pe1,
          self pe2,
          self pe3 )
  | PEis_unsigned pe -> PEis_unsigned (self pe)
  | PEbmc_assume pe -> PEbmc_assume (self pe)
  | PEare_compatible (pe1, pe2) ->
      PEare_compatible
        (self pe1, self pe2) )

let rec subst_sym_expr sym cval =
  let subst_pexpr x = subst_sym_pexpr sym cval x [@@inline] in
  let self x = subst_sym_expr sym cval x [@@inline] in
  Expr.map (function
  | Epure pe -> Epure (subst_pexpr pe)
  | Ememop (memop1, pes) -> Ememop (memop1, List.map subst_pexpr pes)
  | Elet (pat, pe1, e2) ->
      Elet
        ( pat,
          subst_pexpr pe1,
          if in_pattern sym pat then e2 else self e2 )
  | Eif (pe1, e2, e3) ->
      Eif
        ( subst_pexpr pe1,
          self e2,
          self e3 )
  | Ecase (pe, pat_es) ->
      Ecase
        ( subst_pexpr pe,
          List.map
            (fun (pat, e) ->
              ( pat,
                if in_pattern sym pat then e
                else self e ))
            pat_es )
  | Eccall (annot1, pe1, pe2, pes) ->
      Eccall
        ( annot1,
          subst_pexpr pe1,
          subst_pexpr pe2,
          List.map subst_pexpr pes )
  | Eproc (annot1, nm, pes) ->
      Eproc (annot1, nm, List.map subst_pexpr pes)
  | Eaction pact -> Eaction (subst_sym_paction sym cval pact)
  | Eunseq es -> Eunseq (List.map (self) es)
  | Ewseq (pat, e1, e2) ->
      Ewseq
        ( pat,
          self e1,
          if in_pattern sym pat then e2 else self e2 )
  | Esseq (pat, e1, e2) ->
      Esseq
        ( pat,
          self e1,
          if in_pattern sym pat then e2 else self e2 )
  | Ebound e -> Ebound (self e)
  | Esave (lab_sym, sym_bTy_pes, e) ->
      let sym_bTy_pes' =
        List.map
          (fun (z, (bTy, pe)) -> (z, (bTy, subst_pexpr pe)))
          sym_bTy_pes
      in
      if
        List.exists
          (fun (z, _) -> Sym.equal sym z)
          sym_bTy_pes
      then
        let () =
          Cerb_debug.warn [] (fun () -> "subst, Esave ==> shadowing")
        in
        (* TODO: check *)
        Esave (lab_sym, sym_bTy_pes', e)
      else Esave (lab_sym, sym_bTy_pes', self e)
  | Erun (annot1, lab_sym, pes) ->
      Erun (annot1, lab_sym, List.map subst_pexpr pes)
  | End es -> End (List.map (self) es)
  | Epar es -> Epar (List.map (self) es)
  | Ewait _ as expr_ -> expr_
  | Eannot (xs, e) -> Eannot (xs, self e)
  | Eexcluded (n, act) -> Eexcluded (n, subst_sym_action sym cval act) )

and subst_sym_action_ sym cval = function
  | Create (pe1, pe2, pref) ->
      Create (subst_sym_pexpr sym cval pe1, subst_sym_pexpr sym cval pe2, pref)
  | CreateReadOnly (pe1, pe2, pe3, pref) ->
      CreateReadOnly
        ( subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          pref )
  | Alloc (pe1, pe2, pref) ->
      Alloc (subst_sym_pexpr sym cval pe1, subst_sym_pexpr sym cval pe2, pref)
  | Kill (kind1, pe) -> Kill (kind1, subst_sym_pexpr sym cval pe)
  | Store (b, pe1, pe2, pe3, mo) ->
      Store
        ( b,
          subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          mo )
  | Load (pe1, pe2, mo) ->
      Load (subst_sym_pexpr sym cval pe1, subst_sym_pexpr sym cval pe2, mo)
  | SeqRMW (b, pe1, pe2, sym', pe3) ->
      SeqRMW
        ( b,
          subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          sym',
          if Sym.equal sym sym'
          then pe3
          else subst_sym_pexpr sym cval pe3 )
  | RMW (pe1, pe2, pe3, pe4, mo1, mo2) ->
      RMW
        ( subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          subst_sym_pexpr sym cval pe4,
          mo1,
          mo2 )
  | Fence mo1 -> Fence mo1
  | CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2) ->
      CompareExchangeStrong
        ( subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          subst_sym_pexpr sym cval pe4,
          mo1,
          mo2 )
  | CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2) ->
      CompareExchangeWeak
        ( subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          subst_sym_pexpr sym cval pe4,
          mo1,
          mo2 )
  | LinuxFence mo1 -> LinuxFence mo1
  | LinuxStore (pe1, pe2, pe3, mo) ->
      LinuxStore
        ( subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          mo )
  | LinuxLoad (pe1, pe2, mo) ->
      LinuxLoad
        (subst_sym_pexpr sym cval pe1, subst_sym_pexpr sym cval pe2, mo)
  | LinuxRMW (pe1, pe2, pe3, mo) ->
      LinuxRMW
        ( subst_sym_pexpr sym cval pe1,
          subst_sym_pexpr sym cval pe2,
          subst_sym_pexpr sym cval pe3,
          mo )

and subst_sym_action sym cval (Action (loc, bs, act_)) =
  Action (loc, bs, subst_sym_action_ sym cval act_)

and subst_sym_paction sym cval (Paction (p, act)) =
  Paction (p, subst_sym_action sym cval act)

(*val     subst_pattern_val: forall 'a. pattern -> value -> expr 'a -> expr 'a*)
let rec subst_pattern_val (Pattern (_, pat)) cval expr1 =
  (* TODO (maybe), Carray, Civmax, Civmin, Civsizeof, Civalignof *)
  match (pat, cval) with
  | CaseBase (None, _), _ ->
      (* e[_ \ v] = e *)
      expr1
  | CaseBase (Some sym1, _), _ ->
      (* e[sym \ v] *)
      subst_sym_expr sym1 cval expr1
  | CaseDtor (Dnil _, []), Blist (_, []) ->
      (* empty list (value) *)
      expr1
  | CaseDtor (Dcons, [ pat1; pat2 ]), Blist (bTy_elem, cval1 :: cvals) ->
      (* populated list (value) *)
      subst_pattern_val pat1 cval1
        (subst_pattern_val pat2 (Blist (bTy_elem, cvals)) expr1)
  | CaseDtor (Dtuple, pats'), Btuple cvals ->
      List.fold_right
        (fun (pat', cval') acc -> subst_pattern_val pat' cval' acc)
        (List.combine pats' cvals)
        expr1
  | CaseDtor (Dspecified, [ pat' ]), Bloaded (LVspecified oval) ->
      subst_pattern_val pat' (Bobject oval) expr1
  | CaseDtor (Dunspecified, [ pat' ]), Bloaded (LVunspecified ty1) ->
      subst_pattern_val pat' (Bctype ty1) expr1
  | CaseDtor (dtor1, pats), _ ->
      let str_dtor =
        match dtor1 with
        | Dnil _ -> "nil"
        | Dcons -> "cons"
        | Dtuple -> "tuple"
        | Dspecified -> "specified"
        | Dunspecified -> "unspecified"
      in
      Cerb_debug.error
        ("WIP: Core_aux.subst_pattern_val ==> dtor= " ^ str_dtor ^ ", |pats|= "
        ^ string_of_int (List.length pats)
        ^ " -- "
        ^ String_core.string_of_value cval)

(* substitute in an expression a symbolic name with a (pure) expression *)
(* NOTE: this is usually unsound to use if pe' doesn't evaluate to a defined value or generates memory constraints *)
(*val     unsafe_subst_sym_pexpr: Sym.t -> pexpr -> pexpr -> pexpr*)
let rec unsafe_subst_sym_pexpr sym (Pexpr (annot, bty, pe_') as pe')
    (Pexpr (_, _, pe_)) =
  Pexpr
    ( annot,
      bty,
      match pe_ with
      | PEsym sym' ->
          if Sym.equal sym sym'
          then pe_'
          else pe_
      | PEimpl _ -> pe_
      | PEbase _ -> pe_
      | PEundef (_, _) -> pe_
      | PEerror (str, pe) -> PEerror (str, unsafe_subst_sym_pexpr sym pe' pe)
      | PEctor (ctor, pes) ->
          PEctor (ctor, List.map (unsafe_subst_sym_pexpr sym pe') pes)
      | PEcase (pe, xs) ->
          PEcase
            ( unsafe_subst_sym_pexpr sym pe' pe,
              List.map
                (fun (pat, pe) ->
                  ( pat,
                    if in_pattern sym pat then pe
                    else unsafe_subst_sym_pexpr sym pe' pe ))
                xs )
      | PEarray_shift (pe1, ty1, pe2) ->
          PEarray_shift
            ( unsafe_subst_sym_pexpr sym pe' pe1,
              ty1,
              unsafe_subst_sym_pexpr sym pe' pe2 )
      | PEmember_shift (pe, tag_sym, memb_ident) ->
          PEmember_shift
            (unsafe_subst_sym_pexpr sym pe' pe, tag_sym, memb_ident)
      | PEmemop (mop, pes) ->
          PEmemop (mop, List.map (unsafe_subst_sym_pexpr sym pe') pes)
      | PEnot pe -> PEnot (unsafe_subst_sym_pexpr sym pe' pe)
      | PEop (bop, pe1, pe2) ->
          PEop
            ( bop,
              unsafe_subst_sym_pexpr sym pe' pe1,
              unsafe_subst_sym_pexpr sym pe' pe2 )
      | PEconv_int (ty1, pe) ->
          PEconv_int (ty1, unsafe_subst_sym_pexpr sym pe' pe)
      | PEwrapI (ty1, iop1, pe1, pe2) ->
          PEwrapI
            ( ty1,
              iop1,
              unsafe_subst_sym_pexpr sym pe' pe1,
              unsafe_subst_sym_pexpr sym pe' pe2 )
      | PEcatch_exceptional_condition (ty1, iop1, pe1, pe2) ->
          PEcatch_exceptional_condition
            ( ty1,
              iop1,
              unsafe_subst_sym_pexpr sym pe' pe1,
              unsafe_subst_sym_pexpr sym pe' pe2 )
      | PEstruct (tag_sym, xs) ->
          PEstruct
            ( tag_sym,
              List.map
                (fun (ident, pe) -> (ident, unsafe_subst_sym_pexpr sym pe' pe))
                xs )
      | PEunion (tag_sym, ident, pe) ->
          PEunion (tag_sym, ident, unsafe_subst_sym_pexpr sym pe' pe)
      | PEcfunction pe -> PEcfunction (unsafe_subst_sym_pexpr sym pe' pe)
      | PEmemberof (tag_sym, memb_ident, pe) ->
          PEmemberof (tag_sym, memb_ident, unsafe_subst_sym_pexpr sym pe' pe)
      | PEcall (nm, pes) ->
          PEcall (nm, List.map (unsafe_subst_sym_pexpr sym pe') pes)
      | PElet (pat, pe1, pe2) ->
          PElet
            ( pat,
              unsafe_subst_sym_pexpr sym pe' pe1,
              if in_pattern sym pat then pe2
              else unsafe_subst_sym_pexpr sym pe' pe2 )
      | PEif (pe1, pe2, pe3) ->
          PEif
            ( unsafe_subst_sym_pexpr sym pe' pe1,
              unsafe_subst_sym_pexpr sym pe' pe2,
              unsafe_subst_sym_pexpr sym pe' pe3 )
      | PEis_unsigned pe -> PEis_unsigned (unsafe_subst_sym_pexpr sym pe' pe)
      | PEbmc_assume pe -> PEbmc_assume (unsafe_subst_sym_pexpr sym pe' pe)
      | PEare_compatible (pe1, pe2) ->
          PEare_compatible
            ( unsafe_subst_sym_pexpr sym pe' pe1,
              unsafe_subst_sym_pexpr sym pe' pe2 ) )

(* NOTE: this is usually unsound to use if pe' doesn't evaluate to a defined value or generates memory constraints *)
(*val     unsafe_subst_sym_expr: forall 'a. Sym.t -> pexpr -> expr 'a -> expr 'a*)
let rec unsafe_subst_sym_expr sym pe' =
  let unsafe_subst_pexpr x = unsafe_subst_sym_pexpr sym pe' x [@@inline] in
  let self x = unsafe_subst_sym_expr sym pe' x [@@inline] in
  Expr.map (function
  | Epure pe -> Epure (unsafe_subst_pexpr pe)
  | Ememop (memop1, pes) -> Ememop (memop1, List.map (unsafe_subst_pexpr) pes)
  | Elet (pat, pe1, e2) ->
      Elet
        ( pat,
          unsafe_subst_pexpr pe1,
          if in_pattern sym pat then e2
          else self e2 )
  | Eif (pe1, e2, e3) ->
      Eif
        ( unsafe_subst_pexpr pe1,
          self e2,
          self e3 )
  | Ecase (pe, pat_es) ->
      Ecase
        ( unsafe_subst_pexpr pe,
          List.map
            (fun (pat, e) ->
              ( pat,
                if in_pattern sym pat then e
                else self e ))
            pat_es )
  | Eccall (annot1, pe1, pe2, pes) ->
      Eccall
        ( annot1,
          unsafe_subst_pexpr pe1,
          unsafe_subst_pexpr pe2,
          List.map unsafe_subst_pexpr pes )
  | Eproc (annot1, nm, pes) ->
      Eproc (annot1, nm, List.map unsafe_subst_pexpr pes)
  | Eaction pact -> Eaction (unsafe_subst_sym_paction sym pe' pact)
  | Eunseq es -> Eunseq (List.map (self) es)
  | Ewseq (pat, e1, e2) ->
      Ewseq
        ( pat,
          self e1,
          if in_pattern sym pat then e2
          else self e2 )
  | Esseq (pat, e1, e2) ->
      Esseq
        ( pat,
          self e1,
          if in_pattern sym pat then e2
          else self e2 )
  | Ebound e -> Ebound (self e)
  | Esave (lab_sym, sym_bTy_pes, e) ->
      let sym_bTy_pes' =
        List.map
          (fun (z, (bTy, pe)) ->
            (z, (bTy, unsafe_subst_pexpr pe)))
          sym_bTy_pes
      in
      if
        List.exists
          (fun (z, _) -> Sym.equal sym z)
          sym_bTy_pes
      then
        let () =
          Cerb_debug.warn [] (fun () -> "unsafe_subst, Esave ==> shadowing")
        in
        (* TODO: check *)
        Esave (lab_sym, sym_bTy_pes', e)
      else Esave (lab_sym, sym_bTy_pes', self e)
  | Erun (annot1, lab_sym, pes) ->
      Erun
        (annot1, lab_sym, List.map (unsafe_subst_pexpr) pes)
  | End es -> End (List.map (self) es)
  | Epar es -> Epar (List.map (self) es)
  | Ewait _ as expr_ -> expr_
  | Eannot (xs, e) -> Eannot (xs, self e)
  | Eexcluded (n, act) -> Eexcluded (n, unsafe_subst_sym_action sym pe' act) )

(* NOTE: this is usually unsound to use if pe' doesn't evaluate to a defined value or generates memory constraints *)
and unsafe_subst_sym_action_ a pe' = function
  | Create (pe1, pe2, pref) ->
      Create
        (unsafe_subst_sym_pexpr a pe' pe1, unsafe_subst_sym_pexpr a pe' pe2, pref)
  | CreateReadOnly (pe1, pe2, pe3, pref) ->
      CreateReadOnly
        ( unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          pref )
  | Alloc (pe1, pe2, pref) ->
      Alloc
        (unsafe_subst_sym_pexpr a pe' pe1, unsafe_subst_sym_pexpr a pe' pe2, pref)
  | Kill (kind1, pe) -> Kill (kind1, unsafe_subst_sym_pexpr a pe' pe)
  | Store (b, pe1, pe2, pe3, mo1) ->
      Store
        ( b,
          unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          mo1 )
  | Load (pe1, pe2, mo1) ->
      Load
        (unsafe_subst_sym_pexpr a pe' pe1, unsafe_subst_sym_pexpr a pe' pe2, mo1)
  | SeqRMW (b, pe1, pe2, sym', pe3) ->
      SeqRMW
        ( b,
          unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          sym',
          if Sym.equal a sym'
          then pe3
          else unsafe_subst_sym_pexpr a pe' pe3 )
  | RMW (pe1, pe2, pe3, pe4, mo1, mo2) ->
      RMW
        ( unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          unsafe_subst_sym_pexpr a pe' pe4,
          mo1,
          mo2 )
  | Fence mo1 -> Fence mo1
  | CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2) ->
      CompareExchangeStrong
        ( unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          unsafe_subst_sym_pexpr a pe' pe4,
          mo1,
          mo2 )
  | CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2) ->
      CompareExchangeWeak
        ( unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          unsafe_subst_sym_pexpr a pe' pe4,
          mo1,
          mo2 )
  | LinuxFence mo1 -> LinuxFence mo1
  | LinuxStore (pe1, pe2, pe3, mo1) ->
      LinuxStore
        ( unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          mo1 )
  | LinuxLoad (pe1, pe2, mo1) ->
      LinuxLoad
        (unsafe_subst_sym_pexpr a pe' pe1, unsafe_subst_sym_pexpr a pe' pe2, mo1)
  | LinuxRMW (pe1, pe2, pe3, mo1) ->
      LinuxRMW
        ( unsafe_subst_sym_pexpr a pe' pe1,
          unsafe_subst_sym_pexpr a pe' pe2,
          unsafe_subst_sym_pexpr a pe' pe3,
          mo1 )

and unsafe_subst_sym_action a pe' (Action (loc1, bs, act_)) =
  Action (loc1, bs, unsafe_subst_sym_action_ a pe' act_)

and unsafe_subst_sym_paction a pe' (Paction (p, act)) =
  Paction (p, unsafe_subst_sym_action a pe' act)

(* TODO: [unsafe_subst_pattern _as v e] substitute the symbols _as with the corresponding
   of the value expression [v] in the expression [e]. This function leads
   to a crash if [v] is not a value or its type doesn't match the symbolic
   pattern *)
(* NOTE: this is usually unsound to use if pe' doesn't evaluate to a defined value or generates memory constraints *)
(*val     unsafe_subst_pattern: forall 'a. pattern -> pexpr -> expr 'a -> expr 'a*)
let rec unsafe_subst_pattern (Pattern (_, pat)) pe' expr1 =
  match (pat, pe') with
  | CaseBase (None, _), _ -> expr1
  | CaseBase (Some sym1, _), _ -> unsafe_subst_sym_expr sym1 pe' expr1
  | CaseDtor (Dnil _, []), Pexpr (_, _, PEbase (Blist (_, []))) ->
      (* empty list (value) *)
      expr1
  | CaseDtor (Dnil _, []), Pexpr (_, _, PEctor (Cnil _, [])) ->
      (* empty list (pure expr) *)
      expr1
  | ( CaseDtor (Dcons, [ pat1; pat2 ]),
      Pexpr (_, _, PEbase (Blist (bTy_elem, cval :: cvals))) ) ->
      (* populated list (value) *)
      subst_pattern_val pat1 cval
        (subst_pattern_val pat2 (Blist (bTy_elem, cvals)) expr1)
  | CaseDtor (Dcons, [ pat1; pat2 ]), Pexpr (_, _, PEctor (Ccons, [ pe1; pe2 ]))
    ->
      (* populated list (pure expr) *)
      unsafe_subst_pattern pat1 pe1 (unsafe_subst_pattern pat2 pe2 expr1)
  | CaseDtor (Dtuple, pats'), Pexpr (_, _, PEbase (Btuple cvals)) ->
      List.fold_right
        (fun (pat', cval) acc -> subst_pattern_val pat' cval acc)
        (List.combine pats' cvals)
        expr1
  | CaseDtor (Dtuple, pats'), Pexpr (_, _, PEctor (Ctuple, pes)) ->
      List.fold_right
        (fun (pat', pe) acc -> unsafe_subst_pattern pat' pe acc)
        (List.combine pats' pes)
        expr1
      (* TODO (maybe), Carray, Civmax, Civmin, Civsizeof, Civalignof *)
  | ( CaseDtor (Dspecified, [ pat' ]),
      Pexpr (_, _, PEbase (Bloaded (LVspecified oval))) ) ->
      subst_pattern_val pat' (Bobject oval) expr1
  | CaseDtor (Dspecified, [ pat' ]), Pexpr (_, _, PEctor (Cspecified, [ pe'' ]))
    ->
      unsafe_subst_pattern pat' pe'' expr1
  | ( CaseDtor (Dunspecified, [ pat' ]),
      Pexpr (_, _, PEbase (Bloaded (LVunspecified ty1))) ) ->
      subst_pattern_val pat' (Bctype ty1) expr1
  | ( CaseDtor (Dunspecified, [ pat' ]),
      Pexpr (_, _, PEctor (Cunspecified, [ pe'' ])) ) ->
      unsafe_subst_pattern pat' pe'' expr1
  | CaseDtor (dtor1, pats), _ ->
      let str_dtor =
        match dtor1 with
        | Dnil _ -> "nil"
        | Dcons -> "cons"
        | Dtuple -> "tuple"
        | Dspecified -> "specified"
        | Dunspecified -> "unspecified"
      in
      Cerb_debug.error
        ("WIP: Core_aux.unsafe_subst_pattern ==> dtor= " ^ str_dtor
       ^ ", |pats|= "
        ^ string_of_int (List.length pats)
        ^ " -- "
        ^ String_core.string_of_pexpr pe')

(*val     subst_pattern: forall 'a. pattern -> pexpr -> expr 'a -> maybe (expr 'a)*)
let rec subst_pattern (Pattern (_, pat)) pe' expr1 =
  match (pat, pe') with
  | CaseBase (None, _), _ -> Some expr1
  | CaseBase (Some sym1, _), _ -> Some (unsafe_subst_sym_expr sym1 pe' expr1)
  | CaseDtor (Dnil _, []), Pexpr (_, _, PEbase (Blist (_, []))) ->
      (* empty list (value) *)
      Some expr1
  | CaseDtor (Dnil _, []), Pexpr (_, _, PEctor (Cnil _, [])) ->
      (* empty list (pure expr) *)
      Some expr1
  | ( CaseDtor (Dcons, [ pat1; pat2 ]),
      Pexpr (_, _, PEbase (Blist (bTy_elem, cval :: cvals))) ) ->
      (* populated list (value) *)
      Some
        (subst_pattern_val pat1 cval
           (subst_pattern_val pat2 (Blist (bTy_elem, cvals)) expr1))
  | CaseDtor (Dcons, [ pat1; pat2 ]), Pexpr (_, _, PEctor (Ccons, [ pe1; pe2 ]))
    -> (
      (* populated list (pure expr) *)
      match subst_pattern pat2 pe2 expr1 with
      | Some e -> subst_pattern pat1 pe1 e
      | None -> None)
  | CaseDtor (Dtuple, pats'), Pexpr (_, _, PEbase (Btuple cvals)) ->
      Some
        (List.fold_right
           (fun (pat', cval) acc -> subst_pattern_val pat' cval acc)
           (List.combine pats' cvals)
           expr1)
  | CaseDtor (Dtuple, pats'), Pexpr (_, _, PEctor (Ctuple, pes)) ->
      List.fold_right
        (fun (pat', pe) acc ->
          match acc with Some e -> subst_pattern pat' pe e | None -> None)
        (List.combine pats' pes)
        (Some expr1)
      (* TODO (maybe), Carray, Civmax, Civmin, Civsizeof, Civalignof *)
  | ( CaseDtor (Dspecified, [ pat' ]),
      Pexpr (_, _, PEbase (Bloaded (LVspecified oval))) ) ->
      Some (subst_pattern_val pat' (Bobject oval) expr1)
  | CaseDtor (Dspecified, [ pat' ]), Pexpr (_, _, PEctor (Cspecified, [ pe'' ]))
    ->
      subst_pattern pat' pe'' expr1
  | ( CaseDtor (Dunspecified, [ pat' ]),
      Pexpr (_, _, PEbase (Bloaded (LVunspecified ty1))) ) ->
      Some (subst_pattern_val pat' (Bctype ty1) expr1)
  | ( CaseDtor (Dunspecified, [ pat' ]),
      Pexpr (_, _, PEctor (Cunspecified, [ pe'' ])) ) ->
      subst_pattern pat' pe'' expr1
  | CaseDtor (dtor1, pats), _ -> None

let rec to_pure (Expr (annots, expr_)) =
  let to_pure_aux pat pe1 e2 =
    match subst_pattern pat pe1 e2 with
    | Some e -> to_pure e
    | None -> (
        match to_pure e2 with
        | None -> None
        | Some pe2 -> Some (mk_let_pe pat pe1 pe2))
  in
  match expr_ with
  | Ememop (_, _)
  | Eaction _
  | Eccall (_, _, _, _)
  | Eproc (_, _, _)
  | Esave (_, _, _)
  | Erun (_, _, _)
  | End _
  | Epar _
  | Ewait _ -> None
  | Epure pe -> Some pe
  | Elet (pat, pe1, e2) -> (
      match to_pure e2 with
      | Some (Pexpr (_, bTy, _) as pe2) ->
          Some (Pexpr (annots, bTy, PElet (pat, pe1, pe2)))
      | _ -> None)
  | Eif (pe1, e2, e3) -> (
      match to_pure e2, to_pure e3 with
      | Some (Pexpr (_, bTy, _) as pe2), Some pe3 ->
          Some (Pexpr (annots, bTy, PEif (pe1, pe2, pe3)))
      | _ -> None)
  | Eunseq es ->
      Option.map mk_tuple_pe (to_pures es)
  | Ewseq (pat, e1, e2) ->
      (match to_pure e1 with Some pe1 -> to_pure_aux pat pe1 e2 | None -> None)
  | Esseq (pat, e1, e2) ->
      (match to_pure e1 with Some pe1 -> to_pure_aux pat pe1 e2 | None -> None)
  | Ebound e ->
      (* TODO: check *)
      to_pure e
  | Eannot (_, _) -> Cerb_debug.error "to_pure Eannot"
  | Eexcluded (_, _) -> Cerb_debug.error "to_pure Eexcluded"
  | Ecase (pe, pat_es) -> (
      let pats, es = List.split pat_es in
      match to_pures es with
      | Some (Pexpr (annot1, bTy, _) :: _ as pes) ->
          Some
            (Pexpr (annot1, bTy, PEcase (pe, List.combine pats pes)))
      | _ -> None)

and to_pures es =
  List.fold_right
    (fun e acc_opt ->
      match (to_pure e, acc_opt) with
      | Some pe, Some acc -> Some (pe :: acc)
      | _ -> None)
    es (Some [])

(*val subst_wait: forall 'a. Mem_common.thread_id -> value -> expr 'a -> expr 'a*)
let rec subst_wait tid1 v (Expr (annot1, expr_)) =
  Expr
    ( annot1,
      match expr_ with
      | Epure _ -> expr_
      | Ememop (_, _) -> expr_
      | Elet (sym1, pe1, e2) -> Elet (sym1, pe1, subst_wait tid1 v e2)
      | Eif (pe1, e2, e3) ->
          Eif (pe1, subst_wait tid1 v e2, subst_wait tid1 v e3)
      | Ecase (pe, pat_es) ->
          Ecase
            ( pe,
              List.map (fun (pat, e) -> (pat, subst_wait tid1 v e)) pat_es
            )
      | Eccall (_, _, _, _) -> expr_
      | Eproc (_, _, _) -> expr_
      | Eaction _ -> expr_
      | Eunseq es -> Eunseq (List.map (subst_wait tid1 v) es)
      | Ewseq (_as, e1, e2) ->
          Ewseq (_as, subst_wait tid1 v e1, subst_wait tid1 v e2)
      | Esseq (_as, e1, e2) ->
          Esseq (_as, subst_wait tid1 v e1, subst_wait tid1 v e2)
      | Ebound e -> Ebound (subst_wait tid1 v e)
      (*
   | Esave ksym sym_tys e ->
       Esave ksym sym_tys (subst_wait tid v e)
   | (Erun _ _ _ as expr) ->
       expr
*)
      | Esave (sym1, sym_bTys, e) -> Esave (sym1, sym_bTys, subst_wait tid1 v e)
      | Erun (_, _, _) -> expr_
      | End es -> End (List.map (subst_wait tid1 v) es)
      | Epar es -> Epar (List.map (subst_wait tid1 v) es)
      | Ewait tid' ->
          if tid1 = tid' then
            match v with
            | Bunit -> Epure (mk_value_pe Bunit)
            | _ -> Epure (mk_value_pe v)
          else Ewait tid'
      | Eannot (xs, e) -> Eannot (xs, subst_wait tid1 v e)
      | Eexcluded (_, _) -> expr_
      (*
   | Eloc loc e ->
       Eloc loc (subst_wait tid v e)
   | Estd s e ->
       Estd s (subst_wait tid v e)
*)
    )

let rec find_labeled_continuation sym1 (Expr (annot1, expr_)) =
  match expr_ with
  | Epure _ -> None
  | Ememop (_, _) -> None
  | Eaction _ -> None
  | Ecase (_, pat_es) ->
      let () =
        Cerb_debug.warn [] (fun () ->
            "Core_aux.find_labeled_continuation assumes there is atmost single \
             match inside a Ecase")
      in
      List.fold_left
        (fun acc (_, e) ->
          match acc with
          | Some _ -> acc
          | None -> (
              match find_labeled_continuation sym1 e with
              | None -> None
              | Some ret -> Some ret))
        None pat_es
  | Elet (_, _, e2) -> find_labeled_continuation sym1 e2
  | Eif (_, e2, e3) -> (
      (* NOTE: in a well formed Core expr, [sym] cannot be bound in both e2 and e3. *)
      match find_labeled_continuation sym1 e2 with
      | Some z -> Some z
      | None -> find_labeled_continuation sym1 e3)
  | Eccall (_, _, _, _) -> None
  | Eproc (_, _, _) -> None
  | Eunseq _ ->
      (* NOTE: Typing forbids labeled continuation bindings inside unseq() *)
      None
  | Ewseq (pat, e1, e2) -> (
      let () =
        Cerb_debug.warn [] (fun () ->
            "Core_aux.find_labeled_continuation assumes the bindings of an \
             Esave inside a Ewseq don't clash")
      in
      match find_labeled_continuation sym1 e1 with
      | Some (syms, cont_expr) ->
          Some (syms, Expr (annot1, Ewseq (pat, cont_expr, e2)))
      | None -> find_labeled_continuation sym1 e2)
  | Esseq (pat, e1, e2) -> (
      let () =
        Cerb_debug.warn [] (fun () ->
            "Core_aux.find_labeled_continuation assumes the bindings of an \
             Esave inside a Esseq don't clash")
      in
      match find_labeled_continuation sym1 e1 with
      | Some (syms, cont_expr) ->
          Some (syms, Expr (annot1, Esseq (pat, cont_expr, e2)))
      | None -> find_labeled_continuation sym1 e2)
  | Ebound _ ->
      (* NOTE: Typing forbids labeled continuation bindings inside bound() *)
      None
  | End _ ->
      (* NOTE: Typing forbids labeled continuation bindings in inside nd() *)
      None
  | Esave ((sym', _), sym_bTys, e) ->
      if Sym.equal sym1 sym' then Some (Lem_list.map fst sym_bTys, e)
      else find_labeled_continuation sym1 e
  | Erun (annot1, sym1, pes) -> None
  | Epar es ->
      let () =
        Cerb_debug.warn [] (fun () ->
            "Core_aux.find_labeled_continuation assumes there are no Esave \
             inside par()")
      in
      None
  | Ewait _ -> None
  | Eannot (_, _) ->
      (* NOTE: Eannot only appear at runtime, and inside an Ebound, where
                 typing forbids labeled continuation bindings. *)
      None
  | Eexcluded (_, _) ->
      (* NOTE: Eexcluded only appear at runtime, and inside an Eexcluded, where
                 typing forbids labeled continuation bindings. *)
      None
(*
    | Eloc _ e ->
        find_labeled_continuation sym e
    | Estd _ e ->
        find_labeled_continuation sym e
*)

(*
val     has_sseqs: forall 'a. expr 'a -> bool
let rec has_sseqs expr =
  match expr with
    | Epure _ ->
        false
    | Ememop _ _ ->
        false
    | Eaction p ->
        false
    | Ecase _ pat_es ->
        List.any (fun (_, e) -> has_sseqs e) pat_es
    | Elet _ _ e2 ->
        has_sseqs e2
    | Eif _ e2 e3 ->
        has_sseqs e2 || has_sseqs e3
    | Eskip ->
        false
    | Eccall _ _ _ ->
        (* TODO: look into the called body *)
        false
    | Eproc _ _ _ ->
        (* TODO: look into the called body *)
        false
    | Eunseq es ->
        List.any has_sseqs es
    | Ewseq _ e1 e2 ->
        has_sseqs e1 || has_sseqs e2
    | Esseq _ _ _ ->
        true
    | Ebound e ->
        has_sseqs e
    | Esave _ _ e ->
        has_sseqs e
    | Erun _ _ _ ->
        false
    | End es ->
        List.any has_sseqs es
    | Epar _ ->
        (* TODO: I think *)
        false
    | Ewait _ ->
        false
    | Eloc _ e ->
        has_sseqs e
  end
*)

(*val     match_pattern: pattern -> value -> maybe (list (Sym.t * value))*)
let rec match_pattern (Pattern (_, pat)) cval =
  match (pat, cval) with
  | CaseBase (None, _), _ -> Some []
  | CaseBase (Some sym1, _), _ -> Some [ (sym1, cval) ]
  (*      | Bobject of (generic_object_value 'sym) *)
  | CaseDtor (Dspecified, [ pat' ]), Bloaded (LVspecified oval) ->
      match_pattern pat' (Bobject oval)
  | CaseDtor (Dunspecified, [ pat' ]), Bloaded (LVunspecified ty1) ->
      match_pattern pat' (Bctype ty1)
  (*      | Blist of core_base_type * list (generic_value 'sym) *)
  | CaseDtor (Dtuple, pats'), Btuple cvals' ->
      List.fold_right
        (fun (pat', cval') acc ->
          Lem.option_bind acc (fun xs ->
              Lem.option_bind (match_pattern pat' cval') (fun x ->
                  Some (List.rev_append (List.rev x) xs))))
        (List.combine pats' cvals')
        (Some [])
  | CaseDtor (Dnil _, []), Blist (_, []) ->
      let () =
        Cerb_debug.warn [] (fun () ->
            "Pattern matching nil without checking types!")
      in
      Some []
  | CaseDtor (Dcons, [ pat_x; pat_xs ]), Blist (ty1, x :: xs) ->
      Lem.option_bind (match_pattern pat_x x) (fun x ->
          Lem.option_bind
            (match_pattern pat_xs (Blist (ty1, xs)))
            (fun xs -> Some (List.rev_append (List.rev x) xs)))
  | _ -> None

(*val     select_case: forall 'a. (Sym.t -> value -> 'a -> 'a) -> value -> list (pattern * 'a) -> maybe 'a*)
let rec select_case subst_sym cval =
 (function
 | [] -> None
 | (pat, pe) :: pat_pes' -> (
     match match_pattern pat cval with
     | None ->
         (* trying the next branch *)
         select_case subst_sym cval pat_pes'
     | Some sym_cvals ->
         Some
           (List.fold_right
              (fun (sym1, cval') acc -> subst_sym sym1 cval' acc)
              sym_cvals pe)))


(*val add_loc: Loc.t -> expr unit -> expr unit*)
let add_loc loc1 (Expr (annot1, expr_)) =
  let pred = function Aloc _ -> true | _ -> false in
  Expr
    ( (match Lem_list.list_delete_first pred annot1 with
      | None -> Aloc loc1 :: annot1
      | Some xs' -> Aloc loc1 :: xs'),
      expr_ )

(*val add_stmt: expr unit -> expr unit*)
let add_stmt (Expr (annot1, expr_)) = Expr (Astmt :: annot1, expr_)

(*val add_expr: expr unit -> expr unit*)
let add_expr (Expr (annot1, expr_)) = Expr (Aexpr :: annot1, expr_)

(*val add_std: string -> expr unit -> expr unit*)
let add_std str (Expr (annot1, expr_)) = Expr (Astd str :: annot1, expr_)

(*val add_stds: list string -> expr unit -> expr unit*)
let add_stds strs (Expr (annot1, expr_)) =
  Expr
    ( List.rev_append (List.rev (List.map (fun z -> Astd z) strs)) annot1,
      expr_ )

(*val add_attrs: Annot.attributes -> expr unit -> expr unit*)
let add_attrs attrs1 (Expr (annot1, expr_) as expr1) =
  match attrs1 with
  | Attrs [] -> expr1
  | _ -> Expr (Aattrs attrs1 :: annot1, expr_)

(*val add_annot: Annot.annot -> expr unit -> expr unit*)
let add_annot annot1 (Expr (annots1, expr_)) = Expr (annot1 :: annots1, expr_)

(*val add_annots: list Annot.annot -> expr unit -> expr unit*)
let add_annots annots1 (Expr (annots2, expr_)) =
  Expr (List.rev_append (List.rev annots1) annots2, expr_)

type 'a collect_saves_state = {
  tmp_acc :
    (Sym.t, (Sym.t * core_base_type) list * 'a Core.expr) Pmap.map;
      (*Core.labeled_continuations 'a; *)
  closed_acc :
    (Sym.t, (Sym.t * core_base_type) list * 'a Core.expr) Pmap.map;
      (*Core.labeled_continuations 'a; *)
}

let empty_saves =
  { tmp_acc= Sym.empty_pmap
  ; closed_acc = Sym.empty_pmap }

let union_saves st1 st2 =
  {
    tmp_acc = Pmap.union st1.tmp_acc st2.tmp_acc;
    closed_acc = Pmap.union st1.closed_acc st2.closed_acc;
  }

(* NOTE: assumes the expression is well formed/typed *)
(*val     collect_saves_aux: forall 'a. collect_saves_state 'a -> expr 'a -> collect_saves_state 'a*)
let rec collect_saves_aux st (Expr (annots1, expr_)) =
  match expr_ with
  | Epure _ -> st
  | Ememop (_, _) -> st
  | Eaction _ -> st
  | Ecase (_, pat_es) ->
      List.fold_left (fun acc (_, e) -> collect_saves_aux acc e) st pat_es
  | Elet (_, _, e) -> collect_saves_aux st e
  | Eif (_, e1, e2) -> collect_saves_aux (collect_saves_aux st e1) e2
  | Eccall (_, _, _, _) -> st
  | Eproc (_, _, _) -> st
  | Eunseq es -> List.fold_left collect_saves_aux st es
  | Ewseq (pat, e1, e2) ->
      let st1 = collect_saves_aux empty_saves e1 in
      let st2 = collect_saves_aux empty_saves e2 in
      union_saves st
        (union_saves
           {
             st1 with
             tmp_acc =
               Pmap.map
                 (fun (syms, e) -> (syms, Expr (annots1, Ewseq (pat, e, e2))))
                 st1.tmp_acc;
           }
           st2)
  | Esseq (pat, e1, e2) ->
      let st1 = collect_saves_aux empty_saves e1 in
      let st2 = collect_saves_aux empty_saves e2 in
      union_saves st
        (union_saves
           {
             st1 with
             tmp_acc =
               Pmap.map
                 (fun (syms, e) -> (syms, Expr (annots1, Esseq (pat, e, e2))))
                 st1.tmp_acc;
           }
           st2)
  | Ebound _ ->
      (* typing forbids "saves" inside a "bound()" *)
      st
  | End _ ->
      (* typing forbids "saves" inside a "nd()" *)
      st
  | Esave ((sym1, _), params, e) ->
      collect_saves_aux
        {
          st with
          tmp_acc =
            Pmap.add sym1
              (List.map (fun (x, ((y, _), _)) -> (x, y)) params, e)
              st.tmp_acc;
        }
        e
  | Erun (_, _, _) -> st
  | Epar es ->
      let acc = List.fold_left collect_saves_aux empty_saves es in
      {
        st with
        closed_acc =
          Pmap.union (Pmap.union acc.tmp_acc acc.closed_acc) st.closed_acc;
      }
  | Ewait _ -> st
  | Eannot (_, _) ->
      (* typing forbids "saves" inside a "annot()" *)
      st
  | Eexcluded (_, _) ->
      (* typing forbids "saves" inside a "excluded()" *)
      st

(*val collect_saves: forall 'a. expr 'a -> map Sym.t (list (Sym.t * core_base_type) * expr 'a)*)
(*Core.labeled_continuations 'a *)
let collect_saves expr1 =
  let st =
    collect_saves_aux
      { tmp_acc=Sym.empty_pmap; closed_acc= Sym.empty_pmap }
      expr1
  in
  Pmap.union st.tmp_acc st.closed_acc

(* The same again, now collecting more information about the
   esave. The above could be defined in terms of the below, but I
   didn't want to mess that up, so leaving for now. *)

type 'a m_labeled_continuation =
  core_base_type
  * (Sym.t
    * ((core_base_type * (Ctype.ctype * pass_by_value_or_pointer) option)
      * pexpr))
    list
  * 'a expr
  * Annot.annot list

type 'a m_labeled_continuations =
  (Sym.t, 'a m_labeled_continuation) Pmap.map

type 'a m_collect_saves_state = {
  m_tmp_acc : 'a m_labeled_continuations;
  m_closed_acc : 'a m_labeled_continuations;
}

let m_empty_saves =
  { m_tmp_acc= Sym.empty_pmap; m_closed_acc= Sym.empty_pmap }

let m_union_saves st1 st2 =
  {
    m_tmp_acc = Pmap.union st1.m_tmp_acc st2.m_tmp_acc;
    m_closed_acc = Pmap.union st1.m_closed_acc st2.m_closed_acc;
  }

(* NOTE: assumes the expression is well formed/typed *)
(*val     m_collect_saves_aux: forall 'a. m_collect_saves_state 'a -> expr 'a -> m_collect_saves_state 'a*)
let rec m_collect_saves_aux st (Expr (annots1, expr_)) =
  match expr_ with
  | Epure _ -> st
  | Ememop (_, _) -> st
  | Eaction _ -> st
  | Ecase (_, pat_es) ->
      List.fold_left (fun acc (_, e) -> m_collect_saves_aux acc e) st pat_es
  | Elet (_, _, e) -> m_collect_saves_aux st e
  | Eif (_, e1, e2) -> m_collect_saves_aux (m_collect_saves_aux st e1) e2
  | Eccall (_, _, _, _) -> st
  | Eproc (_, _, _) -> st
  | Eunseq es -> List.fold_left m_collect_saves_aux st es
  | Ewseq (pat, e1, e2) ->
      let st1 = m_collect_saves_aux m_empty_saves e1 in
      let st2 = m_collect_saves_aux m_empty_saves e2 in
      m_union_saves st
        (m_union_saves
           {
             st1 with
             m_tmp_acc =
               Pmap.map
                 (fun (cbt, args, body, annots') ->
                   (cbt, args, Expr (annots1, Ewseq (pat, body, e2)), annots'))
                 st1.m_tmp_acc;
           }
           st2)
  | Esseq (pat, e1, e2) ->
      let st1 = m_collect_saves_aux m_empty_saves e1 in
      let st2 = m_collect_saves_aux m_empty_saves e2 in
      m_union_saves st
        (m_union_saves
           {
             st1 with
             m_tmp_acc =
               Pmap.map
                 (fun (cbt, args, body, annots') ->
                   (cbt, args, Expr (annots1, Esseq (pat, body, e2)), annots'))
                 st1.m_tmp_acc;
           }
           st2)
  | Ebound _ ->
      (* typing forbids "saves" inside a "bound()" *)
      st
  | End _ ->
      (* typing forbids "saves" inside a "nd()" *)
      st
  | Esave ((sym1, ty1), params, e) ->
      let oloc = Annot.get_loc annots1 in
      let () =
        match oloc with
        | Some _ -> ()
        | _ ->
            Cerb_debug.print_debug 0 [] (fun () ->
                "label " ^ Sym.show sym1 ^ "missing label location")
      in
      m_collect_saves_aux
        {
          st with
          m_tmp_acc = Pmap.add sym1 (ty1, params, e, annots1) st.m_tmp_acc;
        }
        e
  | Erun (_, _, _) -> st
  | Epar es ->
      let acc = List.fold_left m_collect_saves_aux m_empty_saves es in
      {
        st with
        m_closed_acc =
          Pmap.union (Pmap.union acc.m_tmp_acc acc.m_closed_acc) st.m_closed_acc;
      }
  | Ewait _ -> st
  | Eannot (_, _) -> st
  | Eexcluded (_, _) -> st

(*val m_collect_saves: forall 'a. expr 'a -> m_labeled_continuations 'a*)
let m_collect_saves expr1 =
  let st =
    m_collect_saves_aux
      { m_tmp_acc=Sym.empty_pmap; m_closed_acc= Sym.empty_pmap }
      expr1
  in
  Pmap.union st.m_tmp_acc st.m_closed_acc

(*import Map_extra*)

(*val collect_labeled_continuations_NEW: forall 'a. file 'a -> map Sym.t (map Sym.t (list (Sym.t * core_base_type) * expr 'a) (*Core.labeled_continuations 'a *))*)
let collect_labeled_continuations_NEW file1 =
  (*  let xs =  *)
  Pmap.fold
    (fun fun_sym decl acc ->
      match decl with
      | Fun (_, _, _) -> acc
      | ProcDecl (_, _, _) -> acc
      | BuiltinDecl (_, _, _) -> acc
      | Proc (_, _, _, _, e) -> Pmap.add fun_sym (collect_saves e) acc)
    (Pmap.union file1.stdlib file1.funs)
    Sym.empty_pmap

(*
in
  let _ = Map.mapi (fun sym labs ->
    Debug.print_debug 2 [] (fun () ->
      "PROC " ^ show sym ^ " ==>\n" ^
      List.foldl (fun acc (sym, (_, e)) -> show sym ^ " ==> " ^ Pp.stringFromCore_expr e) "" (Map_extra.toList labs) 
    )
  ) xs in
  xs
*)

(*val     update_env: pattern -> value -> list (map Sym.t value) -> list (map Sym.t value)*)
let rec update_env_aux (Pattern (_, pat)) cval env1 =
  (* TODO (maybe), Carray, Civmax, Civmin, Civsizeof, Civalignof *)
  match (pat, cval) with
  | CaseBase (None, _), _ ->
      (* e[_ \ v] = e *)
      env1
  | CaseBase (Some sym1, _), _ ->
      (* e[sym \ v] *)
      Pmap.add sym1 cval env1
  | CaseDtor (Dnil _, []), Blist (_, []) ->
      (* empty list (value) *)
      env1
  | CaseDtor (Dcons, [ pat1; pat2 ]), Blist (bTy_elem, cval1 :: cvals) ->
      (* populated list (value) *)
      update_env_aux pat1 cval1
        (update_env_aux pat2
           (Blist (bTy_elem, cvals))
           env1)
  | CaseDtor (Dtuple, pats'), Btuple cvals ->
      List.fold_right
        (fun (pat', cval') acc ->
          update_env_aux pat' cval' acc)
        (List.combine pats' cvals)
        env1
  | CaseDtor (Dspecified, [ pat' ]), Bloaded (LVspecified oval) ->
      update_env_aux pat' (Bobject oval) env1
  | CaseDtor (Dunspecified, [ pat' ]), Bloaded (LVunspecified ty1) ->
      update_env_aux pat' (Bctype ty1) env1
  | CaseDtor (dtor1, pats), _ ->
      let str_dtor =
        match dtor1 with
        | Dnil _ -> "nil"
        | Dcons -> "cons"
        | Dtuple -> "tuple"
        | Dspecified -> "specified"
        | Dunspecified -> "unspecified"
      in
      Cerb_debug.error
        ("WIP: Core_aux.update_env_aux ==> dtor= " ^ str_dtor ^ ", |pats|= "
        ^ string_of_int (List.length pats)
        ^ " -- "
        ^ String_core.string_of_value cval)

let update_env pat cval =
 (function
 | [] -> Cerb_debug.error "Core_aux.update_env: found empty env"
 | env1 :: xs ->
     update_env_aux
       pat cval env1
     :: xs)

let rec lookup_env sym1 =
 (function
 | [] -> None
 | env1 :: xs -> (
     match Pmap.lookup sym1 env1 with
     | None -> lookup_env sym1 xs
     | Some ret -> Some ret))
