[@@@landmark "auto"]

(* copy pasted from pp_core.ml and adapted *)
open Lem_pervasives
open Core
open Mucore
open Annot

open Either

open Colour

open Pp_prelude

type budget = int option


let pp_ctype ty =
  P.squotes (Pp_core_ctype.pp_ctype ty)

module Loc = Location_ocaml




module type PP_Typ = sig
  module T : Mucore.TYPES
  val pp_bt: T.bt -> PPrint.document
  val pp_ct: T.ct -> PPrint.document
  val pp_ft: T.ft -> PPrint.document
  val pp_gt: T.gt -> PPrint.document
  val pp_lt: T.lt -> PPrint.document
  val pp_st: T.st -> PPrint.document
  val pp_ut: T.ut -> PPrint.document
end

module type CONFIG = sig
  val ansi_format: ansi_style list -> string -> string
  val show_std: bool
  val show_include: bool
  val show_locations: bool
  val handle_location: Location_ocaml.t -> P.range -> unit
  val handle_uid: string -> P.range -> unit
end




let pp_symbol  a = !^ ((* ansi_format [Blue] *) (Pp_symbol.to_string_pretty a))
(* NOTE: Used to distinguish struct/unions globally *)




module Make (Config: CONFIG) (Pp_typ: PP_Typ) = struct

  open Config

  module Mu = Mucore.Make(Pp_typ.T)
  open Mu

  include Pp_typ

  let pp_keyword w = !^ (ansi_format [Bold; Magenta] w)
  let pp_const   c = !^ (ansi_format [Magenta] c)
  let pp_control w = !^ (ansi_format [Bold; Blue] w)
  let pp_raw_symbol  a = !^ (ansi_format [Blue] (Pp_symbol.to_string a))
  let pp_number  n = !^ (ansi_format [Yellow] n)
  let pp_impl    i = P.angles (!^ (ansi_format [Yellow] (Implementation.string_of_implementation_constant i)))
  let pp_undef ub = 
    P.angles (P.angles (!^ (ansi_format [Magenta] (Undefined.stringFromUndefined_behaviour ub))))


  let maybe_print_location : Loc.t -> P.document =
    if not show_locations then 
      fun loc -> P.empty
    else 
      fun loc -> 
      P.parens (Location_ocaml.pp_location ~clever:true loc) ^^ P.space



  let precedence = function
    | M_PEop (OpExp, _, _) -> Some 1

    | M_PEop (OpMul, _, _)
    | M_PEop (OpDiv, _, _)
    | M_PEop (OpRem_t, _, _)
    | M_PEop (OpRem_f, _, _) -> Some 2

    | M_PEop (OpAdd, _, _)
    | M_PEop (OpSub, _, _) -> Some 3

    | M_PEop (OpLt,  _, _)
    | M_PEop (OpLe,  _, _) -> Some 4

    | M_PEop (OpGt,  _, _)
    | M_PEop (OpGe,  _, _) -> Some 4

    | M_PEop (OpEq,  _, _) -> Some 5

    | M_PEop (OpAnd, _, _) -> Some 6

    | M_PEop (OpOr,  _, _) -> Some 7

    | M_PEerror _
    | M_PEval _
    | M_PEconstrained _
    | M_PEsym _
    | M_PEimpl _
    | M_PEctor _
    | M_PEarray_shift _
    | M_PEmember_shift _
    | M_PEnot _
    | M_PEstruct _
    | M_PEunion _
    | M_PEmemberof _
    | M_PEcall _
    | M_PEconv_int _
    | M_PEwrapI _ ->
       None
    | _ ->
        failwith "FIXME"

  let tprecedence = function
    | M_PEcase _ -> None
    | M_PElet _ -> None
    | M_PEif _ -> None
    | M_PEundef _ -> None
    | M_PEdone _ -> None

  let precedence_expr = function
    | M_Epure _
    | M_Ememop _
    | M_Eaction _
    | M_Eskip
    | M_Eproc _
    | M_Eccall _
    | M_Erpredicate _
    | M_Elpredicate _
    (* | M_Eunseq _ *)
    (* | M_Eindet _ *)
    (* | M_Epar _ *)
    (* | M_Ewait _ -> *)
      -> 
        None



  let precedence_texpr = function
    | M_Ecase _ -> None
    | M_Ebound _ -> None
    | M_End _ -> None
    | M_Eif _ ->
        Some 1
    | M_Elet _ ->
        Some 2
    (* | M_Easeq _ ->
     *     Some 3 *)
    | M_Esseq _ ->
        Some 3
    | M_Ewseq _ ->
        Some 4
    | M_Edone _ -> 
       None
    | M_Eundef _ ->
       None
    | M_Erun _ ->
       None
    (* | M_Esave _ ->
     *     Some 5 *)


  let compare_precedence p1 p2 =
    match (p1, p2) with
      | (Some n1, Some n2) -> n1 <= n2
      | _                  -> true





  (* let pp_core_type = function
   *   | TyBase   baseTy -> pp_base_type baseTy
   *   | TyEffect baseTy -> P.brackets (pp_base_type baseTy) *)


  let pp_binop = function
    | OpAdd -> P.plus
    | OpSub -> P.minus
    | OpMul -> P.star
    | OpDiv -> P.slash
    | OpRem_t -> pp_keyword "rem_t"
    | OpRem_f -> pp_keyword "rem_f"
    | OpExp -> P.caret
    | OpEq  -> P.equals
    | OpLt  -> P.langle
    | OpLe  -> P.langle ^^ P.equals
    | OpGt  -> P.rangle
    | OpGe  -> P.rangle ^^ P.equals
    | OpAnd -> !^ "/\\"
    | OpOr  -> !^ "\\/"








  let pp_polarity = function
    | Pos -> fun z -> z
    | Neg -> fun z -> pp_keyword "neg" ^^ P.parens z

  let pp_name = function
    | Sym a  -> pp_symbol a
    | Impl i -> pp_impl i






  let pp_memory_order = function
    | Cmm_csem.NA      -> !^ "NA"
    | Cmm_csem.Seq_cst -> pp_keyword "seq_cst"
    | Cmm_csem.Relaxed -> pp_keyword "relaxed"
    | Cmm_csem.Release -> pp_keyword "release"
    | Cmm_csem.Acquire -> pp_keyword "acquire"
    | Cmm_csem.Consume -> pp_keyword "consume"
    | Cmm_csem.Acq_rel -> pp_keyword "acq_rel"

  let pp_linux_memory_order = function
    | Linux.Once      -> pp_keyword "once"
    | Linux.LAcquire  -> pp_keyword "acquire"
    | Linux.LRelease  -> pp_keyword "release"
    | Linux.Rmb       -> pp_keyword "rmb"
    | Linux.Wmb       -> pp_keyword "wmb"
    | Linux.Mb        -> pp_keyword "mb"
    | Linux.RbDep     -> pp_keyword "rb-dep"
    | Linux.RcuLock   -> pp_keyword "rcu-lock"
    | Linux.RcuUnlock -> pp_keyword "rcu-unlock"
    | Linux.SyncRcu   -> pp_keyword "sync-rcu"

  let pp_mem_addr (pref, addr) =
  (*
    let rec pp = function
    | Cmm_aux_old.Lbase n          -> Pp_ail.pp_integer n
    | Cmm_aux_old.Lshift (addr, n) -> P.braces (pp addr ^^ P.comma ^^^ Pp_ail.pp_integer n)
    in
    P.at ^^ P.braces (pp_prefix pref ^^ P.colon ^^^ pp addr)
  *)
    P.at ^^ P.braces (Pp_symbol.pp_prefix pref ^^ P.colon ^^^ (!^ "TODO(addr)"))




  let pp_asym asym = pp_symbol asym.sym

  let pp_actype actype = pp_ct actype.ct

  let pp_actype_or_asym = function 
    | Left ct -> pp_actype ct 
    | Right sym -> pp_asym sym


  let pp_thread_id n =
    !^ ("th_" ^ string_of_int n)

  (*
  let pp_pattern pat =
    let g = function
      | Some (sym, _) -> pp_symbol sym
      | None   -> P.underscore in
    match pat with
      | []   -> P.lparen ^^ P.rparen
      | [sym_ty] -> g sym_ty
      | _    -> P.parens (comma_list g pat)
  *)


  (*
  let pp_pointer_action = function
    | PtrEq ->
        pp_keyword "pointer_eq"
    | PtrNe ->
        pp_keyword "pointer_ne"
    | PtrShift ->
        pp_keyword "pointer_shift"
  *)



  let rec pp_object_value = function
    | M_OVinteger ival ->
        Impl_mem.pp_integer_value_for_core ival
    | M_OVfloating fval ->
        Impl_mem.case_fval fval
          (fun () -> !^ "unspec(floating)")
          (fun fval -> !^(string_of_float fval))
  (*
    | M_OVsymbolic symb ->
        !^ "SYMB" ^^ P.parens (Pp_symbolic.pp_symbolic pp_object_value Pp_mem.pp_pointer_value symb)
  *)
    | M_OVpointer ptr_val ->
        Impl_mem.pp_pointer_value ptr_val
    | M_OVarray lvals ->
        pp_const "Array" ^^ P.parens (P.nest 1 (comma_list pp_loaded_value lvals))
    | M_OVstruct (tag_sym, xs) ->
        P.parens (pp_const "struct" ^^^ pp_raw_symbol tag_sym) ^^
        P.braces (
          comma_list (fun (Symbol.Identifier (_, ident), _, mval) ->
            P.dot ^^ !^ ident ^^ P.equals ^^^ Impl_mem.pp_mem_value mval
          ) xs
        )
    | M_OVunion (tag_sym, Symbol.Identifier (_, ident), mval) ->
        P.parens (pp_const "union" ^^^ pp_raw_symbol tag_sym) ^^
        P.braces (
          P.dot ^^ !^ ident ^^ P.equals ^^^ Impl_mem.pp_mem_value mval
        )
    (*| M_OVcfunction nm ->
        !^ "Cfunction" ^^ P.parens (pp_name nm) *)

  and pp_loaded_value = function
    | M_LVspecified oval ->
        pp_const "Specified" ^^ P.parens (pp_object_value oval)


  and pp_value = function
  (*
    | Vconstrained xs ->
        !^ "{-val-}" ^^^ pp_keyword "constrained" ^^ P.parens (
          comma_list (fun (cs, cval) ->
            P.brackets (Pp_mem.pp_mem_constraint Pp_mem.pp_integer_value cs) ^^^
            P.equals ^^ P.rangle ^^ pp_value cval
          ) xs
        )
  *)
    | M_Vunit ->
        pp_const "Unit"
    | M_Vtrue ->
        pp_const "True"
    | M_Vfalse ->
        pp_const "False"
    | M_Vlist (_, cvals) ->
        P.brackets (comma_list pp_value cvals)
    | M_Vtuple cvals ->
        P.parens (comma_list pp_value cvals)
    | M_Vobject oval ->
        pp_object_value oval
    | M_Vloaded lval ->
        pp_loaded_value lval

  let pp_ctor = function
    | M_Cnil _ ->
        !^ "Nil"
    | M_Ccons ->
        !^ "Cons"
    | M_Ctuple ->
        !^ "Tuple"
    | M_Carray ->
        !^ "Array"
    | M_Cspecified ->
        !^ "Specified"



  let rec pp_pattern (M_Pattern (_, _, pat)) =
    match pat with
    | M_CaseBase (None, bTy) ->
        P.underscore ^^ P.colon ^^^ pp_bt bTy
    | M_CaseBase (Some sym, bTy) ->
        pp_symbol sym ^^ P.colon ^^^ pp_bt bTy
  (* Syntactic sugar for tuples and lists *)
    | M_CaseCtor (M_Ctuple, pats) ->
        P.parens (comma_list pp_pattern pats)
    | M_CaseCtor (ctor, pats) ->
        pp_ctor ctor  ^^ P.parens (comma_list pp_pattern pats)

  let pp_sym_or_pattern = function
    | M_Symbol symbol -> pp_symbol symbol
    | M_Pat pat -> pp_pattern pat


  let abbreviated = P.dot ^^ P.dot ^^ P.dot


  let pp_pexpr (M_Pexpr (loc, annot, _, pe)) =
    let open PPrint in
    (maybe_print_location loc) ^^
      begin
        match pe with
          | M_PEerror (str, pe) ->
              pp_keyword "error" ^^ P.parens (P.dquotes (!^ str) ^^ P.comma ^^^ pp_asym pe)
          | M_PEval cval ->
              pp_value cval
          | M_PEconstrained xs ->
              pp_keyword "constrained" ^^ P.parens (
                comma_list (fun (cs, pe) ->
                  P.brackets (Pp_mem.pp_mem_constraint Impl_mem.pp_integer_value cs) ^^^
                  P.equals ^^ P.rangle ^^ pp_asym pe
                ) xs
              )
          | M_PEsym sym ->
              pp_symbol sym
          | M_PEimpl iCst ->
              pp_impl iCst
          | M_PEctor (M_Cnil _, pes) ->
             P.brackets P.empty
          | M_PEctor (M_Ctuple, pes) ->
              P.parens (comma_list pp_asym pes)
          | M_PEctor (ctor, pes) ->
              pp_ctor ctor ^^ P.parens (comma_list pp_asym pes)
          | M_CivCOMPL (ct, p1) ->
              !^"IvCOMPL" ^^ P.parens (separate comma [pp_actype ct; pp_asym p1])
          | M_CivAND (ct, p1, p2) ->
              !^"IvAND" ^^ P.parens (separate comma [pp_actype ct; pp_asym p1; pp_asym p2])
          | M_CivOR (ct, p1, p2) ->
              !^"IvOR" ^^ P.parens (separate comma [pp_actype ct; pp_asym p1; pp_asym p2])
          | M_CivXOR (ct, p1, p2) ->
              !^"IvXOR" ^^ P.parens (separate comma [pp_actype ct; pp_asym p1; pp_asym p2])
          | M_Cfvfromint p1 ->
              !^"Cfvfromint" ^^ P.parens (pp_asym p1)
          | M_Civfromfloat (ct, p1) ->
              !^"Civfromfloat" ^^ P.parens (separate comma [pp_actype ct; pp_asym p1])
          | M_PEarray_shift (pe1, ty, pe2) ->
              pp_keyword "array_shift" ^^ P.parens (
                pp_asym pe1 ^^ P.comma ^^^ pp_ct ty ^^ P.comma ^^^ pp_asym pe2
              )
          | M_PEmember_shift (pe, tag_sym, (Symbol.Identifier (_, memb_ident))) ->
              pp_keyword "member_shift" ^^ P.parens (
                pp_asym pe ^^ P.comma ^^^ pp_raw_symbol tag_sym ^^ P.comma ^^^ P.dot ^^ !^ memb_ident
              )
          | M_PEnot pe ->
              pp_keyword "not" ^^ P.parens (pp_asym pe)
          | M_PEop (bop, pe1, pe2) ->
              pp_asym pe1 ^^^ pp_binop bop ^^^ pp_asym pe2
          | M_PEstruct (tag_sym, xs) ->
              P.parens (pp_const "struct" ^^^ pp_raw_symbol tag_sym) ^^
              P.braces (
                comma_list (fun (Symbol.Identifier (_, ident), pe) ->
                  P.dot ^^ !^ ident ^^ P.equals ^^^ pp_asym pe
                ) xs
              )
          | M_PEunion (tag_sym, Symbol.Identifier (_, ident), pe) ->
              P.parens (pp_const "union" ^^^ pp_raw_symbol tag_sym) ^^
              P.braces (
                P.dot ^^ !^ ident ^^ P.equals ^^^ pp_asym pe
              )
          | M_PEmemberof (tag_sym, memb_ident, pe) ->
              pp_keyword "memberof" ^^ P.parens (
                pp_symbol tag_sym ^^ P.comma ^^^
                Pp_symbol.pp_identifier memb_ident ^^ P.comma ^^^
                pp_asym pe
              )
          | M_PEcall (nm, pes) ->
              pp_name nm ^^ P.parens (comma_list pp_asym pes)
          | M_PEassert_undef (asym, _uloc, ub) ->
              pp_keyword "assert_undef" ^^ P.parens (pp_asym asym ^^ P.comma ^^^pp_undef ub)
          | M_PEbool_to_integer asym ->
              pp_keyword "bool_to_integer" ^^ P.parens (pp_asym asym)
          | M_PEconv_int (act, asym) ->
              !^"conv_int" ^^ P.parens (pp_ct act.ct ^^ P.comma ^^^ pp_asym asym)
          | M_PEwrapI (act, asym) ->
              !^"wrapI" ^^ P.parens (pp_ct act.ct ^^ P.comma ^^^ pp_asym asym)
      end

  let pp_tpexpr budget pe =

    let rec pp budget prec (M_TPexpr (loc, annot, _, pe)) =
      match budget with
      | Some 0 -> abbreviated
      | _ -> 
      let budget' = match budget with
        | Some n -> Some (n-1)
        | None -> None
      in
      let prec' = tprecedence pe in
      let pp z = P.group (pp budget' prec' z) in
      let pp_pexpr pe = P.group (pp_pexpr pe) in
      (maybe_print_location loc) ^^
      (if compare_precedence prec' prec then fun z -> z else P.parens)
      begin
        match pe with
          | M_PEcase (pe, pat_pes) ->
            pp_keyword "case" ^^^ pp_asym pe ^^^ pp_keyword "of" ^^
            P.nest 2 (
              P.break 1 ^^ P.separate_map (P.break 1) (fun (cpat, pe) ->
                P.prefix 4 1
                  (P.bar ^^^ pp_pattern cpat ^^^ P.equals ^^ P.rangle)
                  (pp pe)
              ) pat_pes
            ) ^^ P.break 1 ^^ pp_keyword "end"
          | M_PElet (pat, pe1, pe2) ->
              (* DEBUG  !^ "{-pe-}" ^^^ *)
              pp_control "let" ^^^ pp_sym_or_pattern pat ^^^ P.equals ^^^
              pp_pexpr pe1 ^^^ pp_control "in" ^^ P.break 1 ^^ pp pe2
          | M_PEif (pe1, pe2, pe3) ->
              P.group (
                pp_control "if" ^^^ pp_asym pe1 ^^^ pp_control "then" ^^
                P.nest 2 (P.break 1 ^^ pp pe2) ^^ P.break 1 ^^
                pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp pe3)
              )
          | M_PEdone asym ->
              pp_control "done" ^^^ pp_asym asym
          | M_PEundef (_, ub) ->
              pp_keyword "undef" ^^ P.parens (pp_undef ub)
      end
    in pp budget None pe



  let pp_action act =
    let pp_args args mo =
      P.parens (comma_list pp_actype_or_asym args ^^ if mo = Cmm_csem.NA then P.empty else P.comma ^^^ pp_memory_order mo) in
    match act with
      | M_Create (al, ty, _) ->
          pp_keyword "create" ^^ P.parens (pp_asym al ^^ P.comma ^^^ pp_actype ty)
      | M_CreateReadOnly (al, ty, init, _) ->
          pp_keyword "create_readonly" ^^ P.parens (pp_asym al ^^ P.comma ^^^ pp_actype ty ^^ P.comma ^^^ pp_asym init)
      | M_Alloc (al, n, _) ->
          pp_keyword "alloc" ^^ P.parens (pp_asym al ^^ P.comma ^^^ pp_asym n)
      | M_Kill (M_Dynamic, e) ->
          pp_keyword "free" ^^ P.parens (pp_asym e)
      | M_Kill (M_Static ct, e) ->
          pp_keyword "kill" ^^ P.parens (pp_ct ct ^^ P.comma ^^^ pp_asym e)
      | M_Store (is_locking, ty, e1, e2, mo) ->
         pp_keyword (if is_locking then "store_lock" else "store") ^^ pp_args [Left ty; Right e1; Right e2] mo
      | M_Load (ty, e, mo) ->
         pp_keyword "load" ^^ pp_args [Left ty; Right e] mo
      | M_RMW (ty, e1, e2, e3, mo1, mo2) ->
          pp_keyword "rmw" ^^
          P.parens (pp_actype ty ^^ P.comma ^^^ pp_asym e1 ^^ P.comma ^^^
                    pp_asym e2 ^^ P.comma ^^^ pp_asym e3 ^^ P.comma ^^^
                    pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
      | M_Fence mo ->
          pp_keyword "fence" ^^ P.parens (pp_memory_order mo)
      | M_CompareExchangeStrong (ty, e1, e2, e3, mo1, mo2) ->
          pp_keyword "compare_exchange_strong" ^^
          P.parens (pp_actype ty ^^ P.comma ^^^ pp_asym e1 ^^ P.comma ^^^
                    pp_asym e2 ^^ P.comma ^^^ pp_asym e3 ^^ P.comma ^^^
                    pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
      | M_CompareExchangeWeak (ty, e1, e2, e3, mo1, mo2) ->
          pp_keyword "compare_exchange_weak" ^^
          P.parens (pp_actype ty ^^ P.comma ^^^ pp_asym e1 ^^ P.comma ^^^
                    pp_asym e2 ^^ P.comma ^^^ pp_asym e3 ^^ P.comma ^^^
                    pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
      | M_LinuxFence mo ->
          pp_keyword "linux_fence" ^^ P.parens (pp_linux_memory_order mo)
      | M_LinuxStore (ty, e1, e2, mo) ->
          pp_keyword "linux_store" ^^
          P.parens (comma_list pp_actype_or_asym [Left ty;Right e1;Right e2] ^^ P.comma ^^^
                    pp_linux_memory_order mo)
      | M_LinuxLoad (ty, e, mo) ->
          pp_keyword "linux_load" ^^
          P.parens (comma_list pp_actype_or_asym [Left ty;Right e] ^^ P.comma ^^^
                    pp_linux_memory_order mo)
      | M_LinuxRMW (ty, e1, e2, mo) ->
          pp_keyword "linux_rmw" ^^
          P.parens (comma_list pp_actype_or_asym [Left ty;Right e1;Right e2] ^^ P.comma ^^^
                    pp_linux_memory_order mo)

  let do_annots annot = 
        fun doc ->
          List.fold_left (fun acc annot_elem ->
            match annot_elem with
              | Aloc loc ->
                  P.range (handle_location loc) acc
              | Astd str ->
                  if show_std then
                    !^"{-#" ^^ !^ str ^^ !^"#-}" ^^ P.hardline ^^ acc
                  else
                    acc
              | Auid uid ->
                  P.range (handle_uid uid) acc
              | Abmc annot ->
                  begin match annot with
                  | Abmc_id id ->
                      !^"{-" ^^ !^(string_of_int id) ^^ !^"-}" ^^ acc
                  end
              | Atypedef sym ->
                !^"{-" ^^ pp_symbol sym ^^ !^"-}" ^^ acc
              | Aattrs _ ->
                  !^ "TODO(Aattrs)"
              | Anot_explode ->
                 !^"{-not-explode-}" ^^ acc
              | Alabel _ -> acc
                 (* !^"{-return-}" ^^ acc *)
          ) doc annot

  let pp_expr (M_Expr (loc, annot, e) : 'ty mu_expr) =

    do_annots annot
      begin
        (maybe_print_location loc) ^^
        begin match (e : 'ty mu_expr_) with
          | M_Epure pe ->
              pp_keyword "pure" ^^ P.parens (pp_pexpr pe)
          | M_Ememop memop ->

             let aux memop =
               let open Mem_common in
               let mctype ct1=  (Either.Left ct1) in
               let msym sym1=  (Either.Right sym1) in
               match memop with
               | M_PtrEq (sym1,sym2) ->
                  (PtrEq, 
                   [msym sym1; msym sym2])
               | M_PtrNe (sym1,sym2) ->
                  (PtrNe, 
                   [msym sym1; msym sym2])
               | M_PtrLt (sym1,sym2) ->
                  (PtrLt, 
                   [msym sym1; msym sym2])
               | M_PtrGt (sym1,sym2) ->
                  (PtrGt, 
                   [msym sym1; msym sym2])
               | M_PtrLe (sym1,sym2) ->
                  (PtrLe, 
                   [msym sym1; msym sym2])
               | M_PtrGe (sym1,sym2) ->
                  (PtrGe, 
                   [msym sym1; msym sym2])
               | M_Ptrdiff (ct1,sym1,sym2) ->
                  (Ptrdiff, 
                   [mctype ct1; msym sym1; msym sym2])
               | M_IntFromPtr (ct1,ct2,sym1) ->
                  (IntFromPtr, 
                   [mctype ct1; mctype ct2; msym sym1])
               | M_PtrFromInt (ct1,ct2,sym1) ->
                  (PtrFromInt, 
                   [mctype ct1; mctype ct2; msym sym1])
               | M_PtrValidForDeref (ct1,sym1) ->
                  (PtrValidForDeref, 
                   [mctype ct1; msym sym1])
               | M_PtrWellAligned (ct1,sym1) ->
                  (PtrWellAligned, 
                   [mctype ct1; msym sym1])
               | M_PtrArrayShift (sym1,ct1,sym2) ->
                  (PtrArrayShift, 
                   [msym sym1; mctype ct1; msym sym2])
               | M_PtrMemberShift (tag_sym, memb_ident, sym) ->
                  (PtrMemberShift (tag_sym, memb_ident),
                   [msym sym])
               | M_Memcpy (sym1,sym2,sym3) ->
                  (Memcpy, 
                   [msym sym1; msym sym2; msym sym3])
               | M_Memcmp (sym1,sym2,sym3) ->
                  (Memcmp, 
                   [msym sym1; msym sym2; msym sym3])
               | M_Realloc (sym1,sym2,sym3) ->
                  (Realloc, 
                   [msym sym1; msym sym2; msym sym3])
               | M_Va_start (sym1,sym2) ->
                  (Va_start, 
                   [msym sym1; msym sym2])
               | M_Va_copy sym1 ->
                  (Va_copy, 
                   [msym sym1])
               | M_Va_arg (sym1,ct1) ->
                  (Va_arg, 
                   [msym sym1; mctype ct1])
               | M_Va_end sym1 ->
                  (Va_end, 
                   [msym sym1])
             in
            
             let (memop, pes) = aux memop in
             pp_keyword "memop" ^^ P.parens (Pp_mem.pp_memop memop ^^ P.comma ^^^ comma_list pp_actype_or_asym pes)
          | M_Eaction (M_Paction (p, (M_Action (_, act)))) ->
              pp_polarity p (pp_action act)
          | M_Eskip ->
              pp_keyword "skip"
          | M_Eproc (nm, pes) ->
              pp_keyword "pcall" ^^ P.parens (pp_name nm ^^ P.comma ^^^ comma_list pp_asym pes)
          | M_Eccall (pe_ty, pe, pes) ->
              pp_keyword "ccall" ^^ P.parens (pp_ct pe_ty.ct) ^^
                P.parens (comma_list pp_actype_or_asym ((* Left pe_ty ::  *) Right pe :: (map (fun pe -> Right pe)) pes))
          | M_Erpredicate (pack_unpack, tpu, pes) ->
              pp_keyword (match pack_unpack with Pack -> "pack"  | Unpack -> "unpack") ^^^
                let tpu = match tpu with
                  | TPU_Struct sym -> !^"struct" ^^^ pp_symbol sym
                  | TPU_Predicate (Symbol.Identifier (_, ident)) -> !^ident
                in
                P.parens (tpu ^^ P.comma ^^^ comma_list pp_asym pes)
          | M_Elpredicate (have_show, id, pes) ->
              pp_keyword (match have_show with Have -> "have"  | Show -> "show") ^^^
                P.parens (Pp_symbol.pp_identifier id ^^ P.comma ^^^ comma_list pp_asym pes)
          (* | M_Eunseq [] ->
           *     !^ "BUG: UNSEQ must have at least two arguments (seen 0)" *)
          (* | M_Eunseq [e] ->
           *     !^ "BUG: UNSEQ must have at least two arguments (seen 1)" ^^ (pp_control "[-[-[") ^^ pp e ^^ (pp_control "]-]-]") *)
          (* | M_Eunseq es ->
           *     pp_control "unseq" ^^ P.parens (comma_list pp es) *)
        end
      end


  let pp_texpr budget (expr : 'ty mu_texpr) =

    let rec pp budget prec (M_TExpr (loc, annot, e) : 'ty mu_texpr) =

      match budget with
      | Some 0 -> abbreviated
      | _ -> 

      let budget' = match budget with
        | Some n -> Some (n-1)
        | None -> None
      in

      let prec' = precedence_texpr e in
      (* let pp_ z = pp budget' true prec' z in  (\* TODO: this is sad *\) *)
      let pp z = pp budget' prec' z in

      do_annots annot
      begin
        (maybe_print_location loc) ^^
        begin
          (* Here we check whether parentheses are needed *)
          (* if compare_precedence prec' prec then
           *   (\* right associativity of ; *\)
           *   match (is_semi, e) with
           *     | (true, M_Esseq (M_Pattern (_, M_CaseBase (None, BTy_unit)), _, _)) ->
           *         P.parens
           *     | _ ->
           *         fun z -> z
           * else *)
            P.parens
        end
        begin match (e : 'ty mu_texpr_) with
          | M_Ecase (pe, pat_es) ->
              pp_keyword "case" ^^^ pp_asym pe ^^^ pp_keyword "of" ^^
              P.nest 2 (
                P.break 1 ^^ P.separate_map (P.break 1) (fun (cpat, e) ->
                  P.prefix 4 1
                    (P.bar ^^^ pp_pattern cpat ^^^ P.equals ^^ P.rangle)
                    (pp e)
                ) pat_es
              ) ^^ P.break 1 ^^ pp_keyword "end"
          | M_Elet (pat, pe1, e2) ->
              P.group (
                P.prefix 0 1
                  (pp_control "let" ^^^ pp_sym_or_pattern pat ^^^ P.equals ^^^ 
                     pp_pexpr pe1 ^^^ pp_control "in")
                  (pp e2)
             )
          | M_Eif (pe1, e2, e3) ->
              pp_control "if" ^^^ pp_asym pe1 ^^^ pp_control "then" ^^
              P.nest 2 (P.break 1 ^^ pp e2) ^^ P.break 1 ^^
              pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp e3)
          | M_Ewseq (pat, e1, e2) ->
              P.group (
                pp_control "let weak" ^^^ pp_pattern pat ^^^ P.equals ^^^
                let doc_e1 = pp_expr e1 in
                P.ifflat doc_e1 (P.nest 2 (P.break 1 ^^ doc_e1)) ^^^ pp_control "in"
              ) ^^
              P.break 1 ^^ (pp e2)
          (* | M_Esseq (M_Pattern (_, M_CaseBase (None, BTy_unit)), e1, e2) ->
           *     (pp_ e1 ^^^ P.semi) ^/^ (pp e2) *)
          | M_Esseq (pat, e1, e2) ->
              P.group (
                pp_control "let strong" ^^^ pp_sym_or_pattern pat ^^^ P.equals ^^^
                let doc_e1 = pp_expr e1 in
                P.ifflat doc_e1 (P.nest 2 (P.break 1 ^^ doc_e1)) ^^^ pp_control "in"
              ) ^^
              P.break 1 ^^ (pp e2)
          (* | M_Easeq ((sym, bTy), act1, pact2) ->
           *     pp_control "let atom" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_base_type bTy ^^^ P.equals ^^^
           *     pp (Expr ([], Eaction (Paction (Pos, act1)))) ^^^ pp_control "in" ^^^ pp (Expr ([], Eaction pact2)) *)
          (* | M_Eindet (i, e) ->
           *     pp_control "indet" ^^ P.brackets (!^ (string_of_int i)) ^^ P.parens (pp e) *)
          (* | M_Esave (_, (sym, (bTy,_)), sym_bTy_pes, e) ->
           *     pp_keyword "save" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_bt bTy ^^^
           *     P.parens (comma_list (fun (sym, ((bTy,_), pe)) ->
           *       pp_symbol sym ^^ P.colon ^^^ pp_bt bTy ^^ P.colon ^^ P.equals ^^^ pp_asym pe
           *     ) sym_bTy_pes) ^^^
           *     pp_control "in" ^^^
           *     P.nest 2 (P.break 1 ^^ pp e) *)
          (* | M_Epar es ->
           *     pp_keyword "par" ^^ P.parens (comma_list pp es) *)
          (* | M_Ewait tid ->
           *     pp_keyword "wait" ^^ P.parens (pp_thread_id tid) *)
          | M_End es ->
              pp_keyword "nd" ^^ P.parens (comma_list pp es)
          | M_Ebound (i, e) ->
              pp_keyword "bound" ^^ P.brackets (!^ (string_of_int i)) ^/^
              P.parens (pp e)
          | M_Edone asym ->
              pp_control "done" ^^^ pp_asym asym
          | M_Erun (sym, pes) ->
              pp_keyword "run" ^^^ pp_symbol sym ^^ P.parens (comma_list pp_asym pes)
          | M_Eundef (_, ub) ->
              pp_keyword "undef" ^^ P.parens (pp_undef ub)        
        end
      end
      in pp budget None expr








  (*
      | Ptr (ptr_act, es) ->
         pp_pointer_action ptr_act ^^ P.parens (comma_list pp_pexpr es)
  *)


  (* TODO: hackish (move to core.lem + some of these are implementation stuff ) *)
  let std = [
  (*
    "overflow";
    "conv_int";
    "conv";
    "div_zero";
    "usual_arithmetic";
    "ctype_width";
    "exp";
    "representable";
    "alignof";
    "max";
    "min";
    "offsetof";
    "shift";
    "sizeof";
  *)
  ]

  let symbol_compare =
    Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method

  let pp_tagDefinitions tagDefs =
    let tagDefs = Pmap.bindings_list tagDefs in
    let pp (sym, tagDef) =
      begin match tagDef with
      | M_StructDef sd -> 
         pp_keyword "def" ^^^ pp_keyword "struct" ^^^ 
           pp_raw_symbol sym ^^^ P.colon ^^ P.equals ^^ (pp_st sd)
      | M_UnionDef ut -> 
         pp_keyword "def" ^^^ pp_keyword "union" ^^^ 
           pp_raw_symbol sym ^^^ P.colon ^^ P.equals ^^ (pp_ut ut)
      end
      (* let (ty, tags) = match tagDef with
       *   | M_StructDef (membrs_, flexible_opt) ->
       *       let membrs = match flexible_opt with
       *         | None ->
       *             membrs_
       *         | _ ->
       *           failwith "have to implement that again"
       *         (\* | Some (FlexibleArrayMember (attrs, ident, qs, elem_ty)) ->
       *          *     membrs_ @ [(ident, (attrs, qs, Ctype ([], Array (elem_ty, None))))] in *\)
       *       in
       *       ("struct", membrs)
       *   | M_UnionDef membrs -> ("union", membrs)
       * in
       * pp_keyword "def" ^^^ pp_keyword ty ^^^ pp_raw_symbol sym ^^^ P.colon ^^ P.equals
       * ^^ P.nest 2 (P.break 1 ^^ P.separate_map (P.break 1) pp_tag tags) *)
    in P.separate_map (P.break 1 ^^ P.break 1) pp tagDefs

  let pp_argument (sym, bTy) =
    pp_symbol sym ^^ P.colon ^^^ pp_bt bTy

  let pp_params params =
    P.parens (comma_list pp_argument params)

  let pp_fun_map budget funs =
    let pp_cond loc d =
      if show_include || Location_ocaml.from_main_file loc then d else P.empty
    in
    Pmap.fold (fun sym decl acc ->
      acc ^^
      begin match decl with
        | M_Fun (bTy, params, pe) ->
            pp_keyword "fun" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_bt bTy ^^^
            P.colon ^^ P.equals ^^
            P.nest 2 (P.break 1 ^^ pp_tpexpr budget pe)
        | M_ProcDecl (loc, bTy, bTys) ->
            pp_cond loc @@
            pp_keyword "proc" ^^^ pp_symbol sym ^^^ P.parens (comma_list pp_bt bTys)
        | M_BuiltinDecl (loc, bTy, bTys) ->
            pp_cond loc @@
            pp_keyword "builtin" ^^^ pp_symbol sym ^^^ P.parens (comma_list pp_bt bTys)
        | M_Proc (loc, bTy, params, e, labels) ->
            pp_cond loc @@
            pp_keyword "proc" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_keyword "eff" ^^^ pp_bt bTy ^^^
            P.colon ^^ P.equals ^^
            P.hardline ^^
            P.nest 2 (
                (* pp label definitions *)
              (Pmap.fold (fun sym def acc ->
                   acc ^^
                   begin match def with
                   | M_Return (_, lt) -> 
                      P.break 1 ^^ !^"return label" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_lt lt
                   | M_Label (_, lt, args, lbody, annots) ->
                      P.break 1 ^^ !^"label" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_lt lt ^^
                        (* label core function definition *)
                        P.break 1 ^^ !^"label" ^^^ pp_symbol sym ^^^ 
                          P.parens (comma_list (fun (sym, bt) -> pp_symbol sym ^^ P.colon ^^^ pp_bt bt) args) ^^ P.equals ^^
                            (P.nest 2 (P.break 1 ^^ pp_texpr budget lbody))
                   end  ^^ P.hardline
                 ) labels P.empty
              ) 
              ^^ 
                (* pp body *)
              P.break 1 ^^ !^"body" ^^^ P.equals ^^^ P.nest 2 (P.break 1 ^^ pp_texpr budget e)
            )
      end ^^ P.hardline ^^ P.hardline
               
      ) funs P.empty


  let pp_impl budget impl =
    Pmap.fold (fun iCst iDecl acc ->
      acc ^^
      match iDecl with
        | M_Def (_, bty, pe) ->
            pp_keyword "def" ^^^ pp_impl iCst ^^^ P.equals ^^
            P.nest 2 (P.break 1 ^^ pp_tpexpr budget pe) ^^ P.break 1 ^^ P.break 1

        | M_IFun (_, bTy, params, pe) ->
            pp_keyword "fun" ^^^ pp_impl iCst ^^^ pp_params params ^^ P.colon ^^^ pp_bt bTy ^^^
            P.colon ^^ P.equals ^^
            P.nest 2 (P.break 1 ^^ pp_tpexpr budget pe) ^^ P.break 1 ^^ P.break 1
    ) impl P.empty

  let pp_extern_symmap symmap =
    !^ "-- Extern symbols map:" ^^ P.break 1
    |> Pmap.fold (fun sym_from sym_to acc ->
        acc ^^ pp_raw_symbol sym_from ^^^ !^"->" ^^^ pp_raw_symbol sym_to ^^ P.break 1
      ) symmap

  let mk_comment doc =
    pp_ansi_format [Red] (
      !^ "{-" ^^ P.break 1 ^^ doc ^^ P.break 1 ^^ !^ "-}"
    )

  let pp_globs budget globs =
    List.fold_left (fun acc (sym, decl) ->
        match decl with
        | M_GlobalDef (_, (bTy, gt), e) ->
          acc ^^ pp_keyword "glob" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_bt bTy ^^^
            P.brackets (!^"ct" ^^^ P.equals ^^^ pp_gt gt) ^^^
                P.colon ^^ P.equals ^^
                P.nest 2 (P.break 1 ^^ pp_texpr budget e) ^^ P.break 1 ^^ P.break 1
        | M_GlobalDecl _ ->
          acc) P.empty globs

  let pp_funinfo finfos =
      Pmap.fold (fun sym (M_funinfo (_, _, ft, _trusted, has_proto)) acc ->
          acc ^^ pp_symbol sym ^^ P.colon
          ^^^ pp_ft ft
          ^^ P.hardline) finfos P.empty

    let pp_funinfo_with_attributes finfos =
      Pmap.fold (fun sym (M_funinfo (loc, attrs, ft, _trusted, has_proto)) acc ->
          acc ^^ pp_symbol sym ^^ P.colon
          ^^^ pp_ft ft
          ^^^ (* P.at ^^^ Location_ocaml.pp_location loc ^^^ *) Pp_ail.pp_attributes attrs
          ^^ P.hardline) finfos P.empty


  let pp_file budget file =
    let show_aggregate = not @@ Pmap.is_empty file.mu_tagDefs in
    let show_globs = file.mu_globs != [] in
    let guard b doc = if b then doc else P.empty in

    begin
      if Debug_ocaml.get_debug_level () > 1 then
        fun z ->
          !^ "-- BEGIN STDLIB" ^^ P.break 1 ^^
          (pp_fun_map budget file.mu_stdlib) ^^ P.break 1 ^^
          !^ "-- END STDLIB" ^^ P.break 1 ^^
          !^ "-- BEGIN IMPL" ^^ P.break 1 ^^
          pp_impl budget file.mu_impl ^^ P.break 1 ^^
          !^ "-- END IMPL" ^^ P.break 1 ^^ z
      else
        id
    end

    begin
      guard show_aggregate begin
        !^ "-- Aggregates" ^^ P.break 1 ^^
        pp_tagDefinitions file.mu_tagDefs ^^
        P.break 1 ^^ P.break 1
      end ^^

      guard (show_include || Debug_ocaml.get_debug_level () > 1) begin
        !^ "-- C function types" ^^ P.break 1 ^^
        pp_funinfo file.mu_funinfo
      end ^^

      guard show_globs begin
        !^ "-- Globals" ^^ P.break 1 ^^
        pp_globs budget file.mu_globs
      end ^^

      guard (show_aggregate || show_globs) begin
        !^ "-- Fun map" ^^ P.break 1
      end ^^
      pp_fun_map budget file.mu_funs
    end


  (* let string_of_mucore_object_type oTy =
   *   Pp_utils.to_plain_string (pp_object_type oTy) *)
  let string_of_core_base_type bTy =
    Pp_utils.to_plain_string (pp_bt bTy)
  let string_of_value cval =
    Pp_utils.to_plain_string (pp_value cval)
  let string_of_action act =
    Pp_utils.to_plain_string (pp_action act)
  let string_of_pexpr pe =
    Pp_utils.to_plain_string (pp_pexpr pe)
  let string_of_tpexpr pe =
    Pp_utils.to_plain_string (pp_tpexpr None pe)
  let string_of_expr e =
    Pp_utils.to_plain_string (pp_expr e)
  let string_of_texpr e =
    Pp_utils.to_plain_string (pp_texpr None e)
  let string_of_file f =
    Pp_utils.to_plain_string (pp_file None f)


end


let rec pp_core_object_type = function
  | OTy_integer ->
      !^ "integer"
  | OTy_floating ->
      !^ "floating"
  | OTy_pointer ->
      !^ "pointer"
  | OTy_array bty -> (* TODO: THIS IS NOT BEING PARSED CORRECTLY *)
      !^ "array" ^^ P.parens (pp_core_object_type bty)
  | OTy_struct ident ->
      !^ "struct" ^^^ !^(Pp_symbol.to_string ident)
  | OTy_union ident  ->
      !^ "union" ^^^ !^(Pp_symbol.to_string ident)
  (*| OTy_cfunction (ret_oTy_opt, nparams, isVariadic) ->
      let pp_ret = match ret_oTy_opt with
        | Some ret_oTy ->
            pp_core_object_type ret_oTy
        | None ->
            P.underscore in
      !^ "cfunction" ^^ P.parens (pp_ret ^^ P.comma ^^^ !^ (string_of_int nparams) ^^ if isVariadic then P.comma ^^ P.dot ^^ P.dot ^^ P.dot else P.empty)
*)
let rec pp_core_base_type = function
  | BTy_storable   -> !^ "storable"
  | BTy_object bty ->
      pp_core_object_type bty
  | BTy_loaded bty ->
      !^ "loaded" ^^^ pp_core_object_type bty
  | BTy_boolean    -> !^ "boolean"
  | BTy_ctype      -> !^ "ctype"
  | BTy_unit       -> !^ "unit"
  | BTy_list bTy  -> P.brackets (pp_core_base_type bTy)
  | BTy_tuple bTys -> P.parens (P.separate_map P.comma pp_core_base_type bTys)



module Pp_standard_typ = (struct

  module T = Mucore.SimpleTypes


  (* type object_type = core_object_type
   * type bt = core_base_type
   * let pp_object_type = pp_core_object_type *)

  let pp_bt = pp_core_base_type
  

  let pp_ct ty = P.squotes (Pp_core_ctype.pp_ctype ty)
  let pp_gt = pp_ct

  let pp_ut (membrs) = 
    let (ty, tags) = ("union", membrs) in
    let pp_tag (Symbol.Identifier (_, name), (_,_,ct)) =
      !^name ^^ P.colon ^^^ pp_ct ct
    in
    P.nest 2 (P.break 1 ^^ P.separate_map (P.break 1) pp_tag tags)



  let pp_st (membrs_, flexible_opt) = 
    let membrs = match flexible_opt with
      | None ->
         membrs_
      | _ ->
         failwith "have to implement that again"
    (* | Some (FlexibleArrayMember (attrs, ident, qs, elem_ty)) ->
     *     membrs_ @ [(ident, (attrs, qs, Ctype ([], Array (elem_ty, None))))] in *)
    in
    let (ty, tags) = ("struct", membrs) in
    let pp_tag (Symbol.Identifier (_, name), (_,_,ct)) =
      !^name ^^ P.colon ^^^ pp_ct ct
    in
    P.nest 2 (P.break 1 ^^ P.separate_map (P.break 1) pp_tag tags)



  (* type ft = CA.ft
   * type lt = CA.lt *)

  (* stealing from Pp_core *)
  let pp_ft (ret_ty, params, is_variadic) = 
    let mk_pair (_, ty) = (Ctype.no_qualifiers, ty, false) in
    pp_ct (Ctype ([], Function ((Ctype.no_qualifiers, ret_ty), List.map mk_pair params, is_variadic)))

    (* let pp_lt = None *)
  (* stealing from Pp_core *)
  let pp_lt params =
    comma_list (fun (_,(ty,by_pointer)) -> 
        if by_pointer then pp_ctype ty else pp_ctype ty ^^^ P.parens (P.string "val")
      ) params


  
end)



module Basic = (struct
  (* let ansi_format = Colour.ansi_format *)
  let ansi_format _ s = s
  let show_std = false
  let show_include = true
  let show_locations = false
  let handle_location _ _ = ()
  let handle_uid _ _ = ()
end)

module All = (struct
  (* let ansi_format = Colour.ansi_format *)
  let ansi_format _ s = s
  let show_std = true
  let show_include = true
  let show_locations = false
  let handle_location _ _ = ()
  let handle_uid _ _ = ()
end)

module WithLocations = (struct
  let ansi_format _ s = s
  (* let ansi_format = Colour.ansi_format *)
  let show_std = false
  let show_include = true
  let show_locations = true
  let handle_location _ _ = ()
  let handle_uid _ _ = ()
end)


module Basic_standard_typ = Make(Basic)(Pp_standard_typ)
module All_standard_typ = Make(All)(Pp_standard_typ)
module WithLocations_standard_typ = Make(WithLocations)(Pp_standard_typ)
