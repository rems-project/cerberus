[@@@landmark "auto"]

(* copy pasted from pp_core.ml and adapted *)
open Lem_pervasives
open Core
open Mucore
open Annot

open Either

open Colour

open Pp_prelude

module type CONFIG =
sig
  val show_std: bool
  val show_include: bool
  val handle_location: Location_ocaml.t -> P.range -> unit
  val handle_uid: string -> P.range -> unit
end

module type PP_CORE =
sig
  val pp_core_object_type: mu_object_type -> PPrint.document
  val pp_core_base_type: mu_base_type -> PPrint.document
  val pp_object_value: 'bty mu_value -> PPrint.document
  val pp_value: 'bty mu_value -> PPrint.document
  val pp_params: (Symbol.sym * mu_base_type) list -> PPrint.document
  val pp_pexpr: ('ty) mu_pexpr -> PPrint.document
  val pp_expr: ('a, 'b) mu_expr -> PPrint.document
  val pp_file: ('a, 'b) mu_file -> PPrint.document

  val pp_funinfo: (Symbol.sym, Location_ocaml.t * Annot.attributes * Ctype.ctype * (Symbol.sym option * Ctype.ctype) list * bool * bool) Pmap.map -> PPrint.document
  val pp_funinfo_with_attributes: (Symbol.sym, Location_ocaml.t * Annot.attributes * Ctype.ctype * (Symbol.sym option * Ctype.ctype) list * bool * bool) Pmap.map -> PPrint.document
  val pp_extern_symmap: (Symbol.sym, Symbol.sym) Pmap.map -> PPrint.document

  val pp_action: 'a mu_action_ -> PPrint.document
end

module Make (Config: CONFIG) =
struct
open Config

let rec precedence = function
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

  | M_PEundef _
  | M_PEerror _
  | M_PEval _
  | M_PEconstrained _
  | M_PEsym _
  | M_PEimpl _
  | M_PEctor _
  | M_PEcase _
  | M_PEarray_shift _
  | M_PEmember_shift _
  | M_PEnot _
  | M_PEstruct _
  | M_PEunion _
  | M_PEmemberof _
  | M_PEcall _
  | M_PElet _
  | M_PEif _ -> None

let rec precedence_expr = function
  | M_Epure _
  | M_Ememop _
  | M_Eaction _
  | M_Ecase _
  | M_Eskip
  | M_Eproc _
  | M_Eccall _
  (* | M_Eunseq _ *)
  (* | M_Eindet _ *)
  | M_Ebound _
  | M_End _
  | M_Erun _
  (* | M_Epar _ *)
  (* | M_Ewait _ -> *)
    -> 
      None

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
  | M_Esave _ ->
      Some 5


let compare_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | _                  -> true


let pp_keyword w = !^ (ansi_format [Bold; Magenta] w)
let pp_const   c = !^ (ansi_format [Magenta] c)
let pp_control w = !^ (ansi_format [Bold; Blue] w)
let pp_symbol  a = !^ (ansi_format [Blue] (Pp_symbol.to_string_pretty a))
(* NOTE: Used to distinguish struct/unions globally *)
let pp_raw_symbol  a = !^ (ansi_format [Blue] (Pp_symbol.to_string a))
let pp_number  n = !^ (ansi_format [Yellow] n)
let pp_impl    i = P.angles (!^ (ansi_format [Yellow] (Implementation.string_of_implementation_constant i)))


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


let pp_core_type = function
  | TyBase   baseTy -> pp_core_base_type baseTy
  | TyEffect baseTy -> P.brackets (pp_core_base_type baseTy)


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


let pp_ctype ty =
  P.squotes (Pp_core_ctype.pp_ctype ty)





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




let pp_asym (Annotated (_annots,_bty,sym)) = 
  pp_symbol sym

let pp_actype (Annotated (_annots,_bty,ct)) = 
  pp_ctype ct

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



let pp_object_value = function
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
      pp_const "Array" ^^ P.parens (P.nest 1 (comma_list pp_asym lvals))
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

let pp_loaded_value = function
  | M_LVspecified oval ->
      pp_const "Specified" ^^ P.parens (pp_object_value oval)
  | M_LVunspecified ty ->
      pp_const "Unspecified" ^^ P.parens (P.squotes (Pp_core_ctype.pp_ctype ty))


let rec pp_value = function
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
      P.brackets (comma_list pp_asym cvals)
  | M_Vtuple cvals ->
      P.parens (comma_list pp_asym cvals)
  | M_Vobject oval ->
      pp_object_value oval
  | M_Vloaded lval ->
      pp_loaded_value lval

let pp_ctor = function
  | Cnil _ ->
      !^ "Nil"
  | Ccons ->
      !^ "Cons"
  | Ctuple ->
      !^ "Tuple"
  | Carray ->
      !^ "Array"
  | Civmax ->
      !^ "Ivmax"
  | Civmin ->
      !^ "Ivmin"
  | Civsizeof ->
      !^ "Ivsizeof"
  | Civalignof ->
      !^ "Ivalignof"
  | CivCOMPL ->
      !^ "IvCOMPL"
  | CivAND ->
      !^ "IvAND"
  | CivOR ->
      !^ "IvOR"
  | CivXOR ->
      !^ "IvXOR"
  | Cspecified ->
      !^ "Specified"
  | Cunspecified ->
      !^ "Unspecified"
  | Cfvfromint ->
      !^ "Cfvfromint"
  | Civfromfloat ->
      !^ "Civfromfloat"


let rec pp_pattern (Pattern (_, pat)) =
  match pat with
  | CaseBase (None, bTy) ->
      P.underscore ^^ P.colon ^^^ pp_core_base_type bTy
  | CaseBase (Some sym, bTy) ->
      pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy
(* Syntactic sugar for tuples and lists *)
  | CaseCtor (Ctuple, pats) ->
      P.parens (comma_list pp_pattern pats)
  | CaseCtor (ctor, pats) ->
      pp_ctor ctor  ^^ P.parens (comma_list pp_pattern pats)

let pp_sym_or_pattern = function
  | M_symbol (Annotated (_annots, _bty, sym)) ->
     pp_symbol sym
  | M_normal_pattern pat ->
     pp_pattern pat


let pp_pexpr pe =
  let rec pp prec (M_Pexpr (_, _, pe)) =
    let prec' = precedence pe in
    let pp z = P.group (pp prec' z) in
    (if compare_precedence prec' prec then fun z -> z else P.parens)
    begin
      match pe with
        | M_PEundef (_, ub) ->
            pp_keyword "undef" ^^ P.parens (P.angles (P.angles (!^ (
              ansi_format [Magenta] (Undefined.stringFromUndefined_behaviour ub)
            ))))
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
        | M_PEctor (Cnil _, pes) ->
            if not (pes <> []) then
              Debug_ocaml.warn [] (fun () ->
                "Pp_core found a Cnil with pes <> []"
              );
            P.brackets P.empty
        (* | M_PEctor (Ccons, pes) ->
         *     let to_list_value =
         *       let rec aux acc = function
         *         | M_PEctor (Cnil _, []) ->
         *             Some (List.rev acc)
         *         | M_PEctor (Ccons, [pe1; pe2]) ->
         *               aux (pe1 :: acc) pe2
         *         | _ ->
         *             None
         *       in
         *       aux [] pe in
         *     begin match to_list_value with
         *       | M_Some pes' ->
         *           P.brackets (comma_list pp pes')
         *       | M_None ->
         *           P.separate_map (P.space ^^ P.colon ^^ P.colon ^^ P.space) pp pes
         *     end *)
        | M_PEctor (Ctuple, pes) ->
            P.parens (comma_list pp_asym pes)
        | M_PEctor (ctor, pes) ->
            pp_ctor ctor ^^ P.parens (comma_list pp_asym pes)
        | M_PEcase (pe, pat_pes) ->
          pp_keyword "case" ^^^ pp_asym pe ^^^ pp_keyword "of" ^^
          P.nest 2 (
            P.break 1 ^^ P.separate_map (P.break 1) (fun (cpat, pe) ->
              P.prefix 4 1
                (P.bar ^^^ pp_pattern cpat ^^^ P.equals ^^ P.rangle)
                (pp pe)
            ) pat_pes
          ) ^^ P.break 1 ^^ pp_keyword "end"

(*
            pp_keyword "case" ^^^ pp pe ^^^ pp_keyword "of" ^^
            P.nest 2 (
              P.break 1 ^^ P.separate_map (P.break 1) (fun (cpat, pe) ->
                P.group (
                  P.bar ^^^ pp_pattern cpat ^^^ P.equals ^^ P.rangle ^^^
                  P.ifflat
                    (pp pe)
                    (P.nest 2 (P.break 0 ^^ pp pe))
                )
              ) pat_pes
            ) ^^ P.break 1 ^^ pp_keyword "end"
*)
        | M_PEarray_shift (pe1, ty, pe2) ->
            pp_keyword "array_shift" ^^ P.parens (
              pp_asym pe1 ^^ P.comma ^^^ pp_ctype ty ^^ P.comma ^^^ pp_asym pe2
            )
        | M_PEmember_shift (pe, tag_sym, (Symbol.Identifier (_, memb_ident))) ->
            pp_keyword "member_shift" ^^ P.parens (
              pp_asym pe ^^ P.comma ^^^ pp_raw_symbol tag_sym ^^ P.comma ^^^ P.dot ^^ !^ memb_ident
            )
        | M_PEnot pe ->
            pp_keyword "not" ^^ P.parens (pp_asym pe)
        | M_PEop (bop, pe1, pe2) ->
            pp_asym pe1 ^^^ pp_binop bop ^^^ pp_asym pe2
(*
        | M_PEmemop (pure_memop, pes) ->
            pp_keyword "memop" ^^ P.parens (Pp_mem.pp_pure_memop pure_memop ^^ P.comma ^^^ comma_list pp pes)
*)
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
        | M_PElet (pat, pe1, pe2) ->
            (* DEBUG  !^ "{-pe-}" ^^^ *)
            pp_control "let" ^^^ pp_sym_or_pattern pat ^^^ P.equals ^^^
            pp pe1 ^^^ pp_control "in" ^^ P.break 1 ^^ pp pe2
        | M_PEif (pe1, pe2, pe3) ->
            P.group (
              pp_control "if" ^^^ pp_asym pe1 ^^^ pp_control "then" ^^
              P.nest 2 (P.break 1 ^^ pp pe2) ^^ P.break 1 ^^
              pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp pe3)
            )
    end
  in pp None pe


let rec pp_expr expr =
  let rec pp is_semi prec (M_Expr (annot, e)) =
    let prec' = precedence_expr e in
    let pp_ z = pp true prec' z in  (* TODO: this is sad *)
    let pp  z = pp false prec' z in

    begin
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
            | Aattrs _ ->
                !^ "TODO(Aattrs)"
        ) doc annot
    end
    begin
      begin
        (* Here we check whether parentheses are needed *)
        if compare_precedence prec' prec then
          (* right associativity of ; *)
          match (is_semi, e) with
            | (true, M_Esseq (Pattern (_, CaseBase (None, BTy_unit)), _, _)) ->
                P.parens
            | _ ->
                fun z -> z
        else
          P.parens
      end
      begin match e with
        | M_Epure pe ->
            pp_keyword "pure" ^^ P.parens (pp_pexpr pe)
        | M_Ememop memop ->
           let (memop, pes) = Mucore.mu_to_core__memop__ memop in
            pp_keyword "memop" ^^ P.parens (Pp_mem.pp_memop memop ^^ P.comma ^^^ comma_list pp_actype_or_asym pes)
        | M_Eaction (M_Paction (p, (M_Action (_, bs, act)))) ->
            pp_polarity p (pp_action act)
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
                (pp_control "let" ^^^ pp_sym_or_pattern pat ^^^ P.equals ^^^ pp_pexpr pe1 ^^^ pp_control "in")
                (pp e2)
           )
        | M_Eif (pe1, e2, e3) ->
            pp_control "if" ^^^ pp_asym pe1 ^^^ pp_control "then" ^^
            P.nest 2 (P.break 1 ^^ pp e2) ^^ P.break 1 ^^
            pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp e3)
        | M_Eskip ->
            pp_keyword "skip"
        | M_Eproc (_, nm, pes) ->
            pp_keyword "pcall" ^^ P.parens (pp_name nm ^^ P.comma ^^^ comma_list pp_asym pes)
        | M_Eccall (_, pe_ty, pe, pes) ->
            pp_keyword "ccall" ^^ P.parens (comma_list pp_actype_or_asym (Left pe_ty :: Right pe :: (map (fun pe -> Right pe)) pes))
        (* | M_Eunseq [] ->
         *     !^ "BUG: UNSEQ must have at least two arguments (seen 0)" *)
        (* | M_Eunseq [e] ->
         *     !^ "BUG: UNSEQ must have at least two arguments (seen 1)" ^^ (pp_control "[-[-[") ^^ pp e ^^ (pp_control "]-]-]") *)
        (* | M_Eunseq es ->
         *     pp_control "unseq" ^^ P.parens (comma_list pp es) *)
        | M_Ewseq (pat, e1, e2) ->
            P.group (
              pp_control "let weak" ^^^ pp_pattern pat ^^^ P.equals ^^^
              let doc_e1 = pp e1 in
              P.ifflat doc_e1 (P.nest 2 (P.break 1 ^^ doc_e1)) ^^^ pp_control "in"
            ) ^^
            P.break 1 ^^ (pp e2)
        | M_Esseq (Pattern (_, CaseBase (None, BTy_unit)), e1, e2) ->
            (pp_ e1 ^^^ P.semi) ^/^ (pp e2)
        | M_Esseq (pat, e1, e2) ->
            P.group (
              pp_control "let strong" ^^^ pp_pattern pat ^^^ P.equals ^^^
              let doc_e1 = pp e1 in
              P.ifflat doc_e1 (P.nest 2 (P.break 1 ^^ doc_e1)) ^^^ pp_control "in"
            ) ^^
            P.break 1 ^^ (pp e2)
        (* | M_Easeq ((sym, bTy), act1, pact2) ->
         *     pp_control "let atom" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^^ P.equals ^^^
         *     pp (Expr ([], Eaction (Paction (Pos, act1)))) ^^^ pp_control "in" ^^^ pp (Expr ([], Eaction pact2)) *)
        (* | M_Eindet (i, e) ->
         *     pp_control "indet" ^^ P.brackets (!^ (string_of_int i)) ^^ P.parens (pp e) *)
        | M_Esave ((sym, bTy), sym_bTy_pes, e) ->
            pp_keyword "save" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^^
            P.parens (comma_list (fun (sym, (bTy, pe)) ->
              pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^ P.colon ^^ P.equals ^^^ pp_asym pe
            ) sym_bTy_pes) ^^^
            pp_control "in" ^^^
            P.nest 2 (P.break 1 ^^ pp e)
        | M_Erun (_, sym, pes) ->
            pp_keyword "run" ^^^ pp_symbol sym ^^ P.parens (comma_list pp_asym pes)
        (* | M_Epar es ->
         *     pp_keyword "par" ^^ P.parens (comma_list pp es) *)
        (* | M_Ewait tid ->
         *     pp_keyword "wait" ^^ P.parens (pp_thread_id tid) *)
        | M_End es ->
            pp_keyword "nd" ^^ P.parens (comma_list pp es)
        | M_Ebound (i, e) ->
            pp_keyword "bound" ^^ P.brackets (!^ (string_of_int i)) ^/^
            P.parens (pp e)
      end
    end
    in pp false None expr



and pp_action act =
  let pp_args args mo =
    P.parens (comma_list pp_actype_or_asym args ^^ if mo = Cmm_csem.NA then P.empty else P.comma ^^^ pp_memory_order mo) in
  match act with
    | M_Create (al, ty, _) ->
        pp_keyword "create" ^^ P.parens (pp_asym al ^^ P.comma ^^^ pp_actype ty)
    | M_CreateReadOnly (al, ty, init, _) ->
        pp_keyword "create_readonly" ^^ P.parens (pp_asym al ^^ P.comma ^^^ pp_actype ty ^^ P.comma ^^^ pp_asym init)
    | M_Alloc (al, n, _) ->
        pp_keyword "alloc" ^^ P.parens (pp_actype al ^^ P.comma ^^^ pp_asym n)
    | M_Kill (b, e) ->
        pp_keyword (if b then "free" else "kill") ^^ P.parens (pp_asym e)
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
    let (ty, tags) = match tagDef with
      | Ctype.StructDef (membrs_, flexible_opt) ->
          let membrs = match flexible_opt with
            | None ->
                membrs_
            | Some (FlexibleArrayMember (attrs, ident, qs, elem_ty)) ->
                membrs_ @ [(ident, (attrs, qs, Ctype ([], Array (elem_ty, None))))] in
          ("struct", membrs)
      | Ctype.UnionDef membrs -> ("union", membrs)
    in
    let pp_tag (Symbol.Identifier (_, name), (_, _, ty)) =
      !^name ^^ P.colon ^^^ pp_ctype ty
    in
    pp_keyword "def" ^^^ pp_keyword ty ^^^ pp_raw_symbol sym ^^^ P.colon ^^ P.equals
    ^^ P.nest 2 (P.break 1 ^^ P.separate_map (P.break 1) pp_tag tags)
  in P.separate_map (P.break 1 ^^ P.break 1) pp tagDefs

let pp_argument (sym, bTy) =
  pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy

let pp_params params =
  P.parens (comma_list pp_argument params)

let pp_fun_map funs =
  let pp_cond loc d =
    if show_include || Location_ocaml.from_main_file loc then d else P.empty
  in
  Pmap.fold (fun sym decl acc ->
    acc ^^
    match decl with
      | M_Fun  (bTy, params, pe) ->
          pp_keyword "fun" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.hardline ^^ P.hardline
      | M_ProcDecl (loc, bTy, bTys) ->
          pp_cond loc @@
          pp_keyword "proc" ^^^ pp_symbol sym ^^^ P.parens (comma_list pp_core_base_type bTys) ^^ P.hardline ^^ P.hardline
      | M_BuiltinDecl (loc, bTy, bTys) ->
          pp_cond loc @@
          pp_keyword "builtin" ^^^ pp_symbol sym ^^^ P.parens (comma_list pp_core_base_type bTys) ^^ P.hardline ^^ P.hardline
      | M_Proc (loc, bTy, params, e) ->
          pp_cond loc @@
          pp_keyword "proc" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_keyword "eff" ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.hardline ^^ P.hardline
    ) funs P.empty


let pp_impl impl =
  Pmap.fold (fun iCst iDecl acc ->
    acc ^^
    match iDecl with
      | M_Def (bty, pe) ->
          pp_keyword "def" ^^^ pp_impl iCst ^^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.break 1 ^^ P.break 1

      | M_IFun (bTy, params, pe) ->
          pp_keyword "fun" ^^^ pp_impl iCst ^^^ pp_params params ^^ P.colon ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.break 1 ^^ P.break 1
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

let pp_funinfo finfos =
  let mk_pair (_, ty) = (Ctype.no_qualifiers, ty, false) in
  Pmap.fold (fun sym (_, _, ret_ty, params, is_variadic, has_proto) acc ->
    acc ^^ pp_raw_symbol sym ^^ P.colon
    ^^^ pp_ctype (Ctype ([], Function (false, (Ctype.no_qualifiers, ret_ty), List.map mk_pair params, is_variadic)))
        ^^ P.hardline) finfos P.empty

let pp_funinfo_with_attributes finfos =
  let mk_pair (_, ty) = (Ctype.no_qualifiers, ty, false) in
  Pmap.fold (fun sym (loc, attrs, ret_ty, params, is_variadic, has_proto) acc ->
    acc ^^ pp_raw_symbol sym ^^ P.colon
    ^^^ pp_ctype (Ctype ([], Function (false, (Ctype.no_qualifiers, ret_ty), List.map mk_pair params, is_variadic)))
        ^^^ (* P.at ^^^ Location_ocaml.pp_location loc ^^^ *) Pp_ail.pp_attributes attrs
        ^^ P.hardline) finfos P.empty

let pp_globs globs =
  List.fold_left (fun acc (sym, decl) ->
      match decl with
      | M_GlobalDef (bTy, e) ->
        acc ^^ pp_keyword "glob" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^^
              P.colon ^^ P.equals ^^
              P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.break 1 ^^ P.break 1
      | M_GlobalDecl _ ->
        acc) P.empty globs

let pp_file file =
  let show_aggregate = not @@ Pmap.is_empty file.mu_tagDefs in
  let show_globs = file.mu_globs != [] in
  let guard b doc = if b then doc else P.empty in

  begin
    if Debug_ocaml.get_debug_level () > 1 then
      fun z ->
        !^ "-- BEGIN STDLIB" ^^ P.break 1 ^^
        pp_fun_map file.mu_stdlib ^^ P.break 1 ^^
        !^ "-- END STDLIB" ^^ P.break 1 ^^
        !^ "-- BEGIN IMPL" ^^ P.break 1 ^^
  (*  pp_impl file.impl ^^ P.break 1 ^^ *)
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
      pp_globs file.mu_globs
    end ^^

    guard (show_aggregate || show_globs) begin
      !^ "-- Fun map" ^^ P.break 1
    end ^^
    pp_fun_map file.mu_funs
  end

end




module Basic = Make (struct
  let show_std = false
  let show_include = false
  let handle_location _ _ = ()
  let handle_uid _ _ = ()
end)

module All = Make (struct
  let show_std = true
  let show_include = true
  let handle_location _ _ = ()
  let handle_uid _ _ = ()
end)
