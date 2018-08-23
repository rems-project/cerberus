[@@@landmark "auto"]
open Lem_pervasives
open Core
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
  val pp_core_object_type: core_object_type -> PPrint.document
  val pp_core_base_type: core_base_type -> PPrint.document
  val pp_object_value: object_value -> PPrint.document
  val pp_value: value -> PPrint.document
  val pp_params: (Symbol.sym * core_base_type) list -> PPrint.document
  val pp_pexpr: ('ty, Symbol.sym) generic_pexpr -> PPrint.document
  val pp_expr: ('a, 'b, Symbol.sym) generic_expr -> PPrint.document
  val pp_expr: ('a, 'b, Symbol.sym) generic_expr -> PPrint.document
  val pp_file: ('a, 'b) generic_file -> PPrint.document

  val pp_action: ('a, Symbol.sym) generic_action_ -> PPrint.document
  val pp_stack: 'a stack -> PPrint.document
end

module Make (Config: CONFIG) =
struct
open Config

let rec precedence = function
  | PEop (OpExp, _, _) -> Some 1

  | PEop (OpMul, _, _)
  | PEop (OpDiv, _, _)
  | PEop (OpRem_t, _, _)
  | PEop (OpRem_f, _, _) -> Some 2
  
  | PEop (OpAdd, _, _)
  | PEop (OpSub, _, _) -> Some 3
  
  | PEop (OpLt,  _, _)
  | PEop (OpLe,  _, _) -> Some 4
  
  | PEop (OpGt,  _, _)
  | PEop (OpGe,  _, _) -> Some 4
  
  | PEop (OpEq,  _, _) -> Some 5
  
  | PEop (OpAnd, _, _) -> Some 6
  
  | PEop (OpOr,  _, _) -> Some 7
  
  | PEundef _
  | PEerror _
  | PEval _
  | PEconstrained _
  | PEsym _
  | PEimpl _
  | PEctor _
  | PEcase _
  | PEarray_shift _
  | PEmember_shift _
  | PEnot _
  | PEstruct _
  | PEunion _
  | PEmemberof _
  | PEcall _
  | PElet _
  | PEif _
  | PEis_scalar _
  | PEis_integer _
  | PEis_signed _
  | PEis_unsigned _ -> None

let rec precedence_expr = function
  | Epure _
  | Ememop _
  | Eaction _
  | Ecase _
  | Eskip
  | Eproc _
  | Eccall _
  | Eunseq _
  | Eindet _
  | Ebound _
  | End _
  | Erun _
  | Epar _
  | Ewait _ ->
      None

  | Eif _ ->
      Some 1
  | Elet _ ->
      Some 2
  | Easeq _ ->
      Some 3
  | Esseq _ ->
      Some 3
  | Ewseq _ ->
      Some 4
  | Esave _ ->
      Some 5


let compare_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | _                  -> true


let pp_keyword w = !^ (ansi_format [Bold; Magenta] w)
let pp_const   c = !^ (ansi_format [Magenta] c)
let pp_control w = !^ (ansi_format [Bold; Blue] w)
let pp_symbol  a = !^ (ansi_format [Blue] (Pp_symbol.to_string_pretty a))
let pp_number  n = !^ (ansi_format [Yellow] n)
let pp_impl    i = P.angles (!^ (ansi_format [Yellow] (Implementation_.string_of_implementation_constant i)))


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
      !^ "struct(TODO)"
  | OTy_union ident  ->
      !^ "union(TODO)"
  | OTy_cfunction (ret_oTy_opt, nparams, isVariadic) ->
      let pp_ret = match ret_oTy_opt with
        | Some ret_oTy ->
            pp_core_object_type ret_oTy
        | None ->
            P.underscore in
      !^ "cfunction" ^^ P.parens (pp_ret ^^ P.comma ^^^ !^ (string_of_int nparams) ^^ if isVariadic then P.comma ^^ P.dot ^^ P.dot ^^ P.dot else P.empty)

let rec pp_core_base_type = function
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
  

let pp_mem_addr (pref, addr) =
(*
  let rec pp = function
  | Cmm_aux_old.Lbase n          -> Pp_ail.pp_integer n
  | Cmm_aux_old.Lshift (addr, n) -> P.braces (pp addr ^^ P.comma ^^^ Pp_ail.pp_integer n)
  in
  P.at ^^ P.braces (pp_prefix pref ^^ P.colon ^^^ pp addr)
*)
  P.at ^^ P.braces (Pp_symbol.pp_prefix pref ^^ P.colon ^^^ (!^ "TODO(addr)"))


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
  | OVinteger ival ->
      Ocaml_mem.pp_integer_value_for_core ival
  | OVfloating fval ->
      Ocaml_mem.case_fval fval
        (fun () -> !^ "unspec(floating)")
        (fun fval -> !^(string_of_float fval))
(*
  | OVsymbolic symb ->
      !^ "SYMB" ^^ P.parens (Pp_symbolic.pp_symbolic pp_object_value Pp_mem.pp_pointer_value symb)
*)
  | OVpointer ptr_val ->
      Ocaml_mem.pp_pointer_value ptr_val
  | OVarray lvals ->
      pp_const "Array" ^^ P.parens (P.nest 1 (comma_list pp_loaded_value lvals))
  | OVstruct (tag_sym, xs) ->
      P.parens (pp_const "struct" ^^^ pp_symbol tag_sym) ^^
      P.braces (
        comma_list (fun (ident, mval) -> 
          P.dot ^^ Pp_cabs.pp_cabs_identifier ident ^^
          P.equals ^^^ Ocaml_mem.pp_mem_value mval
        ) xs
      )
  | OVunion (tag_sym, memb_ident, mval) ->
      P.parens (pp_const "union" ^^^ pp_symbol tag_sym) ^^
      P.braces (
        P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident ^^
        P.equals ^^^ Ocaml_mem.pp_mem_value mval
      )
  | OVcfunction nm ->
      !^ "Cfunction" ^^ P.parens (pp_name nm)
  | OVcomposite _ ->
      !^ "TODO(OVcomposite)" 

and pp_loaded_value = function
  | LVspecified oval ->
      pp_const "Specified" ^^ P.parens (pp_object_value oval)
  | LVunspecified ty ->
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
  | Vunit ->
      pp_const "Unit"
  | Vtrue ->
      pp_const "True"
  | Vfalse ->
      pp_const "False"
  | Vlist (_, cvals) ->
      P.brackets (comma_list pp_value cvals)
  | Vtuple cvals ->
      P.parens (comma_list pp_value cvals)
  | Vctype ty ->
      P.squotes (Pp_core_ctype.pp_ctype ty)
  | Vobject oval ->
      pp_object_value oval
  | Vloaded lval ->
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

let pp_pexpr pe =
  let rec pp prec (Pexpr (_, _, pe)) =
    let prec' = precedence pe in
    let pp z = P.group (pp prec' z) in
    (if compare_precedence prec' prec then fun z -> z else P.parens)
    begin
      match pe with
        | PEundef (_, ub) ->
            pp_keyword "undef" ^^ P.parens (P.angles (P.angles (!^ (
              ansi_format [Magenta] (Undefined.stringFromUndefined_behaviour ub)
            ))))
        | PEerror (str, pe) ->
            pp_keyword "error" ^^ P.parens (P.dquotes (!^ str) ^^ P.comma ^^^ pp pe)
        | PEval cval ->
            pp_value cval
        | PEconstrained xs ->
            pp_keyword "constrained" ^^ P.parens (
              comma_list (fun (cs, pe) ->
                P.brackets (Pp_mem.pp_mem_constraint Ocaml_mem.pp_integer_value cs) ^^^
                P.equals ^^ P.rangle ^^ pp pe
              ) xs
            )
        | PEsym sym ->
            pp_symbol sym
        | PEimpl iCst ->
            pp_impl iCst
        | PEctor (Cnil _, pes) ->
            if not (pes <> []) then
              Debug_ocaml.warn [] (fun () ->
                "Pp_core found a Cnil with pes <> []"
              );
            P.brackets P.empty
        | PEctor (Ccons, pes) ->
            let to_list_value =
              let rec aux acc = function
                | PEctor (Cnil _, []) ->
                    Some (List.rev acc)
                | PEctor (Ccons, [pe1; Pexpr (_, _, pe2_)]) ->
                      aux (pe1 :: acc) pe2_
                | _ ->
                    None
              in
              aux [] pe in
            begin match to_list_value with
              | Some pes' ->
                  P.brackets (comma_list pp pes')
              | None ->
                  P.separate_map (P.space ^^ P.colon ^^ P.colon ^^ P.space) pp pes
            end
        | PEctor (Ctuple, pes) ->
            P.parens (comma_list pp pes)
        | PEctor (ctor, pes) ->
            pp_ctor ctor ^^ P.parens (comma_list pp pes)
        | PEcase (pe, pat_pes) ->
          pp_keyword "case" ^^^ pp pe ^^^ pp_keyword "of" ^^
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
        | PEarray_shift (pe1, ty, pe2) ->
            pp_keyword "array_shift" ^^ P.parens (
              pp pe1 ^^ P.comma ^^^ pp_ctype ty ^^ P.comma ^^^ pp pe2
            )
        | PEmember_shift (pe, tag_sym, memb_ident) ->
            pp_keyword "member_shift" ^^ P.parens (
              pp pe ^^ P.comma ^^^ pp_symbol tag_sym ^^ P.dot ^^ Pp_cabs.pp_cabs_identifier memb_ident
            )
        | PEnot pe ->
            pp_keyword "not" ^^ P.parens (pp pe)
        | PEop (bop, pe1, pe2) ->
            pp pe1 ^^^ pp_binop bop ^^^ pp pe2
(*
        | PEmemop (pure_memop, pes) ->
            pp_keyword "memop" ^^ P.parens (Pp_mem.pp_pure_memop pure_memop ^^ P.comma ^^^ comma_list pp pes)
*)
        | PEstruct (tag_sym, xs) ->
            P.parens (pp_keyword "struct" ^^^ pp_symbol tag_sym) ^^ P.braces (
              comma_list (fun (ident, pe) ->
                P.dot ^^ Pp_cabs.pp_cabs_identifier ident ^^ P.equals ^^^ pp pe
              ) xs
            )
        | PEunion (tag_sym, member_ident, pe) ->
            P.parens (pp_keyword "union" ^^^ pp_symbol tag_sym) ^^ P.braces (
              P.dot ^^ Pp_cabs.pp_cabs_identifier member_ident ^^ P.equals ^^^ pp pe
            )
        | PEmemberof (tag_sym, memb_ident, pe) ->
            pp_keyword "memberof" ^^ P.parens (
              pp_symbol tag_sym ^^ P.comma ^^^
              Pp_cabs.pp_cabs_identifier memb_ident ^^ P.comma ^^^
              pp pe
            )
        | PEcall (nm, pes) ->
            pp_name nm ^^ P.parens (comma_list pp pes)
        | PElet (pat, pe1, pe2) ->
            (* DEBUG  !^ "{-pe-}" ^^^ *)
            pp_control "let" ^^^ pp_pattern pat ^^^ P.equals ^^^
            pp pe1 ^^^ pp_control "in" ^^ P.break 1 ^^ pp pe2
        | PEif (pe1, pe2, pe3) ->
            P.group (
              pp_control "if" ^^^ pp pe1 ^^^ pp_control "then" ^^
              P.nest 2 (P.break 1 ^^ pp pe2) ^^ P.break 1 ^^
              pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp pe3)
            )
        | PEis_scalar pe ->
            pp_keyword "is_scalar" ^^^ P.parens (pp pe)
        | PEis_integer pe ->
            pp_keyword "is_integer" ^^^ P.parens (pp pe)
        | PEis_signed pe ->
            pp_keyword "is_signed" ^^^ P.parens (pp pe)
        | PEis_unsigned pe ->
            pp_keyword "is_unsigned" ^^^ P.parens (pp pe)
(*        | PEstd (_, pe) ->
            !^ "{-PEstd-}" ^^^ pp pe *)
    end
  in pp None pe


let rec pp_expr expr =
  let rec pp is_semi prec (Expr (annot, e)) =
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
        ) doc annot
    end
    begin
      begin
        (* Here we check whether parentheses are needed *)
        if compare_precedence prec' prec then
          (* right associativity of ; *)
          match (is_semi, e) with
            | (true, Esseq (Pattern (_, CaseBase (None, BTy_unit)), _, _)) ->
                P.parens
            | _ ->
                fun z -> z
        else
          P.parens
      end
      begin match e with
        | Epure pe ->
            pp_keyword "pure" ^^ P.parens (pp_pexpr pe)
        | Ememop (memop, pes) ->
            pp_keyword "memop" ^^ P.parens (Pp_mem.pp_memop memop ^^ P.comma ^^^ comma_list pp_pexpr pes)
        | Eaction (Paction (p, (Action (_, bs, act)))) ->
            pp_polarity p (pp_action act)
        | Ecase (pe, pat_es) ->
            pp_keyword "case" ^^^ pp_pexpr pe ^^^ pp_keyword "of" ^^
            P.nest 2 (
              P.break 1 ^^ P.separate_map (P.break 1) (fun (cpat, e) ->
                P.prefix 4 1
                  (P.bar ^^^ pp_pattern cpat ^^^ P.equals ^^ P.rangle)
                  (pp e)
              ) pat_es 
            ) ^^ P.break 1 ^^ pp_keyword "end"
        | Elet (pat, pe1, e2) ->
            P.group (
              P.prefix 0 1
                (pp_control "let" ^^^ pp_pattern pat ^^^ P.equals ^^^ pp_pexpr pe1 ^^^ pp_control "in")
                (pp e2)
           )
        | Eif (pe1, e2, e3) ->
            pp_control "if" ^^^ pp_pexpr pe1 ^^^ pp_control "then" ^^
            P.nest 2 (P.break 1 ^^ pp e2) ^^ P.break 1 ^^
            pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp e3)
        | Eskip ->
            pp_keyword "skip"
        | Eproc (_, nm, pes) ->
            pp_keyword "pcall" ^^ P.parens (pp_name nm ^^ P.comma ^^^ comma_list pp_pexpr pes)
        | Eccall (_, pe, pes) ->
            pp_keyword "ccall" ^^ P.parens (comma_list pp_pexpr (pe :: pes))
        | Eunseq [] ->
            !^ "BUG: UNSEQ must have at least two arguments (seen 0)"
        | Eunseq [e] ->
            !^ "BUG: UNSEQ must have at least two arguments (seen 1)" ^^ (pp_control "[-[-[") ^^ pp e ^^ (pp_control "]-]-]")
        | Eunseq es ->
            pp_control "unseq" ^^ P.parens (comma_list pp es)
        | Ewseq (pat, e1, e2) ->
            P.group (
              pp_control "let weak" ^^^ pp_pattern pat ^^^ P.equals ^^^
              let doc_e1 = pp e1 in
              P.ifflat doc_e1 (P.nest 2 (P.break 1 ^^ doc_e1)) ^^^ pp_control "in"
            ) ^^
            P.break 1 ^^ (pp e2)
        | Esseq (Pattern (_, CaseBase (None, BTy_unit)), e1, e2) ->
            (pp_ e1 ^^^ P.semi) ^/^ (pp e2)
        | Esseq (pat, e1, e2) ->
            P.group (
              pp_control "let strong" ^^^ pp_pattern pat ^^^ P.equals ^^^
              let doc_e1 = pp e1 in
              P.ifflat doc_e1 (P.nest 2 (P.break 1 ^^ doc_e1)) ^^^ pp_control "in"
            ) ^^
            P.break 1 ^^ (pp e2)
        | Easeq ((sym, _), act1, pact2) ->
            pp_control "leta" ^^^ pp_symbol sym ^^^ P.equals ^^^
            pp (Expr ([], Eaction (Paction (Pos, act1)))) ^^^ pp_control "in" ^^^ pp (Expr ([], Eaction pact2))
        | Eindet (i, e) ->
            pp_control "indet" ^^ P.brackets (!^ (string_of_int i)) ^^ P.parens (pp e)
        | Esave ((sym, bTy), sym_bTy_pes, e) ->
            pp_keyword "save" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^^
            P.parens (comma_list (fun (sym, (bTy, pe)) ->
              pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^ P.colon ^^ P.equals ^^^ pp_pexpr pe
            ) sym_bTy_pes) ^^^
            pp_control "in" ^^^
            P.nest 2 (P.break 1 ^^ pp e)
        | Erun (_, sym, pes) ->
            pp_keyword "run" ^^^ pp_symbol sym ^^ P.parens (comma_list pp_pexpr pes)
        | Epar es ->
            pp_keyword "par" ^^ P.parens (comma_list pp es)
        | Ewait tid ->
            pp_keyword "wait" ^^ P.parens (pp_thread_id tid)
        | End es ->
            pp_keyword "nd" ^^ P.parens (comma_list pp es)
        | Ebound (i, e) ->
            pp_keyword "bound" ^^ P.brackets (!^ (string_of_int i)) ^/^
            P.parens (pp e)
      end
    end
    in pp false None expr



and pp_action act =
  let pp_args args mo =
    P.parens (comma_list pp_pexpr args ^^ if mo = Cmm_csem.NA then P.empty else P.comma ^^^ pp_memory_order mo) in
  match act with
    | Create (al, ty, _) ->
        pp_keyword "create" ^^ P.parens (pp_pexpr al ^^ P.comma ^^^ pp_pexpr ty)
    | CreateReadOnly (al, ty, init, _) ->
        pp_keyword "create_readonly" ^^ P.parens (pp_pexpr al ^^ P.comma ^^^ pp_pexpr ty ^^ P.comma ^^^ pp_pexpr init)
    | Alloc0 (al, n, _) ->
        pp_keyword "alloc" ^^ P.parens (pp_pexpr al ^^ P.comma ^^^ pp_pexpr n)
    | Kill (b, e) ->
        pp_keyword (if b then "free" else "kill") ^^ P.parens (pp_pexpr e)
    | Store0 (is_locking, ty, e1, e2, mo) ->
       pp_keyword (if is_locking then "store_lock" else "store") ^^ pp_args [ty; e1; e2] mo
    | Load0 (ty, e, mo) ->
       pp_keyword "load" ^^ pp_args [ty; e] mo
    | RMW0 (ty, e1, e2, e3, mo1, mo2) ->
        pp_keyword "rmw" ^^
        P.parens (pp_pexpr ty ^^ P.comma ^^^ pp_pexpr e1 ^^ P.comma ^^^
                  pp_pexpr e2 ^^ P.comma ^^^ pp_pexpr e3 ^^ P.comma ^^^
                  pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
    | Fence0 mo ->
        pp_keyword "fence" ^^ P.parens (pp_memory_order mo)
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
  
  P.separate_map (P.break 1 ^^ P.break 1) (fun (tag, tagDef) ->
    let (str, xs) = begin match tagDef with
      | Tags.StructDef z -> ("struct", z)
      | Tags.UnionDef  z -> ("union", z)
    end in
    pp_keyword str ^^^ pp_symbol tag ^^^ P.braces (P.break 1 ^^
      P.nest 2 (
        P.separate_map (P.semi ^^ P.break 1) (fun (ident, ty) -> Pp_core_ctype.pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) xs
      ) ^^ P.break 1
    ) ^^ P.semi
  ) tagDefs


let pp_argument (sym, bTy) =
  pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy

let pp_params params =
  P.parens (comma_list pp_argument params)

let pp_fun_map funs =
  let pp_cond loc d =
    if show_include || Location_ocaml.from_main_file loc then d else P.empty
  in
  Pmap.fold (fun sym decl acc ->
    acc ^^ P.hardline ^^
    match decl with
      | Fun  (bTy, params, pe) ->
          pp_keyword "fun" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.hardline
      | ProcDecl (loc, bTy, bTys) ->
          pp_cond loc @@
          pp_keyword "proc" ^^^ pp_symbol sym ^^^ P.parens (comma_list pp_core_base_type bTys) ^^ P.break 1 ^^ P.break 1
      | Proc (loc, bTy, params, e) ->
          pp_cond loc @@
          pp_keyword "proc" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_keyword "eff" ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.hardline
    ) funs P.empty


let pp_impl impl =
  Pmap.fold (fun iCst iDecl acc ->
    acc ^^
    match iDecl with
      | Def (bty, pe) ->
          pp_keyword "def" ^^^ pp_impl iCst ^^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.break 1 ^^ P.break 1
          
      | IFun (bTy, params, pe) ->
          pp_keyword "fun" ^^^ pp_impl iCst ^^^ pp_params params ^^ P.colon ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.break 1 ^^ P.break 1
  ) impl P.empty
  


let mk_comment doc =
  pp_ansi_format [Red] (
    !^ "{-" ^^ P.break 1 ^^ doc ^^ P.break 1 ^^ !^ "-}"
  )


let pp_file file =
  let pp_glob acc (sym, bTy, e) =
    acc ^^
    pp_keyword "glob" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_base_type bTy ^^^
    P.colon ^^ P.equals ^^
    P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.break 1 ^^ P.break 1 in
  
  begin
    if Debug_ocaml.get_debug_level () > 1 then
      fun z -> 
        !^ "-- BEGIN STDLIB" ^^ P.break 1 ^^
        pp_fun_map file.stdlib ^^ P.break 1 ^^
        !^ "-- END STDLIB" ^^ P.break 1 ^^
        !^ "-- BEGIN IMPL" ^^ P.break 1 ^^
  (*  pp_impl file.impl ^^ P.break 1 ^^ *)
        !^ "-- END IMPL" ^^ P.break 1 ^^ z
    else
      id
  end
  
  begin
    mk_comment (pp_tagDefinitions (file.tagDefs)) ^^
    P.break 1 ^^ P.break 1 ^^
    
    !^ "-- Globals" ^^ P.break 1 ^^
    List.fold_left pp_glob P.empty file.globs ^^
    
    !^ "-- Fun map" ^^ P.break 1 ^^
    pp_fun_map file.funs
  end


(* Runtime stuff *)
let mk_pp_continuation_element cont_elem = fun z ->
  match cont_elem with
    | Kunseq (es1, es2) ->
        pp_control "unseq" ^^ P.parens (
          comma_list pp_expr es1 ^^ P.comma ^^^ z ^^ P.comma ^^^ comma_list pp_expr es2
        )
    | Kwseq (pat, e2) ->
        pp_control "let weak" ^^^ pp_pattern pat ^^^ P.equals ^^^ z ^^^
        pp_control "in" ^^^ pp_expr e2
    | Ksseq (pat, e2) ->
        pp_control "let strong" ^^^ pp_pattern pat ^^^ P.equals ^^^ z ^^^
        pp_control "in" ^^^ pp_expr e2

let rec pp_continuation = function
  | [] ->
      !^ "[]"
  | cont_elem :: cont ->
      (mk_pp_continuation_element cont_elem) (pp_continuation cont)



let rec pp_stack = function
  | Stack_empty ->
      !^ "empty"
  | Stack_cons (_, cont, sk') ->
      P.nest 2 (
        pp_continuation cont
      ) ^^ P.break 1 ^^ P.dot ^^ P.break 1 ^^
      pp_stack sk'

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
