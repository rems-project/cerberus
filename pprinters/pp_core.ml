open Lem_pervasives
open Global
open Core

open Either

open Colour

open Pp_prelude

let isatty = ref false





let precedence = function
  | PEop (OpExp, _, _) -> Some 1

  | PEop (OpMul, _, _)
  | PEop (OpDiv, _, _)
  | PEop (OpMod, _, _) -> Some 2
  
  | PEop (OpAdd, _, _)
  | PEop (OpSub, _, _) -> Some 3
  
  | PEop (OpLt,  _, _) -> Some 4
  
  | PEop (OpEq,  _, _) -> Some 5
  
  | PEop (OpAnd, _, _) -> Some 6
  
  | PEop (OpOr,  _, _) -> Some 7
  
  | PEmemop _
  | PEundef _
  | PEerror _
  | PEval _
  | PEsym _
  | PEimpl _
  | PEcons _
  | PEcase_list _
  | PEcase_ctype _
  | PEarray_shift _
  | PEmember_shift _
  | PEnot _
  | PEtuple _
  | PEarray _
  | PEstruct _
  | PEcall _
  | PElet _
  | PEif _
  | PEis_scalar _
  | PEis_integer _
  | PEis_signed _
  | PEis_unsigned _ -> None


let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | _                  -> true


let pp_keyword w = !^ (if !isatty then ansi_format [Bold; Magenta] w else w)
let pp_const   c = !^ (if !isatty then ansi_format [Magenta] c else c)
let pp_control w = !^ (if !isatty then ansi_format [Bold; Blue] w else w)
let pp_symbol  a = !^ (if !isatty then ansi_format [Blue] (Pp_symbol.to_string_pretty a) else (Pp_symbol.to_string_pretty a))
let pp_number  n = !^ (if !isatty then ansi_format [Yellow] n else n)
let pp_impl    i = P.angles (!^ (if !isatty then ansi_format [Yellow] (Implementation_.string_of_implementation_constant i)
                                            else Implementation_.string_of_implementation_constant i))


let rec pp_core_base_type = function
  | BTy_integer    -> !^ "integer"
  | BTy_boolean    -> !^ "boolean"
  | BTy_pointer    -> !^ "pointer"
  | BTy_ctype      -> !^ "ctype"
  | BTy_cfunction  -> !^ "cfunction"
  | BTy_unit       -> !^ "unit"
  | BTy_list bTys  -> !^ "TODO(BTy_list)"
  | BTy_tuple bTys -> P.parens (P.separate_map P.comma pp_core_base_type bTys)
  | BTy_any        -> !^ "any"


let pp_core_type = function
  | TyBase   baseTy -> pp_core_base_type baseTy
  | TyEffect baseTy -> P.brackets (pp_core_base_type baseTy)


let pp_binop = function
  | OpAdd -> P.plus
  | OpSub -> P.minus
  | OpMul -> P.star
  | OpDiv -> P.slash
  | OpMod -> P.percent
  | OpExp -> P.caret
  | OpEq  -> P.equals
  | OpLt  -> P.langle
  | OpAnd -> !^ "/\\"
  | OpOr  -> !^ "\\/"


let pp_ctype ty =
  P.dquotes (Pp_core_ctype.pp_ctype ty)





let pp_polarity = function
  | Pos -> P.empty
  | Neg -> P.tilde

let pp_name = function
  | Sym a  -> pp_symbol a
  | Impl i -> pp_impl i






let pp_memory_order = function
  | Cmm.NA      -> !^ "NA"
  | Cmm.Seq_cst -> pp_keyword "seq_cst"
  | Cmm.Relaxed -> pp_keyword "relaxed"
  | Cmm.Release -> pp_keyword "release"
  | Cmm.Acquire -> pp_keyword "acquire"
  | Cmm.Consume -> pp_keyword "consume"
  | Cmm.Acq_rel -> pp_keyword "acq_rel"
  

let pp_mem_addr (pref, addr) =
(*
  let rec pp = function
  | Cmm_aux_old.Lbase n          -> Pp_ail.pp_integer n
  | Cmm_aux_old.Lshift (addr, n) -> P.braces (pp addr ^^ P.comma ^^^ Pp_ail.pp_integer n)
  in
  P.at ^^ P.braces (pp_prefix pref ^^ P.colon ^^^ pp addr)
*)
  P.at ^^ P.braces (Pp_symbol.pp_prefix pref ^^ P.colon ^^^ (!^ "TODO"))


let pp_thread_id n =
  !^ ("th_" ^ string_of_int n)


let pp_pattern _as =
  let g = function
    | Some x -> pp_symbol x
    | None   -> P.underscore in
  match _as with
    | []   -> P.lparen ^^ P.rparen
    | [_a] -> g _a
    | _    -> P.parens (comma_list g _as)


(*
let pp_pointer_action = function
  | PtrEq ->
      pp_keyword "pointer_eq"
  | PtrNe ->
      pp_keyword "pointer_ne"
  | PtrShift ->
      pp_keyword "pointer_shift"
*)




let rec pp_value = function
  | Vunit ->
      pp_const "unit"
  | Vtrue ->
      pp_const "true"
  | Vfalse ->
      pp_const "false"
  | Vlist cvals ->
      P.brackets (comma_list pp_value cvals)
  | Vtuple cvals ->
      P.parens (comma_list pp_value cvals)
  | Vctype ty ->
      P.dquotes (Pp_core_ctype.pp_ctype ty)
  | Vunspecified ty ->
      pp_const "unspec" ^^ P.parens (P.dquotes (Pp_core_ctype.pp_ctype ty))
  | Vinteger ival ->
      Mem.case_integer_value0 ival
        (fun n -> !^ (Nat_big_num.to_string n))
        (fun () -> Pp_mem.pp_integer_value ival)
  | Vfloating str ->
      !^ str
  | Vsymbolic symb ->
      !^ "SYMB" ^^ P.parens (Pp_symbolic.pp_symbolic symb)
  | Vpointer ptr_val ->
      Pp_mem.pp_pointer_value ptr_val
  | Varray cvals ->
      pp_const "array" ^^ P.parens (comma_list pp_value cvals)
  | Vstruct (sym, xs) ->
      !^ "TODO(Vstruct)" 
      (* pp_const "struct" ^^ P.parens *)
  | Vunion (sym, ident, mem_val) ->
      !^ "TODO(Vunion)" 
      (* pp_const "struct" ^^ P.parens *)


let pp_pexpr pe =
  let rec pp prec pe =
    let prec' = precedence pe in
    let pp z = P.group (pp prec' z) in
    (if lt_precedence prec' prec then fun z -> z else P.parens)
    begin
      match pe with
        | PEundef ub ->
            pp_keyword "undef" ^^ P.angles (P.angles (!^ (
              if !isatty then ansi_format [Magenta] (Undefined.string_of_undefined_behaviour ub)
                         else Undefined.string_of_undefined_behaviour ub)))
        | PEerror str ->
            pp_keyword "error" ^^^ P.dquotes (!^ str)
        | PEval cval ->
            pp_value cval
        | PEsym sym ->
            pp_symbol sym
        | PEimpl iCst ->
            pp_impl iCst
        | PEcons (pe1, pe2) ->
            pp_const "cons" ^^ P.parens (pp pe1 ^^ P.comma ^^^ pp pe2)
        | PEcase_list (pe1, pe2, nm) ->
            pp_keyword "case_list" ^^ P.parens (
              pp pe1 ^^ P.comma ^^^ pp pe2 ^^ P.comma ^^^ pp_name nm
            )
        | PEcase_ctype (pe1, pe2, nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8) ->
            pp_keyword "case_ctype" ^^ P.parens (
              pp pe1 ^^ P.comma ^^^ pp pe2 ^^ P.comma ^^^
              pp_name nm1 ^^ P.comma ^^^ pp_name nm2 ^^ P.comma ^^^ pp_name nm3 ^^ P.comma ^^^
              pp_name nm4 ^^ P.comma ^^^ pp_name nm5 ^^ P.comma ^^^ pp_name nm6 ^^ P.comma ^^^
              pp_name nm7 ^^ P.comma ^^^ pp_name nm8 ^^ P.comma
            )
(*
        | PEshift (pe, ty_pes) ->
            pp_keyword "shift" ^^ P.parens (
              pp pe ^^ P.comma ^^^
              P.braces (comma_list (fun (ty, pe) -> P.parens (pp_ctype ty ^^ P.comma ^^^ pp pe)) ty_pes)
            )
*)
        | PEarray_shift (pe1, ty, pe2) ->
            pp_keyword "array_shift" ^^ P.parens (
              pp pe1 ^^ P.comma ^^^ pp_ctype ty ^^ P.comma ^^^ pp pe2
            )
        | PEmember_shift (pe, tag_sym, memb_ident) ->
            pp_keyword "member_shift" ^^ P.parens (
              pp pe ^^ P.comma ^^^ pp_symbol tag_sym ^^ Pp_cabs.pp_cabs_identifier memb_ident
            )
        | PEnot pe ->
            pp_keyword "not" ^^ P.parens (pp pe)
        | PEop (bop, pe1, pe2) ->
            pp pe1 ^^^ pp_binop bop ^^^ pp pe2
        | PEmemop (pure_memop, pes) ->
            pp_keyword "memop" ^^ P.parens (Pp_mem.pp_pure_memop pure_memop ^^ P.comma ^^^ comma_list pp pes)
        | PEtuple pes ->
            P.parens (comma_list pp pes)
        | PEarray pes ->
            pp_keyword "array" ^^ P.parens (comma_list pp pes)
        | PEstruct (tag_sym, xs) ->
            pp_keyword "struct" ^^ P.parens (
              pp_symbol tag_sym ^^ P.comma ^^^ comma_list (
                (fun (ident, pe) -> Pp_cabs.pp_cabs_identifier ident ^^ P.equals ^^^ pp pe)
              ) xs
            )
(*
        | PEarray xs -> (* of ( (Mem.mem_value, sym)Either.either) list *)
            pp_keyword "array" ^^ P.parens (
              comma_list (function
                | Left mem_val ->
                    pp_mem_value mem_val
                | Right sym ->
                    pp_symbol sym
              ) xs
            )
*)
        | PEcall (nm, pes) ->
            pp_name nm ^^ P.parens (comma_list pp pes)
        | PElet (sym, pe1, pe2) ->
            (* DEBUG *) !^ "{-pe-}" ^^^ pp_control "let" ^^^ pp_symbol sym ^^^ P.equals ^^^
            pp pe1 ^^^ pp_control "in" ^^ P.break 1 ^^ pp pe2 ^^^ pp_control "end"
        | PEif (pe1, pe2, pe3) ->
            pp_control "if" ^^^ pp pe1 ^^^ pp_control "then" ^^
            P.nest 2 (P.break 1 ^^ pp pe2) ^^ P.break 1 ^^
            pp_control "else" ^^
            P.nest 2 (P.break 1 ^^ pp pe3) ^^ P.break 1 ^^^
            pp_control "end"
        | PEis_scalar pe ->
            pp_keyword "is_scalar" ^^^ P.parens (pp pe)
        | PEis_integer pe ->
            pp_keyword "is_integer" ^^^ P.parens (pp pe)
        | PEis_signed pe ->
            pp_keyword "is_signed" ^^^ P.parens (pp pe)
        | PEis_unsigned pe ->
            pp_keyword "is_unsigned" ^^^ P.parens (pp pe)
    end
  in pp None pe



let rec pp_expr = function
  | Epure pe ->
      pp_pexpr pe
  | Ememop (memop, pes) ->
      pp_keyword "memop" ^^ P.parens (Pp_mem.pp_memop memop ^^ P.comma ^^^ comma_list pp_pexpr pes)
  | Eraise str ->
      pp_keyword "raise" ^^ P.parens (!^ str)
  | Eregister (str, nm) ->
      pp_keyword "register" ^^ P.parens (!^ str ^^ P.comma ^^^ pp_name nm)
  | Eskip ->
      pp_keyword "skip"
  | Elet (sym, pe1, e2) ->
      (* DEBUG *) !^ "{-e-}" ^^^ pp_control "let" ^^^ pp_symbol sym ^^^ P.equals ^^^
      pp_pexpr pe1 ^^^ pp_control "in" ^^ P.break 1 ^^ pp_expr e2 ^^^ pp_control "end"
  | Eif (pe1, e2, e3) ->
      pp_control "if" ^^^ pp_pexpr pe1 ^^^ pp_control "then" ^^
      P.nest 2 (P.break 1 ^^ pp_expr e2) ^^ P.break 1 ^^
      pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp_expr e3) ^^ P.break 1 ^^^ pp_control "end"
  | Eproc (_, nm, es) ->
      pp_name nm ^^ P.braces (comma_list pp_pexpr es)
  | Eaction (Paction (p, (Action (bs, act)))) ->
      (* (if Set.is_empty bs then P.empty else P.langle ^^ (P.sepmap P.space pp_trace_action (Set.to_list bs)) ^^
         P.rangle ^^ P.space) ^^ *)
      pp_polarity p ^^ pp_action act
  | Eunseq [] ->
      !^ "BUG: UNSEQ must have at least two arguments (seen 0)"
  | Eunseq [e] ->
      !^ "BUG: UNSEQ must have at least two arguments (seen 1)" ^^ (pp_control "[-[-[") ^^ pp_expr e ^^ (pp_control "]-]-]")
  | Eunseq es ->
      pp_control "unseq" ^^ P.parens (comma_list pp_expr es)
(*
(*      | Ewseq es ret -> (P.sepmap (wseq ^^ P.break1) pp_wseq es) ^^^ wseq ^^ P.break1 ^^ f ret *)
        | Ewseq ([], e1, e2) ->
            pp_control "let" ^^^ pp_control "weak" ^^ P.lparen ^^ P.rparen ^^^ P.equals ^^^
            pp e1 ^^^ pp_control "in"  ^^ P.break 1 ^^ pp e2 ^^^ pp_control "end"
(*            P.parens (pp e1 ^^^ wseq ^^ P.break 1 ^^ pp e2) *)
        | Ewseq ([Some a], e1, e2) ->
            pp_symbol a ^^^ !^ "<-" ^^^ ((* P.align $ *) pp e1) ^^^ wseq ^^ P.break 1 ^^
            pp e2  ^^^ pp_control "end"
        | Ewseq ([None], e1, e2) ->
            pp e1 ^^^ (!^ ">>") ^^ P.break 1 ^^ pp e2 ^^^ pp_control "end"
        | Ewseq (_as, e1, e2) ->
            let g = function
              | Some x -> pp_symbol x
              | None   -> P.underscore in
            
            pp_control "let" ^^^ pp_control "weak" ^^^ P.parens (comma_list g _as) ^^^ P.equals ^^^
            pp e1 ^^^ pp_control "in"  ^^ P.break 1 ^^ pp e2 ^^^ pp_control "end"
 *)
          (* TODO: update the parser to be sync ... *)
(*
        | Ewseq ([], e1, e2) ->
            pp e1 ^^ P.semi ^^ P.break 1 ^^ pp e2
*)
  | Ewseq (([] as _as), e1, e2)
  | Ewseq (_as, e1, e2) when List.for_all (function None -> true | _ -> false) _as ->
      pp_expr e1 ^^ P.semi ^^ P.break 1 ^^
      pp_expr e2
  | Ewseq (_as, e1, e2) ->
      pp_control "let" ^^^ pp_control "weak" ^^^ pp_pattern _as ^^^ P.equals ^^^
      pp_expr e1 ^^^ pp_control "in" ^^ P.break 1 ^^
      (* P.nest 2 *) (pp_expr e2) ^^ P.break 1 ^^ pp_control "end"
  | Esseq (([] as _as), e1, e2)
  | Esseq (_as, e1, e2) when List.for_all (function None -> true | _ -> false) _as ->
      pp_expr e1 ^^ P.semi ^^ P.break 1 ^^
      pp_expr e2
  | Esseq (_as, e1, e2) -> 
      pp_control "let" ^^^ pp_control "strong" ^^^ pp_pattern _as ^^^ P.equals ^^^
      pp_expr e1 ^^^ pp_control "in" ^^ P.break 1 ^^
      (* P.nest 2 *) (pp_expr e2) ^^ P.break 1 ^^ pp_control "end"
  | Easeq (None, act1, pact2) ->
      pp_control "let" ^^^ pp_control "atom" ^^^ P.underscore ^^^ P.equals ^^^
      pp_expr (Eaction (Paction (Pos, act1))) ^^^ pp_control "in" ^^^ pp_expr (Eaction pact2)
  | Easeq (Some sym, act1, pact2) ->
      pp_control "let" ^^^ pp_control "atom" ^^^ pp_symbol sym ^^^ P.equals ^^^
      pp_expr (Eaction (Paction (Pos, act1))) ^^^ pp_control "in" ^^^ pp_expr (Eaction pact2)
  | Eindet e ->
      pp_control "indet" ^^ P.parens (pp_expr e)
  | Esave (sym, sym_tys, e) ->
      pp_keyword "save" ^^^ pp_symbol sym ^^
      P.parens (comma_list (fun (sym,ty) -> pp_symbol sym ^^ P.colon ^^^ Pp_core_ctype.pp_ctype ty) sym_tys) ^^
      P.dot ^^^ pp_expr e ^^^ pp_control "end"
  | Erun (_, sym, sym_pes) ->
      pp_keyword "run" ^^^ pp_symbol sym ^^ P.parens (comma_list (fun (sym, pe) -> pp_symbol sym ^^ P.colon ^^^ pp_pexpr pe) sym_pes)
  | Eret pe ->
      pp_keyword "return" ^^^ P.parens (pp_pexpr pe)
  | Epar es ->
      pp_keyword "par" ^^ P.parens (comma_list pp_expr es)
  | Ewait tid ->
      pp_keyword "wait" ^^ P.parens (pp_thread_id tid)
  | End es ->
      pp_keyword "nd" ^^ P.parens (comma_list pp_expr es)

and pp_shift_path sh_path =
  P.braces (
    comma_list (fun (ty, pe) -> P.parens (P.dquotes (Pp_core_ctype.pp_ctype ty) ^^ P.comma ^^^ pp_pexpr pe)) sh_path
  )


and pp_action act =
  let pp_args args mo =
    P.parens (comma_list pp_pexpr args ^^ if mo = Cmm.NA then P.empty else P.comma ^^^ pp_memory_order mo) in
  match act with
    | Create (al, ty, _) ->
        pp_keyword "create" ^^ P.parens (pp_pexpr al ^^ P.comma ^^^ pp_pexpr ty)
    | Alloc0 (al, n, _) ->
        pp_keyword "alloc" ^^ P.parens (pp_pexpr al ^^ P.comma ^^^ pp_pexpr n)
    | Kill e ->
        pp_keyword "kill" ^^ P.parens (pp_pexpr e)
    | Store0 (ty, e1, e2, mo) ->
       pp_keyword "store" ^^ pp_args [ty; e1; e2] mo
    | Load0 (ty, e, mo) ->
       pp_keyword "load" ^^ pp_args [ty; e] mo
    | CompareExchangeStrong (ty, e1, e2, e3, mo1, mo2) ->
        pp_keyword "compare_exchange_strong" ^^
        P.parens (pp_pexpr ty ^^ P.comma ^^^ pp_pexpr e1 ^^ P.comma ^^^
                  pp_pexpr e2 ^^ P.comma ^^^ pp_pexpr e3 ^^ P.comma ^^^
                  pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
    | CompareExchangeWeak (ty, e1, e2, e3, mo1, mo2) ->
        pp_keyword "compare_exchange_weak" ^^
        P.parens (pp_pexpr ty ^^ P.comma ^^^ pp_pexpr e1 ^^ P.comma ^^^
                  pp_pexpr e2 ^^ P.comma ^^^ pp_pexpr e3 ^^ P.comma ^^^
                  pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
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
  Symbol.instance_Basic_classes_Ord_Symbol_t_dict.compare_method



let pp_tagDefinitions tagDefs =
  let tagDefs = Pmap.bindings_list tagDefs in
  
  P.separate_map (P.break 1 ^^ P.break 1) (fun (tag, ident_tys) ->
    pp_keyword "struct" ^^^ pp_symbol tag ^^^ P.braces (P.break 1 ^^
      P.nest 2 (
        P.separate_map (P.semi ^^ P.break 1) (fun (ident, ty) -> Pp_core_ctype.pp_ctype ty ^^^ Pp_cabs.pp_cabs_identifier ident) ident_tys
      ) ^^ P.break 1
    ) ^^ P.semi
  ) tagDefs



let pp_argument (sym, ty) =
  pp_symbol sym ^^ P.colon ^^^ pp_core_base_type ty

let pp_params params =
  P.parens (comma_list pp_argument params)

let pp_fun_map funs =
  Pmap.fold (fun sym decl acc ->
    acc ^^
    match decl with
      | Fun  (bTy, params, pe) ->
          pp_keyword "fun" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_pexpr pe) ^^ P.break 1 ^^ P.break 1
      | Proc (bTy, params, e) ->
          pp_keyword "proc" ^^^ pp_symbol sym ^^^ pp_params params ^^ P.colon ^^^ pp_keyword "eff" ^^^ pp_core_base_type bTy ^^^
          P.colon ^^ P.equals ^^
          P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.break 1 ^^ P.break 1
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
  



let pp_file file =
  let pp_glob acc (sym, coreTy, e) =
    acc ^^
    pp_keyword "glob" ^^^ pp_symbol sym ^^ P.colon ^^^ pp_core_type coreTy ^^^
    P.colon ^^ P.equals ^^
    P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.break 1 ^^ P.break 1 in
  
  isatty := Unix.isatty Unix.stdout;
  
  !^ "-- BEGIN STDLIB" ^^ P.break 1 ^^
  pp_fun_map file.stdlib ^^ P.break 1 ^^
  !^ "-- END STDLIB" ^^ P.break 1 ^^
  !^ "-- BEGIN IMPL" ^^ P.break 1 ^^
(*  pp_impl file.impl ^^ P.break 1 ^^ *)
  !^ "-- END IMPL" ^^ P.break 1 ^^


  
  
  
  
  !^ "{-" ^^ P.break 1 ^^
  pp_tagDefinitions file.tagDefinitions ^^ P.break 1 ^^
  !^ "-}" ^^ P.break 1 ^^
  
  List.fold_left pp_glob P.empty file.globs ^^
  pp_fun_map file.funs
