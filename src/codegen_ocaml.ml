(* Created by Victor Gomes 2016-01-19 *)
(* It generates an Ocaml file from Core AST *)

open Pp_prelude
open Core

(* Ocaml Keywords *)
module K = struct
  let let_  = !^"let"
  let in_   = !^"in"
  let unit_ = !^"()"
  let if_   = !^"if"
  let then_ = !^"then"
  let else_ = !^"else"
  let true_ = !^"true"
  let false_ = !^"false"

  let main_ = !^"main"
  let exit_ = !^"exit"
end

let todo str = !^"TODO(" ^^ !^str ^^ !^")" 

(* Binary operations and precedences *)
let binop = function
  | OpAdd -> P.plus
  | OpSub -> P.minus
  | OpMul -> P.star
  | OpDiv -> P.slash
  | OpRem_t -> !^"rem_t"
  | OpRem_f -> !^"rem_f"
  | OpExp -> P.caret
  | OpEq  -> P.equals
  | OpLt  -> P.langle
  | OpLe  -> P.langle ^^ P.equals
  | OpGt  -> P.rangle
  | OpGe  -> P.rangle ^^ P.equals
  | OpAnd -> !^ "/\\"
  | OpOr  -> !^ "\\/"

let precedence = function
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
  
  | PEis_unspec _
  | PEmemop _
  | PEundef _
  | PEerror _
  | PEval _
  | PEsym _
  | PEimpl _
  | PEctor _
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

let symbol a = !^(Pp_symbol.to_string_pretty a)

let pattern _as =
  let g = function
    | Some x -> symbol x
    | None   -> P.underscore in
  match _as with
    | []   -> P.lparen ^^ P.rparen
    | [_a] -> g _a
    | _    -> P.parens (comma_list g _as)

let rec base_type = function
  | BTy_integer    ->  !^"int"
  | BTy_boolean    ->  !^"bool"
  | BTy_pointer    ->  !^"TODO(pointer)"
  | BTy_ctype      ->  !^"TODO(ctype)"
  | BTy_cfunction  ->  !^"TODO(cfunction)"
  | BTy_unit       ->  K.unit_
  | BTy_list bTys  ->  P.lbrace ^^ base_type bTys ^^ P.rbrace
  | BTy_tuple bTys ->  P.parens (P.separate_map P.star base_type bTys)
  | BTy_any        ->  !^"TODO(any)"

let core_type = function
  | TyBase   baseTy -> base_type baseTy
  | TyEffect baseTy -> base_type baseTy

let param params = 
  let args (sym, ty) = P.parens (symbol sym ^^ P.colon ^^ base_type ty)
  in P.separate_map P.space args params

let fun_name = function
  | Sym a  -> symbol a
  | Impl i -> todo "fun impl"

let rec value = function
  | Vunit             -> K.unit_
  | Vtrue             -> K.true_
  | Vfalse            -> K.false_
  | Vlist cvals       -> todo "list"
  | Vtuple cvals      -> P.parens (comma_list value cvals)
  | Vctype ty         -> todo "ctype"
  | Vunspecified ty   -> todo "unspecified"
  | Vinteger ival     -> 
      Mem.case_integer_value0 ival
        (fun n -> !^ (Nat_big_num.to_string n))
        (fun () -> Pp_mem.pp_integer_value ival)
  | Vsymbolic symb    -> todo "symbolic"
  | Vpointer ptr_val  -> todo "pointer"
  | Varray cvals      -> todo "arrays"
  | Vstruct (sym, xs) -> todo "struct"
  | Vunion (sym, ident, mem_val) -> todo "union"

let pexpr pe =
  let rec pp prec pe =
    let prec' = precedence pe in
    let pp z = P.group (pp prec' z) in
    (if lt_precedence prec' prec then fun z -> z else P.parens)
    begin
      match pe with
        | PEundef ub -> todo "pure: undef"
        | PEerror (str, pe) -> todo "pure: error"
        | PEval cval -> value cval
        | PEsym sym -> symbol sym
        | PEimpl iCst -> todo "pure: impl"
        | PEctor (ctor, pes) -> todo "pure: ctor"
        | PEcons (pe1, pe2) -> todo "pure: cons"
        | PEcase_list (pe1, pe2, nm) -> todo "pure: case_list"
        | PEcase_ctype (pe1, pe2, nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8) -> todo "pure: case_ctype"
        | PEarray_shift (pe1, ty, pe2) -> todo "pure: array_shift"
        | PEmember_shift (pe, tag_sym, memb_ident) -> todo "pure: member_shift"
        | PEnot pe -> todo "pure: not"
        | PEop (bop, pe1, pe2) -> pp pe1 ^^^ binop bop ^^^ pp pe2
        | PEis_unspec pe -> todo "pure: is_unspec"
        | PEmemop (pure_memop, pes) -> todo "pure: mmop"
        | PEtuple pes -> P.parens (comma_list pp pes)
        | PEarray pes -> todo "pure: array"
        | PEstruct (tag_sym, xs) -> todo "pure: struct"
        | PEcall (nm, pes) -> P.parens (fun_name nm ^^^ P.separate_map P.space (fun x -> P.parens (pp x)) pes)
        | PElet (sym, pe1, pe2) -> todo "pure: let"
        | PEif (pe1, pe2, pe3) -> todo "pure: if"
        | PEis_scalar pe -> todo "pure: is_scalar"
        | PEis_integer pe -> todo "pure: is_integer"
        | PEis_signed pe -> todo "pure: is_signed"
        | PEis_unsigned pe -> todo "pure: is_unsigned"
    end
  in pp None pe

let rec expr = function
  | Epure pe ->
      pexpr pe
  | Ememop (memop, pes) ->
      todo "memop"
  | Eraise str ->
      todo "raise"
  | Eregister (str, nm) ->
      todo "register"
  | Eskip ->
	    K.unit_
  | Elet (sym, pe1, e2) ->
      todo "let"
  | Eif (pe1, e2, e3) ->
      todo "if"
  | Eproc (_, nm, es) ->
      todo "proc"
  | Eaction (Paction (p, (Action (_, bs, act)))) ->
      action act
  | Eunseq [] ->
      !^"BUG: UNSEQ must have at least two arguments (seen 0)"
  | Eunseq [e] ->
      !^"BUG: UNSEQ must have at least two arguments (seen 1)"
  | Eunseq es ->
      todo "unseq"
  | Ewseq (_as, e1, e2) ->
	    K.let_ ^^^ pattern _as ^^^ P.equals ^^^ expr e1 ^^^ K.in_ ^/^ expr e2 
  | Esseq (_as, e1, e2) -> 
	    K.let_ ^^^ pattern _as ^^^ P.equals ^^^ expr e1 ^^^ K.in_ ^/^ expr e2 
  | Easeq (None, act1, pact2) ->
      todo "aseq"
  | Easeq (Some sym, act1, pact2) ->
      todo "aseq"
  | Eindet e ->
      todo "ident"
  | Esave (sym, sym_tys, e) ->
      todo "save"
  | Erun (_, sym, sym_pes) ->
      todo "run"
  | Eret pe ->
	    pexpr pe
  | Epar es ->
      todo "par"
  | Ewait tid ->
      todo "wait"
  | Eloc (_, e) ->
      expr e
  | End es ->
      todo "end"
  | Ebound _ ->
      todo "bound"

and memory_order = function
  | Cmm.NA      -> !^"NA"
  | Cmm.Seq_cst -> !^"seq_cst"
  | Cmm.Relaxed -> !^"relaxed"
  | Cmm.Release -> !^"release"
  | Cmm.Acquire -> !^"acquire"
  | Cmm.Consume -> !^"consume"
  | Cmm.Acq_rel -> !^"acq_rel"

and action act =
  let args args mo =
    P.parens (comma_list pexpr args ^^ if mo = Cmm.NA then P.empty else P.comma ^^^ memory_order mo) in
  match act with
    | Create (al, ty, _) ->
        !^"create" ^^ P.parens (pexpr al ^^ P.comma ^^^ pexpr ty)
    | Alloc0 (al, n, _) ->
        !^"alloc" ^^ P.parens (pexpr al ^^ P.comma ^^^ pexpr n)
    | Kill e ->
        !^"kill" ^^ P.parens (pexpr e)
    | Store0 (ty, e1, e2, mo) ->
       !^"store" ^^ args [ty; e1; e2] mo
    | Load0 (ty, e, mo) ->
       !^"load" ^^ args [ty; e] mo
    | RMW0 (ty, e1, e2, e3, mo1, mo2) ->
        !^"rmw" ^^
        P.parens (pexpr ty ^^ P.comma ^^^ pexpr e1 ^^ P.comma ^^^
                  pexpr e2 ^^ P.comma ^^^ pexpr e3 ^^ P.comma ^^^
                  memory_order mo1 ^^ P.comma ^^^ memory_order mo2)

let fun_map funs =
  Pmap.fold (fun sym decl acc ->
    acc ^^
    match decl with
      | Fun  (bTy, params, pe) ->
          todo "fun"
      | Proc (bTy, params, e) ->
          let prms = if List.length params > 0 then P.space ^^ param params else P.empty
          in K.let_ ^^^ symbol sym ^^ prms ^^^ P.colon ^^^ base_type bTy  ^^^ P.equals ^^
             P.nest 2 (P.break 1 ^^ expr e ^^ P.semi ^^ P.semi) ^/^ P.break 1
  ) funs P.empty

let generate_ocaml core =
  let globals acc (sym, coreTy, e) =
    acc ^^
    K.let_ ^^^ symbol sym ^^^ P.colon ^^^ core_type coreTy ^^^ P.equals ^^
    P.nest 2 (P.break 1 ^^ expr e ^^ P.semi ^^ P.semi) ^/^ P.break 1
  in
    fun_map core.stdlib ^^ 
    List.fold_left globals P.empty core.globs ^^
    fun_map core.funs ^^ 
    K.exit_ ^^^ K.main_ ^^^ P.break 2

let compile filename stdout_flag core =
  let fl = Filename.chop_extension filename in
  let fl_ml = fl ^ ".ml" in
  let fl_native = fl ^ ".native" in
  let firstline = !^"(* Generated by Cerberus from" ^^^ !^filename ^^ !^" *)" in
  let oc = open_out fl_ml in
  begin
    P.ToChannel.pretty 1. 80 oc (firstline ^/^ generate_ocaml core); 
    close_out oc;
    if stdout_flag then Sys.command ("cat " ^ fl_ml) else 0;
    Sys.command ("ocamlbuild " ^ fl_native);
    Exception.return2 0
  end
