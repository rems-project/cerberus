open Lem_pervasives
open Global
open Core

open Colour

module P = PPrint

let isatty = ref false




let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f



module Mem = Naive_memory


let precedence = function
  | Eunit
  | Etrue
  | Efalse
  | Econst _
  | Elist _
  | Ectype _
  | Esym _
  | Eimpl _
  | Etuple _
  | Eundef _
  | Eerror
  | Eskip
  | Erun _            -> Some 0
  
  | Enot _
  | Esave _
  | Eret _
  | Eindet _          -> Some 1
  
  | Eaction _
  | Eproc _
  | Ecall _
  | Eoutput _         -> Some 2
  
  | Eop (OpMul, _, _)
  | Eop (OpDiv, _, _)
  | Eop (OpMod, _, _) -> Some 3
  
  | Eop (OpAdd, _, _)
  | Eop (OpSub, _, _) -> Some 4
  
  | Eop (OpLt,  _, _) -> Some 5
  
  | Eop (OpEq,  _, _) -> Some 6
  
  | Eop (OpAnd, _, _) -> Some 7
  
  | Eop (OpOr,  _, _) -> Some 8
  
  | Eif _             -> Some 9
  
  | Elet _            -> Some 10
  
  | Easeq _           -> Some 11
  
  | Ewseq _           -> Some 12
  
  | Esseq _           -> Some 13
  
  | Eunseq _          -> Some 14
  | Epar _            -> None
  | Ewait _           -> None
  | Etuple _          -> None (* shouldn't be needed *)
  | Ebound _          -> None (* shouldn't be needed *)
(* TODO: hack *)
  | End _             -> None

(* TODO: temporary *)
  | Eis_scalar _   -> Some 2
  | Eis_integer _  -> Some 2
  | Eis_signed _   -> Some 2
  | Eis_unsigned _ -> Some 2



let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | (Some _ , None   ) -> true
    | (None   , _      ) -> false


let pp_keyword w = !^ (if !isatty then ansi_format [Bold; Magenta] w else w)
let pp_const   c = !^ (if !isatty then ansi_format [Magenta] c else c)
let pp_control w = !^ (if !isatty then ansi_format [Bold; Blue] w else w)
let pp_symbol  a = !^ (if !isatty then ansi_format [Blue] (Pp_symbol.to_string a) else (Pp_symbol.to_string a))
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


let pp_integer_base_ctype ibty =
  let open AilTypes in
  match ibty with
    | Ichar    -> !^ "ichar"
    | Short    -> !^ "short"
    | Int_     -> !^ "int"
    | Long     -> !^ "long"
    | LongLong -> !^ "long_long"

let pp_integer_ctype ity =
  let open AilTypes in
  match ity with
    | Char             -> !^ "char"
    | Bool             -> !^ "_Bool"
    | Signed Int8_t    -> !^ "int8_t"
    | Signed Int16_t   -> !^ "int16_t"
    | Signed Int32_t   -> !^ "int32_t"
    | Signed Int64_t   -> !^ "int64_t"
    | Unsigned Int8_t  -> !^ "uint8_t"
    | Unsigned Int16_t -> !^ "uint16_t"
    | Unsigned Int32_t -> !^ "uint32_t"
    | Unsigned Int64_t -> !^ "uint64_t"
    | Signed ibty      -> !^ "signed"   ^^^ pp_integer_base_ctype ibty
    | Unsigned ibty    -> !^ "unsigned" ^^^ pp_integer_base_ctype ibty

let pp_basic_ctype bty =
  let open AilTypes in
  match bty with
    | Integer ity -> pp_integer_ctype ity


let rec pp_ctype t =
(*   let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)
  let open Core_ctype in
  match t with
    | Void0 ->
        !^ "void"
    | Basic0 bty ->
        pp_basic_ctype bty
    | Array0 (ty, n) ->
        pp_ctype ty ^^ P.brackets (Pp_ail.pp_integer n)
(*
    | STRUCT (tag, mems)      -> !^ "struct" ^^^ Pp_ail.pp_id tag ^^^ P.braces (pp_mems mems)
    | UNION (tag, mems)       -> !^ "union" ^^^ Pp_ail.pp_id tag ^^^ P.braces (pp_mems mems)
    | ENUM name               -> !^ "enum" ^^^ Pp_ail.pp_id name
*)
    | Function0 (ty, args_tys, is_variadic) ->
        pp_ctype ty ^^^ P.parens (
          comma_list (fun (qs, ty) -> Pp_ail.pp_qualifiers qs (pp_ctype ty)) args_tys ^^
          (if is_variadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty)
        )
    | Pointer0 (qs, ty) ->
        Pp_ail.pp_qualifiers qs (pp_ctype ty) ^^ P.star
    | Atomic0 ty ->
        !^ "_Atomic" ^^^ P.parens (pp_ctype ty)

(*
and pp_member = function
  | Core_ctype.MEMBER ty ->
      fun z -> pp_ctype ty ^^^ Pp_ail.pp_id z ^^ P.semi
  | Core_ctype.BITFIELD (ty, w, _) ->
      fun z -> pp_ctype ty ^^^ Pp_ail.pp_id z ^^ P.colon ^^^ Pp_ail.pp_integer w ^^ P.semi
 *)


let pp_binop = function
  | OpAdd -> P.plus
  | OpSub -> P.minus
  | OpMul -> P.star
  | OpDiv -> P.slash
  | OpMod -> P.percent
  | OpEq  -> P.equals
  | OpLt  -> P.langle
  | OpAnd -> !^ "/\\"
  | OpOr  -> !^ "\\/"


(* Qualification prefix for memory addresses *)
let rec pp_prefix = function
  | []    -> P.empty
  | x::xs -> pp_symbol x ^^ P.dot ^^ pp_prefix xs


let pp_polarity = function
  | Pos -> P.empty
  | Neg -> P.tilde

let pp_name = function
  | Sym a  -> pp_symbol a
  | Impl i -> pp_impl i


let rec pp_symbolic = function
  | Symbolic.Symbolic_constant n ->
      !^ (Big_int.string_of_big_int n)
  | Symbolic.Symbolic_symbol sym ->
      pp_symbol sym
  | Symbolic.Symbolic_op (op, symb1, symb2) ->
      let str_opt = match op with
        | Symbolic.Add -> "+"
        | Symbolic.Sub -> "-"
        | Symbolic.Mul -> "*"
        | Symbolic.Div -> "/"
        | Symbolic.Mod -> "mod" in

      P.parens (!^ str_opt ^^^ pp_symbolic symb1 ^^^ pp_symbolic symb2)


let rec pp_constant = function
(*
  | Mem.MV_pointer (Mem.Pointer_function f) ->
      !^ "TODO(MV_pointer(function))"
*)
  | Mem.MV_pointer (Mem.Pointer_nonnull n) ->
      !^ ("@" ^ Big_int.string_of_big_int n)
  | Mem.MV_pointer ptr_val ->
      !^ "TODO(MV_pointer)" 
  | Mem.MV_integer (Symbolic.Symbolic_constant n) ->
      !^ (Big_int.string_of_big_int n)
  | Mem.MV_integer symb ->
      !^ "SYMB" ^^ P.parens (pp_symbolic symb)
(*
  | Mem.MV_array vs ->
      pp_const "array" ^^ P.parens (comma_list pp_constant vs)
  | Mem.MV_struct _ ->
      !^ "TODO(MV_struct)"
  | Mem.MV_union _ ->
      !^ "TODO(MV_union)"
  | Mem.MV_pointer_byte _ ->
      !^ "TODO(MV_pointer_byte)"
  | Mem.MV_unspecified ty ->
      !^ "unspecified" ^^ P.parens (pp_ctype ty)
*)

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
  P.at ^^ P.braces (pp_prefix pref ^^ P.colon ^^^ (!^ "TODO"))


let pp_thread_id n =
  !^ ("th_" ^ Big_int.string_of_big_int n)


let pp_pattern _as =
  let g = function
    | Some x -> pp_symbol x
    | None   -> P.underscore in
  match _as with
    | []   -> P.lparen ^^ P.rparen
    | [_a] -> g _a
    | _    -> P.parens (comma_list g _as)


let rec pp_expr e =
  let rec pp p e =
    let p'   = precedence e in
    let pp z = P.group (pp p' z) in
    (if lt_precedence p' p then fun x -> x else P.parens)
      (match e with
        | Eunit ->
            pp_const "unit"
        | Etrue ->
            pp_const "true"
        | Efalse ->
            pp_const "false"
        | Econst c ->
            pp_constant c
        | Elist pes ->
            P.brackets (comma_list pp pes)
        | Ectype ty ->
            P.dquotes (pp_ctype ty)
        | Esym sym ->
            pp_symbol sym
        | Eimpl i ->
            pp_impl i
        | Etuple pes ->
            P.parens (comma_list pp pes)
        | Enot e ->
            pp_keyword "not" ^^^ P.parens (pp e)
        | Eop (op, e1, e2) ->
            pp e1 ^^^ pp_binop op ^^^ pp e2
        | Ecall (fname, es) ->
            pp_name fname ^^ P.parens (comma_list pp es)
        | Eoutput str ->
            (* TODO: the string should be quoted and escaped *)
            pp_keyword "output" ^^ P.parens (!^ str)
        | Eundef u ->
            pp_keyword "undef" ^^ P.angles (P.angles (!^ (
              if !isatty then ansi_format [Magenta] (Undefined.string_of_undefined_behaviour u)
                         else Undefined.string_of_undefined_behaviour u)))
        | Eerror ->
            pp_keyword "error"
        | Eskip ->
            pp_keyword "skip"
        | Elet (a, e1, e2) ->
            pp_control "let" ^^^ pp_symbol a ^^^ P.equals ^^^
            pp e1 ^^^ pp_control "in" ^^ P.break 1 ^^ pp e2 ^^^ pp_control "end"
        | Eif (b, e1, e2) ->
            pp_control "if" ^^^ pp b ^^^ pp_control "then" ^^
            P.nest 2 (P.break 1 ^^ pp e1) ^^ P.break 1 ^^
            pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp e2) ^^ P.break 1 ^^^ pp_control "end"
        | Eproc (_, fname, es) ->
            pp_name fname ^^ P.braces (comma_list pp es)
        | Eaction (Paction (p, (Action (bs, a)))) ->
          (* (if Set.is_empty bs then P.empty else P.langle ^^ (P.sepmap P.space pp_trace_action (Set.to_list bs)) ^^
             P.rangle ^^ P.space) ^^ *)
          pp_polarity p ^^ pp_action a
        | Eunseq [] ->
            !^ "BUG: UNSEQ must have at least two arguments (seen 0)"
        | Eunseq [e] ->
            !^ "BUG: UNSEQ must have at least two arguments (seen 1)" ^^ (pp_control "[-[-[") ^^ pp e ^^ (pp_control "]-]-]")
        | Eunseq es ->
            P.brackets (P.separate_map (P.space ^^ (pp_control "||") ^^ P.space) pp es)


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
        | Ewseq (_as, e1, e2) ->
            pp_control "let" ^^^ pp_control "weak" ^^^ pp_pattern _as ^^^ P.equals ^^^
            pp e1 ^^^ pp_control "in" ^^ P.break 1 ^^
            P.nest 2 (pp e2) ^^ P.break 1 ^^ pp_control "end"
        | Esseq (_as, e1, e2) ->
            pp_control "let" ^^^ pp_control "strong" ^^^ pp_pattern _as ^^^ P.equals ^^^
            pp e1 ^^^ pp_control "in" ^^ P.break 1 ^^
            P.nest 2 (pp e2) ^^ P.break 1 ^^ pp_control "end"
        | Easeq (None, act, y) ->
            pp_control "let" ^^^ pp_control "atom" ^^^ P.lparen ^^ P.rparen ^^^ P.equals ^^^
            pp (Eaction (Paction (Pos, act))) ^^^ pp_control "in" ^^^ pp (Eaction y) ^^^ pp_control "end"
        | Easeq (Some a, act, y) ->
            pp_control "let" ^^^ pp_control "atom" ^^^ pp_symbol a ^^^ P.equals ^^^
            pp (Eaction (Paction (Pos, act))) ^^^ pp_control "in" ^^^ pp (Eaction y) ^^^ pp_control "end"
        | Eindet e ->
            pp_control "indet" ^^ P.parens (pp e)
        | Esave (l, a_ty_s, e) ->
            pp_keyword "save" ^^^ pp_symbol l ^^
            P.parens (comma_list (fun (a,ty) -> pp_symbol a ^^ P.colon ^^^ pp_ctype ty) a_ty_s) ^^
            P.dot ^^^ pp e ^^^ pp_control "end"
        | Erun (_, l, es) ->
            pp_keyword "run" ^^^ pp_symbol l ^^ P.parens (comma_list (fun (a, e) -> pp_symbol a ^^ P.colon ^^^ pp e) es)
        | Eret e ->
            pp_keyword "return" ^^^ P.parens (pp e)
        | Epar es ->
            pp_keyword "par" ^^ P.parens (comma_list pp es)
        | Ewait tid ->
            pp_keyword "wait" ^^ P.parens (pp_thread_id tid)
        | End es ->
            pp_keyword "nd" ^^ P.parens (comma_list pp es)
        
        (* TODO: temporary *)
        | Eis_scalar e ->
            pp_keyword "is_scalar" ^^^ P.parens (pp e)
        | Eis_integer e ->
            pp_keyword "is_integer" ^^^ P.parens (pp e)
        | Eis_signed e ->
            pp_keyword "is_signed" ^^^ P.parens (pp e)
        | Eis_unsigned e ->
            pp_keyword "is_unsigned" ^^^ P.parens (pp e)
      )
  in pp None e

and pp_action act =
  let pp_args args mo =
    P.parens (comma_list pp_expr args ^^ if mo = Cmm.NA then P.empty else P.comma ^^^ pp_memory_order mo) in
  match act with
    | Create (al, ty, _) ->
        pp_keyword "create" ^^ P.parens (pp_expr al ^^ P.comma ^^^ pp_expr ty)
    | Alloc0 (al, n, _) ->
        pp_keyword "alloc" ^^ P.parens (pp_expr al ^^ P.comma ^^^ pp_expr n)
    | Kill e ->
        pp_keyword "kill" ^^ P.parens (pp_expr e)
    | Store0 (ty, e1, e2, mo) ->
       pp_keyword "store" ^^ pp_args [ty; e1; e2] mo
    | Load0 (ty, e, mo) ->
       pp_keyword "load" ^^ pp_args [ty; e] mo
    | CompareExchangeStrong (ty, e1, e2, e3, mo1, mo2) ->
        pp_keyword "compare_exchange_strong" ^^
        P.parens (pp_expr ty ^^ P.comma ^^^ pp_expr e1 ^^ P.comma ^^^
                  pp_expr e2 ^^ P.comma ^^^ pp_expr e3 ^^ P.comma ^^^
                  pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)
    | CompareExchangeWeak (ty, e1, e2, e3, mo1, mo2) ->
        pp_keyword "compare_exchange_weak" ^^
        P.parens (pp_expr ty ^^ P.comma ^^^ pp_expr e1 ^^ P.comma ^^^
                  pp_expr e2 ^^ P.comma ^^^ pp_expr e3 ^^ P.comma ^^^
                  pp_memory_order mo1 ^^ P.comma ^^^ pp_memory_order mo2)



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


let pp_argument (aname, atype) = pp_symbol aname ^^ P.colon ^^^ pp_core_base_type atype

let pp_params params =
  P.parens (comma_list pp_argument params)

let pp_file file =
  isatty := Unix.isatty Unix.stdout;
  let f acc (fname, (ftype, args, body)) =
    acc ^^
      pp_keyword "fun" ^^^ pp_symbol fname ^^^ P.parens (comma_list pp_argument args) ^^ P.colon ^^^ pp_core_type ftype ^^^
      P.colon ^^ P.equals ^^
      P.nest 2 (P.break 1 ^^ pp_expr body) ^^ P.break 1 ^^ P.break 1 in
  let g acc (gsym, gbTy, e) =
    acc ^^
    pp_keyword "def" ^^^ pp_symbol gsym ^^ P.colon ^^^ pp_core_base_type gbTy ^^^
    P.colon ^^ P.equals ^^
    P.nest 2 (P.break 1 ^^ pp_expr e) ^^ P.break 1 ^^ P.break 1 in
  
  List.fold_left g P.empty file.defs ^^
  List.fold_left f P.empty (List.filter (function (Symbol.Symbol (_, Some f), _) -> not (List.mem f std) | _ -> true)
    (Pset.elements (Pmap.bindings (pairCompare symbol_compare (fun _ _ -> 0)) file.funs))) ^^ P.break 1
