%{
open Lem_pervasives
open Global

module Cmm = Cmm_csem

type ctype_ =
  | Void_
  | Basic_ of AilTypes.basicType
  | Array_ of ctype_ * Big_int.big_int (* NOTE: if the element type is WILDCARD, we ignore the size, ie. _[n] is the same as _[m] *)
(*
  | STRUCT_ of Ail.id * (Ail.id * Core.member) list
  | UNION_  of Ail.id * (Ail.id * Core.member) list
  | ENUM_ of Ail.id
*)
  | Function_ of Core_ctype.ctype0 * Core_ctype.ctype0 list
  | Pointer_ of ctype_
  | Atomic_ of ctype_
(*
  | SIZE_T_
  | INTPTR_T_
  | WCHAR_T_
  | CHAR16_T_
  | CHAR32_T_
*)
  | WILDCARD


let rec project_ctype_ = function
  | Void_ ->
      Core_ctype.Void0
  | Basic_ bty ->
      Core_ctype.Basic0 bty
  | Array_ (ty_, n) ->
    Core_ctype.Array0 (project_ctype_ ty_, n)
(*
  | STRUCT_ (x, membrs) ->
      Core.STRUCT (x, membrs)
  | UNION_ (x, membrs) ->
      Core.UNION (x, membrs)
  | ENUM_ id ->
      Core.ENUM id
*)
  | Function_ (ty, tys) ->
      Core_ctype.Function0 (ty, tys)
  | Pointer_ ty_ ->
      Core_ctype.Pointer0 (project_ctype_ ty_)
  | Atomic_ ty_ ->
      Core_ctype.Atomic1 (project_ctype_ ty_)
(*
  | SIZE_T_ ->
      Core.SIZE_T
  | INTPTR_T_ ->
      Core.INTPTR_T
  | WCHAR_T_ ->
      Core.WCHAR_T
  | CHAR16_T_ ->
      Core.CHAR16_T
  | CHAR32_T_ ->
      Core.CHAR32_T
*)
  | WILDCARD ->
      failwith "This is not a completely defined ctype."

type name =
  | Sym of string
  | Impl of Implementation_.implementation_constant

type expr =
  | Eskip
  | Econst of Cmm_aux.constant1
(*  | Eaddr of Core.mem_addr *)
  | Esym of string
  | Eimpl of Implementation_.implementation_constant
  | Eop of Core.binop * expr * expr
  | Etrue
  | Efalse
  | Eis_scalar of expr
  | Eis_integer of expr
  | Eis_signed of expr
  | Eis_unsigned of expr
  | Enot of expr
  | Ectype of Core_ctype.ctype0
  | Elet of string * expr * expr
  | Eif of expr * expr * expr
  | Ecase of expr * (ctype_ * expr) list (* This is a hackish syntactic sugar, that should really only used to case over ctypes *)
  | Eproc of string * expr list
  | Ecall of name * expr list
  | Esame of expr * expr
  | Eundef
  | Eerror
  | Eaction of paction
  | Eunseq of expr list
  | Epar of expr list
  | Ewseq of (string option) list * expr * expr
  | Esseq of (string option) list * expr * expr
  | Easeq of string option * action * paction
  | Eindet of expr (* TODO: add unique indices *)
  | Ebound of int * expr
  | Esave of string * expr
  | Erun of string
  | Eret of expr

and action =
  | Create of expr
  | Alloc of expr
  | Kill of expr
  | Store of expr * expr * expr * Cmm.memory_order
  | Load of expr * expr * Cmm.memory_order
  | CompareExchangeStrong of expr * expr * expr * expr * Cmm.memory_order * Cmm.memory_order
  | CompareExchangeWeak of expr * expr * expr * expr * Cmm.memory_order * Cmm.memory_order
and paction = Core.polarity * action

type declaration =
  | Def_decl  of Implementation_.implementation_constant * Core.core_base_type * expr
  | IFun_decl of Implementation_.implementation_constant * (Core.core_base_type * (string * Core.core_base_type) list * expr)
  | Fun_decl  of string * (Core.core_type * (string * Core.core_base_type) list * expr)

(* TODO *)
let convert e arg_syms fsyms =
  let rec f ((count, syms) as st) = function
    | Eskip                     -> Core.Eskip
    | Econst c                  -> Core.Econst c
    | Esym a                    -> (* Boot.print_debug ("LOOKING FOR> " ^ a) *) (Core.Esym (Pmap.find a syms)) (* Error handling *)
    | Eimpl i                   -> Core.Eimpl i
    | Eop (binop, e1, e2)       -> Core.Eop (binop, f st e1, f st e2)
    | Etrue                     -> Core.Etrue
    | Efalse                    -> Core.Efalse
    | Eis_scalar e              -> Core.Eis_scalar (f st e)
    | Eis_integer e             -> Core.Eis_integer (f st e)
    | Eis_signed e              -> Core.Eis_signed (f st e)
    | Eis_unsigned e            -> Core.Eis_unsigned (f st e)
    | Enot e                    -> Core.Enot (f st e)
    | Ectype ty                 -> Core.Ectype ty
    | Elet (a, e1, e2) ->
        let _a = Symbol.Symbol (count, Some a) in
        Core.Elet (_a, f st e1, f (count+1, Pmap.add a _a syms) e2)

    | Eif (e1, e2, e3)          -> Core.Eif (f st e1, f st e2, f st e3)

    | Ecase (e, es) ->
        (* TODO: if we use Error here, then error isn't anymore just the delayed C static error. *)
        List.fold_right (fun (ty_, e') acc ->
          Core.Eif (Core.Eop (Core.OpEq, f st e, Core.Ectype (project_ctype_ ty_)), f st e', acc)
        ) es Core.Eerror

    | Eproc (func, args)        -> Core.Eproc (Pset.empty compare, Pmap.find func fsyms, List.map (f st) args)
    | Ecall (Impl func, args)   -> Core.Ecall (Core.Impl func, List.map (f st) args)
    | Ecall (Sym func, args)    ->
        let fsym =
          try
            Pmap.find func fsyms
          with Not_found ->
            try
              Pmap.find func M.std
            with Not_found ->
              prerr_endline (Colour.ansi_format [Colour.Red] ("PARSING ERROR: the function `" ^ func ^ "' was not declared."));
              exit 1 in
        Core.Ecall (Core.Sym fsym, List.map (f st) args)
    | Esame (e1, e2)            -> Core.Esame (f st e1, f st e2)
    | Eundef                    -> Core.Eundef Undefined.DUMMY
    | Eerror                    -> Core.Eerror
    | Eaction pact              -> Core.Eaction (g st pact)
    | Eunseq es                 -> Core.Eunseq (List.map (f st) es)
    | Epar    es                 -> Core.Epar (List.map (f st) es)
    | Ewseq (_as, e1, e2) ->
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = Symbol.Symbol (c, Some sym) in
                          (* Boot.print_debug ("ADDING> " ^ sym) *) (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        
        Core.Ewseq (List.rev _as', f st e1, f (count', syms') e2)



    | Esseq (_as, e1, e2)       ->
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = Symbol.Symbol (c, Some sym) in
                          (* Boot.print_debug ("ADDING> " ^ sym) *) (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        
        Core.Esseq (List.rev _as', f st e1, f (count', syms') e2)

(*
let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
                                     match sym_opt with
                                       | Some sym -> let _a = (c, Some sym) in (c+1, Some _a :: _as, Pmap.add sym _a syms)
                                       | None     -> (c+1, None :: _as, syms)) (count, [], Pmap.empty compare) _as in
                                   
                                   Core.Esseq (List.rev _as', f st e1, f (count', syms') e2)
*)
    | Easeq (_a_opt, act, pact) ->
(
        match _a_opt with
          | Some _a -> let _a' = Symbol.Symbol (count, Some _a) in
                       (* print_endline ("ADDING> " ^ _a); *)
                       Core.Easeq (Some _a', snd (g st (Core.Pos, act)), g (count+1, Pmap.add _a _a' syms) pact)
          | None    -> Core.Easeq (None, snd (g st (Core.Pos, act)), g st pact)
            
)            
            

    | Eindet e                  -> Core.Eindet (f st e)
    | Ebound (i, e)             -> failwith "TODO: bound"
    | Esave (k, e)              -> failwith "TODO: save"
    | Erun k                    -> failwith "TODO: run"
    | Eret e -> Core.Eret (f st e)
  and g st (p, act) =(p,
    match act with
      | Create e_ty            -> (Pset.empty compare, Core.Create0 (f st e_ty, []))
      | Alloc e_n              -> (Pset.empty compare, Core.Alloc (f st e_n, []))
      | Kill e_o               -> (Pset.empty compare, Core.Kill0 (f st e_o))
      | Store (e_ty, e_o, e_n, mo) -> (Pset.empty compare, Core.Store0 (f st e_ty, f st e_o, f st e_n, mo))
      | Load (e_ty, e_o, mo)       -> (Pset.empty compare, Core.Load0 (f st e_ty, f st e_o, mo))
      | CompareExchangeStrong (e_ty, e_o, e_e, e_d, mo1, mo2)-> (Pset.empty compare,
                                                                 Core.CompareExchangeStrong (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
      | CompareExchangeWeak (e_ty, e_o, e_e, e_d, mo1, mo2) -> (Pset.empty compare,
                                                                Core.CompareExchangeWeak (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
    )
  in f (0, arg_syms) e


(* TODO: clean up this mess *)
let mk_file decls =
  (* if this is not an implementation file. *)
  if List.for_all (function Fun_decl _ -> true | _ -> false) decls then
    let (main, _, fsyms, fun_map) =
      List.fold_left (fun (main, count, fsyms, fun_map) decl ->
        match decl with
          | Fun_decl (fname, fdef) ->
            (* TODO: better error *)
            if Pmap.mem fname fsyms then
              failwith ("duplicate definition of `" ^ fname ^ "'")
            else
              let a_fun = Symbol.Symbol (count, Some fname) in
              ((if fname = "main" then Some a_fun else main),
               count+1,
               Pmap.add fname a_fun fsyms,
               Pmap.add a_fun fdef fun_map)
          | _ -> assert false
      ) (None, 0, Pmap.empty compare, Pmap.empty compare) decls
    in
    let fun_map' =
      Pmap.map (fun (coreTy_ret, args, fbody) ->
        let (_, arg_syms, args') = List.fold_left (fun (i, m, args') (x, ty) ->
          let _a = Symbol.Symbol (i, Some x) in (i+1, Pmap.add x _a m, (_a, ty) :: args'))
          (0, Pmap.empty compare, []) args in
        (coreTy_ret, args', convert fbody arg_syms fsyms)) fun_map in
    match main with
      | Some a_main -> Core_parser_util.Rfile (a_main, fun_map')
      | None        -> Core_parser_util.Rstd fun_map'
  else
    let impl_map =
      List.fold_left (fun impl_map decl ->
        match decl with
          | Def_decl (i, bty, e) ->
              if Pmap.mem i impl_map then
                failwith ("(TODO_MSG) duplication declaration of " ^ Implementation_.string_of_implementation_constant i)
              else
                Pmap.add i (Core.Def (bty, convert e (Pmap.empty compare) (Pmap.empty compare))) impl_map
          | IFun_decl (i, (bty, args, fbody)) ->
              let (_, arg_syms, args') = List.fold_left (fun (count, m, args') (x, ty) ->
                let _a = Symbol.Symbol (count, Some x) in (count+1, Pmap.add x _a m, (_a, ty) :: args'))
                (0, Pmap.empty compare, []) args in
              Pmap.add i (Core.IFun (bty, args', convert fbody arg_syms (Pmap.empty compare))) impl_map
          | Fun_decl _ ->
              failwith "(TODO_MSG) found a function declaration in an implementation file."
      ) (Pmap.empty compare) decls in
    
    (* TODO: add a check for completeness *)
    Core_parser_util.Rimpl impl_map



(* HACK for now (maybe we should just get back to concrete names for ctypes) *)
let ctypes_names = ref (0, Pmap.empty Pervasives.compare)

(*val subst: string -> Symbol.t *)
let subst name =
  let (z, ns) = !ctypes_names in
  if Pmap.mem name ns then
    Pmap.find name ns
  else
    let n = (z, Some name) in
    ctypes_names := (z+1, Pmap.add name n ns);
    n

%}

%token CREATE ALLOC KILL STORE LOAD COMPARE_EXCHANGE_STRONG COMPARE_EXCHANGE_WEAK
%token <Big_int.big_int> INT_CONST
%token <string> SYM
%token <Core.name> NAME
%token <Implementation_.implementation_constant> IMPL
%token SKIP RET
%token NOT
%token TRUE FALSE
%token LET IN
%token DEF FUN PROC END
%token SAVE RUN
%token PLUS MINUS STAR SLASH PERCENT
%token EQ LT LE
%token SLASH_BACKSLASH BACKSLASH_SLASH
%token TILDE
%token EXCLAM
%token PIPE PIPE_PIPE SEMICOLON PIPE_GT GT_GT
%token UNDERSCORE
%token LANGLE RANGLE
%token LT_MINUS MINUS_GT
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET DOT COMMA COLON COLON_EQ LBRACES RBRACES PIPES
%token SAME
%token UNDEF ERROR
%token IF THEN ELSE
%token CASE OF
%token INTEGER BOOLEAN ADDRESS CTYPE UNIT

(* TODO: temporary *)
%token IS_SCALAR IS_INTEGER IS_SIGNED IS_UNSIGNED

(* Memory orders *)
%token NA SEQ_CST RELAXED RELEASE ACQUIRE CONSUME ACQ_REL

(* ctype tokens *)
%token ATOMIC SHORT INT LONG LONG_LONG
%token BOOL SIGNED UNSIGNED FLOAT DOUBLE LONG_DOUBLE COMPLEX ICHAR CHAR VOID STRUCT UNION ENUM
%token SIZE_T INTPTR_T WCHAR_T CHAR16_T CHAR32_T


%token EOF

%left SLASH_BACKSLASH BACKSLASH_SLASH
%left ELSE
%left NOT
%left PLUS MINUS
%left STAR SLASH PERCENT
%left EQ LT LE

%start <Core_parser_util.result>start
%parameter <M : sig val std : (string, Core.sym) Pmap.map end>

%%

n_ary_operator(separator, X):
  x1 = X separator x2 = X
    { [ x1; x2 ] }
| x = X; separator; xs = n_ary_operator(separator, X)
    { x :: xs }

delimited_nonempty_list(opening, separator, X, closing):
  x = X
   { [x] }
| xs = delimited(opening, n_ary_operator(separator, X),
  closing)
   { xs }

start:
| decls = nonempty_list(declaration) EOF
    { mk_file decls }

core_base_type:
| INTEGER
    { Core.Integer0 }
| BOOLEAN
    { Core.Boolean }
| ADDRESS
    { Core.Address0 }
| CTYPE
    { Core.Ctype }
| UNIT
    { Core.Unit }

core_derived_type:
| baseTy = core_base_type
    { baseTy }
| baseTys = n_ary_operator(STAR, core_base_type)
    { Core.Tuple baseTys }

core_type:
| baseTy = core_derived_type
    { Core.TyBase baseTy }
| baseTy = delimited(LBRACKET, core_derived_type, RBRACKET)
    { Core.TyEffect baseTy }

(* BEGIN Ail types *)
integer_base_type:
| ICHAR
    { AilTypes.Ichar }
| SHORT
    { AilTypes.Short }
| INT
    { AilTypes.Int_ }
| LONG
    { AilTypes.Long }
| LONG_LONG
    { AilTypes.LongLong }
(*| EXTENDED_INTEGER of string *)

integer_type:
| CHAR
    { AilTypes.Char }
| BOOL
    { AilTypes.Bool }
| SIGNED ibt= integer_base_type
    { AilTypes.Signed ibt }
| UNSIGNED ibt= integer_base_type
    { AilTypes.Unsigned ibt }

(*
real_floating_type:
| FLOAT
    { Ail.FLOAT }
| DOUBLE
    { Ail.DOUBLE }
| LONG_DOUBLE
    { Ail.LONG_DOUBLE }
*)

basic_type:
| it= integer_type
    { AilTypes.Integer it }
(*
| rft= real_floating_type
    { Ail.REAL_FLOATING rft }
| rft= real_floating_type COMPLEX
    { Ail.COMPLEX rft }
*)

(*
member_def:
| ty_= ctype_ name= SYM 
    { (subst name, Core.MEMBER (project_ctype_ ty_)) }
| ty_= ctype_ name= SYM COLON n= INT_CONST
    { (subst name, Core.BITFIELD (project_ctype_ ty_, n, None)) }
*)

ctype_:
| VOID
    { Void_ }
| ATOMIC LPAREN ty_= ctype_ RPAREN
    { Atomic_ ty_ }
| bty= basic_type
    { Basic_ bty }
| ty_= ctype_ LBRACKET n= INT_CONST RBRACKET
    { Array_ (ty_, n) }
(*
| STRUCT tag= SYM mems= delimited(LBRACKET, separated_list(SEMICOLON, member_def), RBRACKET)
    { STRUCT_ (subst tag, mems) }
| UNION tag= SYM mems= delimited(LBRACKET, separated_list(SEMICOLON, member_def), RBRACKET)
    { UNION_ (subst tag, mems) }
| ENUM name= SYM
    { ENUM_ (subst name) }
*)
| ty_= ctype_ tys_= delimited(LPAREN, separated_list(COMMA, ctype_), RPAREN)
    { Function_ (project_ctype_ ty_, List.map project_ctype_ tys_) }
| ty_= ctype_ STAR
    { Pointer_ ty_ }
(*
| SIZE_T
    { SIZE_T_ }
| INTPTR_T
    { INTPTR_T_ }
| WCHAR_T
    { WCHAR_T_ }
| CHAR16_T
    { CHAR16_T_ }
| CHAR32_T
    { CHAR32_T_ }
| UNDERSCORE
    { WILDCARD }
*)


(* END Ail types *)

%inline binary_operator:
| PLUS            { Core.OpAdd }
| MINUS           { Core.OpSub }
| STAR            { Core.OpMul }
| SLASH           { Core.OpDiv }
| PERCENT         { Core.OpMod }
| EQ              { Core.OpEq  }
| LT              { Core.OpLt  }
| SLASH_BACKSLASH { Core.OpAnd }
| BACKSLASH_SLASH { Core.OpOr  }

memory_order:
| SEQ_CST { Cmm.Seq_cst }
| RELAXED { Cmm.Relaxed }
| RELEASE { Cmm.Release }
| ACQUIRE { Cmm.Acquire }
| CONSUME { Cmm.Consume }
| ACQ_REL { Cmm.Acq_rel }

action:
| CREATE ty = delimited(LPAREN, expr, RPAREN)
    { Create ty }
| ALLOC n = expr
    { Alloc n }
| KILL e = expr
    { Kill e }
| STORE LPAREN ty = expr COMMA x = expr COMMA n = expr RPAREN
    { Store (ty, x, n, Cmm.NA) }
| LOAD LPAREN ty = expr COMMA x = expr RPAREN
    { Load (ty, x, Cmm.NA) }
| STORE LPAREN ty = expr COMMA x = expr COMMA n = expr COMMA mo = memory_order RPAREN
    { Store (ty, x, n, mo) }
| LOAD LPAREN ty = expr COMMA x = expr COMMA mo = memory_order RPAREN
    { Load (ty, x, mo) }
| COMPARE_EXCHANGE_STRONG LPAREN ty = expr COMMA x = expr COMMA e = expr COMMA d = expr COMMA mo1 = memory_order COMMA mo2 = memory_order RPAREN
    { CompareExchangeStrong (ty, x, e, d, mo1, mo2) }
| COMPARE_EXCHANGE_WEAK LPAREN ty = expr COMMA x = expr COMMA e = expr COMMA d = expr COMMA mo1 = memory_order COMMA mo2 = memory_order RPAREN
    { CompareExchangeWeak (ty, x, e, d, mo1, mo2) }

paction:
| act = action
    { (Core.Pos, act) }
| TILDE act = action
    { (Core.Neg, act) }

pattern_elem:
| UNDERSCORE    { None   }
| LPAREN RPAREN { None   } (* TODO: add a new constructor in the Ast for better type/syntax checking *)
| a = SYM       { Some a }

pattern:
| _as = delimited_nonempty_list(LPAREN, COMMA, pattern_elem, RPAREN) { _as }

unseq_expr:
| es = delimited(LBRACKET, n_ary_operator(PIPE_PIPE, seq_expr), RBRACKET)
    { Eunseq es }


basic_expr:
| e = expr
    { e }
| p = paction
    { Eaction p }

extended_expr:
| e = basic_expr
    { e }
| es = delimited(LBRACES, n_ary_operator(PIPES, seq_expr), RBRACES)
    { Epar es }
| e = unseq_expr
    { e }

seq_expr:
| e = basic_expr
    { e }
| _as = pattern LT_MINUS e1 = extended_expr SEMICOLON e2 = impure_expr
    { Esseq (_as, e1, e2) }
| e1 = extended_expr SEMICOLON e2 = impure_expr
    { Esseq ([], e1, e2) }
| _as = pattern LT_MINUS e1 = extended_expr GT_GT e2 = impure_expr
    { Ewseq (_as, e1, e2) }
| e1 = extended_expr GT_GT e2 = impure_expr
    { Ewseq ([], e1, e2) }
| _as = pattern LT_MINUS a = action PIPE_GT p = paction
    { match _as with
      | [alpha] -> Easeq (alpha, a, p)
      | _       -> assert false }
    (* TODO Really, we just want to parse a "SYM" an not a "pattern". *)
| SAVE d = SYM DOT e = impure_expr
    { Esave (d, e) }
| RUN d = SYM
    { Erun d }


impure_expr:
| e = seq_expr
    { e }
| e = unseq_expr
    { e }


guards:
|
    { [] }
| PIPE ty_ = ctype_ MINUS_GT e= impure_expr gs= guards
    { (ty_, e) :: gs }

name:
| a = SYM
    { Sym a }
| i = IMPL
    { Impl i }

expr:
| e = delimited(LPAREN, expr, RPAREN)
    { e }

| SKIP
    { Eskip }

| n = INT_CONST
    { Econst (Cmm_aux.Cint n) }

| i = IMPL
    { Eimpl i }

| a = SYM
    { Esym a }

(* some sugar *)
| e1 = expr LE e2 = expr
    { Eop (Core.OpOr, Eop (Core.OpLt, e1, e2), Eop (Core.OpEq, e1, e2)) }

| e1 = expr op = binary_operator e2 = expr
    { Eop (op, e1, e2) }

| TRUE
    { Etrue }

| FALSE
    { Efalse }

(* TODO: temporary *)
| IS_SCALAR LPAREN e = expr RPAREN
    { Eis_scalar e }
| IS_INTEGER LPAREN e= expr RPAREN
    { Eis_integer e }
| IS_SIGNED LPAREN e= expr RPAREN
    { Eis_signed e }
| IS_UNSIGNED LPAREN e= expr RPAREN
    { Eis_unsigned e }

| NOT e = expr
    { Enot e }

| ty_ = ctype_
    { Ectype (project_ctype_ ty_) }

| LET a = SYM EQ e1 = expr IN e2 = impure_expr END (* TODO: END is tasteless. *)
    { Elet (a, e1, e2) }

| IF b = expr THEN e1 = impure_expr ELSE e2 = impure_expr (* TODO: may need to also allow unseq_expr *)
    { Eif (b, e1, e2) }

| CASE e = expr OF es = guards END
    { Ecase (e, es) }

(* HACK: shouldn't be in the parser, but insted impure Ecall should be converted to Eproc by the typechecker *)
| f = SYM es = delimited(LBRACE, separated_list(COMMA, expr), RBRACE)
    { Eproc (f, es) }

| f = name es = delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Ecall (f, es) }
(*
| SAME LPAREN e1 = expr e2 = expr RPAREN
    { Esame (e1, e2) }
*)
| UNDEF
    { Eundef }
| ERROR
    { Eerror }

| e = delimited(LBRACKET, seq_expr, RBRACKET) (* TODO: may need to also allow unseq_expr *)
    { Eindet e } (* TODO: the index *)


| RET e = expr
    { Eret e }


fun_argument:
| x = SYM COLON bty = core_base_type
    { (x, bty) }


def_declaration:
| DEF dname = IMPL COLON bty = core_base_type COLON_EQ e = impure_expr
  { Def_decl (dname, bty, e) }

ifun_declaration:
| FUN fname = IMPL args = delimited(LPAREN, separated_list(COMMA, fun_argument), RPAREN) COLON coreBTy_ret = core_base_type COLON_EQ fbody = impure_expr
  { IFun_decl (fname, (coreBTy_ret, List.rev args, fbody)) }

fun_declaration:
| FUN fname = SYM args = delimited(LPAREN, separated_list(COMMA, fun_argument), RPAREN) COLON coreTy_ret = core_type COLON_EQ fbody = impure_expr
  { Fun_decl (fname, (coreTy_ret, List.rev args, fbody)) }



declaration:
| d= def_declaration
    { d }
| d= ifun_declaration
    { d }
| d= fun_declaration
    { d }

%%
