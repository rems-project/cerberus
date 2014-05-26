%{
open Lem_pervasives
open Global


type name =
  | Sym of string
  | Impl of Implementation_.implementation_constant

type expr =
  | Eunit
  | Enull
  | Etrue
  | Efalse
  | Econst of Cmm_aux_old.constant
  | Ectype of Core_ctype.ctype0
(*  | Eaddr of Core.mem_addr *)
  | Esym of string
  | Eimpl of Implementation_.implementation_constant
  | Etuple of expr list
  | Enot of expr
  | Eop of Core.binop * expr * expr
  | Ecall of name * expr list
  | Eundef of Undefined.undefined_behaviour
  | Eerror
  | Eskip
  | Elet of string * expr * expr
  | Eif of expr * expr * expr
  | Eproc of name * expr list
(* HIP
  | Ecase of expr *
             (expr * (* void *)
              expr * (* char *)
              expr * (* _Bool *)
              (AilTypes.integerBaseType * expr) list * (* Signed *)
              (AilTypes.integerBaseType * expr) list * (* Unsigned *)
              (string * string * expr) * (* Array *)
              (string * expr) * (* Pointer *)
              (string * expr)) (* Atomic *)
*)
  | Esame of expr * expr
  | Eaction of paction
  | Eunseq of expr list
  | Ewseq of (string option) list * expr * expr
  | Esseq of (string option) list * expr * expr
  | Easeq of string option * action * paction
  | Eindet of expr (* TODO: add unique indices *)
  | Ebound of int * expr
  | Esave of string * (string * Core_ctype.ctype0) list * expr
  | Erun of string * (string * expr) list
  | Eret of expr
  | End of expr list
  | Epar of expr list
  | Eshift of expr * expr
  
  | Eis_scalar of expr
  | Eis_integer of expr
  | Eis_signed of expr
  | Eis_unsigned of expr


and action =
  | Create of expr
  | Alloc of expr
  | Kill of expr
  | Store of expr * expr * expr * Memory_order.memory_order
  | Load of expr * expr * Memory_order.memory_order
  | CompareExchangeStrong of expr * expr * expr * expr * Memory_order.memory_order * Memory_order.memory_order
  | CompareExchangeWeak of expr * expr * expr * expr * Memory_order.memory_order * Memory_order.memory_order
and paction = Core.polarity * action

type declaration =
  | Def_decl  of Implementation_.implementation_constant * Core.core_base_type * expr
  | IFun_decl of Implementation_.implementation_constant * (Core.core_base_type * (string * Core.core_base_type) list * expr)
  | Fun_decl  of string * (Core.core_type * (string * Core.core_base_type) list * expr)



let register_cont_symbols e =
  let rec f st = function
    | Eunit
    | Enull
    | Etrue
    | Efalse
    | Econst _
    | Ectype _
    | Esym _
    | Eimpl _
    | Etuple _
    | Enot _
    | Eop _
    | Ecall _
    | Eundef _
    | Eerror
    | Eskip
    | Eproc _
    | Esame _
    | Eaction _
    | Eunseq _
    | Easeq _
    | Eret _
    | Erun _
    | Eshift _
    | Eis_scalar _
    | Eis_integer _
    | Eis_signed _
    | Eis_unsigned _ ->
        st
    
    | Elet (_, _, e2) ->
        f st e2
    | Eif (_, e1, e2)
    | Ewseq (_, e1, e2)
    | Esseq (_, e1, e2) ->
        f (f st e1) e2
    | Eindet e ->
        f st e
    | Ebound (_, e) ->
       f st e
    | Esave (k, _, e) ->
        let sym_n = !M.sym_counter in
        M.sym_counter := sym_n + 1;
        f (Pmap.add k (Symbol.Symbol (sym_n, Some k)) st) e
    | End es
    | Epar es ->
        List.fold_left f st es
  
  in f (Pmap.empty compare) e


(*  convert_expr: expr -> .. -> .. -> Core.expr 'a *)
let convert_expr e arg_syms fsyms =
  let lookup_symbol str syms =
    Boot_ocaml.dprint ("[Core_parser.convert_expr] LOOKING FOR: " ^ str);
    begin try
        Pmap.find str syms (* TODO: Error handling *)
      with
        | e -> print_endline ("[Core_parser.convert_expr] Failed to find: " ^ str);
               raise e
    end in
  
  let rec f st = function
    | Eunit ->
        Core.Eunit
    | Enull ->
        Core.Enull Core_ctype.Void0 (* TODO *)
    | Etrue ->
        Core.Etrue
    | Efalse ->
        Core.Efalse
    | Econst c ->
        Core.Econst c
    | Ectype ty ->
        Core.Ectype ty
    | Esym a ->
        Core.Esym (lookup_symbol a st)
    | Eimpl ic ->
        Core.Eimpl ic
    | Etuple es ->
        Core.Etuple (List.map (f st) es)
    | Enot e ->
        Core.Enot (f st e)
    | Eop (binop, e1, e2) ->
        Core.Eop (binop, f st e1, f st e2)
    | Ecall (Impl func, args) ->
        Core.Ecall (Core.Impl func, List.map (f st) args)
    | Ecall (Sym func, args) ->
        let fsym = try
            Pmap.find func fsyms
          with Not_found -> try
              Pmap.find func M.std
            with Not_found ->
              prerr_endline (Colour.ansi_format [Colour.Red] ("PARSING ERROR: the function `" ^ func ^ "' was not declared."));
              exit 1 in
        Core.Ecall (Core.Sym fsym, List.map (f st) args)
    | Eundef ub ->
        Core.Eundef ub
    | Eerror ->
        Core.Eerror
    | Eskip ->
        Core.Eskip
    | Elet (a, e1, e2) ->
        let sym_n = !M.sym_counter in
        let _a = Symbol.Symbol (sym_n, Some a) in
        M.sym_counter := sym_n + 1;
        Core.Elet (_a, f st e1, f (Pmap.add a _a st) e2)
    | Eif (e1, e2, e3) ->
        Core.Eif (f st e1, f st e2, f st e3)
    | Eproc (Impl func, args) ->
        Core.Eproc (Pset.empty compare, Core.Impl func, List.map (f st) args)
    | Eproc (Sym func, args) ->
        Core.Eproc (Pset.empty compare, Core.Sym (Pmap.find func fsyms), List.map (f st) args)
    | Esame (e1, e2) ->
        Core.Esame (f st e1, f st e2)
    | Eaction pact ->
        let (p, (s, act)) = g st pact in
        Core.Eaction (Core.Paction (p, Core.Action (s, act)))
    | Eunseq es ->
        Core.Eunseq (List.map (f st) es)
    | Ewseq (_as, e1, e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) sym_opt ->
          match sym_opt with
            | Some sym ->
                let sym_n = !M.sym_counter in
                let _a = Symbol.Symbol (sym_n, Some sym) in
                M.sym_counter := sym_n + 1;
                (Some _a :: _as, Pmap.add sym _a st)
            | None ->
                (None :: _as, st)
        ) ([], st) _as in
        Core.Ewseq (List.rev _as', f st e1, f st' e2)
(*
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = Symbol.Symbol (c, Some sym) in
                          (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        Core.Ewseq (List.rev _as', f st e1, f (count', syms') e2)
*)
    | Esseq (_as, e1, e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) sym_opt ->
          match sym_opt with
            | Some sym ->
                let sym_n = !M.sym_counter in
                let _a = Symbol.Symbol (sym_n, Some sym) in
                M.sym_counter := sym_n + 1;
                (Some _a :: _as, Pmap.add sym _a st)
            | None ->
                (None :: _as, st)
        ) ([], st) _as in
        Core.Esseq (List.rev _as', f st e1, f st' e2)

(*
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = Symbol.Symbol (c, Some sym) in
                          (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        Core.Esseq (List.rev _as', f st e1, f (count', syms') e2)
 *)
    | Easeq (_a_opt, act, pact) ->
        begin match _a_opt with
                | Some _a ->
                    let sym_n = !M.sym_counter in
                    let _a' = Symbol.Symbol (sym_n, Some _a) in
                    M.sym_counter := sym_n + 1;
                    let (_, (s1, act1)) = g st (Core.Pos, act) in
                    let (p2, (s2, act2)) = g (Pmap.add _a _a' st) pact in
                    Core.Easeq (Some _a', Core.Action (s1, act1), Core.Paction (p2, Core.Action (s2, act2)))
                | None ->
                    let (_, (s1, act1)) = g st (Core.Pos, act) in
                    let (p2, (s2, pact2)) = g st pact in
                    Core.Easeq (None, Core.Action (s1, act1), Core.Paction (p2, Core.Action (s2, pact2)))
        end
    | Eindet e ->
        Core.Eindet (f st e)
    | Ebound (j, e) ->
        failwith "[Core_parser.convert_expr] #Ebound: TODO"
    | Esave (k, a_tys, e) ->
        let a_tys' = List.map (fun (a, ty) -> (lookup_symbol a st, ty)) a_tys in
        Core.Esave (lookup_symbol k st, a_tys', f st e)
(* HIP
        let (st', a_tys') = List.fold_left (fun ((count, syms) as st, acc) (a, ty) ->
          let _a = Symbol.Symbol (count, Some a) in
          ((count+1, Pmap.add a _a syms), (_a, ty) :: acc)
        ) (st, []) a_tys in
        Core.Esave (lookup_symbol k syms, List.rev a_tys', f st' e)
 *)
    | Erun (k, a_es) ->
        let a_es' = List.map (fun (a, e) -> (lookup_symbol a st, f st e)) a_es in
        Core.Erun (Pset.empty compare, lookup_symbol k st, a_es')
    | Eret e ->
        Core.Eret (f st e)
    | End es ->
        Core.End (List.map (f st) es)
    | Epar es ->
        Core.Epar (List.map (f st) es)
    | Eshift (e1, e2) ->
        Core.Eshift (f st e1, f st e2)
    | Eis_scalar e ->
        Core.Eis_scalar (f st e)
    | Eis_integer e ->
        Core.Eis_integer (f st e)
    | Eis_signed e ->
        Core.Eis_signed (f st e)
    | Eis_unsigned e ->
        Core.Eis_unsigned (f st e)
  
  and g st (p, act) =(p,
    match act with
      | Create e_ty ->
          (Pset.empty compare, Core.Create (f st e_ty, []))
      | Alloc e_n ->
          (Pset.empty compare, Core.Alloc (f st e_n, []))
      | Kill e_o ->
          (Pset.empty compare, Core.Kill (f st e_o))
      | Store (e_ty, e_o, e_n, mo) ->
          (Pset.empty compare, Core.Store (f st e_ty, f st e_o, f st e_n, mo))
      | Load (e_ty, e_o, mo) ->
          (Pset.empty compare, Core.Load (f st e_ty, f st e_o, mo))
      | CompareExchangeStrong (e_ty, e_o, e_e, e_d, mo1, mo2) ->
          (Pset.empty compare, Core.CompareExchangeStrong (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
      | CompareExchangeWeak (e_ty, e_o, e_e, e_d, mo1, mo2) ->
          (Pset.empty compare, Core.CompareExchangeWeak (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
    )
  in
  let conts = register_cont_symbols e in
  f (Pmap.union arg_syms conts) e


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
        (coreTy_ret, args', convert_expr fbody arg_syms fsyms)) fun_map in
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
                Pmap.add i (Core.Def (bty, convert_expr e (Pmap.empty compare) (Pmap.empty compare))) impl_map
          | IFun_decl (i, (bty, args, fbody)) ->
              let (_, arg_syms, args') = List.fold_left (fun (count, m, args') (x, ty) ->
                let _a = Symbol.Symbol (count, Some x) in (count+1, Pmap.add x _a m, (_a, ty) :: args'))
                (0, Pmap.empty compare, []) args in
              Pmap.add i (Core.IFun (bty, args', convert_expr fbody arg_syms (Pmap.empty compare))) impl_map
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

%token <Big_int.big_int> INT_CONST
%token <string> SYM
%token <Implementation_.implementation_constant> IMPL
%token <Undefined.undefined_behaviour> UB

(* ctype tokens *)
%token VOID ATOMIC SIZE_T INTPTR_T WCHAR_T CHAR16_T CHAR32_T (* DOTS *)
%token ICHAR SHORT INT LONG LONG_LONG
%token CHAR BOOL SIGNED UNSIGNED
%token INT8_T INT16_T INT32_T INT64_T UINT8_T UINT16_T UINT32_T UINT64_T

(* C11 memory orders *)
%token SEQ_CST RELAXED RELEASE ACQUIRE CONSUME ACQ_REL

(* definition keywords *)
%token DEF FUN

(* Core types *)
%token INTEGER BOOLEAN ADDRESS CTYPE UNIT

(* Core constant keywords *)
%token NULL TRUE FALSE
%token UNDEF ERROR
%token SKIP IF THEN ELSE

(* Core sequencing operators *)
%token LET STRONG WEAK ATOM IN END PIPE_PIPE INDET RETURN


%token DQUOTE LPAREN RPAREN LBRACKET RBRACKET COLON_EQ COLON COMMA LBRACE RBRACE TILDE

(* %token CASE_TY SIGNED_PATTERN UNSIGNED_PATTERN ARRAY_PATTERN POINTER_PATTERN ATOMIC_PATTERN EQ_GT *)

%token IS_INTEGER IS_SIGNED IS_UNSIGNED IS_SCALAR

(* unary operators *)
%token NOT

(* binary operators *)
%token STAR SLASH PERCENT MINUS EQ PLUS

(* boolean operators *)
%token LE LT

(* logical operators *)
%token SLASH_BACKSLASH BACKSLASH_SLASH

(* memory actions *)
%token CREATE ALLOC STORE LOAD KILL COMPARE_EXCHANGE_STRONG COMPARE_EXCHANGE_WEAK

(* continuation operators *)
%token SAVE RUN DOT

(* binder patterns *)
%token UNDERSCORE



(* TODO: not used yet, but the tracing mode of the parser crash othewise ..... *)
(*
%token FLOAT DOUBLE LONG_DOUBLE STRUCT UNION ENUM FUNCTION
RETURN   PROC CASE OF  TILDE PIPES PIPE MINUS_GT LBRACE RBRACE LBRACES RBRACES LANGLE RANGLE DOT SEMICOLON
 *)


%right BACKSLASH_SLASH
%right SLASH_BACKSLASH
%left EQ LT LE
%left PLUS MINUS
%left STAR SLASH PERCENT

(* %right ELSE (* TODO: CHECK !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *) *)


(* HIP
%token CREATE ALLOC KILL STORE LOAD COMPARE_EXCHANGE_STRONG COMPARE_EXCHANGE_WEAK
%token <string> SYM
%token <Core.name> NAME
%token <Implementation_.implementation_constant> IMPL
%token SKIP RETURN
%token NOT
%token TRUE FALSE
%token LET STRONG WEAK ATOM IN
%token DEF FUN PROC END
%token SAVE RUN
%token PLUS MINUS STAR SLASH PERCENT
%token EQ LT LE
%token SLASH_BACKSLASH BACKSLASH_SLASH
%token TILDE
%token EXCLAM
%token PIPE PIPE_PIPE SEMICOLON
%token UNDERSCORE
%token LANGLE RANGLE
%token LT_MINUS MINUS_GT
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET DOT DOTS COMMA COLON COLON_EQ LBRACES RBRACES PIPES
%token SAME
%token UNDEF ERROR
%token IF THEN ELSE
%token CASE OF
%token INTEGER BOOLEAN ADDRESS CTYPE UNIT

(* TODO: temporary *)
%token IS_SCALAR IS_INTEGER IS_SIGNED IS_UNSIGNED

(* Memory orders *)
%token SEQ_CST RELAXED RELEASE ACQUIRE CONSUME ACQ_REL

(* ctype tokens *)
%token ATOMIC SHORT INT LONG LONG_LONG
%token BOOL SIGNED UNSIGNED FLOAT DOUBLE LONG_DOUBLE COMPLEX ICHAR CHAR VOID STRUCT UNION ENUM
%token SIZE_T INTPTR_T WCHAR_T CHAR16_T CHAR32_T

 *)


%token EOF

(* HIP
%left SLASH_BACKSLASH BACKSLASH_SLASH
%left ELSE
%left NOT
%left PLUS MINUS
%left STAR SLASH PERCENT
%left EQ LT LE
 *)

%start <Core_parser_util.result>start
%parameter <M : sig
                  val sym_counter: Symbol.counter ref
                  val std: (string, Core.sym) Pmap.map
                end>

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
| decls= nonempty_list(declaration) EOF
    { mk_file decls }
;











(* HIP





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
| LET STRONG _as= pattern EQ e1= extended_expr IN e2= impure_expr
    { Esseq (_as, e1, e2) }
| LET STRONG LPAREN RPAREN EQ e1= extended_expr IN e2= impure_expr
    { Esseq ([], e1, e2) }
| LET WEAK _as= pattern EQ e1= extended_expr IN e2= impure_expr
    { Ewseq (_as, e1, e2) }
| LET WEAK LPAREN RPAREN EQ e1= extended_expr IN e2= impure_expr
    { Ewseq ([], e1, e2) }
| LET ATOM _as= pattern EQ a= action IN p= paction
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



expr:

| CASE e = expr OF es = guards END
    { Ecase (e, es) }


| e = delimited(LBRACKET, seq_expr, RBRACKET) (* TODO: may need to also allow unseq_expr *)
    { Eindet e } (* TODO: the index *)





*)


(* == CLEAN AFTER THAT =================================================================================================== *)

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
;

integer_type:
| CHAR
    { AilTypes.Char }
| BOOL
    { AilTypes.Bool }
| INT8_T
    { AilTypes.Signed AilTypes.Int8_t }
| INT16_T
    { AilTypes.Signed AilTypes.Int16_t }
| INT32_T
    { AilTypes.Signed AilTypes.Int32_t }
| INT64_T
    { AilTypes.Signed AilTypes.Int64_t }
| UINT8_T
    { AilTypes.Unsigned AilTypes.Int8_t }
| UINT16_T
    { AilTypes.Unsigned AilTypes.Int16_t }
| UINT32_T
    { AilTypes.Unsigned AilTypes.Int32_t }
| UINT64_T
    { AilTypes.Unsigned AilTypes.Int64_t }
| SIGNED ibt= integer_base_type
    { AilTypes.Signed ibt }
| UNSIGNED ibt= integer_base_type
    { AilTypes.Unsigned ibt }
;

basic_type:
| it= integer_type
    { AilTypes.Integer it }
;

ctype:
| VOID
    { Core_ctype.Void0 }
| bty= basic_type
    { Core_ctype.Basic0 bty }
| ty= ctype LBRACKET n= INT_CONST RBRACKET
    { Core_ctype.Array0 (ty, n) }
| ty= ctype tys= delimited(LPAREN, separated_list(COMMA, ctype), RPAREN)
    { Core_ctype.Function0 (ty, tys, false) }
(* TODO *)
(* | ty= ctype LPAREN tys= separated_list(COMMA, ctype) COMMA DOTS RPAREN *)
(*     { Core_ctype.Function0 (ty, tys, true) } *)
| ty= ctype STAR
    { Core_ctype.Pointer0 ty }
| ATOMIC ty= delimited(LPAREN, ctype, RPAREN)
    { Core_ctype.Atomic0 ty }
(*
| SIZE_T
    { Core_ctype.SIZE_T }
| INTPTR_T
    { Core_ctype.INTPTR_T }
| WCHAR_T
    { Core_ctype.WCHAR_T }
| CHAR16_T
    { Core_ctype.CHAR16_T }
| CHAR32_T
    { Core_ctype.CHAR32_T }
 *)
;
(* END Ail types *)


core_base_type:
| INTEGER
    { Core.Integer0 }
| BOOLEAN
    { Core.Boolean }
| ADDRESS
    { Core.Address }
| CTYPE
    { Core.Ctype }
| UNIT
    { Core.Unit }
;

core_derived_type:
| baseTy = core_base_type
    { baseTy }
| baseTys= delimited(LPAREN, separated_list(COMMA, core_base_type), RPAREN)
    { Core.Tuple baseTys }
;

core_type:
| baseTy = core_derived_type
    { Core.TyBase baseTy }
| baseTy = delimited(LBRACKET, core_derived_type, RBRACKET)
    { Core.TyEffect baseTy }
;


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
;


name:
| a= SYM
    { Sym a }
| i= IMPL
    { Impl i }
;


(*
case_pattern:
| DQUOTE VOID DQUOTE
    { (* TODO *) }
| DQUOTE CHAR DQUOTE
    { (* TODO *) }
| DQUOTE BOOL DQUOTE
    { (* TODO *) }
| SIGNED_PATTERN DQUOTE ibty= integer_base_type DQUOTE
    { (* TODO *) }
| UNSIGNED_PATTERN DQUOTE ibty= integer_base_type DQUOTE
    { (* TODO *) }
| ARRAY_PATTERN ty= SYM n= SYM
    { (* TODO *) }
| POINTER_PATTERN ty= SYM
    { (* TODO *) }
| ATOMIC_PATTERN ty= SYM
    { (* TODO *) }
| DQUOTE SIZE_T DQUOTE
    { (* TODO *) }
| DQUOTE INTPTR_T DQUOTE
    { (* TODO *) }
| DQUOTE WCHAR_T DQUOTE
    { (* TODO *) }
| DQUOTE CHAR16_T DQUOTE
    { (* TODO *) }
| DQUOTE CHAR32_T DQUOTE
    { (* TODO *) }
;


case_rules:
| pat= case_pattern EQ_GT e= expr
    { }

| pat= case_pattern EQ_GT e= expr PIPE rs= case_rules
    {  (pat, e) }
;
*)



memory_order:
| SEQ_CST { Memory_order.Seq_cst }
| RELAXED { Memory_order.Relaxed }
| RELEASE { Memory_order.Release }
| ACQUIRE { Memory_order.Acquire }
| CONSUME { Memory_order.Consume }
| ACQ_REL { Memory_order.Acq_rel }
;

action:
| CREATE e= delimited(LPAREN, expr, RPAREN)
    { Create e }
| ALLOC e= delimited(LPAREN, expr, RPAREN)
    { Alloc e }
| KILL e= delimited(LPAREN, expr, RPAREN)
    { Kill e }
| STORE LPAREN e1= expr COMMA e2= expr COMMA e3= expr RPAREN
    { Store (e1, e2, e3, Memory_order.NA) }
| LOAD LPAREN e1= expr COMMA e2= expr RPAREN
    { Load (e1, e2, Memory_order.NA) }
| STORE LPAREN e1= expr COMMA e2= expr COMMA e3= expr COMMA mo= memory_order RPAREN
    { Store (e1, e2, e3, mo) }
| LOAD LPAREN e1= expr COMMA e2= expr COMMA mo= memory_order RPAREN
    { Load (e1, e2, mo) }
| COMPARE_EXCHANGE_STRONG LPAREN e1= expr COMMA e2= expr COMMA e3= expr COMMA e4= expr COMMA mo1= memory_order COMMA mo2= memory_order RPAREN
    { CompareExchangeStrong (e1, e2, e3, e4, mo1, mo2) }
| COMPARE_EXCHANGE_WEAK LPAREN e1= expr COMMA e2= expr COMMA e3= expr COMMA e4= expr COMMA mo1= memory_order COMMA mo2= memory_order RPAREN
    { CompareExchangeWeak (e1, e2, e3, e4, mo1, mo2) }
;

paction:
| act= action
    { (Core.Pos, act) }
| TILDE act= action
    { (Core.Neg, act) }
;


pattern_elem:
| UNDERSCORE    { None   }
(* | LPAREN RPAREN { None   } (\* TODO: add a new constructor in the Ast for better type/syntax checking *\) *)
| a= SYM        { Some a }
;

pattern:
| _as= delimited_nonempty_list(LPAREN, COMMA, pattern_elem, RPAREN)
    { _as }
;


expr:
| e= delimited(LPAREN, expr, RPAREN)
    { e }
| LPAREN RPAREN
    { Eunit }
| NULL
    { Enull }
| TRUE
    { Etrue }
| FALSE
    { Efalse }
(* TODO: other constants *)
| n= INT_CONST
    { Econst (Cmm_aux_old.Cint n) }
| ty= delimited(DQUOTE, ctype, DQUOTE)
    { Ectype ty }
(* TODO
| Eaddr of Memory.mem_addr
*)
| a= SYM
    { Esym a }
| i= IMPL
    { Eimpl i }
| LPAREN e= expr COMMA es= separated_nonempty_list(COMMA, expr) RPAREN
    { Etuple (e::es) }
| NOT e = delimited(LPAREN, expr, RPAREN)
    { Enot e }
(* some sugar *)
| e1= expr LE e2= expr
    { Eop (Core.OpOr, Eop (Core.OpLt, e1, e2), Eop (Core.OpEq, e1, e2)) }
| e1= expr bop= binary_operator e2= expr
    { Eop (bop, e1, e2) }
| f= name es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Ecall (f, es) }
| UNDEF ub= UB
    { Eundef ub }
| ERROR
    { Eerror }
| SKIP
    { Eskip }
| LET a= SYM EQ e1= expr IN e2= expr END
    { Elet (a, e1, e2) }
| IF b= expr THEN e1= expr ELSE e2= expr END
    { Eif (b, e1, e2) }
(* HIP
| CASE_TY e= expr OF rs= case_rules END
    { Ecase (e, rs) }
*)
| f= name es= delimited(LBRACE, separated_list(COMMA, expr), RBRACE)
    { Eproc (f, es) }
(* HIP
  | Esame of expr 'a * expr 'a

 *)
| p= paction
    { Eaction p }
| es= delimited(LBRACKET, separated_nonempty_list(PIPE_PIPE, expr), RBRACKET)
    { Eunseq es }
| LET STRONG _as= pattern EQ e1= expr IN e2= expr END
    { Esseq (_as, e1, e2) }
| LET STRONG LPAREN RPAREN EQ e1= expr IN e2= expr END
    { Esseq ([], e1, e2) }
| LET WEAK _as= pattern EQ e1= expr IN e2= expr END
    { Ewseq (_as, e1, e2) }
| LET WEAK LPAREN RPAREN EQ e1= expr IN e2= expr END
    { Ewseq ([], e1, e2) }
| LET ATOM LPAREN RPAREN EQ a= action IN p= paction END
    { Easeq (None, a, p) }
| LET ATOM _a= SYM EQ a= action IN p= paction END
    { Easeq (Some _a, a, p) }
| INDET e= delimited(LPAREN, expr, RPAREN)
    { Eindet e }
(*
  | Ebound of natural * expr 'a (* this ctor doesn't exist at runtine *)
*)
| SAVE d= SYM a_tys= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, ctype)), RPAREN) DOT e= expr END
    { Esave (d, a_tys, e) }
| RUN d= SYM a_es= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, expr)), RPAREN)
    { Erun (d, a_es) }
| RETURN e= delimited(LPAREN, expr, RPAREN)
    { Eret e }
(*  HIP
  | End of list (expr 'a)
  | Epar of list (expr 'a)
  | Eshift of expr 'a * expr 'a (* Shift (obj: Address) (index: Integer) *)
*)
(* TODO: these are temporary *)
| IS_SCALAR LPAREN e= expr RPAREN
    { Eis_scalar e }
| IS_INTEGER LPAREN e= expr RPAREN
    { Eis_integer e }
| IS_SIGNED LPAREN e= expr RPAREN
    { Eis_signed e }
| IS_UNSIGNED LPAREN e= expr RPAREN
    { Eis_unsigned e }


def_declaration:
| DEF dname= IMPL COLON bTy= core_base_type COLON_EQ e= expr
    { Def_decl (dname, bTy, e) }
;

ifun_declaration:
| FUN fname= IMPL args= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON bTy= core_base_type
  COLON_EQ fbody= expr
    { IFun_decl (fname, (bTy, List.rev args, fbody)) }
;

fun_declaration:
| FUN fname= SYM args= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON coreTy= core_type
  COLON_EQ fbody= expr
    { Fun_decl (fname, (coreTy, List.rev args, fbody)) }
;


declaration:
| d= def_declaration
    { d }
| d= ifun_declaration
    { d }
| d= fun_declaration
    { d }

%%
