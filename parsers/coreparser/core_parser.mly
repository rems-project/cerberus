%{
open Lem_pervasives
open Either
open Global

module Cmm = Cmm_master

let symbol_compare =
  Symbol.instance_Basic_classes_Ord_Symbol_t_dict.compare_method


type name =
  | Sym of string
  | Impl of Implementation_.implementation_constant

type expr =
  | Eunit
  | Etrue
  | Efalse
  | Econst of Naive_memory.mem_value
  | Elist of expr list
  | Econs of expr * expr
  | Ectype of Core_ctype.ctype0
  | Esym of string
  | Eimpl of Implementation_.implementation_constant
  | Etuple of expr list
  | Enot of expr
  | Eop of Core.binop * expr * expr
  | Ecall of name * expr list
  | Eundef of Undefined.undefined_behaviour
  | Eerror of string
  | Eraise of string
  | Eregister of string * name
  | Eshift of expr * (Core_ctype.ctype0 * expr) list
(*
  | Etry of expr * (string * expr) list
*)
  | Eskip
  | Elet of string * expr * expr
  | Eif of expr * expr * expr
  | Eproc of name * expr list
  
  (* TODO: hack *)
  | Ecase of expr * name * name * name * name * name * name * name * name * name


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
(*  | Esame of expr * expr *)
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
(*  | Ewait of list Thread.thread_id *)

  
  | Eis_scalar of expr
  | Eis_integer of expr
  | Eis_signed of expr
  | Eis_unsigned of expr


and action =
  | Create of expr * expr
  | Alloc of expr * expr
  | Kill of expr
  | Store of expr * expr * expr * Cmm.memory_order
  | Load of expr * expr * Cmm.memory_order
  | CompareExchangeStrong of expr * expr * expr * expr * Cmm.memory_order * Cmm.memory_order
  | CompareExchangeWeak of expr * expr * expr * expr * Cmm.memory_order * Cmm.memory_order
and paction = Core.polarity * action

type declaration =
  | Def_decl  of Implementation_.implementation_constant * Core.core_base_type * expr
  | IFun_decl of Implementation_.implementation_constant * (Core.core_base_type * (string * Core.core_base_type) list * expr)
  | Glob_decl of string * Core.core_type * expr
  | Fun_decl  of string * (Core.core_type * (string * Core.core_base_type) list * expr)



let fresh_symbol str =
  let n = !M.sym_counter in
  M.sym_counter := n+1;
  Symbol.Symbol (n, Some str)









let register_cont_symbols e =
  let rec f st = function
    | Eunit
(*    | Enull *)
    | Etrue
    | Efalse
    | Econst _
    | Elist _
    | Econs _
    | Ectype _
    | Esym _
    | Eimpl _
    | Etuple _
    | Enot _
    | Eop _
    | Ecall _
    | Eundef _
    | Eerror _
    | Eskip
    | Eraise _
    | Eregister _
    | Eshift _
(*
    | Etry _
*)

    | Ecase _

    | Eproc _
(*    | Esame _ *)
    | Eaction _
    | Eunseq _
    | Easeq _
    | Eret _
    | Erun _
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
        let sym_n = fresh_symbol k in
        f (Pmap.add k sym_n st) e
    | End es
    | Epar es ->
        List.fold_left f st es
  
  in f (Pmap.empty compare) e


let symbolify (_Sigma, fsyms) expr =
  let lookup_symbol str syms =
    Debug.print_debug 7 ("[Core_parser.convert_expr] LOOKING FOR: " ^ str);
    begin try
        Pmap.find str syms (* TODO: Error handling *)
      with
        | e -> print_endline ("[Core_parser.convert_expr] Failed to find: " ^ str);
               raise e
    end in
  
  let rec f st = function
    | Eunit ->
        Core.Eunit
(*
    | Enull ->
        Core.Enull Core_ctype.Void0 (* TODO *)
*)
    | Etrue ->
        Core.Etrue
    | Efalse ->
        Core.Efalse
    | Econst c ->
        Core.Econst c
    | Elist es ->
        Core.Elist (List.map (f st) es)
    | Econs (pe1, pe2) ->
        Core.Econs (f st pe1, f st pe2)
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
    | Ecall (Impl func, params) ->
        Core.Ecall (Core.Impl func, List.map (f st) params)
    | Ecall (Sym func, params) ->
        let fsym = try
            Pmap.find func fsyms
          with Not_found -> try
              Pmap.find func M.std
            with Not_found ->
              prerr_endline (Colour.ansi_format [Colour.Red] ("PARSING ERROR: the function `" ^ func ^ "' was not declared."));
              exit 1 in
        Core.Ecall (Core.Sym fsym, List.map (f st) params)
    | Eundef ub ->
        Core.Eundef ub
    | Eerror str ->
        Core.Eerror str
    | Eraise evnt ->
        Core.Eraise evnt
    | Eregister (evnt, nm) ->
        let nm' = match nm with
          | Impl f ->
              Core.Impl f
          | Sym str ->
              Core.Sym (Pmap.find str fsyms) in
        Core.Eregister (evnt, nm')
(*
    | Etry (e, str_es) ->
        Core.Etry (f st e, List.map (fun (str, e) -> (str, f st e)) str_es)
*)
    | Eshift (pe, sh) ->
        Core.Eshift (f st pe, List.map (fun (ty, e) -> (ty, f st e)) sh)

    | Eskip ->
        Core.Eskip
    | Elet (a, e1, e2) ->
        let sym_n = fresh_symbol a in
        Core.Elet (sym_n, f st e1, f (Pmap.add a sym_n st) e2)
    | Eif (e1, e2, e3) ->
        Core.Eif (f st e1, f st e2, f st e3)
    | Eproc (Impl func, params) ->
        Core.Eproc ((), Core.Impl func, List.map (f st) params)
    | Eproc (Sym func, params) ->
        Core.Eproc ((), Core.Sym (Pmap.find func fsyms), List.map (f st) params)

    | Ecase (e, nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8, nm9) ->
        let g = (function
          | Impl f -> Core.Impl f
          | Sym f  ->
              begin try
                Core.Sym (Pmap.find f fsyms)
              with
                | e -> print_endline ("[Core_parser.symbolify, Ecase] Failed to find: " ^ f);
                    raise e
              end) in
        Core.Ecase (f st e, g nm1, g nm2, g nm3, g nm4, g nm5, g nm6, g nm7, g nm8, g nm9)


(*
    | Esame (e1, e2) ->
        Core.Esame (f st e1, f st e2)
*)
    | Eaction pact ->
        let (p, (s, act)) = g st pact in
        Core.Eaction (Core.Paction (p, Core.Action (s, act)))
    | Eunseq es ->
        Core.Eunseq (List.map (f st) es)
    | Ewseq (_as, e1, e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) str_opt ->
          match str_opt with
            | Some str ->
                let sym_n = fresh_symbol str in
                (Some sym_n :: _as, Pmap.add str sym_n st)
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
        let (_as', st') = List.fold_left (fun (_as, st) str_opt ->
          match str_opt with
            | Some str ->
                let sym_n = fresh_symbol str in
                (Some sym_n :: _as, Pmap.add str sym_n st)
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
                    M.sym_counter := sym_n+1;
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
        failwith "[Core_parser.symbolify] #Ebound: TODO"
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
        Core.Erun ((), lookup_symbol k st, a_es')
    | Eret e ->
        Core.Eret (f st e)
    | End es ->
        Core.End (List.map (f st) es)
    | Epar es ->
        Core.Epar (List.map (f st) es)
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
      | Create (e_al, e_ty) ->
          ((), Core.Create (f st e_al, f st e_ty, []))
      | Alloc (e_al, e_n) ->
          ((), Core.Alloc0 (f st e_al, f st e_n, []))
      | Kill e_o ->
          ((), Core.Kill (f st e_o))
      | Store (e_ty, e_o, e_n, mo) ->
          ((), Core.Store0 (f st e_ty, f st e_o, f st e_n, mo))
      | Load (e_ty, e_o, mo) ->
          ((), Core.Load0 (f st e_ty, f st e_o, mo))
      | CompareExchangeStrong (e_ty, e_o, e_e, e_d, mo1, mo2) ->
          ((), Core.CompareExchangeStrong (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
      | CompareExchangeWeak (e_ty, e_o, e_e, e_d, mo1, mo2) ->
          ((), Core.CompareExchangeWeak (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
    )
  in
  let conts = register_cont_symbols expr in
  f (Pmap.union _Sigma conts) expr






(* symbolify_impl_map: (Implementation_.implementation_constant, Core.core_basic_type * () list) Pmap.map -> unit Core.impl *)
let symbolify_impl_map global_syms xs : unit Core.impl =
  Pmap.map (function
    | Left (bTy, e) ->
        Core.Def (bTy, symbolify (Pmap.empty compare, global_syms) e)
    
    | Right (bTy, params_, body) ->
    let (_Sigma, params) =
      List.fold_left (fun (_Sigma_acc, params_acc) (param_str, param_ty) ->
        let param_sym = fresh_symbol param_str in
        ( Pmap.add param_str param_sym _Sigma_acc, (param_sym, param_ty) :: params_acc )
      ) (Pmap.empty compare, []) params_ in
    
    Core.IFun (bTy, params, symbolify (_Sigma, global_syms) body)
  ) xs


(* symbolify_fun_map: *)
let symbolify_fun_map global_syms xs : unit Core.fun_map =
  Pmap.map (fun (coreTy, params_, body) ->
    let (_Sigma, params) =
      List.fold_left (fun (_Sigma_acc, params_acc) (param_str, param_ty) ->
        let param_sym = fresh_symbol param_str in
        (Pmap.add param_str param_sym _Sigma_acc, (param_sym, param_ty) :: params_acc)
      ) (Pmap.empty compare, []) params_ in
    
    (coreTy, params, symbolify (_Sigma, global_syms) body)
  ) xs








(* TODO: clean up this mess *)
let mk_file decls =
  if List.for_all (function Fun_decl _ -> true | _ -> false) decls then
    (* CASE: this is not an implementation file. *)
    let (main_opt, _Sigma, fun_map_) =
      List.fold_left (fun (main_opt_acc, _Sigma_acc, fun_map_acc) decl ->
        match decl with
          | Fun_decl (fun_str, fun_def) ->
            (* TODO: better error *)
            if Pmap.mem fun_str _Sigma_acc then
              failwith ("duplicate definition of `" ^ fun_str ^ "'")
            else
              let fun_sym = fresh_symbol fun_str in
              ((if fun_str = "main" then Some fun_sym else main_opt_acc),
               Pmap.add fun_str fun_sym _Sigma_acc,
               Pmap.add fun_sym fun_def fun_map_acc)
          | _ -> assert false
      ) (None, Pmap.empty compare, Pmap.empty symbol_compare) decls
    in
    
    let fun_map = symbolify_fun_map _Sigma fun_map_ in
    match main_opt with
      | Some sym_main ->
          Core_parser_util.Rfile (sym_main, fun_map)
      | None ->
          Core_parser_util.Rstd fun_map
  
  else
    (* CASE: this is an implementation file *)
    let (impl_map_, (_Sigma, fun_map_)) =
      List.fold_left (fun (impl_map_acc, ((fsyms, fun_map) as funs_acc)) decl ->
        match decl with
          | Def_decl (i, bty, e) ->
              if Pmap.mem i impl_map_acc then
                failwith ("(TODO_MSG) duplication declaration of " ^ Implementation_.string_of_implementation_constant i)
              else
                (Pmap.add i (Left (bty, e)) impl_map_acc, funs_acc)
          
          | IFun_decl (implConst, decl) ->
              if Pmap.mem implConst impl_map_acc then
                failwith ("multiple declaration of " ^ Implementation_.string_of_implementation_constant implConst)
              else
              (Pmap.add implConst (Right decl) impl_map_acc, funs_acc)
          
          | Glob_decl _ ->
              failwith "(TODO_MSG) found a global declaration in an implementation file."
          
          | Fun_decl (fname, fdef) ->
            (* TODO: better error *)
            if Pmap.mem fname fsyms then
              failwith ("duplicate definition of `" ^ fname ^ "'")
            else
              let fun_sym = fresh_symbol fname in
              (impl_map_acc, (Pmap.add fname fun_sym fsyms, Pmap.add fun_sym fdef fun_map))
      ) (Pmap.empty compare, (Pmap.empty compare, Pmap.empty symbol_compare)) decls in
    
    
    (* We perform the symbolification as a second step to allow mutual recursion *)
    let impl_map = symbolify_impl_map _Sigma impl_map_ in
    let fun_map = symbolify_fun_map _Sigma fun_map_ in
    
    (* TODO: add a check for completeness of the impl map *)
    Core_parser_util.Rimpl (impl_map, fun_map)



(* HACK for now (maybe we should just get back to concrete names for ctypes) *)
let ctypes_names = ref (0, Pmap.empty symbol_compare)

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
%token VOID ATOMIC (* SIZE_T INTPTR_T PTRDIFF_T WCHAR_T CHAR16_T CHAR32_T *) (* DOTS *)
%token ICHAR SHORT INT LONG LONG_LONG
%token CHAR BOOL SIGNED UNSIGNED
%token INT8_T INT16_T INT32_T INT64_T UINT8_T UINT16_T UINT32_T UINT64_T

(* C11 memory orders *)
%token SEQ_CST RELAXED RELEASE ACQUIRE CONSUME ACQ_REL

(* definition keywords *)
%token DEF GLOB FUN

(* Core types *)
%token INTEGER BOOLEAN POINTER CTYPE CFUNCTION UNIT EFF

(* Core constant keywords *)
%token LIST CONS ARRAY TRUE FALSE
%token SHIFT
%token UNDEF ERROR
%token<string> STRING
%token SKIP IF THEN ELSE

(* Core exception operators *)
%token RAISE REGISTER (* TRY WITH PIPE MINUS_GT *)

(* Core sequencing operators *)
%token LET STRONG WEAK ATOM IN END PIPE_PIPE INDET RETURN


%token DQUOTE LPAREN RPAREN LBRACKET RBRACKET COLON_EQ COLON (* SEMICOLON *) COMMA LBRACE RBRACE TILDE

%token CASE_TY (* SIGNED_PATTERN UNSIGNED_PATTERN ARRAY_PATTERN POINTER_PATTERN ATOMIC_PATTERN EQ_GT *)

%token IS_INTEGER IS_SIGNED IS_UNSIGNED IS_SCALAR

(* unary operators *)
%token NOT

(* binary operators *)
%token STAR SLASH PERCENT MINUS EQ PLUS CARET

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


%token ND PAR 


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
%nonassoc CARET

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
                  val sym_counter: int ref
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
    { AilTypes.Signed (AilTypes.IBBuiltin "int8_t") }
| INT16_T
    { AilTypes.Signed (AilTypes.IBBuiltin "int16_t") }
| INT32_T
    { AilTypes.Signed (AilTypes.IBBuiltin "int32_t") }
| INT64_T
    { AilTypes.Signed (AilTypes.IBBuiltin "int64_t") }
| UINT8_T
    { AilTypes.Unsigned (AilTypes.IBBuiltin "int8_t") }
| UINT16_T
    { AilTypes.Unsigned (AilTypes.IBBuiltin "int16_t") }
| UINT32_T
    { AilTypes.Unsigned (AilTypes.IBBuiltin "int32_t") }
| UINT64_T
    { AilTypes.Unsigned (AilTypes.IBBuiltin "int64_t") }
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
| ty= ctype LBRACKET n_opt= INT_CONST? RBRACKET
    { Core_ctype.Array0 (ty, n_opt) }
| ty= ctype tys= delimited(LPAREN, separated_list(COMMA, ctype), RPAREN)
    { Core_ctype.Function0 (ty, List.map (fun ty -> (AilTypes.no_qualifiers, ty)) tys, false) }
(* TODO *)
(* | ty= ctype LPAREN tys= separated_list(COMMA, ctype) COMMA DOTS RPAREN *)
(*     { Core_ctype.Function0 (ty, tys, true) } *)
| ty= ctype STAR
    { Core_ctype.Pointer0 (AilTypes.no_qualifiers, ty) }
| ATOMIC ty= delimited(LPAREN, ctype, RPAREN)
    { Core_ctype.Atomic0 ty }
;
(* END Ail types *)


core_base_type:
| INTEGER
    { Core.BTy_integer }
| BOOLEAN
    { Core.BTy_boolean }
| POINTER
    { Core.BTy_pointer }
| CTYPE
    { Core.BTy_ctype }
| CFUNCTION
    { Core.BTy_cfunction }
| UNIT
    { Core.BTy_unit }
| baseTys= delimited(LPAREN, separated_list(COMMA, core_base_type), RPAREN)
    { Core.BTy_tuple baseTys }
| baseTy= delimited(LBRACKET, core_base_type, RBRACKET)
    { Core.BTy_list baseTy }
;

(*
core_derived_type:
| baseTy = core_base_type
    { baseTy }
| baseTys= delimited(LPAREN, separated_list(COMMA, core_base_type), RPAREN)
    { Core.BTy_tuple baseTys }
| LIST baseTy= core_base_type
    { Core.BTy_list baseTy }
;
*)

core_type:
| baseTy = core_base_type (* core_derived_type *)
    { Core.TyBase baseTy }
(*
| baseTy = delimited(LBRACKET, (* core_derived_type *) core_base_type, RBRACKET)
    { Core.TyEffect baseTy }
*)
| EFF baseTy= core_base_type
    { Core.TyEffect baseTy }
;


%inline binary_operator:
| PLUS            { Core.OpAdd }
| MINUS           { Core.OpSub }
| STAR            { Core.OpMul }
| SLASH           { Core.OpDiv }
| PERCENT         { Core.OpMod }
| CARET           { Core.OpExp }
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
| SEQ_CST { Cmm.Seq_cst }
| RELAXED { Cmm.Relaxed }
| RELEASE { Cmm.Release }
| ACQUIRE { Cmm.Acquire }
| CONSUME { Cmm.Consume }
| ACQ_REL { Cmm.Acq_rel }
;

action:
| CREATE LPAREN e1= expr COMMA e2= expr RPAREN
    { Create (e1, e2) }
| ALLOC LPAREN e1= expr COMMA e2= expr RPAREN
    { Alloc (e1, e2) }
| KILL e= delimited(LPAREN, expr, RPAREN)
    { Kill e }
| STORE LPAREN e1= expr COMMA e2= expr COMMA e3= expr RPAREN
    { Store (e1, e2, e3, Cmm.NA) }
| LOAD LPAREN e1= expr COMMA e2= expr RPAREN
    { Load (e1, e2, Cmm.NA) }
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


constant:
| n= INT_CONST
    { Naive_memory.MVinteger (Symbolic.SYMBconst n) }
| ARRAY LPAREN vs= separated_nonempty_list (COMMA, constant) RPAREN
    { Naive_memory.MVarray vs }


(*
try_clauses:
| PIPE str= SYM (* TODO: hack *) MINUS_GT e= expr
    { [(str, e)] }
| str= SYM (* TODO: hack *) MINUS_GT e= expr str_es= try_clauses
    { (str, e) :: str_es }
*)


shift_elem:
| LPAREN ty= delimited(DQUOTE, ctype, DQUOTE) COMMA pe= expr RPAREN
  { (ty, pe) }

expr:
| e= delimited(LPAREN, expr, RPAREN)
    { e }
| UNIT
    { Eunit }
(*
| NULL
    { Enull }
*)
| TRUE
    { Etrue }
| FALSE
    { Efalse }
(* TODO: other constants *)
| cst= constant
    { Econst cst }

| LIST LPAREN es= separated_list(COMMA, expr) RPAREN
    { Elist es }
| CONS LPAREN pe1= expr COMMA pe2= expr RPAREN
    { Econs (pe1, pe2) }

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
| ERROR str= STRING
    { Eerror str }
| RAISE LPAREN evnt= SYM (* TODO: hack *) RPAREN
    { Eraise evnt }


| SHIFT LPAREN pe= expr COMMA sh= delimited(LBRACE, separated_nonempty_list(COMMA, shift_elem), RBRACE) RPAREN
    { Eshift (pe, sh) }

(*
| TRY e= expr WITH str_es= try_clauses END
    { Etry (e, str_es) }
*)
| REGISTER LPAREN evnt= SYM COMMA nm= name RPAREN
    { Eregister (evnt, nm) }
| SKIP
    { Eskip }
| LET a= SYM EQ e1= expr IN e2= expr END
    { Elet (a, e1, e2) }
| IF b= expr THEN e1= expr ELSE e2= expr END
    { Eif (b, e1, e2) }
(* TODO: temporary restricted version *)
| CASE_TY LPAREN e= expr COMMA f_void= name COMMA f_basic= name COMMA f_array= name COMMA
                 f_fun= name COMMA f_ptr= name COMMA f_atom= name COMMA f_struct= name COMMA f_union= name COMMA f_builtin= name RPAREN
    { Ecase (e, f_void, f_basic, f_array, f_fun, f_ptr, f_atom, f_struct, f_union, f_builtin) }


| f= name es= delimited(LBRACE, separated_list(COMMA, expr), RBRACE)
    { Eproc (f, es) }
(* HIP
  | Esame of expr 'a * expr 'a

 *)
| p= paction
    { Eaction p }
| es= delimited(LBRACKET, separated_nonempty_list(PIPE_PIPE, expr), RBRACKET)
    { Eunseq es }
(*
| e1= expr SEMICOLON e2= expr
    { Esseq ([], e1, e2) }
*)
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

| ND es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { End es }
| PAR es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Epar es }


(*  HIP
  | Ewait
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
| FUN fname= IMPL params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON bTy= core_base_type
  COLON_EQ fbody= expr
    { IFun_decl (fname, (bTy, List.rev params, fbody)) }
;

glob_declaration:
| GLOB gname= SYM COLON cTy= core_type COLON_EQ e= expr
  {
   print_endline "GLOB";
   Glob_decl (gname, cTy, e) }
;

fun_declaration:
| FUN fname= SYM params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON coreTy= core_type
  COLON_EQ fbody= expr
    { Fun_decl (fname, (coreTy, List.rev params, fbody)) }
;


declaration:
| d= def_declaration
    { d }
| d= ifun_declaration
    { d }
| d= glob_declaration
    { d }
| d= fun_declaration
    { d }

%%
