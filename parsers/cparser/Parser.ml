open Alphabet
open BinNat
open BinPos
open Cabs0
open Datatypes
open Int0
open List0
open Validator_main
open Peano
open Specif
open Streams
open Tuples

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Gram = 
 struct 
  type terminal' =
  | ADD_ASSIGN_t
  | AND_t
  | ANDAND_t
  | AND_ASSIGN_t
  | AUTO_t
  | BANG_t
  | BAR_t
  | BARBAR_t
  | BOOL_t
  | BREAK_t
  | BUILTIN_VA_ARG_t
  | CASE_t
  | CHAR_t
  | COLON_t
  | COMMA_t
  | CONST_t
  | CONSTANT_t
  | CONTINUE_t
  | DEC_t
  | DEFAULT_t
  | DIV_ASSIGN_t
  | DO_t
  | DOT_t
  | DOUBLE_t
  | ELLIPSIS_t
  | ELSE_t
  | ENUM_t
  | EOF_t
  | EQ_t
  | EQEQ_t
  | EXTERN_t
  | FLOAT_t
  | FOR_t
  | GEQ_t
  | GOTO_t
  | GT_t
  | HAT_t
  | IF_t
  | INC_t
  | INLINE_t
  | INT_t
  | LBRACE_t
  | LBRACK_t
  | LEFT_t
  | LEFT_ASSIGN_t
  | LEQ_t
  | LONG_t
  | LPAREN_t
  | LT_t
  | MINUS_t
  | MOD_ASSIGN_t
  | MUL_ASSIGN_t
  | NEQ_t
  | OR_ASSIGN_t
  | OTHER_NAME_t
  | PERCENT_t
  | PLUS_t
  | PTR_t
  | QUESTION_t
  | RBRACE_t
  | RBRACK_t
  | REGISTER_t
  | RESTRICT_t
  | RETURN_t
  | RIGHT_t
  | RIGHT_ASSIGN_t
  | RPAREN_t
  | SEMICOLON_t
  | SHORT_t
  | SIGNED_t
  | SIZEOF_t
  | SLASH_t
  | STAR_t
  | STATIC_t
  | STRUCT_t
  | SUB_ASSIGN_t
  | SWITCH_t
  | TILDE_t
  | TYPEDEF_t
  | TYPEDEF_NAME_t
  | UNION_t
  | UNSIGNED_t
  | VAR_NAME_t
  | VOID_t
  | VOLATILE_t
  | WHILE_t
  | XOR_ASSIGN_t
  
  (** val terminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1 **)
  
  let terminal'_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 = function
  | ADD_ASSIGN_t -> f
  | AND_t -> f0
  | ANDAND_t -> f1
  | AND_ASSIGN_t -> f2
  | AUTO_t -> f3
  | BANG_t -> f4
  | BAR_t -> f5
  | BARBAR_t -> f6
  | BOOL_t -> f7
  | BREAK_t -> f8
  | BUILTIN_VA_ARG_t -> f9
  | CASE_t -> f10
  | CHAR_t -> f11
  | COLON_t -> f12
  | COMMA_t -> f13
  | CONST_t -> f14
  | CONSTANT_t -> f15
  | CONTINUE_t -> f16
  | DEC_t -> f17
  | DEFAULT_t -> f18
  | DIV_ASSIGN_t -> f19
  | DO_t -> f20
  | DOT_t -> f21
  | DOUBLE_t -> f22
  | ELLIPSIS_t -> f23
  | ELSE_t -> f24
  | ENUM_t -> f25
  | EOF_t -> f26
  | EQ_t -> f27
  | EQEQ_t -> f28
  | EXTERN_t -> f29
  | FLOAT_t -> f30
  | FOR_t -> f31
  | GEQ_t -> f32
  | GOTO_t -> f33
  | GT_t -> f34
  | HAT_t -> f35
  | IF_t -> f36
  | INC_t -> f37
  | INLINE_t -> f38
  | INT_t -> f39
  | LBRACE_t -> f40
  | LBRACK_t -> f41
  | LEFT_t -> f42
  | LEFT_ASSIGN_t -> f43
  | LEQ_t -> f44
  | LONG_t -> f45
  | LPAREN_t -> f46
  | LT_t -> f47
  | MINUS_t -> f48
  | MOD_ASSIGN_t -> f49
  | MUL_ASSIGN_t -> f50
  | NEQ_t -> f51
  | OR_ASSIGN_t -> f52
  | OTHER_NAME_t -> f53
  | PERCENT_t -> f54
  | PLUS_t -> f55
  | PTR_t -> f56
  | QUESTION_t -> f57
  | RBRACE_t -> f58
  | RBRACK_t -> f59
  | REGISTER_t -> f60
  | RESTRICT_t -> f61
  | RETURN_t -> f62
  | RIGHT_t -> f63
  | RIGHT_ASSIGN_t -> f64
  | RPAREN_t -> f65
  | SEMICOLON_t -> f66
  | SHORT_t -> f67
  | SIGNED_t -> f68
  | SIZEOF_t -> f69
  | SLASH_t -> f70
  | STAR_t -> f71
  | STATIC_t -> f72
  | STRUCT_t -> f73
  | SUB_ASSIGN_t -> f74
  | SWITCH_t -> f75
  | TILDE_t -> f76
  | TYPEDEF_t -> f77
  | TYPEDEF_NAME_t -> f78
  | UNION_t -> f79
  | UNSIGNED_t -> f80
  | VAR_NAME_t -> f81
  | VOID_t -> f82
  | VOLATILE_t -> f83
  | WHILE_t -> f84
  | XOR_ASSIGN_t -> f85
  
  (** val terminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1 **)
  
  let terminal'_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 = function
  | ADD_ASSIGN_t -> f
  | AND_t -> f0
  | ANDAND_t -> f1
  | AND_ASSIGN_t -> f2
  | AUTO_t -> f3
  | BANG_t -> f4
  | BAR_t -> f5
  | BARBAR_t -> f6
  | BOOL_t -> f7
  | BREAK_t -> f8
  | BUILTIN_VA_ARG_t -> f9
  | CASE_t -> f10
  | CHAR_t -> f11
  | COLON_t -> f12
  | COMMA_t -> f13
  | CONST_t -> f14
  | CONSTANT_t -> f15
  | CONTINUE_t -> f16
  | DEC_t -> f17
  | DEFAULT_t -> f18
  | DIV_ASSIGN_t -> f19
  | DO_t -> f20
  | DOT_t -> f21
  | DOUBLE_t -> f22
  | ELLIPSIS_t -> f23
  | ELSE_t -> f24
  | ENUM_t -> f25
  | EOF_t -> f26
  | EQ_t -> f27
  | EQEQ_t -> f28
  | EXTERN_t -> f29
  | FLOAT_t -> f30
  | FOR_t -> f31
  | GEQ_t -> f32
  | GOTO_t -> f33
  | GT_t -> f34
  | HAT_t -> f35
  | IF_t -> f36
  | INC_t -> f37
  | INLINE_t -> f38
  | INT_t -> f39
  | LBRACE_t -> f40
  | LBRACK_t -> f41
  | LEFT_t -> f42
  | LEFT_ASSIGN_t -> f43
  | LEQ_t -> f44
  | LONG_t -> f45
  | LPAREN_t -> f46
  | LT_t -> f47
  | MINUS_t -> f48
  | MOD_ASSIGN_t -> f49
  | MUL_ASSIGN_t -> f50
  | NEQ_t -> f51
  | OR_ASSIGN_t -> f52
  | OTHER_NAME_t -> f53
  | PERCENT_t -> f54
  | PLUS_t -> f55
  | PTR_t -> f56
  | QUESTION_t -> f57
  | RBRACE_t -> f58
  | RBRACK_t -> f59
  | REGISTER_t -> f60
  | RESTRICT_t -> f61
  | RETURN_t -> f62
  | RIGHT_t -> f63
  | RIGHT_ASSIGN_t -> f64
  | RPAREN_t -> f65
  | SEMICOLON_t -> f66
  | SHORT_t -> f67
  | SIGNED_t -> f68
  | SIZEOF_t -> f69
  | SLASH_t -> f70
  | STAR_t -> f71
  | STATIC_t -> f72
  | STRUCT_t -> f73
  | SUB_ASSIGN_t -> f74
  | SWITCH_t -> f75
  | TILDE_t -> f76
  | TYPEDEF_t -> f77
  | TYPEDEF_NAME_t -> f78
  | UNION_t -> f79
  | UNSIGNED_t -> f80
  | VAR_NAME_t -> f81
  | VOID_t -> f82
  | VOLATILE_t -> f83
  | WHILE_t -> f84
  | XOR_ASSIGN_t -> f85
  
  type terminal = terminal'
  
  (** val terminalNum : terminal coq_Numbered **)
  
  let terminalNum =
    { injN = (fun x ->
      match x with
      | ADD_ASSIGN_t -> N0
      | AND_t -> Npos Coq_xH
      | ANDAND_t -> Npos (Coq_xO Coq_xH)
      | AND_ASSIGN_t -> Npos (Coq_xI Coq_xH)
      | AUTO_t -> Npos (Coq_xO (Coq_xO Coq_xH))
      | BANG_t -> Npos (Coq_xI (Coq_xO Coq_xH))
      | BAR_t -> Npos (Coq_xO (Coq_xI Coq_xH))
      | BARBAR_t -> Npos (Coq_xI (Coq_xI Coq_xH))
      | BOOL_t -> Npos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | BREAK_t -> Npos (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | BUILTIN_VA_ARG_t -> Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | CASE_t -> Npos (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | CHAR_t -> Npos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | COLON_t -> Npos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | COMMA_t -> Npos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | CONST_t -> Npos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | CONSTANT_t -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | CONTINUE_t -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | DEC_t -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | DEFAULT_t -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | DIV_ASSIGN_t -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | DO_t -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | DOT_t -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | DOUBLE_t -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | ELLIPSIS_t -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | ELSE_t -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | ENUM_t -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | EOF_t -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | EQ_t -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | EQEQ_t -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | EXTERN_t -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | FLOAT_t -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | FOR_t -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | GEQ_t -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | GOTO_t -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | GT_t -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | HAT_t -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | IF_t -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | INC_t -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | INLINE_t -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | INT_t -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | LBRACE_t -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | LBRACK_t -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | LEFT_t -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | LEFT_ASSIGN_t ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | LEQ_t -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | LONG_t -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | LPAREN_t -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | LT_t -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | MINUS_t -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | MOD_ASSIGN_t ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | MUL_ASSIGN_t ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | NEQ_t -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | OR_ASSIGN_t ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | OTHER_NAME_t ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | PERCENT_t -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | PLUS_t -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | PTR_t -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | QUESTION_t ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | RBRACE_t -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | RBRACK_t -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | REGISTER_t ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | RESTRICT_t ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | RETURN_t -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | RIGHT_t ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | RIGHT_ASSIGN_t ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | RPAREN_t ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | SEMICOLON_t ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | SHORT_t ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | SIGNED_t ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | SIZEOF_t ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | SLASH_t ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | STAR_t ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | STATIC_t ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | STRUCT_t ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | SUB_ASSIGN_t ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | SWITCH_t ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | TILDE_t ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | TYPEDEF_t ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | TYPEDEF_NAME_t ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | UNION_t ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | UNSIGNED_t ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | VAR_NAME_t ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | VOID_t ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | VOLATILE_t ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | WHILE_t ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | XOR_ASSIGN_t ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))));
      surjN = (fun n ->
      match n with
      | N0 -> ADD_ASSIGN_t
      | Npos p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> RETURN_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> TYPEDEF_NAME_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LPAREN_t)
                     | Coq_xH -> FLOAT_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> PERCENT_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SLASH_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> INLINE_t)
                     | Coq_xH -> DOUBLE_t)
                  | Coq_xH -> CONST_t)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> RBRACE_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SUB_ASSIGN_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LEFT_t)
                     | Coq_xH -> EOF_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> VOID_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> MUL_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SEMICOLON_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> GT_t)
                     | Coq_xH -> DEFAULT_t)
                  | Coq_xH -> CASE_t)
               | Coq_xH -> BARBAR_t)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> REGISTER_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> TILDE_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LEQ_t)
                     | Coq_xH -> EQEQ_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> WHILE_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> OR_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SIGNED_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> IF_t)
                     | Coq_xH -> DO_t)
                  | Coq_xH -> COLON_t)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> PTR_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> STATIC_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LBRACE_t)
                     | Coq_xH -> ELSE_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> UNSIGNED_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> MINUS_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> RIGHT_ASSIGN_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> GEQ_t)
                     | Coq_xH -> CONTINUE_t)
                  | Coq_xH -> BREAK_t)
               | Coq_xH -> BANG_t)
            | Coq_xH -> AND_ASSIGN_t)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> RESTRICT_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> TYPEDEF_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LONG_t)
                     | Coq_xH -> EXTERN_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> XOR_ASSIGN_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> OTHER_NAME_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SIZEOF_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> INC_t)
                     | Coq_xH -> DOT_t)
                  | Coq_xH -> COMMA_t)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> QUESTION_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> STRUCT_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LBRACK_t)
                     | Coq_xH -> ENUM_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> VAR_NAME_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> MOD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> RPAREN_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> GOTO_t)
                     | Coq_xH -> DEC_t)
                  | Coq_xH -> BUILTIN_VA_ARG_t)
               | Coq_xH -> BAR_t)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> RBRACK_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SWITCH_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LEFT_ASSIGN_t)
                     | Coq_xH -> EQ_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> VOLATILE_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> NEQ_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> SHORT_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> HAT_t)
                     | Coq_xH -> DIV_ASSIGN_t)
                  | Coq_xH -> CHAR_t)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> PLUS_t
                        | _ -> ADD_ASSIGN_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> STAR_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> INT_t)
                     | Coq_xH -> ELLIPSIS_t)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> UNION_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> LT_t)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> ADD_ASSIGN_t
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> RIGHT_t
                           | _ -> ADD_ASSIGN_t)
                        | Coq_xH -> FOR_t)
                     | Coq_xH -> CONSTANT_t)
                  | Coq_xH -> BOOL_t)
               | Coq_xH -> AUTO_t)
            | Coq_xH -> ANDAND_t)
         | Coq_xH -> AND_t)); injN_bound = (Npos (Coq_xI (Coq_xI (Coq_xI
      (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))) }
  
  (** val coq_TerminalAlph : terminal coq_Alphabet **)
  
  let coq_TerminalAlph =
    coq_NumberedAlphabet terminalNum
  
  type nonterminal' =
  | AND_expression_nt
  | Coq_abstract_declarator_nt
  | Coq_additive_expression_nt
  | Coq_argument_expression_list_nt
  | Coq_assignment_expression_nt
  | Coq_assignment_operator_nt
  | Coq_block_item_nt
  | Coq_block_item_list_nt
  | Coq_c_initializer_nt
  | Coq_cast_expression_nt
  | Coq_compound_statement_nt
  | Coq_conditional_expression_nt
  | Coq_constant_expression_nt
  | Coq_declaration_nt
  | Coq_declaration_specifiers_nt
  | Coq_declarator_nt
  | Coq_designation_nt
  | Coq_designator_nt
  | Coq_designator_list_nt
  | Coq_direct_abstract_declarator_nt
  | Coq_direct_declarator_nt
  | Coq_enum_specifier_nt
  | Coq_enumeration_constant_nt
  | Coq_enumerator_nt
  | Coq_enumerator_list_nt
  | Coq_equality_expression_nt
  | Coq_exclusive_OR_expression_nt
  | Coq_expression_nt
  | Coq_expression_statement_nt
  | Coq_external_declaration_nt
  | Coq_function_definition_nt
  | Coq_function_specifier_nt
  | Coq_inclusive_OR_expression_nt
  | Coq_init_declarator_nt
  | Coq_init_declarator_list_nt
  | Coq_initializer_list_nt
  | Coq_iteration_statement_statement_dangerous__nt
  | Coq_iteration_statement_statement_safe__nt
  | Coq_jump_statement_nt
  | Coq_labeled_statement_statement_dangerous__nt
  | Coq_labeled_statement_statement_safe__nt
  | Coq_logical_AND_expression_nt
  | Coq_logical_OR_expression_nt
  | Coq_multiplicative_expression_nt
  | Coq_parameter_declaration_nt
  | Coq_parameter_list_nt
  | Coq_parameter_type_list_nt
  | Coq_pointer_nt
  | Coq_postfix_expression_nt
  | Coq_primary_expression_nt
  | Coq_relational_expression_nt
  | Coq_selection_statement_dangerous_nt
  | Coq_selection_statement_safe_nt
  | Coq_shift_expression_nt
  | Coq_specifier_qualifier_list_nt
  | Coq_statement_dangerous_nt
  | Coq_statement_safe_nt
  | Coq_storage_class_specifier_nt
  | Coq_struct_declaration_nt
  | Coq_struct_declaration_list_nt
  | Coq_struct_declarator_nt
  | Coq_struct_declarator_list_nt
  | Coq_struct_or_union_nt
  | Coq_struct_or_union_specifier_nt
  | Coq_translation_unit_nt
  | Coq_translation_unit_file_nt
  | Coq_type_name_nt
  | Coq_type_qualifier_nt
  | Coq_type_qualifier_list_nt
  | Coq_type_specifier_nt
  | Coq_unary_expression_nt
  | Coq_unary_operator_nt
  
  (** val nonterminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> nonterminal' -> 'a1 **)
  
  let nonterminal'_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 = function
  | AND_expression_nt -> f
  | Coq_abstract_declarator_nt -> f0
  | Coq_additive_expression_nt -> f1
  | Coq_argument_expression_list_nt -> f2
  | Coq_assignment_expression_nt -> f3
  | Coq_assignment_operator_nt -> f4
  | Coq_block_item_nt -> f5
  | Coq_block_item_list_nt -> f6
  | Coq_c_initializer_nt -> f7
  | Coq_cast_expression_nt -> f8
  | Coq_compound_statement_nt -> f9
  | Coq_conditional_expression_nt -> f10
  | Coq_constant_expression_nt -> f11
  | Coq_declaration_nt -> f12
  | Coq_declaration_specifiers_nt -> f13
  | Coq_declarator_nt -> f14
  | Coq_designation_nt -> f15
  | Coq_designator_nt -> f16
  | Coq_designator_list_nt -> f17
  | Coq_direct_abstract_declarator_nt -> f18
  | Coq_direct_declarator_nt -> f19
  | Coq_enum_specifier_nt -> f20
  | Coq_enumeration_constant_nt -> f21
  | Coq_enumerator_nt -> f22
  | Coq_enumerator_list_nt -> f23
  | Coq_equality_expression_nt -> f24
  | Coq_exclusive_OR_expression_nt -> f25
  | Coq_expression_nt -> f26
  | Coq_expression_statement_nt -> f27
  | Coq_external_declaration_nt -> f28
  | Coq_function_definition_nt -> f29
  | Coq_function_specifier_nt -> f30
  | Coq_inclusive_OR_expression_nt -> f31
  | Coq_init_declarator_nt -> f32
  | Coq_init_declarator_list_nt -> f33
  | Coq_initializer_list_nt -> f34
  | Coq_iteration_statement_statement_dangerous__nt -> f35
  | Coq_iteration_statement_statement_safe__nt -> f36
  | Coq_jump_statement_nt -> f37
  | Coq_labeled_statement_statement_dangerous__nt -> f38
  | Coq_labeled_statement_statement_safe__nt -> f39
  | Coq_logical_AND_expression_nt -> f40
  | Coq_logical_OR_expression_nt -> f41
  | Coq_multiplicative_expression_nt -> f42
  | Coq_parameter_declaration_nt -> f43
  | Coq_parameter_list_nt -> f44
  | Coq_parameter_type_list_nt -> f45
  | Coq_pointer_nt -> f46
  | Coq_postfix_expression_nt -> f47
  | Coq_primary_expression_nt -> f48
  | Coq_relational_expression_nt -> f49
  | Coq_selection_statement_dangerous_nt -> f50
  | Coq_selection_statement_safe_nt -> f51
  | Coq_shift_expression_nt -> f52
  | Coq_specifier_qualifier_list_nt -> f53
  | Coq_statement_dangerous_nt -> f54
  | Coq_statement_safe_nt -> f55
  | Coq_storage_class_specifier_nt -> f56
  | Coq_struct_declaration_nt -> f57
  | Coq_struct_declaration_list_nt -> f58
  | Coq_struct_declarator_nt -> f59
  | Coq_struct_declarator_list_nt -> f60
  | Coq_struct_or_union_nt -> f61
  | Coq_struct_or_union_specifier_nt -> f62
  | Coq_translation_unit_nt -> f63
  | Coq_translation_unit_file_nt -> f64
  | Coq_type_name_nt -> f65
  | Coq_type_qualifier_nt -> f66
  | Coq_type_qualifier_list_nt -> f67
  | Coq_type_specifier_nt -> f68
  | Coq_unary_expression_nt -> f69
  | Coq_unary_operator_nt -> f70
  
  (** val nonterminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> nonterminal' -> 'a1 **)
  
  let nonterminal'_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 = function
  | AND_expression_nt -> f
  | Coq_abstract_declarator_nt -> f0
  | Coq_additive_expression_nt -> f1
  | Coq_argument_expression_list_nt -> f2
  | Coq_assignment_expression_nt -> f3
  | Coq_assignment_operator_nt -> f4
  | Coq_block_item_nt -> f5
  | Coq_block_item_list_nt -> f6
  | Coq_c_initializer_nt -> f7
  | Coq_cast_expression_nt -> f8
  | Coq_compound_statement_nt -> f9
  | Coq_conditional_expression_nt -> f10
  | Coq_constant_expression_nt -> f11
  | Coq_declaration_nt -> f12
  | Coq_declaration_specifiers_nt -> f13
  | Coq_declarator_nt -> f14
  | Coq_designation_nt -> f15
  | Coq_designator_nt -> f16
  | Coq_designator_list_nt -> f17
  | Coq_direct_abstract_declarator_nt -> f18
  | Coq_direct_declarator_nt -> f19
  | Coq_enum_specifier_nt -> f20
  | Coq_enumeration_constant_nt -> f21
  | Coq_enumerator_nt -> f22
  | Coq_enumerator_list_nt -> f23
  | Coq_equality_expression_nt -> f24
  | Coq_exclusive_OR_expression_nt -> f25
  | Coq_expression_nt -> f26
  | Coq_expression_statement_nt -> f27
  | Coq_external_declaration_nt -> f28
  | Coq_function_definition_nt -> f29
  | Coq_function_specifier_nt -> f30
  | Coq_inclusive_OR_expression_nt -> f31
  | Coq_init_declarator_nt -> f32
  | Coq_init_declarator_list_nt -> f33
  | Coq_initializer_list_nt -> f34
  | Coq_iteration_statement_statement_dangerous__nt -> f35
  | Coq_iteration_statement_statement_safe__nt -> f36
  | Coq_jump_statement_nt -> f37
  | Coq_labeled_statement_statement_dangerous__nt -> f38
  | Coq_labeled_statement_statement_safe__nt -> f39
  | Coq_logical_AND_expression_nt -> f40
  | Coq_logical_OR_expression_nt -> f41
  | Coq_multiplicative_expression_nt -> f42
  | Coq_parameter_declaration_nt -> f43
  | Coq_parameter_list_nt -> f44
  | Coq_parameter_type_list_nt -> f45
  | Coq_pointer_nt -> f46
  | Coq_postfix_expression_nt -> f47
  | Coq_primary_expression_nt -> f48
  | Coq_relational_expression_nt -> f49
  | Coq_selection_statement_dangerous_nt -> f50
  | Coq_selection_statement_safe_nt -> f51
  | Coq_shift_expression_nt -> f52
  | Coq_specifier_qualifier_list_nt -> f53
  | Coq_statement_dangerous_nt -> f54
  | Coq_statement_safe_nt -> f55
  | Coq_storage_class_specifier_nt -> f56
  | Coq_struct_declaration_nt -> f57
  | Coq_struct_declaration_list_nt -> f58
  | Coq_struct_declarator_nt -> f59
  | Coq_struct_declarator_list_nt -> f60
  | Coq_struct_or_union_nt -> f61
  | Coq_struct_or_union_specifier_nt -> f62
  | Coq_translation_unit_nt -> f63
  | Coq_translation_unit_file_nt -> f64
  | Coq_type_name_nt -> f65
  | Coq_type_qualifier_nt -> f66
  | Coq_type_qualifier_list_nt -> f67
  | Coq_type_specifier_nt -> f68
  | Coq_unary_expression_nt -> f69
  | Coq_unary_operator_nt -> f70
  
  type nonterminal = nonterminal'
  
  (** val nonterminalNum : nonterminal coq_Numbered **)
  
  let nonterminalNum =
    { injN = (fun x ->
      match x with
      | AND_expression_nt -> N0
      | Coq_abstract_declarator_nt -> Npos Coq_xH
      | Coq_additive_expression_nt -> Npos (Coq_xO Coq_xH)
      | Coq_argument_expression_list_nt -> Npos (Coq_xI Coq_xH)
      | Coq_assignment_expression_nt -> Npos (Coq_xO (Coq_xO Coq_xH))
      | Coq_assignment_operator_nt -> Npos (Coq_xI (Coq_xO Coq_xH))
      | Coq_block_item_nt -> Npos (Coq_xO (Coq_xI Coq_xH))
      | Coq_block_item_list_nt -> Npos (Coq_xI (Coq_xI Coq_xH))
      | Coq_c_initializer_nt -> Npos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Coq_cast_expression_nt -> Npos (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Coq_compound_statement_nt -> Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Coq_conditional_expression_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Coq_constant_expression_nt -> Npos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Coq_declaration_nt -> Npos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Coq_declaration_specifiers_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Coq_declarator_nt -> Npos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Coq_designation_nt -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Coq_designator_nt -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Coq_designator_list_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Coq_direct_abstract_declarator_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Coq_direct_declarator_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Coq_enum_specifier_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Coq_enumeration_constant_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Coq_enumerator_nt -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Coq_enumerator_list_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Coq_equality_expression_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Coq_exclusive_OR_expression_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Coq_expression_nt -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Coq_expression_statement_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Coq_external_declaration_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Coq_function_definition_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Coq_function_specifier_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Coq_inclusive_OR_expression_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_init_declarator_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_init_declarator_list_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_initializer_list_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_iteration_statement_statement_dangerous__nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_iteration_statement_statement_safe__nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_jump_statement_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_labeled_statement_statement_dangerous__nt ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Coq_labeled_statement_statement_safe__nt ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_logical_AND_expression_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_logical_OR_expression_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_multiplicative_expression_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_parameter_declaration_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_parameter_list_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_parameter_type_list_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_pointer_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Coq_postfix_expression_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_primary_expression_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_relational_expression_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_selection_statement_dangerous_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_selection_statement_safe_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_shift_expression_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_specifier_qualifier_list_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_statement_dangerous_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Coq_statement_safe_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_storage_class_specifier_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_struct_declaration_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_struct_declaration_list_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_struct_declarator_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_struct_declarator_list_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_struct_or_union_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_struct_or_union_specifier_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Coq_translation_unit_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_translation_unit_file_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_type_name_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_type_qualifier_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_type_qualifier_list_nt ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_type_specifier_nt ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_unary_expression_nt ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Coq_unary_operator_nt ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))));
      surjN = (fun n ->
      match n with
      | N0 -> AND_expression_nt
      | Npos p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_or_union_specifier_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_pointer_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_function_specifier_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_statement_dangerous_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_unary_operator_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH ->
                          Coq_labeled_statement_statement_dangerous__nt)
                     | Coq_xH -> Coq_enumerator_nt)
                  | Coq_xH -> Coq_declarator_nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declaration_list_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_multiplicative_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_expression_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_selection_statement_dangerous_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_type_qualifier_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH -> Coq_initializer_list_nt)
                     | Coq_xH -> Coq_direct_abstract_declarator_nt)
                  | Coq_xH -> Coq_conditional_expression_nt)
               | Coq_xH -> Coq_block_item_list_nt)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declarator_list_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_parameter_list_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_external_declaration_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_shift_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_type_specifier_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH ->
                          Coq_iteration_statement_statement_safe__nt)
                     | Coq_xH -> Coq_enum_specifier_nt)
                  | Coq_xH -> Coq_declaration_nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_storage_class_specifier_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_logical_AND_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_equality_expression_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_primary_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_translation_unit_file_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH -> Coq_init_declarator_nt)
                     | Coq_xH -> Coq_designator_nt)
                  | Coq_xH -> Coq_cast_expression_nt)
               | Coq_xH -> Coq_assignment_operator_nt)
            | Coq_xH -> Coq_argument_expression_list_nt)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_or_union_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_parameter_type_list_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_function_definition_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_specifier_qualifier_list_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_unary_expression_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH -> Coq_jump_statement_nt)
                     | Coq_xH -> Coq_enumeration_constant_nt)
                  | Coq_xH -> Coq_declaration_specifiers_nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declaration_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_logical_OR_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_exclusive_OR_expression_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_relational_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_type_name_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH -> Coq_init_declarator_list_nt)
                     | Coq_xH -> Coq_designator_list_nt)
                  | Coq_xH -> Coq_compound_statement_nt)
               | Coq_xH -> Coq_block_item_nt)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_struct_declarator_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_parameter_declaration_nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_expression_statement_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_selection_statement_safe_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_type_qualifier_list_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH ->
                          Coq_iteration_statement_statement_dangerous__nt)
                     | Coq_xH -> Coq_direct_declarator_nt)
                  | Coq_xH -> Coq_constant_expression_nt)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_statement_safe_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_labeled_statement_statement_safe__nt
                        | _ -> AND_expression_nt)
                     | Coq_xH -> Coq_enumerator_list_nt)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xH -> Coq_postfix_expression_nt
                        | _ -> AND_expression_nt)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 -> AND_expression_nt
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xH -> Coq_translation_unit_nt
                           | _ -> AND_expression_nt)
                        | Coq_xH -> Coq_inclusive_OR_expression_nt)
                     | Coq_xH -> Coq_designation_nt)
                  | Coq_xH -> Coq_c_initializer_nt)
               | Coq_xH -> Coq_assignment_expression_nt)
            | Coq_xH -> Coq_additive_expression_nt)
         | Coq_xH -> Coq_abstract_declarator_nt)); injN_bound = (Npos (Coq_xO
      (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))) }
  
  (** val coq_NonTerminalAlph : nonterminal coq_Alphabet **)
  
  let coq_NonTerminalAlph =
    coq_NumberedAlphabet nonterminalNum
  
  type symbol =
  | T of terminal
  | NT of nonterminal
  
  (** val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)
  
  let symbol_rect f f0 = function
  | T x -> f x
  | NT x -> f0 x
  
  (** val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1 **)
  
  let symbol_rec f f0 = function
  | T x -> f x
  | NT x -> f0 x
  
  (** val coq_SymbolAlph : symbol coq_Alphabet **)
  
  let coq_SymbolAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | T x0 ->
        (match y with
         | T y0 -> compare coq_TerminalAlph.coq_AlphabetComparable x0 y0
         | NT n -> Gt)
      | NT x0 ->
        (match y with
         | T t0 -> Lt
         | NT y0 -> compare coq_NonTerminalAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (app
        (List0.map (fun x -> T x)
          (all_list coq_TerminalAlph.coq_AlphabetFinite))
        (List0.map (fun x -> NT x)
          (all_list coq_NonTerminalAlph.coq_AlphabetFinite))) }
  
  type symbol_semantic_type = __
  
  type production' =
  | Prod_263
  | Prod_262
  | Prod_261
  | Prod_260
  | Prod_259
  | Prod_258
  | Prod_257
  | Prod_256
  | Prod_255
  | Prod_254
  | Prod_253
  | Prod_252
  | Prod_251
  | Prod_250
  | Prod_249
  | Prod_248
  | Prod_247
  | Prod_246
  | Prod_245
  | Prod_244
  | Prod_243
  | Prod_242
  | Prod_241
  | Prod_240
  | Prod_239
  | Prod_238
  | Prod_237
  | Prod_236
  | Prod_235
  | Prod_234
  | Prod_233
  | Prod_232
  | Prod_231
  | Prod_230
  | Prod_229
  | Prod_228
  | Prod_227
  | Prod_226
  | Prod_225
  | Prod_224
  | Prod_223
  | Prod_222
  | Prod_221
  | Prod_220
  | Prod_219
  | Prod_218
  | Prod_217
  | Prod_216
  | Prod_215
  | Prod_214
  | Prod_213
  | Prod_212
  | Prod_211
  | Prod_210
  | Prod_209
  | Prod_208
  | Prod_207
  | Prod_206
  | Prod_205
  | Prod_204
  | Prod_203
  | Prod_202
  | Prod_201
  | Prod_200
  | Prod_199
  | Prod_198
  | Prod_197
  | Prod_196
  | Prod_195
  | Prod_194
  | Prod_193
  | Prod_192
  | Prod_191
  | Prod_190
  | Prod_189
  | Prod_188
  | Prod_187
  | Prod_186
  | Prod_185
  | Prod_184
  | Prod_183
  | Prod_182
  | Prod_181
  | Prod_180
  | Prod_179
  | Prod_178
  | Prod_177
  | Prod_176
  | Prod_175
  | Prod_174
  | Prod_173
  | Prod_172
  | Prod_171
  | Prod_170
  | Prod_169
  | Prod_168
  | Prod_167
  | Prod_166
  | Prod_165
  | Prod_164
  | Prod_163
  | Prod_162
  | Prod_161
  | Prod_160
  | Prod_159
  | Prod_158
  | Prod_157
  | Prod_156
  | Prod_155
  | Prod_154
  | Prod_153
  | Prod_152
  | Prod_151
  | Prod_150
  | Prod_149
  | Prod_148
  | Prod_147
  | Prod_146
  | Prod_145
  | Prod_144
  | Prod_143
  | Prod_142
  | Prod_141
  | Prod_140
  | Prod_139
  | Prod_138
  | Prod_137
  | Prod_136
  | Prod_135
  | Prod_134
  | Prod_133
  | Prod_132
  | Prod_131
  | Prod_130
  | Prod_129
  | Prod_128
  | Prod_127
  | Prod_126
  | Prod_125
  | Prod_124
  | Prod_123
  | Prod_122
  | Prod_121
  | Prod_120
  | Prod_119
  | Prod_118
  | Prod_117
  | Prod_116
  | Prod_115
  | Prod_114
  | Prod_113
  | Prod_112
  | Prod_111
  | Prod_110
  | Prod_109
  | Prod_108
  | Prod_107
  | Prod_106
  | Prod_105
  | Prod_104
  | Prod_103
  | Prod_102
  | Prod_101
  | Prod_100
  | Prod_99
  | Prod_98
  | Prod_97
  | Prod_96
  | Prod_95
  | Prod_94
  | Prod_93
  | Prod_92
  | Prod_91
  | Prod_90
  | Prod_89
  | Prod_88
  | Prod_87
  | Prod_86
  | Prod_85
  | Prod_84
  | Prod_83
  | Prod_82
  | Prod_81
  | Prod_80
  | Prod_79
  | Prod_78
  | Prod_77
  | Prod_76
  | Prod_75
  | Prod_74
  | Prod_73
  | Prod_72
  | Prod_71
  | Prod_70
  | Prod_69
  | Prod_68
  | Prod_67
  | Prod_66
  | Prod_65
  | Prod_64
  | Prod_63
  | Prod_62
  | Prod_61
  | Prod_60
  | Prod_59
  | Prod_58
  | Prod_57
  | Prod_56
  | Prod_55
  | Prod_54
  | Prod_53
  | Prod_52
  | Prod_51
  | Prod_50
  | Prod_49
  | Prod_48
  | Prod_47
  | Prod_46
  | Prod_45
  | Prod_44
  | Prod_43
  | Prod_42
  | Prod_41
  | Prod_40
  | Prod_39
  | Prod_38
  | Prod_37
  | Prod_36
  | Prod_35
  | Prod_34
  | Prod_33
  | Prod_32
  | Prod_31
  | Prod_30
  | Prod_29
  | Prod_28
  | Prod_27
  | Prod_26
  | Prod_25
  | Prod_24
  | Prod_23
  | Prod_22
  | Prod_21
  | Prod_20
  | Prod_19
  | Prod_18
  | Prod_17
  | Prod_16
  | Prod_15
  | Prod_14
  | Prod_13
  | Prod_12
  | Prod_11
  | Prod_10
  | Prod_9
  | Prod_8
  | Prod_7
  | Prod_6
  | Prod_5
  | Prod_4
  | Prod_3
  | Prod_2
  | Prod_1
  
  (** val production'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> production' -> 'a1 **)
  
  let production'_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 f158 f159 f160 f161 f162 f163 f164 f165 f166 f167 f168 f169 f170 f171 f172 f173 f174 f175 f176 f177 f178 f179 f180 f181 f182 f183 f184 f185 f186 f187 f188 f189 f190 f191 f192 f193 f194 f195 f196 f197 f198 f199 f200 f201 f202 f203 f204 f205 f206 f207 f208 f209 f210 f211 f212 f213 f214 f215 f216 f217 f218 f219 f220 f221 f222 f223 f224 f225 f226 f227 f228 f229 f230 f231 f232 f233 f234 f235 f236 f237 f238 f239 f240 f241 f242 f243 f244 f245 f246 f247 f248 f249 f250 f251 f252 f253 f254 f255 f256 f257 f258 f259 f260 f261 = function
  | Prod_263 -> f
  | Prod_262 -> f0
  | Prod_261 -> f1
  | Prod_260 -> f2
  | Prod_259 -> f3
  | Prod_258 -> f4
  | Prod_257 -> f5
  | Prod_256 -> f6
  | Prod_255 -> f7
  | Prod_254 -> f8
  | Prod_253 -> f9
  | Prod_252 -> f10
  | Prod_251 -> f11
  | Prod_250 -> f12
  | Prod_249 -> f13
  | Prod_248 -> f14
  | Prod_247 -> f15
  | Prod_246 -> f16
  | Prod_245 -> f17
  | Prod_244 -> f18
  | Prod_243 -> f19
  | Prod_242 -> f20
  | Prod_241 -> f21
  | Prod_240 -> f22
  | Prod_239 -> f23
  | Prod_238 -> f24
  | Prod_237 -> f25
  | Prod_236 -> f26
  | Prod_235 -> f27
  | Prod_234 -> f28
  | Prod_233 -> f29
  | Prod_232 -> f30
  | Prod_231 -> f31
  | Prod_230 -> f32
  | Prod_229 -> f33
  | Prod_228 -> f34
  | Prod_227 -> f35
  | Prod_226 -> f36
  | Prod_225 -> f37
  | Prod_224 -> f38
  | Prod_223 -> f39
  | Prod_222 -> f40
  | Prod_221 -> f41
  | Prod_220 -> f42
  | Prod_219 -> f43
  | Prod_218 -> f44
  | Prod_217 -> f45
  | Prod_216 -> f46
  | Prod_215 -> f47
  | Prod_214 -> f48
  | Prod_213 -> f49
  | Prod_212 -> f50
  | Prod_211 -> f51
  | Prod_210 -> f52
  | Prod_209 -> f53
  | Prod_208 -> f54
  | Prod_207 -> f55
  | Prod_206 -> f56
  | Prod_205 -> f57
  | Prod_204 -> f58
  | Prod_203 -> f59
  | Prod_202 -> f60
  | Prod_201 -> f61
  | Prod_200 -> f62
  | Prod_199 -> f63
  | Prod_198 -> f64
  | Prod_197 -> f65
  | Prod_196 -> f66
  | Prod_195 -> f67
  | Prod_194 -> f68
  | Prod_193 -> f69
  | Prod_192 -> f70
  | Prod_191 -> f71
  | Prod_190 -> f72
  | Prod_189 -> f73
  | Prod_188 -> f74
  | Prod_187 -> f75
  | Prod_186 -> f76
  | Prod_185 -> f77
  | Prod_184 -> f78
  | Prod_183 -> f79
  | Prod_182 -> f80
  | Prod_181 -> f81
  | Prod_180 -> f82
  | Prod_179 -> f83
  | Prod_178 -> f84
  | Prod_177 -> f85
  | Prod_176 -> f86
  | Prod_175 -> f87
  | Prod_174 -> f88
  | Prod_173 -> f89
  | Prod_172 -> f90
  | Prod_171 -> f91
  | Prod_170 -> f92
  | Prod_169 -> f93
  | Prod_168 -> f94
  | Prod_167 -> f95
  | Prod_166 -> f96
  | Prod_165 -> f97
  | Prod_164 -> f98
  | Prod_163 -> f99
  | Prod_162 -> f100
  | Prod_161 -> f101
  | Prod_160 -> f102
  | Prod_159 -> f103
  | Prod_158 -> f104
  | Prod_157 -> f105
  | Prod_156 -> f106
  | Prod_155 -> f107
  | Prod_154 -> f108
  | Prod_153 -> f109
  | Prod_152 -> f110
  | Prod_151 -> f111
  | Prod_150 -> f112
  | Prod_149 -> f113
  | Prod_148 -> f114
  | Prod_147 -> f115
  | Prod_146 -> f116
  | Prod_145 -> f117
  | Prod_144 -> f118
  | Prod_143 -> f119
  | Prod_142 -> f120
  | Prod_141 -> f121
  | Prod_140 -> f122
  | Prod_139 -> f123
  | Prod_138 -> f124
  | Prod_137 -> f125
  | Prod_136 -> f126
  | Prod_135 -> f127
  | Prod_134 -> f128
  | Prod_133 -> f129
  | Prod_132 -> f130
  | Prod_131 -> f131
  | Prod_130 -> f132
  | Prod_129 -> f133
  | Prod_128 -> f134
  | Prod_127 -> f135
  | Prod_126 -> f136
  | Prod_125 -> f137
  | Prod_124 -> f138
  | Prod_123 -> f139
  | Prod_122 -> f140
  | Prod_121 -> f141
  | Prod_120 -> f142
  | Prod_119 -> f143
  | Prod_118 -> f144
  | Prod_117 -> f145
  | Prod_116 -> f146
  | Prod_115 -> f147
  | Prod_114 -> f148
  | Prod_113 -> f149
  | Prod_112 -> f150
  | Prod_111 -> f151
  | Prod_110 -> f152
  | Prod_109 -> f153
  | Prod_108 -> f154
  | Prod_107 -> f155
  | Prod_106 -> f156
  | Prod_105 -> f157
  | Prod_104 -> f158
  | Prod_103 -> f159
  | Prod_102 -> f160
  | Prod_101 -> f161
  | Prod_100 -> f162
  | Prod_99 -> f163
  | Prod_98 -> f164
  | Prod_97 -> f165
  | Prod_96 -> f166
  | Prod_95 -> f167
  | Prod_94 -> f168
  | Prod_93 -> f169
  | Prod_92 -> f170
  | Prod_91 -> f171
  | Prod_90 -> f172
  | Prod_89 -> f173
  | Prod_88 -> f174
  | Prod_87 -> f175
  | Prod_86 -> f176
  | Prod_85 -> f177
  | Prod_84 -> f178
  | Prod_83 -> f179
  | Prod_82 -> f180
  | Prod_81 -> f181
  | Prod_80 -> f182
  | Prod_79 -> f183
  | Prod_78 -> f184
  | Prod_77 -> f185
  | Prod_76 -> f186
  | Prod_75 -> f187
  | Prod_74 -> f188
  | Prod_73 -> f189
  | Prod_72 -> f190
  | Prod_71 -> f191
  | Prod_70 -> f192
  | Prod_69 -> f193
  | Prod_68 -> f194
  | Prod_67 -> f195
  | Prod_66 -> f196
  | Prod_65 -> f197
  | Prod_64 -> f198
  | Prod_63 -> f199
  | Prod_62 -> f200
  | Prod_61 -> f201
  | Prod_60 -> f202
  | Prod_59 -> f203
  | Prod_58 -> f204
  | Prod_57 -> f205
  | Prod_56 -> f206
  | Prod_55 -> f207
  | Prod_54 -> f208
  | Prod_53 -> f209
  | Prod_52 -> f210
  | Prod_51 -> f211
  | Prod_50 -> f212
  | Prod_49 -> f213
  | Prod_48 -> f214
  | Prod_47 -> f215
  | Prod_46 -> f216
  | Prod_45 -> f217
  | Prod_44 -> f218
  | Prod_43 -> f219
  | Prod_42 -> f220
  | Prod_41 -> f221
  | Prod_40 -> f222
  | Prod_39 -> f223
  | Prod_38 -> f224
  | Prod_37 -> f225
  | Prod_36 -> f226
  | Prod_35 -> f227
  | Prod_34 -> f228
  | Prod_33 -> f229
  | Prod_32 -> f230
  | Prod_31 -> f231
  | Prod_30 -> f232
  | Prod_29 -> f233
  | Prod_28 -> f234
  | Prod_27 -> f235
  | Prod_26 -> f236
  | Prod_25 -> f237
  | Prod_24 -> f238
  | Prod_23 -> f239
  | Prod_22 -> f240
  | Prod_21 -> f241
  | Prod_20 -> f242
  | Prod_19 -> f243
  | Prod_18 -> f244
  | Prod_17 -> f245
  | Prod_16 -> f246
  | Prod_15 -> f247
  | Prod_14 -> f248
  | Prod_13 -> f249
  | Prod_12 -> f250
  | Prod_11 -> f251
  | Prod_10 -> f252
  | Prod_9 -> f253
  | Prod_8 -> f254
  | Prod_7 -> f255
  | Prod_6 -> f256
  | Prod_5 -> f257
  | Prod_4 -> f258
  | Prod_3 -> f259
  | Prod_2 -> f260
  | Prod_1 -> f261
  
  (** val production'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> production' -> 'a1 **)
  
  let production'_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 f158 f159 f160 f161 f162 f163 f164 f165 f166 f167 f168 f169 f170 f171 f172 f173 f174 f175 f176 f177 f178 f179 f180 f181 f182 f183 f184 f185 f186 f187 f188 f189 f190 f191 f192 f193 f194 f195 f196 f197 f198 f199 f200 f201 f202 f203 f204 f205 f206 f207 f208 f209 f210 f211 f212 f213 f214 f215 f216 f217 f218 f219 f220 f221 f222 f223 f224 f225 f226 f227 f228 f229 f230 f231 f232 f233 f234 f235 f236 f237 f238 f239 f240 f241 f242 f243 f244 f245 f246 f247 f248 f249 f250 f251 f252 f253 f254 f255 f256 f257 f258 f259 f260 f261 = function
  | Prod_263 -> f
  | Prod_262 -> f0
  | Prod_261 -> f1
  | Prod_260 -> f2
  | Prod_259 -> f3
  | Prod_258 -> f4
  | Prod_257 -> f5
  | Prod_256 -> f6
  | Prod_255 -> f7
  | Prod_254 -> f8
  | Prod_253 -> f9
  | Prod_252 -> f10
  | Prod_251 -> f11
  | Prod_250 -> f12
  | Prod_249 -> f13
  | Prod_248 -> f14
  | Prod_247 -> f15
  | Prod_246 -> f16
  | Prod_245 -> f17
  | Prod_244 -> f18
  | Prod_243 -> f19
  | Prod_242 -> f20
  | Prod_241 -> f21
  | Prod_240 -> f22
  | Prod_239 -> f23
  | Prod_238 -> f24
  | Prod_237 -> f25
  | Prod_236 -> f26
  | Prod_235 -> f27
  | Prod_234 -> f28
  | Prod_233 -> f29
  | Prod_232 -> f30
  | Prod_231 -> f31
  | Prod_230 -> f32
  | Prod_229 -> f33
  | Prod_228 -> f34
  | Prod_227 -> f35
  | Prod_226 -> f36
  | Prod_225 -> f37
  | Prod_224 -> f38
  | Prod_223 -> f39
  | Prod_222 -> f40
  | Prod_221 -> f41
  | Prod_220 -> f42
  | Prod_219 -> f43
  | Prod_218 -> f44
  | Prod_217 -> f45
  | Prod_216 -> f46
  | Prod_215 -> f47
  | Prod_214 -> f48
  | Prod_213 -> f49
  | Prod_212 -> f50
  | Prod_211 -> f51
  | Prod_210 -> f52
  | Prod_209 -> f53
  | Prod_208 -> f54
  | Prod_207 -> f55
  | Prod_206 -> f56
  | Prod_205 -> f57
  | Prod_204 -> f58
  | Prod_203 -> f59
  | Prod_202 -> f60
  | Prod_201 -> f61
  | Prod_200 -> f62
  | Prod_199 -> f63
  | Prod_198 -> f64
  | Prod_197 -> f65
  | Prod_196 -> f66
  | Prod_195 -> f67
  | Prod_194 -> f68
  | Prod_193 -> f69
  | Prod_192 -> f70
  | Prod_191 -> f71
  | Prod_190 -> f72
  | Prod_189 -> f73
  | Prod_188 -> f74
  | Prod_187 -> f75
  | Prod_186 -> f76
  | Prod_185 -> f77
  | Prod_184 -> f78
  | Prod_183 -> f79
  | Prod_182 -> f80
  | Prod_181 -> f81
  | Prod_180 -> f82
  | Prod_179 -> f83
  | Prod_178 -> f84
  | Prod_177 -> f85
  | Prod_176 -> f86
  | Prod_175 -> f87
  | Prod_174 -> f88
  | Prod_173 -> f89
  | Prod_172 -> f90
  | Prod_171 -> f91
  | Prod_170 -> f92
  | Prod_169 -> f93
  | Prod_168 -> f94
  | Prod_167 -> f95
  | Prod_166 -> f96
  | Prod_165 -> f97
  | Prod_164 -> f98
  | Prod_163 -> f99
  | Prod_162 -> f100
  | Prod_161 -> f101
  | Prod_160 -> f102
  | Prod_159 -> f103
  | Prod_158 -> f104
  | Prod_157 -> f105
  | Prod_156 -> f106
  | Prod_155 -> f107
  | Prod_154 -> f108
  | Prod_153 -> f109
  | Prod_152 -> f110
  | Prod_151 -> f111
  | Prod_150 -> f112
  | Prod_149 -> f113
  | Prod_148 -> f114
  | Prod_147 -> f115
  | Prod_146 -> f116
  | Prod_145 -> f117
  | Prod_144 -> f118
  | Prod_143 -> f119
  | Prod_142 -> f120
  | Prod_141 -> f121
  | Prod_140 -> f122
  | Prod_139 -> f123
  | Prod_138 -> f124
  | Prod_137 -> f125
  | Prod_136 -> f126
  | Prod_135 -> f127
  | Prod_134 -> f128
  | Prod_133 -> f129
  | Prod_132 -> f130
  | Prod_131 -> f131
  | Prod_130 -> f132
  | Prod_129 -> f133
  | Prod_128 -> f134
  | Prod_127 -> f135
  | Prod_126 -> f136
  | Prod_125 -> f137
  | Prod_124 -> f138
  | Prod_123 -> f139
  | Prod_122 -> f140
  | Prod_121 -> f141
  | Prod_120 -> f142
  | Prod_119 -> f143
  | Prod_118 -> f144
  | Prod_117 -> f145
  | Prod_116 -> f146
  | Prod_115 -> f147
  | Prod_114 -> f148
  | Prod_113 -> f149
  | Prod_112 -> f150
  | Prod_111 -> f151
  | Prod_110 -> f152
  | Prod_109 -> f153
  | Prod_108 -> f154
  | Prod_107 -> f155
  | Prod_106 -> f156
  | Prod_105 -> f157
  | Prod_104 -> f158
  | Prod_103 -> f159
  | Prod_102 -> f160
  | Prod_101 -> f161
  | Prod_100 -> f162
  | Prod_99 -> f163
  | Prod_98 -> f164
  | Prod_97 -> f165
  | Prod_96 -> f166
  | Prod_95 -> f167
  | Prod_94 -> f168
  | Prod_93 -> f169
  | Prod_92 -> f170
  | Prod_91 -> f171
  | Prod_90 -> f172
  | Prod_89 -> f173
  | Prod_88 -> f174
  | Prod_87 -> f175
  | Prod_86 -> f176
  | Prod_85 -> f177
  | Prod_84 -> f178
  | Prod_83 -> f179
  | Prod_82 -> f180
  | Prod_81 -> f181
  | Prod_80 -> f182
  | Prod_79 -> f183
  | Prod_78 -> f184
  | Prod_77 -> f185
  | Prod_76 -> f186
  | Prod_75 -> f187
  | Prod_74 -> f188
  | Prod_73 -> f189
  | Prod_72 -> f190
  | Prod_71 -> f191
  | Prod_70 -> f192
  | Prod_69 -> f193
  | Prod_68 -> f194
  | Prod_67 -> f195
  | Prod_66 -> f196
  | Prod_65 -> f197
  | Prod_64 -> f198
  | Prod_63 -> f199
  | Prod_62 -> f200
  | Prod_61 -> f201
  | Prod_60 -> f202
  | Prod_59 -> f203
  | Prod_58 -> f204
  | Prod_57 -> f205
  | Prod_56 -> f206
  | Prod_55 -> f207
  | Prod_54 -> f208
  | Prod_53 -> f209
  | Prod_52 -> f210
  | Prod_51 -> f211
  | Prod_50 -> f212
  | Prod_49 -> f213
  | Prod_48 -> f214
  | Prod_47 -> f215
  | Prod_46 -> f216
  | Prod_45 -> f217
  | Prod_44 -> f218
  | Prod_43 -> f219
  | Prod_42 -> f220
  | Prod_41 -> f221
  | Prod_40 -> f222
  | Prod_39 -> f223
  | Prod_38 -> f224
  | Prod_37 -> f225
  | Prod_36 -> f226
  | Prod_35 -> f227
  | Prod_34 -> f228
  | Prod_33 -> f229
  | Prod_32 -> f230
  | Prod_31 -> f231
  | Prod_30 -> f232
  | Prod_29 -> f233
  | Prod_28 -> f234
  | Prod_27 -> f235
  | Prod_26 -> f236
  | Prod_25 -> f237
  | Prod_24 -> f238
  | Prod_23 -> f239
  | Prod_22 -> f240
  | Prod_21 -> f241
  | Prod_20 -> f242
  | Prod_19 -> f243
  | Prod_18 -> f244
  | Prod_17 -> f245
  | Prod_16 -> f246
  | Prod_15 -> f247
  | Prod_14 -> f248
  | Prod_13 -> f249
  | Prod_12 -> f250
  | Prod_11 -> f251
  | Prod_10 -> f252
  | Prod_9 -> f253
  | Prod_8 -> f254
  | Prod_7 -> f255
  | Prod_6 -> f256
  | Prod_5 -> f257
  | Prod_4 -> f258
  | Prod_3 -> f259
  | Prod_2 -> f260
  | Prod_1 -> f261
  
  type production = production'
  
  (** val productionNum : production coq_Numbered **)
  
  let productionNum =
    { injN = (fun x ->
      match x with
      | Prod_263 -> N0
      | Prod_262 -> Npos Coq_xH
      | Prod_261 -> Npos (Coq_xO Coq_xH)
      | Prod_260 -> Npos (Coq_xI Coq_xH)
      | Prod_259 -> Npos (Coq_xO (Coq_xO Coq_xH))
      | Prod_258 -> Npos (Coq_xI (Coq_xO Coq_xH))
      | Prod_257 -> Npos (Coq_xO (Coq_xI Coq_xH))
      | Prod_256 -> Npos (Coq_xI (Coq_xI Coq_xH))
      | Prod_255 -> Npos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Prod_254 -> Npos (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Prod_253 -> Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Prod_252 -> Npos (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Prod_251 -> Npos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Prod_250 -> Npos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Prod_249 -> Npos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Prod_248 -> Npos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Prod_247 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Prod_246 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Prod_245 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Prod_244 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Prod_243 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Prod_242 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Prod_241 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Prod_240 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Prod_239 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Prod_238 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Prod_237 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Prod_236 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Prod_235 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Prod_234 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Prod_233 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Prod_232 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Prod_231 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_230 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_229 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_228 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_227 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_226 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_225 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_224 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Prod_223 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_222 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_221 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_220 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_219 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_218 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_217 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_216 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Prod_215 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_214 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_213 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_212 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_211 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_210 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_209 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_208 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Prod_207 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_206 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_205 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_204 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_203 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_202 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_201 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_200 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Prod_199 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_198 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_197 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_196 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_195 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_194 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_193 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_192 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_191 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_190 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_189 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_188 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_187 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_186 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_185 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_184 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Prod_183 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_182 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_181 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_180 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_179 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_178 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_177 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_176 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_175 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_174 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_173 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_172 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_171 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_170 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_169 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_168 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Prod_167 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_166 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_165 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_164 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_163 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_162 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_161 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_160 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_159 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_158 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_157 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_156 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_155 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_154 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_153 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_152 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Prod_151 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_150 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_149 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_148 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_147 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_146 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_145 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_144 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_143 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_142 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_141 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_140 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_139 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_138 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_137 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_136 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Prod_135 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_134 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_133 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_132 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_131 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_130 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_129 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_128 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_127 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_126 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_125 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_124 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_123 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_122 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_121 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_120 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_119 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_118 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_117 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_116 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_115 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_114 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_113 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_112 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_111 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_110 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_109 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_108 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_107 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_106 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_105 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_104 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Prod_103 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_102 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_101 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_100 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_99 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_98 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_97 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_96 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_95 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_94 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_93 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_92 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_91 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_90 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_89 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_88 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_87 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_86 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_85 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_84 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_83 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_82 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_81 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_80 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_79 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_78 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_77 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_76 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_75 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_74 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_73 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_72 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Prod_71 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_70 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_69 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_68 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_67 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_66 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_65 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_64 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_63 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_62 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_61 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_60 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_59 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_58 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_57 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_56 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_55 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_54 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_53 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_52 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_51 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_50 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_49 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_48 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_47 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_46 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_45 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_44 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_43 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_42 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_41 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_40 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Prod_39 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_38 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_37 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_36 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_35 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_34 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_33 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_32 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_31 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_30 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_29 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_28 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_27 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_26 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_25 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_24 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_23 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_22 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_21 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_20 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_19 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_18 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_17 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_16 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_15 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_14 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_13 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_12 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_11 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_10 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_9 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_8 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Prod_7 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Prod_6 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Prod_5 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Prod_4 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Prod_3 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Prod_2 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Prod_1 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))); surjN = (fun n ->
      match n with
      | N0 -> Prod_263
      | Npos p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_8
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_72
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_136)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_40
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_104
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_168)
                        | Coq_xH -> Prod_200)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_24
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_88
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_152)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_56
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_120
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_184)
                        | Coq_xH -> Prod_216)
                     | Coq_xH -> Prod_232)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_16
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_80
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_144)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_48
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_112
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_176)
                        | Coq_xH -> Prod_208)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_32
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_96
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_160)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_64
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_128
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_192)
                        | Coq_xH -> Prod_224)
                     | Coq_xH -> Prod_240)
                  | Coq_xH -> Prod_248)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_12
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_76
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_140)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_44
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_108
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_172)
                        | Coq_xH -> Prod_204)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_28
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_92
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_156)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_60
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_124
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_188)
                        | Coq_xH -> Prod_220)
                     | Coq_xH -> Prod_236)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_20
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_84
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_148)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_52
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_116
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_180)
                        | Coq_xH -> Prod_212)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_36
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_100
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_164)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_68
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_4
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_132)
                           | Coq_xH -> Prod_196)
                        | Coq_xH -> Prod_228)
                     | Coq_xH -> Prod_244)
                  | Coq_xH -> Prod_252)
               | Coq_xH -> Prod_256)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_10
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_74
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_138)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_42
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_106
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_170)
                        | Coq_xH -> Prod_202)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_26
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_90
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_154)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_58
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_122
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_186)
                        | Coq_xH -> Prod_218)
                     | Coq_xH -> Prod_234)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_18
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_82
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_146)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_50
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_114
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_178)
                        | Coq_xH -> Prod_210)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_34
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_98
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_162)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_66
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_2
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_130)
                           | Coq_xH -> Prod_194)
                        | Coq_xH -> Prod_226)
                     | Coq_xH -> Prod_242)
                  | Coq_xH -> Prod_250)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_14
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_78
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_142)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_46
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_110
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_174)
                        | Coq_xH -> Prod_206)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_30
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_94
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_158)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_62
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_126
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_190)
                        | Coq_xH -> Prod_222)
                     | Coq_xH -> Prod_238)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_22
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_86
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_150)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_54
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_118
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_182)
                        | Coq_xH -> Prod_214)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_38
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_102
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_166)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_70
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_6
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_134)
                           | Coq_xH -> Prod_198)
                        | Coq_xH -> Prod_230)
                     | Coq_xH -> Prod_246)
                  | Coq_xH -> Prod_254)
               | Coq_xH -> Prod_258)
            | Coq_xH -> Prod_260)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_9
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_73
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_137)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_41
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_105
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_169)
                        | Coq_xH -> Prod_201)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_25
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_89
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_153)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_57
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_121
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_185)
                        | Coq_xH -> Prod_217)
                     | Coq_xH -> Prod_233)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_17
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_81
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_145)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_49
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_113
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_177)
                        | Coq_xH -> Prod_209)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_33
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_97
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_161)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_65
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_1
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_129)
                           | Coq_xH -> Prod_193)
                        | Coq_xH -> Prod_225)
                     | Coq_xH -> Prod_241)
                  | Coq_xH -> Prod_249)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_13
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_77
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_141)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_45
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_109
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_173)
                        | Coq_xH -> Prod_205)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_29
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_93
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_157)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_61
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_125
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_189)
                        | Coq_xH -> Prod_221)
                     | Coq_xH -> Prod_237)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_21
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_85
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_149)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_53
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_117
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_181)
                        | Coq_xH -> Prod_213)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_37
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_101
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_165)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_69
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_5
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_133)
                           | Coq_xH -> Prod_197)
                        | Coq_xH -> Prod_229)
                     | Coq_xH -> Prod_245)
                  | Coq_xH -> Prod_253)
               | Coq_xH -> Prod_257)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_11
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_75
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_139)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_43
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_107
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_171)
                        | Coq_xH -> Prod_203)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_27
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_91
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_155)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_59
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_123
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_187)
                        | Coq_xH -> Prod_219)
                     | Coq_xH -> Prod_235)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_19
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_83
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_147)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_51
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_115
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_179)
                        | Coq_xH -> Prod_211)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_35
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_99
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_163)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_67
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_3
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_131)
                           | Coq_xH -> Prod_195)
                        | Coq_xH -> Prod_227)
                     | Coq_xH -> Prod_243)
                  | Coq_xH -> Prod_251)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_15
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_79
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_143)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_47
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_111
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_175)
                        | Coq_xH -> Prod_207)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_31
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_95
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_159)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_63
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_127
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_191)
                        | Coq_xH -> Prod_223)
                     | Coq_xH -> Prod_239)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_23
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_87
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_151)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_55
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_119
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_183)
                        | Coq_xH -> Prod_215)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_39
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_103
                              | _ -> Prod_263)
                           | Coq_xH -> Prod_167)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xH -> Prod_71
                              | _ -> Prod_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Prod_263
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Prod_7
                                 | _ -> Prod_263)
                              | Coq_xH -> Prod_135)
                           | Coq_xH -> Prod_199)
                        | Coq_xH -> Prod_231)
                     | Coq_xH -> Prod_247)
                  | Coq_xH -> Prod_255)
               | Coq_xH -> Prod_259)
            | Coq_xH -> Prod_261)
         | Coq_xH -> Prod_262)); injN_bound = (Npos (Coq_xI (Coq_xI (Coq_xI
      (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))) }
  
  (** val coq_ProductionAlph : production coq_Alphabet **)
  
  let coq_ProductionAlph =
    coq_NumberedAlphabet productionNum
  
  (** val prod_contents :
      production -> (nonterminal*symbol list, symbol_semantic_type arrows)
      sigT **)
  
  let prod_contents p =
    let box = fun x x0 -> Coq_existT (x, x0) in
    (match p with
     | Prod_263 ->
       Obj.magic box (Coq_unary_operator_nt,((T BANG_t)::[])) (fun loc ->
         NOT,loc)
     | Prod_262 ->
       Obj.magic box (Coq_unary_operator_nt,((T TILDE_t)::[])) (fun loc ->
         BNOT,loc)
     | Prod_261 ->
       Obj.magic box (Coq_unary_operator_nt,((T MINUS_t)::[])) (fun loc ->
         MINUS,loc)
     | Prod_260 ->
       Obj.magic box (Coq_unary_operator_nt,((T PLUS_t)::[])) (fun loc ->
         PLUS,loc)
     | Prod_259 ->
       Obj.magic box (Coq_unary_operator_nt,((T STAR_t)::[])) (fun loc ->
         MEMOF,loc)
     | Prod_258 ->
       Obj.magic box (Coq_unary_operator_nt,((T AND_t)::[])) (fun loc ->
         ADDROF,loc)
     | Prod_257 ->
       Obj.magic box (Coq_unary_expression_nt,((T SIZEOF_t)::((T
         LPAREN_t)::((NT Coq_type_name_nt)::((T RPAREN_t)::[])))))
         (fun loc _2 typ _4 -> (TYPE_SIZEOF typ),loc)
     | Prod_256 ->
       Obj.magic box (Coq_unary_expression_nt,((T SIZEOF_t)::((NT
         Coq_unary_expression_nt)::[]))) (fun loc expr -> (EXPR_SIZEOF
         (fst expr)),loc)
     | Prod_255 ->
       Obj.magic box (Coq_unary_expression_nt,((NT
         Coq_unary_operator_nt)::((NT Coq_cast_expression_nt)::[])))
         (fun op expr -> (UNARY ((fst op), (fst expr))),(snd op))
     | Prod_254 ->
       Obj.magic box (Coq_unary_expression_nt,((T DEC_t)::((NT
         Coq_unary_expression_nt)::[]))) (fun loc expr -> (UNARY (PREDECR,
         (fst expr))),loc)
     | Prod_253 ->
       Obj.magic box (Coq_unary_expression_nt,((T INC_t)::((NT
         Coq_unary_expression_nt)::[]))) (fun loc expr -> (UNARY (PREINCR,
         (fst expr))),loc)
     | Prod_252 ->
       Obj.magic box (Coq_unary_expression_nt,((NT
         Coq_postfix_expression_nt)::[])) (fun expr -> expr)
     | Prod_251 ->
       Obj.magic box (Coq_type_specifier_nt,((T TYPEDEF_NAME_t)::[]))
         (fun id -> (Tnamed (fst id)),(snd id))
     | Prod_250 ->
       Obj.magic box (Coq_type_specifier_nt,((NT Coq_enum_specifier_nt)::[]))
         (fun spec -> spec)
     | Prod_249 ->
       Obj.magic box (Coq_type_specifier_nt,((NT
         Coq_struct_or_union_specifier_nt)::[])) (fun spec -> spec)
     | Prod_248 ->
       Obj.magic box (Coq_type_specifier_nt,((T BOOL_t)::[])) (fun loc ->
         T_Bool,loc)
     | Prod_247 ->
       Obj.magic box (Coq_type_specifier_nt,((T UNSIGNED_t)::[])) (fun loc ->
         Tunsigned,loc)
     | Prod_246 ->
       Obj.magic box (Coq_type_specifier_nt,((T SIGNED_t)::[])) (fun loc ->
         Tsigned,loc)
     | Prod_245 ->
       Obj.magic box (Coq_type_specifier_nt,((T DOUBLE_t)::[])) (fun loc ->
         Tdouble,loc)
     | Prod_244 ->
       Obj.magic box (Coq_type_specifier_nt,((T FLOAT_t)::[])) (fun loc ->
         Tfloat,loc)
     | Prod_243 ->
       Obj.magic box (Coq_type_specifier_nt,((T LONG_t)::[])) (fun loc ->
         Tlong,loc)
     | Prod_242 ->
       Obj.magic box (Coq_type_specifier_nt,((T INT_t)::[])) (fun loc ->
         Tint,loc)
     | Prod_241 ->
       Obj.magic box (Coq_type_specifier_nt,((T SHORT_t)::[])) (fun loc ->
         Tshort,loc)
     | Prod_240 ->
       Obj.magic box (Coq_type_specifier_nt,((T CHAR_t)::[])) (fun loc ->
         Tchar,loc)
     | Prod_239 ->
       Obj.magic box (Coq_type_specifier_nt,((T VOID_t)::[])) (fun loc ->
         Tvoid,loc)
     | Prod_238 ->
       Obj.magic box (Coq_type_qualifier_list_nt,((NT
         Coq_type_qualifier_list_nt)::((NT Coq_type_qualifier_nt)::[])))
         (fun qualq qualt -> (fst qualt)::qualq)
     | Prod_237 ->
       Obj.magic box (Coq_type_qualifier_list_nt,((NT
         Coq_type_qualifier_nt)::[])) (fun qual -> (fst qual)::[])
     | Prod_236 ->
       Obj.magic box (Coq_type_qualifier_nt,((T VOLATILE_t)::[])) (fun loc ->
         CV_VOLATILE,loc)
     | Prod_235 ->
       Obj.magic box (Coq_type_qualifier_nt,((T RESTRICT_t)::[])) (fun loc ->
         CV_RESTRICT,loc)
     | Prod_234 ->
       Obj.magic box (Coq_type_qualifier_nt,((T CONST_t)::[])) (fun loc ->
         CV_CONST,loc)
     | Prod_233 ->
       Obj.magic box (Coq_type_name_nt,((NT
         Coq_specifier_qualifier_list_nt)::((NT
         Coq_abstract_declarator_nt)::[]))) (fun specqual typ ->
         (fst specqual),typ)
     | Prod_232 ->
       Obj.magic box (Coq_type_name_nt,((NT
         Coq_specifier_qualifier_list_nt)::[])) (fun specqual ->
         (fst specqual),JUSTBASE)
     | Prod_231 ->
       Obj.magic box (Coq_translation_unit_file_nt,((NT
         Coq_translation_unit_nt)::((T EOF_t)::[]))) (fun lst _2 -> rev lst)
     | Prod_230 ->
       Obj.magic box (Coq_translation_unit_nt,((NT
         Coq_translation_unit_nt)::((NT Coq_external_declaration_nt)::[])))
         (fun defq deft -> deft::defq)
     | Prod_229 ->
       Obj.magic box (Coq_translation_unit_nt,((NT
         Coq_external_declaration_nt)::[])) (fun def -> def::[])
     | Prod_228 ->
       Obj.magic box (Coq_struct_or_union_specifier_nt,((NT
         Coq_struct_or_union_nt)::((T OTHER_NAME_t)::[]))) (fun str_uni id ->
         (fst str_uni (Some (fst id)) None []),(snd str_uni))
     | Prod_227 ->
       Obj.magic box (Coq_struct_or_union_specifier_nt,((NT
         Coq_struct_or_union_nt)::((T LBRACE_t)::((NT
         Coq_struct_declaration_list_nt)::((T RBRACE_t)::[])))))
         (fun str_uni _2 decls _4 ->
         (fst str_uni None (Some (rev decls)) []),(snd str_uni))
     | Prod_226 ->
       Obj.magic box (Coq_struct_or_union_specifier_nt,((NT
         Coq_struct_or_union_nt)::((T OTHER_NAME_t)::((T LBRACE_t)::((NT
         Coq_struct_declaration_list_nt)::((T RBRACE_t)::[]))))))
         (fun str_uni id _3 decls _5 ->
         (fst str_uni (Some (fst id)) (Some (rev decls)) []),(snd str_uni))
     | Prod_225 ->
       Obj.magic box (Coq_struct_or_union_nt,((T UNION_t)::[])) (fun loc ->
         (fun x x0 x1 -> Tunion (x, x0, x1)),loc)
     | Prod_224 ->
       Obj.magic box (Coq_struct_or_union_nt,((T STRUCT_t)::[])) (fun loc ->
         (fun x x0 x1 -> Tstruct (x, x0, x1)),loc)
     | Prod_223 ->
       Obj.magic box (Coq_struct_declarator_list_nt,((NT
         Coq_struct_declarator_list_nt)::((T COMMA_t)::((NT
         Coq_struct_declarator_nt)::[])))) (fun declq _2 declt ->
         declt::declq)
     | Prod_222 ->
       Obj.magic box (Coq_struct_declarator_list_nt,((NT
         Coq_struct_declarator_nt)::[])) (fun decl -> decl::[])
     | Prod_221 ->
       Obj.magic box (Coq_struct_declarator_nt,((T COLON_t)::((NT
         Coq_constant_expression_nt)::[]))) (fun _1 expr -> None,(Some
         (fst expr)))
     | Prod_220 ->
       Obj.magic box (Coq_struct_declarator_nt,((NT Coq_declarator_nt)::((T
         COLON_t)::((NT Coq_constant_expression_nt)::[]))))
         (fun decl _2 expr -> (Some decl),(Some (fst expr)))
     | Prod_219 ->
       Obj.magic box (Coq_struct_declarator_nt,((NT Coq_declarator_nt)::[]))
         (fun decl -> (Some decl),None)
     | Prod_218 ->
       Obj.magic box (Coq_struct_declaration_list_nt,((NT
         Coq_struct_declaration_list_nt)::((NT
         Coq_struct_declaration_nt)::[]))) (fun qdecls tdecls ->
         tdecls::qdecls)
     | Prod_217 ->
       Obj.magic box (Coq_struct_declaration_list_nt,((NT
         Coq_struct_declaration_nt)::[])) (fun decl -> decl::[])
     | Prod_216 ->
       Obj.magic box (Coq_struct_declaration_nt,((NT
         Coq_specifier_qualifier_list_nt)::((T SEMICOLON_t)::[])))
         (fun decspec _2 -> Field_group ((fst decspec), [], (snd decspec)))
     | Prod_215 ->
       Obj.magic box (Coq_struct_declaration_nt,((NT
         Coq_specifier_qualifier_list_nt)::((NT
         Coq_struct_declarator_list_nt)::((T SEMICOLON_t)::[]))))
         (fun decspec decls _3 -> Field_group ((fst decspec), (rev decls),
         (snd decspec)))
     | Prod_214 ->
       Obj.magic box (Coq_storage_class_specifier_nt,((T REGISTER_t)::[]))
         (fun loc -> REGISTER,loc)
     | Prod_213 ->
       Obj.magic box (Coq_storage_class_specifier_nt,((T AUTO_t)::[]))
         (fun loc -> AUTO,loc)
     | Prod_212 ->
       Obj.magic box (Coq_storage_class_specifier_nt,((T STATIC_t)::[]))
         (fun loc -> STATIC,loc)
     | Prod_211 ->
       Obj.magic box (Coq_storage_class_specifier_nt,((T EXTERN_t)::[]))
         (fun loc -> EXTERN,loc)
     | Prod_210 ->
       Obj.magic box (Coq_storage_class_specifier_nt,((T TYPEDEF_t)::[]))
         (fun loc -> TYPEDEF,loc)
     | Prod_209 ->
       Obj.magic box (Coq_statement_safe_nt,((NT Coq_jump_statement_nt)::[]))
         (fun stmt -> stmt)
     | Prod_208 ->
       Obj.magic box (Coq_statement_safe_nt,((NT
         Coq_iteration_statement_statement_safe__nt)::[])) (fun stmt -> stmt)
     | Prod_207 ->
       Obj.magic box (Coq_statement_safe_nt,((NT
         Coq_selection_statement_safe_nt)::[])) (fun stmt -> stmt)
     | Prod_206 ->
       Obj.magic box (Coq_statement_safe_nt,((NT
         Coq_expression_statement_nt)::[])) (fun stmt -> stmt)
     | Prod_205 ->
       Obj.magic box (Coq_statement_safe_nt,((NT
         Coq_compound_statement_nt)::[])) (fun stmt -> stmt)
     | Prod_204 ->
       Obj.magic box (Coq_statement_safe_nt,((NT
         Coq_labeled_statement_statement_safe__nt)::[])) (fun stmt -> stmt)
     | Prod_203 ->
       Obj.magic box (Coq_statement_dangerous_nt,((NT
         Coq_jump_statement_nt)::[])) (fun stmt -> stmt)
     | Prod_202 ->
       Obj.magic box (Coq_statement_dangerous_nt,((NT
         Coq_iteration_statement_statement_dangerous__nt)::[])) (fun stmt ->
         stmt)
     | Prod_201 ->
       Obj.magic box (Coq_statement_dangerous_nt,((NT
         Coq_selection_statement_dangerous_nt)::[])) (fun stmt -> stmt)
     | Prod_200 ->
       Obj.magic box (Coq_statement_dangerous_nt,((NT
         Coq_expression_statement_nt)::[])) (fun stmt -> stmt)
     | Prod_199 ->
       Obj.magic box (Coq_statement_dangerous_nt,((NT
         Coq_compound_statement_nt)::[])) (fun stmt -> stmt)
     | Prod_198 ->
       Obj.magic box (Coq_statement_dangerous_nt,((NT
         Coq_labeled_statement_statement_dangerous__nt)::[])) (fun stmt ->
         stmt)
     | Prod_197 ->
       Obj.magic box (Coq_specifier_qualifier_list_nt,((NT
         Coq_type_qualifier_nt)::[])) (fun qual -> ((SpecCV
         (fst qual))::[]),(snd qual))
     | Prod_196 ->
       Obj.magic box (Coq_specifier_qualifier_list_nt,((NT
         Coq_type_qualifier_nt)::((NT Coq_specifier_qualifier_list_nt)::[])))
         (fun qual rest -> ((SpecCV (fst qual))::(fst rest)),(snd qual))
     | Prod_195 ->
       Obj.magic box (Coq_specifier_qualifier_list_nt,((NT
         Coq_type_specifier_nt)::[])) (fun typ -> ((SpecType
         (fst typ))::[]),(snd typ))
     | Prod_194 ->
       Obj.magic box (Coq_specifier_qualifier_list_nt,((NT
         Coq_type_specifier_nt)::((NT Coq_specifier_qualifier_list_nt)::[])))
         (fun typ rest -> ((SpecType (fst typ))::(fst rest)),(snd typ))
     | Prod_193 ->
       Obj.magic box (Coq_shift_expression_nt,((NT
         Coq_shift_expression_nt)::((T RIGHT_t)::((NT
         Coq_additive_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY
         (SHR, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_192 ->
       Obj.magic box (Coq_shift_expression_nt,((NT
         Coq_shift_expression_nt)::((T LEFT_t)::((NT
         Coq_additive_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY
         (SHL, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_191 ->
       Obj.magic box (Coq_shift_expression_nt,((NT
         Coq_additive_expression_nt)::[])) (fun expr -> expr)
     | Prod_190 ->
       Obj.magic box (Coq_selection_statement_safe_nt,((T SWITCH_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[])))))) (fun loc _2 expr _4 stmt -> SWITCH
         ((fst expr), stmt, loc))
     | Prod_189 ->
       Obj.magic box (Coq_selection_statement_safe_nt,((T IF_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::((T ELSE_t)::((NT
         Coq_statement_safe_nt)::[]))))))))
         (fun loc _2 expr _4 stmt1 _6 stmt2 -> If ((fst expr), stmt1, (Some
         stmt2), loc))
     | Prod_188 ->
       Obj.magic box (Coq_selection_statement_dangerous_nt,((T SWITCH_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[])))))) (fun loc _2 expr _4 stmt ->
         SWITCH ((fst expr), stmt, loc))
     | Prod_187 ->
       Obj.magic box (Coq_selection_statement_dangerous_nt,((T IF_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::((T ELSE_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))
         (fun loc _2 expr _4 stmt1 _6 stmt2 -> If ((fst expr), stmt1, (Some
         stmt2), loc))
     | Prod_186 ->
       Obj.magic box (Coq_selection_statement_dangerous_nt,((T IF_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[])))))) (fun loc _2 expr _4 stmt -> If
         ((fst expr), stmt, None, loc))
     | Prod_185 ->
       Obj.magic box (Coq_relational_expression_nt,((NT
         Coq_relational_expression_nt)::((T GEQ_t)::((NT
         Coq_shift_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (GE,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_184 ->
       Obj.magic box (Coq_relational_expression_nt,((NT
         Coq_relational_expression_nt)::((T LEQ_t)::((NT
         Coq_shift_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (LE,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_183 ->
       Obj.magic box (Coq_relational_expression_nt,((NT
         Coq_relational_expression_nt)::((T GT_t)::((NT
         Coq_shift_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (GT,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_182 ->
       Obj.magic box (Coq_relational_expression_nt,((NT
         Coq_relational_expression_nt)::((T LT_t)::((NT
         Coq_shift_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (LT,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_181 ->
       Obj.magic box (Coq_relational_expression_nt,((NT
         Coq_shift_expression_nt)::[])) (fun expr -> expr)
     | Prod_180 ->
       Obj.magic box (Coq_primary_expression_nt,((T LPAREN_t)::((NT
         Coq_expression_nt)::((T RPAREN_t)::[])))) (fun loc expr _3 ->
         (fst expr),loc)
     | Prod_179 ->
       Obj.magic box (Coq_primary_expression_nt,((T CONSTANT_t)::[]))
         (fun cst -> (CONSTANT (fst cst)),(snd cst))
     | Prod_178 ->
       Obj.magic box (Coq_primary_expression_nt,((T VAR_NAME_t)::[]))
         (fun var -> (VARIABLE (fst var)),(snd var))
     | Prod_177 ->
       Obj.magic box (Coq_postfix_expression_nt,((T LPAREN_t)::((NT
         Coq_type_name_nt)::((T RPAREN_t)::((T LBRACE_t)::((NT
         Coq_initializer_list_nt)::((T COMMA_t)::((T RBRACE_t)::[]))))))))
         (fun loc typ _3 _4 init _6 _7 -> (CAST (typ, (COMPOUND_INIT
         (rev init)))),loc)
     | Prod_176 ->
       Obj.magic box (Coq_postfix_expression_nt,((T LPAREN_t)::((NT
         Coq_type_name_nt)::((T RPAREN_t)::((T LBRACE_t)::((NT
         Coq_initializer_list_nt)::((T RBRACE_t)::[])))))))
         (fun loc typ _3 _4 init _6 -> (CAST (typ, (COMPOUND_INIT
         (rev init)))),loc)
     | Prod_175 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T DEC_t)::[]))) (fun expr _2 -> (UNARY
         (POSDECR, (fst expr))),(snd expr))
     | Prod_174 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T INC_t)::[]))) (fun expr _2 -> (UNARY
         (POSINCR, (fst expr))),(snd expr))
     | Prod_173 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T PTR_t)::((T OTHER_NAME_t)::[]))))
         (fun expr _2 mem0 -> (MEMBEROFPTR ((fst expr),
         (fst mem0))),(snd expr))
     | Prod_172 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T DOT_t)::((T OTHER_NAME_t)::[]))))
         (fun expr _2 mem0 -> (MEMBEROF ((fst expr), (fst mem0))),(snd expr))
     | Prod_171 ->
       Obj.magic box (Coq_postfix_expression_nt,((T BUILTIN_VA_ARG_t)::((T
         LPAREN_t)::((NT Coq_assignment_expression_nt)::((T COMMA_t)::((NT
         Coq_type_name_nt)::((T RPAREN_t)::[])))))))
         (fun loc _2 expr _4 ty _6 -> (BUILTIN_VA_ARG ((fst expr), ty)),loc)
     | Prod_170 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T LPAREN_t)::((T RPAREN_t)::[]))))
         (fun expr _2 _3 -> (CALL ((fst expr), [])),(snd expr))
     | Prod_169 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T LPAREN_t)::((NT
         Coq_argument_expression_list_nt)::((T RPAREN_t)::[])))))
         (fun expr _2 args _4 -> (CALL ((fst expr), (rev args))),(snd expr))
     | Prod_168 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_postfix_expression_nt)::((T LBRACK_t)::((NT
         Coq_expression_nt)::((T RBRACK_t)::[]))))) (fun expr _2 index _4 ->
         (INDEX ((fst expr), (fst index))),(snd expr))
     | Prod_167 ->
       Obj.magic box (Coq_postfix_expression_nt,((NT
         Coq_primary_expression_nt)::[])) (fun expr -> expr)
     | Prod_166 ->
       Obj.magic box (Coq_pointer_nt,((T STAR_t)::((NT
         Coq_type_qualifier_list_nt)::((NT Coq_pointer_nt)::[]))))
         (fun loc quallst pt -> (fun typ -> PTR ((rev quallst), [],
         (fst pt typ))),loc)
     | Prod_165 ->
       Obj.magic box (Coq_pointer_nt,((T STAR_t)::((NT Coq_pointer_nt)::[])))
         (fun loc pt -> (fun typ -> PTR ([], [], (fst pt typ))),loc)
     | Prod_164 ->
       Obj.magic box (Coq_pointer_nt,((T STAR_t)::((NT
         Coq_type_qualifier_list_nt)::[]))) (fun loc quallst -> (fun x -> PTR
         ((rev quallst), [], x)),loc)
     | Prod_163 ->
       Obj.magic box (Coq_pointer_nt,((T STAR_t)::[])) (fun loc -> (fun x ->
         PTR ([], [], x)),loc)
     | Prod_162 ->
       Obj.magic box (Coq_parameter_type_list_nt,((NT
         Coq_parameter_list_nt)::((T COMMA_t)::((T ELLIPSIS_t)::[]))))
         (fun lst _2 _3 -> (rev lst),true)
     | Prod_161 ->
       Obj.magic box (Coq_parameter_type_list_nt,((NT
         Coq_parameter_list_nt)::[])) (fun lst -> (rev lst),false)
     | Prod_160 ->
       Obj.magic box (Coq_parameter_list_nt,((NT Coq_parameter_list_nt)::((T
         COMMA_t)::((NT Coq_parameter_declaration_nt)::[]))))
         (fun paramq _2 paramt -> paramt::paramq)
     | Prod_159 ->
       Obj.magic box (Coq_parameter_list_nt,((NT
         Coq_parameter_declaration_nt)::[])) (fun param -> param::[])
     | Prod_158 ->
       Obj.magic box (Coq_parameter_declaration_nt,((NT
         Coq_declaration_specifiers_nt)::[])) (fun specs -> PARAM
         ((fst specs), None, JUSTBASE, [], (snd specs)))
     | Prod_157 ->
       Obj.magic box (Coq_parameter_declaration_nt,((NT
         Coq_declaration_specifiers_nt)::((NT
         Coq_abstract_declarator_nt)::[]))) (fun specs decl -> PARAM
         ((fst specs), None, decl, [], (snd specs)))
     | Prod_156 ->
       Obj.magic box (Coq_parameter_declaration_nt,((NT
         Coq_declaration_specifiers_nt)::((NT Coq_declarator_nt)::[])))
         (fun specs decl ->
         let Name (name, typ, attr, c) = decl in
         PARAM ((fst specs), (Some name), typ, attr, (snd specs)))
     | Prod_155 ->
       Obj.magic box (Coq_multiplicative_expression_nt,((NT
         Coq_multiplicative_expression_nt)::((T PERCENT_t)::((NT
         Coq_cast_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (MOD,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_154 ->
       Obj.magic box (Coq_multiplicative_expression_nt,((NT
         Coq_multiplicative_expression_nt)::((T SLASH_t)::((NT
         Coq_cast_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (DIV,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_153 ->
       Obj.magic box (Coq_multiplicative_expression_nt,((NT
         Coq_multiplicative_expression_nt)::((T STAR_t)::((NT
         Coq_cast_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (MUL,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_152 ->
       Obj.magic box (Coq_multiplicative_expression_nt,((NT
         Coq_cast_expression_nt)::[])) (fun expr -> expr)
     | Prod_151 ->
       Obj.magic box (Coq_logical_OR_expression_nt,((NT
         Coq_logical_OR_expression_nt)::((T BARBAR_t)::((NT
         Coq_logical_AND_expression_nt)::[])))) (fun expr1 _2 expr2 ->
         (BINARY (OR, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_150 ->
       Obj.magic box (Coq_logical_OR_expression_nt,((NT
         Coq_logical_AND_expression_nt)::[])) (fun expr -> expr)
     | Prod_149 ->
       Obj.magic box (Coq_logical_AND_expression_nt,((NT
         Coq_logical_AND_expression_nt)::((T ANDAND_t)::((NT
         Coq_inclusive_OR_expression_nt)::[])))) (fun expr1 _2 expr2 ->
         (BINARY (AND, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_148 ->
       Obj.magic box (Coq_logical_AND_expression_nt,((NT
         Coq_inclusive_OR_expression_nt)::[])) (fun expr -> expr)
     | Prod_147 ->
       Obj.magic box (Coq_labeled_statement_statement_safe__nt,((T
         DEFAULT_t)::((T COLON_t)::((NT Coq_statement_safe_nt)::[]))))
         (fun loc _2 stmt -> DEFAULT (stmt, loc))
     | Prod_146 ->
       Obj.magic box (Coq_labeled_statement_statement_safe__nt,((T
         CASE_t)::((NT Coq_constant_expression_nt)::((T COLON_t)::((NT
         Coq_statement_safe_nt)::[]))))) (fun loc expr _3 stmt -> CASE
         ((fst expr), stmt, loc))
     | Prod_145 ->
       Obj.magic box (Coq_labeled_statement_statement_safe__nt,((T
         OTHER_NAME_t)::((T COLON_t)::((NT Coq_statement_safe_nt)::[]))))
         (fun lbl _2 stmt -> LABEL ((fst lbl), stmt, (snd lbl)))
     | Prod_144 ->
       Obj.magic box (Coq_labeled_statement_statement_dangerous__nt,((T
         DEFAULT_t)::((T COLON_t)::((NT Coq_statement_dangerous_nt)::[]))))
         (fun loc _2 stmt -> DEFAULT (stmt, loc))
     | Prod_143 ->
       Obj.magic box (Coq_labeled_statement_statement_dangerous__nt,((T
         CASE_t)::((NT Coq_constant_expression_nt)::((T COLON_t)::((NT
         Coq_statement_dangerous_nt)::[]))))) (fun loc expr _3 stmt -> CASE
         ((fst expr), stmt, loc))
     | Prod_142 ->
       Obj.magic box (Coq_labeled_statement_statement_dangerous__nt,((T
         OTHER_NAME_t)::((T COLON_t)::((NT
         Coq_statement_dangerous_nt)::[])))) (fun lbl _2 stmt -> LABEL
         ((fst lbl), stmt, (snd lbl)))
     | Prod_141 ->
       Obj.magic box (Coq_jump_statement_nt,((T RETURN_t)::((T
         SEMICOLON_t)::[]))) (fun loc _2 -> RETURN (None, loc))
     | Prod_140 ->
       Obj.magic box (Coq_jump_statement_nt,((T RETURN_t)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::[])))) (fun loc expr _3 ->
         RETURN ((Some (fst expr)), loc))
     | Prod_139 ->
       Obj.magic box (Coq_jump_statement_nt,((T BREAK_t)::((T
         SEMICOLON_t)::[]))) (fun loc _2 -> BREAK loc)
     | Prod_138 ->
       Obj.magic box (Coq_jump_statement_nt,((T CONTINUE_t)::((T
         SEMICOLON_t)::[]))) (fun loc _2 -> CONTINUE loc)
     | Prod_137 ->
       Obj.magic box (Coq_jump_statement_nt,((T GOTO_t)::((T
         OTHER_NAME_t)::((T SEMICOLON_t)::[])))) (fun loc id _3 -> GOTO
         ((fst id), loc))
     | Prod_136 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((T SEMICOLON_t)::((T
         RPAREN_t)::((NT Coq_statement_safe_nt)::[])))))))
         (fun loc _2 _3 _4 _5 stmt -> FOR (None, None, None, stmt, loc))
     | Prod_135 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((T
         SEMICOLON_t)::((T RPAREN_t)::((NT Coq_statement_safe_nt)::[])))))))
         (fun loc _2 decl1 _4 _5 stmt -> FOR ((Some (FC_DECL decl1)), None,
         None, stmt, loc))
     | Prod_134 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((T SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[]))))))))
         (fun loc _2 expr1 _4 _5 _6 stmt -> FOR ((Some (FC_EXP (fst expr1))),
         None, None, stmt, loc))
     | Prod_133 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[]))))))))
         (fun loc _2 _3 expr2 _5 _6 stmt -> FOR (None, (Some (fst expr2)),
         None, stmt, loc))
     | Prod_132 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[]))))))))
         (fun loc _2 decl1 expr2 _5 _6 stmt -> FOR ((Some (FC_DECL decl1)),
         (Some (fst expr2)), None, stmt, loc))
     | Prod_131 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((NT Coq_expression_nt)::((T SEMICOLON_t)::((T
         RPAREN_t)::((NT Coq_statement_safe_nt)::[])))))))))
         (fun loc _2 expr1 _4 expr2 _6 _7 stmt -> FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), None, stmt, loc))
     | Prod_130 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[]))))))))
         (fun loc _2 _3 _4 expr3 _6 stmt -> FOR (None, None, (Some
         (fst expr3)), stmt, loc))
     | Prod_129 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((T
         SEMICOLON_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[]))))))))
         (fun loc _2 decl1 _4 expr3 _6 stmt -> FOR ((Some (FC_DECL decl1)),
         None, (Some (fst expr3)), stmt, loc))
     | Prod_128 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((T SEMICOLON_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_safe_nt)::[])))))))))
         (fun loc _2 expr1 _4 _5 expr3 _7 stmt -> FOR ((Some (FC_EXP
         (fst expr1))), None, (Some (fst expr3)), stmt, loc))
     | Prod_127 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_safe_nt)::[])))))))))
         (fun loc _2 _3 expr2 _5 expr3 _7 stmt -> FOR (None, (Some
         (fst expr2)), (Some (fst expr3)), stmt, loc))
     | Prod_126 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_safe_nt)::[])))))))))
         (fun loc _2 decl1 expr2 _5 expr3 _7 stmt -> FOR ((Some (FC_DECL
         decl1)), (Some (fst expr2)), (Some (fst expr3)), stmt, loc))
     | Prod_125 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((NT Coq_expression_nt)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_safe_nt)::[]))))))))))
         (fun loc _2 expr1 _4 expr2 _6 expr3 _8 stmt -> FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), (Some (fst expr3)), stmt, loc))
     | Prod_124 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         DO_t)::((NT Coq_statement_dangerous_nt)::((T WHILE_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((T
         SEMICOLON_t)::[])))))))) (fun loc stmt _3 _4 expr _6 _7 -> DOWHILE
         ((fst expr), stmt, loc))
     | Prod_123 ->
       Obj.magic box (Coq_iteration_statement_statement_safe__nt,((T
         WHILE_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_safe_nt)::[]))))))
         (fun loc _2 expr _4 stmt -> WHILE ((fst expr), stmt, loc))
     | Prod_122 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((T SEMICOLON_t)::((T
         RPAREN_t)::((NT Coq_statement_dangerous_nt)::[])))))))
         (fun loc _2 _3 _4 _5 stmt -> FOR (None, None, None, stmt, loc))
     | Prod_121 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((T
         SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[])))))))
         (fun loc _2 decl1 _4 _5 stmt -> FOR ((Some (FC_DECL decl1)), None,
         None, stmt, loc))
     | Prod_120 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((T SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))
         (fun loc _2 expr1 _4 _5 _6 stmt -> FOR ((Some (FC_EXP (fst expr1))),
         None, None, stmt, loc))
     | Prod_119 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))
         (fun loc _2 _3 expr2 _5 _6 stmt -> FOR (None, (Some (fst expr2)),
         None, stmt, loc))
     | Prod_118 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))
         (fun loc _2 decl1 expr2 _5 _6 stmt -> FOR ((Some (FC_DECL decl1)),
         (Some (fst expr2)), None, stmt, loc))
     | Prod_117 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((NT Coq_expression_nt)::((T SEMICOLON_t)::((T
         RPAREN_t)::((NT Coq_statement_dangerous_nt)::[])))))))))
         (fun loc _2 expr1 _4 expr2 _6 _7 stmt -> FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), None, stmt, loc))
     | Prod_116 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))
         (fun loc _2 _3 _4 expr3 _6 stmt -> FOR (None, None, (Some
         (fst expr3)), stmt, loc))
     | Prod_115 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((T
         SEMICOLON_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))
         (fun loc _2 decl1 _4 expr3 _6 stmt -> FOR ((Some (FC_DECL decl1)),
         None, (Some (fst expr3)), stmt, loc))
     | Prod_114 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((T SEMICOLON_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_dangerous_nt)::[])))))))))
         (fun loc _2 expr1 _4 _5 expr3 _7 stmt -> FOR ((Some (FC_EXP
         (fst expr1))), None, (Some (fst expr3)), stmt, loc))
     | Prod_113 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_dangerous_nt)::[])))))))))
         (fun loc _2 _3 expr2 _5 expr3 _7 stmt -> FOR (None, (Some
         (fst expr2)), (Some (fst expr3)), stmt, loc))
     | Prod_112 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_declaration_nt)::((NT
         Coq_expression_nt)::((T SEMICOLON_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_dangerous_nt)::[])))))))))
         (fun loc _2 decl1 expr2 _5 expr3 _7 stmt -> FOR ((Some (FC_DECL
         decl1)), (Some (fst expr2)), (Some (fst expr3)), stmt, loc))
     | Prod_111 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         FOR_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         SEMICOLON_t)::((NT Coq_expression_nt)::((T SEMICOLON_t)::((NT
         Coq_expression_nt)::((T RPAREN_t)::((NT
         Coq_statement_dangerous_nt)::[]))))))))))
         (fun loc _2 expr1 _4 expr2 _6 expr3 _8 stmt -> FOR ((Some (FC_EXP
         (fst expr1))), (Some (fst expr2)), (Some (fst expr3)), stmt, loc))
     | Prod_110 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         DO_t)::((NT Coq_statement_dangerous_nt)::((T WHILE_t)::((T
         LPAREN_t)::((NT Coq_expression_nt)::((T RPAREN_t)::((T
         SEMICOLON_t)::[])))))))) (fun loc stmt _3 _4 expr _6 _7 -> DOWHILE
         ((fst expr), stmt, loc))
     | Prod_109 ->
       Obj.magic box (Coq_iteration_statement_statement_dangerous__nt,((T
         WHILE_t)::((T LPAREN_t)::((NT Coq_expression_nt)::((T
         RPAREN_t)::((NT Coq_statement_dangerous_nt)::[]))))))
         (fun loc _2 expr _4 stmt -> WHILE ((fst expr), stmt, loc))
     | Prod_108 ->
       Obj.magic box (Coq_initializer_list_nt,((NT
         Coq_initializer_list_nt)::((T COMMA_t)::((NT
         Coq_c_initializer_nt)::[])))) (fun initq _2 init ->
         ([],init)::initq)
     | Prod_107 ->
       Obj.magic box (Coq_initializer_list_nt,((NT
         Coq_initializer_list_nt)::((T COMMA_t)::((NT
         Coq_designation_nt)::((NT Coq_c_initializer_nt)::[])))))
         (fun initq _2 design init -> (design,init)::initq)
     | Prod_106 ->
       Obj.magic box (Coq_initializer_list_nt,((NT
         Coq_c_initializer_nt)::[])) (fun init -> ([],init)::[])
     | Prod_105 ->
       Obj.magic box (Coq_initializer_list_nt,((NT Coq_designation_nt)::((NT
         Coq_c_initializer_nt)::[]))) (fun design init -> (design,init)::[])
     | Prod_104 ->
       Obj.magic box (Coq_init_declarator_list_nt,((NT
         Coq_init_declarator_list_nt)::((T COMMA_t)::((NT
         Coq_init_declarator_nt)::[])))) (fun initq _2 initt -> initt::initq)
     | Prod_103 ->
       Obj.magic box (Coq_init_declarator_list_nt,((NT
         Coq_init_declarator_nt)::[])) (fun init -> init::[])
     | Prod_102 ->
       Obj.magic box (Coq_init_declarator_nt,((NT Coq_declarator_nt)::((T
         EQ_t)::((NT Coq_c_initializer_nt)::[])))) (fun name _2 init ->
         Init_name (name, init))
     | Prod_101 ->
       Obj.magic box (Coq_init_declarator_nt,((NT Coq_declarator_nt)::[]))
         (fun name -> Init_name (name, NO_INIT))
     | Prod_100 ->
       Obj.magic box (Coq_inclusive_OR_expression_nt,((NT
         Coq_inclusive_OR_expression_nt)::((T BAR_t)::((NT
         Coq_exclusive_OR_expression_nt)::[])))) (fun expr1 _2 expr2 ->
         (BINARY (BOR, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_99 ->
       Obj.magic box (Coq_inclusive_OR_expression_nt,((NT
         Coq_exclusive_OR_expression_nt)::[])) (fun expr -> expr)
     | Prod_98 ->
       Obj.magic box (Coq_function_specifier_nt,((T INLINE_t)::[]))
         (fun loc -> loc)
     | Prod_97 ->
       Obj.magic box (Coq_function_definition_nt,((NT
         Coq_declaration_specifiers_nt)::((NT Coq_declarator_nt)::((NT
         Coq_compound_statement_nt)::[])))) (fun specs decl stmt -> FUNDEF
         ((fst specs), decl, stmt, (snd specs)))
     | Prod_96 ->
       Obj.magic box (Coq_external_declaration_nt,((NT
         Coq_declaration_nt)::[])) (fun def -> def)
     | Prod_95 ->
       Obj.magic box (Coq_external_declaration_nt,((NT
         Coq_function_definition_nt)::[])) (fun def -> def)
     | Prod_94 ->
       Obj.magic box (Coq_expression_statement_nt,((T SEMICOLON_t)::[]))
         (fun loc -> NOP loc)
     | Prod_93 ->
       Obj.magic box (Coq_expression_statement_nt,((NT
         Coq_expression_nt)::((T SEMICOLON_t)::[]))) (fun expr _2 ->
         COMPUTATION ((fst expr), (snd expr)))
     | Prod_92 ->
       Obj.magic box (Coq_expression_nt,((NT Coq_expression_nt)::((T
         COMMA_t)::((NT Coq_assignment_expression_nt)::[]))))
         (fun expr1 _2 expr2 -> (BINARY (COMMA, (fst expr1),
         (fst expr2))),(snd expr1))
     | Prod_91 ->
       Obj.magic box (Coq_expression_nt,((NT
         Coq_assignment_expression_nt)::[])) (fun expr -> expr)
     | Prod_90 ->
       Obj.magic box (Coq_exclusive_OR_expression_nt,((NT
         Coq_exclusive_OR_expression_nt)::((T HAT_t)::((NT
         AND_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY (XOR,
         (fst expr1), (fst expr2))),(snd expr1))
     | Prod_89 ->
       Obj.magic box (Coq_exclusive_OR_expression_nt,((NT
         AND_expression_nt)::[])) (fun expr -> expr)
     | Prod_88 ->
       Obj.magic box (Coq_equality_expression_nt,((NT
         Coq_equality_expression_nt)::((T NEQ_t)::((NT
         Coq_relational_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY
         (NE, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_87 ->
       Obj.magic box (Coq_equality_expression_nt,((NT
         Coq_equality_expression_nt)::((T EQEQ_t)::((NT
         Coq_relational_expression_nt)::[])))) (fun expr1 _2 expr2 -> (BINARY
         (EQ, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_86 ->
       Obj.magic box (Coq_equality_expression_nt,((NT
         Coq_relational_expression_nt)::[])) (fun expr -> expr)
     | Prod_85 ->
       Obj.magic box (Coq_enumerator_list_nt,((NT
         Coq_enumerator_list_nt)::((T COMMA_t)::((NT
         Coq_enumerator_nt)::[])))) (fun enumsq _2 enumst -> enumst::enumsq)
     | Prod_84 ->
       Obj.magic box (Coq_enumerator_list_nt,((NT Coq_enumerator_nt)::[]))
         (fun enum -> enum::[])
     | Prod_83 ->
       Obj.magic box (Coq_enumerator_nt,((NT
         Coq_enumeration_constant_nt)::((T EQ_t)::((NT
         Coq_constant_expression_nt)::[])))) (fun atom _2 expr ->
         ((fst atom),(Some (fst expr))),(snd atom))
     | Prod_82 ->
       Obj.magic box (Coq_enumerator_nt,((NT
         Coq_enumeration_constant_nt)::[])) (fun atom ->
         ((fst atom),None),(snd atom))
     | Prod_81 ->
       Obj.magic box (Coq_enumeration_constant_nt,((T VAR_NAME_t)::[]))
         (fun loc -> loc)
     | Prod_80 ->
       Obj.magic box (Coq_enum_specifier_nt,((T ENUM_t)::((T
         OTHER_NAME_t)::[]))) (fun loc name -> (Tenum ((Some (fst name)),
         None, [])),loc)
     | Prod_79 ->
       Obj.magic box (Coq_enum_specifier_nt,((T ENUM_t)::((T LBRACE_t)::((NT
         Coq_enumerator_list_nt)::((T COMMA_t)::((T RBRACE_t)::[]))))))
         (fun loc _2 enum_list _4 _5 -> (Tenum (None, (Some (rev enum_list)),
         [])),loc)
     | Prod_78 ->
       Obj.magic box (Coq_enum_specifier_nt,((T ENUM_t)::((T
         OTHER_NAME_t)::((T LBRACE_t)::((NT Coq_enumerator_list_nt)::((T
         COMMA_t)::((T RBRACE_t)::[])))))))
         (fun loc name _3 enum_list _5 _6 -> (Tenum ((Some (fst name)), (Some
         (rev enum_list)), [])),loc)
     | Prod_77 ->
       Obj.magic box (Coq_enum_specifier_nt,((T ENUM_t)::((T LBRACE_t)::((NT
         Coq_enumerator_list_nt)::((T RBRACE_t)::[])))))
         (fun loc _2 enum_list _4 -> (Tenum (None, (Some (rev enum_list)),
         [])),loc)
     | Prod_76 ->
       Obj.magic box (Coq_enum_specifier_nt,((T ENUM_t)::((T
         OTHER_NAME_t)::((T LBRACE_t)::((NT Coq_enumerator_list_nt)::((T
         RBRACE_t)::[])))))) (fun loc name _3 enum_list _5 -> (Tenum ((Some
         (fst name)), (Some (rev enum_list)), [])),loc)
     | Prod_75 ->
       Obj.magic box (Coq_direct_declarator_nt,((NT
         Coq_direct_declarator_nt)::((T LPAREN_t)::((T RPAREN_t)::[]))))
         (fun decl _2 _3 ->
         let Name (name, typ, attr, loc) = decl in
         Name (name, (PROTO (typ, ([],false))), attr, loc))
     | Prod_74 ->
       Obj.magic box (Coq_direct_declarator_nt,((NT
         Coq_direct_declarator_nt)::((T LPAREN_t)::((NT
         Coq_parameter_type_list_nt)::((T RPAREN_t)::[])))))
         (fun decl _2 params _4 ->
         let Name (name, typ, attr, loc) = decl in
         Name (name, (PROTO (typ, params)), attr, loc))
     | Prod_73 ->
       Obj.magic box (Coq_direct_declarator_nt,((NT
         Coq_direct_declarator_nt)::((T LBRACK_t)::((T RBRACK_t)::[]))))
         (fun decl _2 _3 ->
         let Name (name, typ, attr, loc) = decl in
         Name (name, (ARRAY (typ, [], [], None)), attr, loc))
     | Prod_72 ->
       Obj.magic box (Coq_direct_declarator_nt,((NT
         Coq_direct_declarator_nt)::((T LBRACK_t)::((NT
         Coq_type_qualifier_list_nt)::((T RBRACK_t)::[])))))
         (fun decl _2 quallst _4 ->
         let Name (name, typ, attr, loc) = decl in
         Name (name, (ARRAY (typ, (rev quallst), [], None)), attr, loc))
     | Prod_71 ->
       Obj.magic box (Coq_direct_declarator_nt,((NT
         Coq_direct_declarator_nt)::((T LBRACK_t)::((NT
         Coq_assignment_expression_nt)::((T RBRACK_t)::[])))))
         (fun decl _2 expr _4 ->
         let Name (name, typ, attr, loc) = decl in
         Name (name, (ARRAY (typ, [], [], (Some (fst expr)))), attr, loc))
     | Prod_70 ->
       Obj.magic box (Coq_direct_declarator_nt,((NT
         Coq_direct_declarator_nt)::((T LBRACK_t)::((NT
         Coq_type_qualifier_list_nt)::((NT Coq_assignment_expression_nt)::((T
         RBRACK_t)::[])))))) (fun decl _2 quallst expr _5 ->
         let Name (name, typ, attr, loc) = decl in
         Name (name, (ARRAY (typ, (rev quallst), [], (Some (fst expr)))),
         attr, loc))
     | Prod_69 ->
       Obj.magic box (Coq_direct_declarator_nt,((T LPAREN_t)::((NT
         Coq_declarator_nt)::((T RPAREN_t)::[])))) (fun _1 decl _3 -> decl)
     | Prod_68 ->
       Obj.magic box (Coq_direct_declarator_nt,((T VAR_NAME_t)::[]))
         (fun id -> Name ((fst id), JUSTBASE, [], (snd id)))
     | Prod_67 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LPAREN_t)::((T
         RPAREN_t)::[]))) (fun _1 _2 -> PROTO (JUSTBASE, ([],false)))
     | Prod_66 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::((T LPAREN_t)::((T
         RPAREN_t)::[])))) (fun typ _2 _3 -> PROTO (typ, ([],false)))
     | Prod_65 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LPAREN_t)::((NT
         Coq_parameter_type_list_nt)::((T RPAREN_t)::[]))))
         (fun _1 params _3 -> PROTO (JUSTBASE, params))
     | Prod_64 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::((T LPAREN_t)::((NT
         Coq_parameter_type_list_nt)::((T RPAREN_t)::[])))))
         (fun typ _2 params _4 -> PROTO (typ, params))
     | Prod_63 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LBRACK_t)::((T
         RBRACK_t)::[]))) (fun _1 _2 -> ARRAY (JUSTBASE, [], [], None))
     | Prod_62 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::((T LBRACK_t)::((T
         RBRACK_t)::[])))) (fun typ _2 _3 -> ARRAY (typ, [], [], None))
     | Prod_61 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LBRACK_t)::((NT
         Coq_type_qualifier_list_nt)::((T RBRACK_t)::[]))))
         (fun _1 cvspec _3 -> ARRAY (JUSTBASE, cvspec, [], None))
     | Prod_60 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::((T LBRACK_t)::((NT
         Coq_type_qualifier_list_nt)::((T RBRACK_t)::[])))))
         (fun typ _2 cvspec _4 -> ARRAY (typ, cvspec, [], None))
     | Prod_59 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LBRACK_t)::((NT
         Coq_assignment_expression_nt)::((T RBRACK_t)::[]))))
         (fun _1 expr _3 -> ARRAY (JUSTBASE, [], [], (Some (fst expr))))
     | Prod_58 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::((T LBRACK_t)::((NT
         Coq_assignment_expression_nt)::((T RBRACK_t)::[])))))
         (fun typ _2 expr _4 -> ARRAY (typ, [], [], (Some (fst expr))))
     | Prod_57 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LBRACK_t)::((NT
         Coq_type_qualifier_list_nt)::((NT Coq_assignment_expression_nt)::((T
         RBRACK_t)::[]))))) (fun _1 cvspec expr _4 -> ARRAY (JUSTBASE,
         cvspec, [], (Some (fst expr))))
     | Prod_56 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::((T LBRACK_t)::((NT
         Coq_type_qualifier_list_nt)::((NT Coq_assignment_expression_nt)::((T
         RBRACK_t)::[])))))) (fun typ _2 cvspec expr _5 -> ARRAY (typ,
         cvspec, [], (Some (fst expr))))
     | Prod_55 ->
       Obj.magic box (Coq_direct_abstract_declarator_nt,((T LPAREN_t)::((NT
         Coq_abstract_declarator_nt)::((T RPAREN_t)::[])))) (fun _1 typ _3 ->
         typ)
     | Prod_54 ->
       Obj.magic box (Coq_designator_list_nt,((NT
         Coq_designator_list_nt)::((NT Coq_designator_nt)::[])))
         (fun designq designt -> designt::designq)
     | Prod_53 ->
       Obj.magic box (Coq_designator_list_nt,((NT Coq_designator_nt)::[]))
         (fun design -> design::[])
     | Prod_52 ->
       Obj.magic box (Coq_designator_nt,((T DOT_t)::((T OTHER_NAME_t)::[])))
         (fun _1 id -> INFIELD_INIT (fst id))
     | Prod_51 ->
       Obj.magic box (Coq_designator_nt,((T LBRACK_t)::((NT
         Coq_constant_expression_nt)::((T RBRACK_t)::[]))))
         (fun _1 expr _3 -> ATINDEX_INIT (fst expr))
     | Prod_50 ->
       Obj.magic box (Coq_designation_nt,((NT Coq_designator_list_nt)::((T
         EQ_t)::[]))) (fun design _2 -> rev design)
     | Prod_49 ->
       Obj.magic box (Coq_declarator_nt,((NT Coq_pointer_nt)::((NT
         Coq_direct_declarator_nt)::[]))) (fun pt decl ->
         let Name (name, typ, attr, c) = decl in
         Name (name, (fst pt typ), attr, (snd pt)))
     | Prod_48 ->
       Obj.magic box (Coq_declarator_nt,((NT Coq_direct_declarator_nt)::[]))
         (fun decl -> decl)
     | Prod_47 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_function_specifier_nt)::[])) (fun loc -> (SpecInline::[]),loc)
     | Prod_46 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_function_specifier_nt)::((NT
         Coq_declaration_specifiers_nt)::[]))) (fun loc rest ->
         (SpecInline::(fst rest)),loc)
     | Prod_45 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_type_qualifier_nt)::[])) (fun qual -> ((SpecCV
         (fst qual))::[]),(snd qual))
     | Prod_44 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_type_qualifier_nt)::((NT Coq_declaration_specifiers_nt)::[])))
         (fun qual rest -> ((SpecCV (fst qual))::(fst rest)),(snd qual))
     | Prod_43 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_type_specifier_nt)::[])) (fun typ -> ((SpecType
         (fst typ))::[]),(snd typ))
     | Prod_42 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_type_specifier_nt)::((NT Coq_declaration_specifiers_nt)::[])))
         (fun typ rest -> ((SpecType (fst typ))::(fst rest)),(snd typ))
     | Prod_41 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_storage_class_specifier_nt)::[])) (fun storage -> ((SpecStorage
         (fst storage))::[]),(snd storage))
     | Prod_40 ->
       Obj.magic box (Coq_declaration_specifiers_nt,((NT
         Coq_storage_class_specifier_nt)::((NT
         Coq_declaration_specifiers_nt)::[]))) (fun storage rest ->
         ((SpecStorage (fst storage))::(fst rest)),(snd storage))
     | Prod_39 ->
       Obj.magic box (Coq_declaration_nt,((NT
         Coq_declaration_specifiers_nt)::((T SEMICOLON_t)::[])))
         (fun decspec _2 -> DECDEF (((fst decspec),[]), (snd decspec)))
     | Prod_38 ->
       Obj.magic box (Coq_declaration_nt,((NT
         Coq_declaration_specifiers_nt)::((NT
         Coq_init_declarator_list_nt)::((T SEMICOLON_t)::[]))))
         (fun decspec decls _3 -> DECDEF (((fst decspec),(rev decls)),
         (snd decspec)))
     | Prod_37 ->
       Obj.magic box (Coq_constant_expression_nt,((NT
         Coq_conditional_expression_nt)::[])) (fun expr -> expr)
     | Prod_36 ->
       Obj.magic box (Coq_conditional_expression_nt,((NT
         Coq_logical_OR_expression_nt)::((T QUESTION_t)::((NT
         Coq_expression_nt)::((T COLON_t)::((NT
         Coq_conditional_expression_nt)::[]))))))
         (fun expr1 _2 expr2 _4 expr3 -> (QUESTION ((fst expr1), (fst expr2),
         (fst expr3))),(snd expr1))
     | Prod_35 ->
       Obj.magic box (Coq_conditional_expression_nt,((NT
         Coq_logical_OR_expression_nt)::[])) (fun expr -> expr)
     | Prod_34 ->
       Obj.magic box (Coq_compound_statement_nt,((T LBRACE_t)::((T
         RBRACE_t)::[]))) (fun loc _2 -> BLOCK ([], loc))
     | Prod_33 ->
       Obj.magic box (Coq_compound_statement_nt,((T LBRACE_t)::((NT
         Coq_block_item_list_nt)::((T RBRACE_t)::[])))) (fun loc lst _3 ->
         BLOCK ((rev lst), loc))
     | Prod_32 ->
       Obj.magic box (Coq_cast_expression_nt,((T LPAREN_t)::((NT
         Coq_type_name_nt)::((T RPAREN_t)::((NT
         Coq_cast_expression_nt)::[]))))) (fun loc typ _3 expr -> (CAST (typ,
         (SINGLE_INIT (fst expr)))),loc)
     | Prod_31 ->
       Obj.magic box (Coq_cast_expression_nt,((NT
         Coq_unary_expression_nt)::[])) (fun expr -> expr)
     | Prod_30 ->
       Obj.magic box (Coq_c_initializer_nt,((T LBRACE_t)::((NT
         Coq_initializer_list_nt)::((T COMMA_t)::((T RBRACE_t)::[])))))
         (fun _1 init _3 _4 -> COMPOUND_INIT (rev init))
     | Prod_29 ->
       Obj.magic box (Coq_c_initializer_nt,((T LBRACE_t)::((NT
         Coq_initializer_list_nt)::((T RBRACE_t)::[])))) (fun _1 init _3 ->
         COMPOUND_INIT (rev init))
     | Prod_28 ->
       Obj.magic box (Coq_c_initializer_nt,((NT
         Coq_assignment_expression_nt)::[])) (fun expr -> SINGLE_INIT
         (fst expr))
     | Prod_27 ->
       Obj.magic box (Coq_block_item_list_nt,((NT
         Coq_block_item_list_nt)::((NT Coq_block_item_nt)::[])))
         (fun stmtq stmtt -> stmtt::stmtq)
     | Prod_26 ->
       Obj.magic box (Coq_block_item_list_nt,((NT Coq_block_item_nt)::[]))
         (fun stmt -> stmt::[])
     | Prod_25 ->
       Obj.magic box (Coq_block_item_nt,((NT
         Coq_statement_dangerous_nt)::[])) (fun stmt -> stmt)
     | Prod_24 ->
       Obj.magic box (Coq_block_item_nt,((NT Coq_declaration_nt)::[]))
         (fun decl -> DEFINITION decl)
     | Prod_23 ->
       Obj.magic box (Coq_assignment_operator_nt,((T AND_ASSIGN_t)::[]))
         (fun _1 -> BAND_ASSIGN)
     | Prod_22 ->
       Obj.magic box (Coq_assignment_operator_nt,((T OR_ASSIGN_t)::[]))
         (fun _1 -> BOR_ASSIGN)
     | Prod_21 ->
       Obj.magic box (Coq_assignment_operator_nt,((T XOR_ASSIGN_t)::[]))
         (fun _1 -> XOR_ASSIGN)
     | Prod_20 ->
       Obj.magic box (Coq_assignment_operator_nt,((T RIGHT_ASSIGN_t)::[]))
         (fun _1 -> SHR_ASSIGN)
     | Prod_19 ->
       Obj.magic box (Coq_assignment_operator_nt,((T LEFT_ASSIGN_t)::[]))
         (fun _1 -> SHL_ASSIGN)
     | Prod_18 ->
       Obj.magic box (Coq_assignment_operator_nt,((T SUB_ASSIGN_t)::[]))
         (fun _1 -> SUB_ASSIGN)
     | Prod_17 ->
       Obj.magic box (Coq_assignment_operator_nt,((T ADD_ASSIGN_t)::[]))
         (fun _1 -> ADD_ASSIGN)
     | Prod_16 ->
       Obj.magic box (Coq_assignment_operator_nt,((T MOD_ASSIGN_t)::[]))
         (fun _1 -> MOD_ASSIGN)
     | Prod_15 ->
       Obj.magic box (Coq_assignment_operator_nt,((T DIV_ASSIGN_t)::[]))
         (fun _1 -> DIV_ASSIGN)
     | Prod_14 ->
       Obj.magic box (Coq_assignment_operator_nt,((T MUL_ASSIGN_t)::[]))
         (fun _1 -> MUL_ASSIGN)
     | Prod_13 ->
       Obj.magic box (Coq_assignment_operator_nt,((T EQ_t)::[])) (fun _1 ->
         ASSIGN)
     | Prod_12 ->
       Obj.magic box (Coq_assignment_expression_nt,((NT
         Coq_unary_expression_nt)::((NT Coq_assignment_operator_nt)::((NT
         Coq_assignment_expression_nt)::[])))) (fun expr1 op expr2 -> (BINARY
         (op, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_11 ->
       Obj.magic box (Coq_assignment_expression_nt,((NT
         Coq_conditional_expression_nt)::[])) (fun expr -> expr)
     | Prod_10 ->
       Obj.magic box (Coq_argument_expression_list_nt,((NT
         Coq_argument_expression_list_nt)::((T COMMA_t)::((NT
         Coq_assignment_expression_nt)::[])))) (fun exprq _2 exprt ->
         (fst exprt)::exprq)
     | Prod_9 ->
       Obj.magic box (Coq_argument_expression_list_nt,((NT
         Coq_assignment_expression_nt)::[])) (fun expr -> (fst expr)::[])
     | Prod_8 ->
       Obj.magic box (Coq_additive_expression_nt,((NT
         Coq_additive_expression_nt)::((T MINUS_t)::((NT
         Coq_multiplicative_expression_nt)::[])))) (fun expr1 _2 expr2 ->
         (BINARY (SUB, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_7 ->
       Obj.magic box (Coq_additive_expression_nt,((NT
         Coq_additive_expression_nt)::((T PLUS_t)::((NT
         Coq_multiplicative_expression_nt)::[])))) (fun expr1 _2 expr2 ->
         (BINARY (ADD, (fst expr1), (fst expr2))),(snd expr1))
     | Prod_6 ->
       Obj.magic box (Coq_additive_expression_nt,((NT
         Coq_multiplicative_expression_nt)::[])) (fun expr -> expr)
     | Prod_5 ->
       Obj.magic box (Coq_abstract_declarator_nt,((NT
         Coq_direct_abstract_declarator_nt)::[])) (fun typ -> typ)
     | Prod_4 ->
       Obj.magic box (Coq_abstract_declarator_nt,((NT Coq_pointer_nt)::((NT
         Coq_direct_abstract_declarator_nt)::[]))) (fun pt typ -> fst pt typ)
     | Prod_3 ->
       Obj.magic box (Coq_abstract_declarator_nt,((NT Coq_pointer_nt)::[]))
         (fun pt -> fst pt JUSTBASE)
     | Prod_2 ->
       Obj.magic box (AND_expression_nt,((NT AND_expression_nt)::((T
         AND_t)::((NT Coq_equality_expression_nt)::[]))))
         (fun expr1 _2 expr2 -> (BINARY (BAND, (fst expr1),
         (fst expr2))),(snd expr1))
     | Prod_1 ->
       Obj.magic box (AND_expression_nt,((NT
         Coq_equality_expression_nt)::[])) (fun expr -> expr))
  
  (** val prod_lhs : production -> nonterminal **)
  
  let prod_lhs p =
    fst (projT1 (prod_contents p))
  
  (** val prod_rhs : production -> symbol list **)
  
  let prod_rhs p =
    snd (projT1 (prod_contents p))
  
  (** val prod_action : production -> symbol_semantic_type arrows **)
  
  let prod_action p =
    projT2 (prod_contents p)
  
  (** val start_symbol : symbol **)
  
  let start_symbol =
    NT Coq_translation_unit_file_nt
  
  type token = (terminal, symbol_semantic_type) sigT
  
  type parse_tree =
  | Terminal_pt of terminal * symbol_semantic_type
  | Non_terminal_pt of production * token list * tuple * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of token list * symbol * symbol_semantic_type * parse_tree
     * token list * symbol list * tuple * parse_tree_list
  
  (** val parse_tree_rect :
      (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list
      -> tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
      symbol_semantic_type -> parse_tree -> 'a1 **)
  
  let parse_tree_rect f f0 head_symbol word semantic_value = function
  | Terminal_pt (x, x0) -> f x x0
  | Non_terminal_pt (x, x0, x1, x2) -> f0 x x0 x1 x2
  
  (** val parse_tree_rec :
      (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list
      -> tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
      symbol_semantic_type -> parse_tree -> 'a1 **)
  
  let parse_tree_rec f f0 head_symbol word semantic_value = function
  | Terminal_pt (x, x0) -> f x x0
  | Non_terminal_pt (x, x0, x1, x2) -> f0 x x0 x1 x2
  
  (** val parse_tree_list_rect :
      'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
      token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
      symbol list -> token list -> tuple -> parse_tree_list -> 'a1 **)
  
  let rec parse_tree_list_rect f f0 head_symbols word semantic_values = function
  | Nil_ptl -> f
  | Cons_ptl
      (wordt, head_symbolt, semantic_valuet, p0, wordq, head_symbolsq,
       semantic_valuesq, p1) ->
    f0 wordt head_symbolt semantic_valuet p0 wordq head_symbolsq
      semantic_valuesq p1
      (parse_tree_list_rect f f0 head_symbolsq wordq semantic_valuesq p1)
  
  (** val parse_tree_list_rec :
      'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
      token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
      symbol list -> token list -> tuple -> parse_tree_list -> 'a1 **)
  
  let rec parse_tree_list_rec f f0 head_symbols word semantic_values = function
  | Nil_ptl -> f
  | Cons_ptl
      (wordt, head_symbolt, semantic_valuet, p0, wordq, head_symbolsq,
       semantic_valuesq, p1) ->
    f0 wordt head_symbolt semantic_valuet p0 wordq head_symbolsq
      semantic_valuesq p1
      (parse_tree_list_rec f f0 head_symbolsq wordq semantic_valuesq p1)
  
  (** val parse_tree_size :
      symbol -> token list -> symbol_semantic_type -> parse_tree -> nat **)
  
  let rec parse_tree_size head_symbol word sem = function
  | Terminal_pt (t0, sem0) -> O
  | Non_terminal_pt (p, word0, semantic_values, l) ->
    parse_tree_list_size (prod_rhs p) word0 semantic_values l
  
  (** val parse_tree_list_size :
      symbol list -> token list -> tuple -> parse_tree_list -> nat **)
  
  and parse_tree_list_size head_symbols word sems = function
  | Nil_ptl -> O
  | Cons_ptl
      (wordt, head_symbolt, semantic_valuet, t0, wordq, head_symbolsq,
       semantic_valuesq, q) ->
    plus (parse_tree_size head_symbolt wordt semantic_valuet t0) (S
      (parse_tree_list_size head_symbolsq wordq semantic_valuesq q))
 end
module Coq__1 = Gram

module Aut = 
 struct 
  module Gram = Gram
  
  module GramDefs = Gram
  
  (** val nullable_nterm : Coq__1.nonterminal -> bool **)
  
  let nullable_nterm nt =
    false
  
  (** val first_nterm : Coq__1.nonterminal -> Coq__1.terminal list **)
  
  let first_nterm = function
  | Coq__1.Coq_abstract_declarator_nt ->
    Coq__1.STAR_t::(Coq__1.LPAREN_t::(Coq__1.LBRACK_t::[]))
  | Coq__1.Coq_assignment_operator_nt ->
    Coq__1.XOR_ASSIGN_t::(Coq__1.SUB_ASSIGN_t::(Coq__1.RIGHT_ASSIGN_t::(Coq__1.OR_ASSIGN_t::(Coq__1.MUL_ASSIGN_t::(Coq__1.MOD_ASSIGN_t::(Coq__1.LEFT_ASSIGN_t::(Coq__1.EQ_t::(Coq__1.DIV_ASSIGN_t::(Coq__1.AND_ASSIGN_t::(Coq__1.ADD_ASSIGN_t::[]))))))))))
  | Coq__1.Coq_block_item_nt ->
    Coq__1.WHILE_t::(Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.VAR_NAME_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.TILDE_t::(Coq__1.SWITCH_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.SEMICOLON_t::(Coq__1.RETURN_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.PLUS_t::(Coq__1.OTHER_NAME_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.LONG_t::(Coq__1.LBRACE_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.INC_t::(Coq__1.IF_t::(Coq__1.GOTO_t::(Coq__1.FOR_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.DO_t::(Coq__1.DEFAULT_t::(Coq__1.DEC_t::(Coq__1.CONTINUE_t::(Coq__1.CONSTANT_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.CASE_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BREAK_t::(Coq__1.BOOL_t::(Coq__1.BANG_t::(Coq__1.AUTO_t::(Coq__1.AND_t::[])))))))))))))))))))))))))))))))))))))))))))))))))
  | Coq__1.Coq_block_item_list_nt ->
    Coq__1.WHILE_t::(Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.VAR_NAME_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.TILDE_t::(Coq__1.SWITCH_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.SEMICOLON_t::(Coq__1.RETURN_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.PLUS_t::(Coq__1.OTHER_NAME_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.LONG_t::(Coq__1.LBRACE_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.INC_t::(Coq__1.IF_t::(Coq__1.GOTO_t::(Coq__1.FOR_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.DO_t::(Coq__1.DEFAULT_t::(Coq__1.DEC_t::(Coq__1.CONTINUE_t::(Coq__1.CONSTANT_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.CASE_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BREAK_t::(Coq__1.BOOL_t::(Coq__1.BANG_t::(Coq__1.AUTO_t::(Coq__1.AND_t::[])))))))))))))))))))))))))))))))))))))))))))))))))
  | Coq__1.Coq_c_initializer_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.TILDE_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.PLUS_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.LBRACE_t::(Coq__1.INC_t::(Coq__1.DEC_t::(Coq__1.CONSTANT_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BANG_t::(Coq__1.AND_t::[])))))))))))))
  | Coq__1.Coq_compound_statement_nt -> Coq__1.LBRACE_t::[]
  | Coq__1.Coq_declaration_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_declaration_specifiers_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_declarator_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.STAR_t::(Coq__1.LPAREN_t::[]))
  | Coq__1.Coq_designation_nt -> Coq__1.LBRACK_t::(Coq__1.DOT_t::[])
  | Coq__1.Coq_designator_nt -> Coq__1.LBRACK_t::(Coq__1.DOT_t::[])
  | Coq__1.Coq_designator_list_nt -> Coq__1.LBRACK_t::(Coq__1.DOT_t::[])
  | Coq__1.Coq_direct_abstract_declarator_nt ->
    Coq__1.LPAREN_t::(Coq__1.LBRACK_t::[])
  | Coq__1.Coq_direct_declarator_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.LPAREN_t::[])
  | Coq__1.Coq_enum_specifier_nt -> Coq__1.ENUM_t::[]
  | Coq__1.Coq_enumeration_constant_nt -> Coq__1.VAR_NAME_t::[]
  | Coq__1.Coq_enumerator_nt -> Coq__1.VAR_NAME_t::[]
  | Coq__1.Coq_enumerator_list_nt -> Coq__1.VAR_NAME_t::[]
  | Coq__1.Coq_expression_statement_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.TILDE_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.SEMICOLON_t::(Coq__1.PLUS_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.INC_t::(Coq__1.DEC_t::(Coq__1.CONSTANT_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BANG_t::(Coq__1.AND_t::[])))))))))))))
  | Coq__1.Coq_external_declaration_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_function_definition_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_function_specifier_nt -> Coq__1.INLINE_t::[]
  | Coq__1.Coq_init_declarator_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.STAR_t::(Coq__1.LPAREN_t::[]))
  | Coq__1.Coq_init_declarator_list_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.STAR_t::(Coq__1.LPAREN_t::[]))
  | Coq__1.Coq_initializer_list_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.TILDE_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.PLUS_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.LBRACK_t::(Coq__1.LBRACE_t::(Coq__1.INC_t::(Coq__1.DOT_t::(Coq__1.DEC_t::(Coq__1.CONSTANT_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BANG_t::(Coq__1.AND_t::[])))))))))))))))
  | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
    Coq__1.WHILE_t::(Coq__1.FOR_t::(Coq__1.DO_t::[]))
  | Coq__1.Coq_iteration_statement_statement_safe__nt ->
    Coq__1.WHILE_t::(Coq__1.FOR_t::(Coq__1.DO_t::[]))
  | Coq__1.Coq_jump_statement_nt ->
    Coq__1.RETURN_t::(Coq__1.GOTO_t::(Coq__1.CONTINUE_t::(Coq__1.BREAK_t::[])))
  | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
    Coq__1.OTHER_NAME_t::(Coq__1.DEFAULT_t::(Coq__1.CASE_t::[]))
  | Coq__1.Coq_labeled_statement_statement_safe__nt ->
    Coq__1.OTHER_NAME_t::(Coq__1.DEFAULT_t::(Coq__1.CASE_t::[]))
  | Coq__1.Coq_parameter_declaration_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_parameter_list_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_parameter_type_list_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_pointer_nt -> Coq__1.STAR_t::[]
  | Coq__1.Coq_postfix_expression_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.LPAREN_t::(Coq__1.CONSTANT_t::(Coq__1.BUILTIN_VA_ARG_t::[])))
  | Coq__1.Coq_primary_expression_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.LPAREN_t::(Coq__1.CONSTANT_t::[]))
  | Coq__1.Coq_selection_statement_dangerous_nt ->
    Coq__1.SWITCH_t::(Coq__1.IF_t::[])
  | Coq__1.Coq_selection_statement_safe_nt ->
    Coq__1.SWITCH_t::(Coq__1.IF_t::[])
  | Coq__1.Coq_specifier_qualifier_list_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.STRUCT_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.FLOAT_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::[]))))))))))))))))
  | Coq__1.Coq_statement_dangerous_nt ->
    Coq__1.WHILE_t::(Coq__1.VAR_NAME_t::(Coq__1.TILDE_t::(Coq__1.SWITCH_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.SEMICOLON_t::(Coq__1.RETURN_t::(Coq__1.PLUS_t::(Coq__1.OTHER_NAME_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.LBRACE_t::(Coq__1.INC_t::(Coq__1.IF_t::(Coq__1.GOTO_t::(Coq__1.FOR_t::(Coq__1.DO_t::(Coq__1.DEFAULT_t::(Coq__1.DEC_t::(Coq__1.CONTINUE_t::(Coq__1.CONSTANT_t::(Coq__1.CASE_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BREAK_t::(Coq__1.BANG_t::(Coq__1.AND_t::[]))))))))))))))))))))))))))
  | Coq__1.Coq_statement_safe_nt ->
    Coq__1.WHILE_t::(Coq__1.VAR_NAME_t::(Coq__1.TILDE_t::(Coq__1.SWITCH_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.SEMICOLON_t::(Coq__1.RETURN_t::(Coq__1.PLUS_t::(Coq__1.OTHER_NAME_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.LBRACE_t::(Coq__1.INC_t::(Coq__1.IF_t::(Coq__1.GOTO_t::(Coq__1.FOR_t::(Coq__1.DO_t::(Coq__1.DEFAULT_t::(Coq__1.DEC_t::(Coq__1.CONTINUE_t::(Coq__1.CONSTANT_t::(Coq__1.CASE_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BREAK_t::(Coq__1.BANG_t::(Coq__1.AND_t::[]))))))))))))))))))))))))))
  | Coq__1.Coq_storage_class_specifier_nt ->
    Coq__1.TYPEDEF_t::(Coq__1.STATIC_t::(Coq__1.REGISTER_t::(Coq__1.EXTERN_t::(Coq__1.AUTO_t::[]))))
  | Coq__1.Coq_struct_declaration_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.STRUCT_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.FLOAT_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::[]))))))))))))))))
  | Coq__1.Coq_struct_declaration_list_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.STRUCT_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.FLOAT_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::[]))))))))))))))))
  | Coq__1.Coq_struct_declarator_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.STAR_t::(Coq__1.LPAREN_t::(Coq__1.COLON_t::[])))
  | Coq__1.Coq_struct_declarator_list_nt ->
    Coq__1.VAR_NAME_t::(Coq__1.STAR_t::(Coq__1.LPAREN_t::(Coq__1.COLON_t::[])))
  | Coq__1.Coq_struct_or_union_nt -> Coq__1.UNION_t::(Coq__1.STRUCT_t::[])
  | Coq__1.Coq_struct_or_union_specifier_nt ->
    Coq__1.UNION_t::(Coq__1.STRUCT_t::[])
  | Coq__1.Coq_translation_unit_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_translation_unit_file_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.TYPEDEF_t::(Coq__1.STRUCT_t::(Coq__1.STATIC_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.REGISTER_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.INLINE_t::(Coq__1.FLOAT_t::(Coq__1.EXTERN_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::(Coq__1.AUTO_t::[]))))))))))))))))))))))
  | Coq__1.Coq_type_name_nt ->
    Coq__1.VOLATILE_t::(Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.STRUCT_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.RESTRICT_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.FLOAT_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CONST_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::[]))))))))))))))))
  | Coq__1.Coq_type_qualifier_nt ->
    Coq__1.VOLATILE_t::(Coq__1.RESTRICT_t::(Coq__1.CONST_t::[]))
  | Coq__1.Coq_type_qualifier_list_nt ->
    Coq__1.VOLATILE_t::(Coq__1.RESTRICT_t::(Coq__1.CONST_t::[]))
  | Coq__1.Coq_type_specifier_nt ->
    Coq__1.VOID_t::(Coq__1.UNSIGNED_t::(Coq__1.UNION_t::(Coq__1.TYPEDEF_NAME_t::(Coq__1.STRUCT_t::(Coq__1.SIGNED_t::(Coq__1.SHORT_t::(Coq__1.LONG_t::(Coq__1.INT_t::(Coq__1.FLOAT_t::(Coq__1.ENUM_t::(Coq__1.DOUBLE_t::(Coq__1.CHAR_t::(Coq__1.BOOL_t::[])))))))))))))
  | Coq__1.Coq_unary_operator_nt ->
    Coq__1.TILDE_t::(Coq__1.STAR_t::(Coq__1.PLUS_t::(Coq__1.MINUS_t::(Coq__1.BANG_t::(Coq__1.AND_t::[])))))
  | _ ->
    Coq__1.VAR_NAME_t::(Coq__1.TILDE_t::(Coq__1.STAR_t::(Coq__1.SIZEOF_t::(Coq__1.PLUS_t::(Coq__1.MINUS_t::(Coq__1.LPAREN_t::(Coq__1.INC_t::(Coq__1.DEC_t::(Coq__1.CONSTANT_t::(Coq__1.BUILTIN_VA_ARG_t::(Coq__1.BANG_t::(Coq__1.AND_t::[]))))))))))))
  
  type noninitstate' =
  | Nis_504
  | Nis_503
  | Nis_502
  | Nis_501
  | Nis_500
  | Nis_499
  | Nis_498
  | Nis_497
  | Nis_496
  | Nis_495
  | Nis_494
  | Nis_493
  | Nis_492
  | Nis_491
  | Nis_490
  | Nis_489
  | Nis_488
  | Nis_487
  | Nis_486
  | Nis_485
  | Nis_484
  | Nis_483
  | Nis_482
  | Nis_481
  | Nis_480
  | Nis_479
  | Nis_478
  | Nis_477
  | Nis_476
  | Nis_475
  | Nis_474
  | Nis_473
  | Nis_472
  | Nis_471
  | Nis_470
  | Nis_469
  | Nis_468
  | Nis_467
  | Nis_466
  | Nis_465
  | Nis_464
  | Nis_463
  | Nis_462
  | Nis_461
  | Nis_460
  | Nis_459
  | Nis_458
  | Nis_457
  | Nis_456
  | Nis_455
  | Nis_454
  | Nis_453
  | Nis_452
  | Nis_451
  | Nis_450
  | Nis_449
  | Nis_448
  | Nis_447
  | Nis_446
  | Nis_445
  | Nis_444
  | Nis_443
  | Nis_442
  | Nis_441
  | Nis_440
  | Nis_439
  | Nis_438
  | Nis_437
  | Nis_436
  | Nis_435
  | Nis_434
  | Nis_433
  | Nis_432
  | Nis_431
  | Nis_430
  | Nis_429
  | Nis_428
  | Nis_427
  | Nis_426
  | Nis_425
  | Nis_424
  | Nis_423
  | Nis_422
  | Nis_421
  | Nis_420
  | Nis_419
  | Nis_418
  | Nis_417
  | Nis_416
  | Nis_415
  | Nis_414
  | Nis_413
  | Nis_412
  | Nis_411
  | Nis_410
  | Nis_409
  | Nis_408
  | Nis_407
  | Nis_406
  | Nis_405
  | Nis_404
  | Nis_403
  | Nis_402
  | Nis_401
  | Nis_400
  | Nis_399
  | Nis_398
  | Nis_397
  | Nis_396
  | Nis_395
  | Nis_394
  | Nis_393
  | Nis_392
  | Nis_391
  | Nis_390
  | Nis_389
  | Nis_388
  | Nis_387
  | Nis_386
  | Nis_385
  | Nis_384
  | Nis_383
  | Nis_382
  | Nis_381
  | Nis_380
  | Nis_379
  | Nis_378
  | Nis_377
  | Nis_376
  | Nis_375
  | Nis_374
  | Nis_373
  | Nis_372
  | Nis_371
  | Nis_370
  | Nis_369
  | Nis_368
  | Nis_367
  | Nis_366
  | Nis_365
  | Nis_364
  | Nis_363
  | Nis_362
  | Nis_361
  | Nis_360
  | Nis_359
  | Nis_358
  | Nis_357
  | Nis_356
  | Nis_355
  | Nis_354
  | Nis_353
  | Nis_352
  | Nis_351
  | Nis_350
  | Nis_349
  | Nis_348
  | Nis_347
  | Nis_346
  | Nis_345
  | Nis_344
  | Nis_343
  | Nis_342
  | Nis_341
  | Nis_340
  | Nis_339
  | Nis_338
  | Nis_337
  | Nis_336
  | Nis_335
  | Nis_334
  | Nis_333
  | Nis_332
  | Nis_331
  | Nis_330
  | Nis_329
  | Nis_328
  | Nis_327
  | Nis_326
  | Nis_325
  | Nis_324
  | Nis_323
  | Nis_322
  | Nis_321
  | Nis_320
  | Nis_319
  | Nis_318
  | Nis_317
  | Nis_316
  | Nis_315
  | Nis_314
  | Nis_313
  | Nis_312
  | Nis_311
  | Nis_310
  | Nis_309
  | Nis_308
  | Nis_307
  | Nis_306
  | Nis_305
  | Nis_304
  | Nis_303
  | Nis_302
  | Nis_301
  | Nis_300
  | Nis_299
  | Nis_298
  | Nis_297
  | Nis_296
  | Nis_295
  | Nis_294
  | Nis_293
  | Nis_292
  | Nis_291
  | Nis_290
  | Nis_289
  | Nis_288
  | Nis_287
  | Nis_286
  | Nis_285
  | Nis_284
  | Nis_283
  | Nis_282
  | Nis_281
  | Nis_280
  | Nis_279
  | Nis_278
  | Nis_277
  | Nis_276
  | Nis_275
  | Nis_274
  | Nis_273
  | Nis_272
  | Nis_271
  | Nis_270
  | Nis_269
  | Nis_268
  | Nis_267
  | Nis_266
  | Nis_265
  | Nis_264
  | Nis_263
  | Nis_262
  | Nis_261
  | Nis_260
  | Nis_259
  | Nis_258
  | Nis_257
  | Nis_256
  | Nis_255
  | Nis_254
  | Nis_253
  | Nis_252
  | Nis_251
  | Nis_250
  | Nis_249
  | Nis_248
  | Nis_247
  | Nis_246
  | Nis_245
  | Nis_244
  | Nis_243
  | Nis_242
  | Nis_241
  | Nis_240
  | Nis_239
  | Nis_238
  | Nis_237
  | Nis_236
  | Nis_235
  | Nis_234
  | Nis_233
  | Nis_232
  | Nis_231
  | Nis_230
  | Nis_229
  | Nis_228
  | Nis_227
  | Nis_226
  | Nis_225
  | Nis_224
  | Nis_223
  | Nis_222
  | Nis_221
  | Nis_220
  | Nis_219
  | Nis_218
  | Nis_217
  | Nis_216
  | Nis_215
  | Nis_214
  | Nis_213
  | Nis_212
  | Nis_211
  | Nis_210
  | Nis_209
  | Nis_208
  | Nis_207
  | Nis_206
  | Nis_205
  | Nis_204
  | Nis_203
  | Nis_202
  | Nis_201
  | Nis_200
  | Nis_199
  | Nis_198
  | Nis_197
  | Nis_196
  | Nis_195
  | Nis_194
  | Nis_193
  | Nis_192
  | Nis_191
  | Nis_190
  | Nis_189
  | Nis_188
  | Nis_187
  | Nis_186
  | Nis_185
  | Nis_184
  | Nis_183
  | Nis_182
  | Nis_181
  | Nis_180
  | Nis_179
  | Nis_178
  | Nis_177
  | Nis_176
  | Nis_175
  | Nis_174
  | Nis_173
  | Nis_172
  | Nis_171
  | Nis_170
  | Nis_169
  | Nis_168
  | Nis_167
  | Nis_166
  | Nis_165
  | Nis_164
  | Nis_163
  | Nis_162
  | Nis_161
  | Nis_160
  | Nis_159
  | Nis_158
  | Nis_157
  | Nis_156
  | Nis_155
  | Nis_154
  | Nis_153
  | Nis_152
  | Nis_151
  | Nis_150
  | Nis_149
  | Nis_148
  | Nis_147
  | Nis_146
  | Nis_145
  | Nis_144
  | Nis_143
  | Nis_142
  | Nis_141
  | Nis_140
  | Nis_139
  | Nis_138
  | Nis_137
  | Nis_136
  | Nis_135
  | Nis_134
  | Nis_133
  | Nis_132
  | Nis_131
  | Nis_130
  | Nis_129
  | Nis_128
  | Nis_127
  | Nis_126
  | Nis_125
  | Nis_124
  | Nis_123
  | Nis_122
  | Nis_121
  | Nis_120
  | Nis_119
  | Nis_118
  | Nis_117
  | Nis_116
  | Nis_115
  | Nis_114
  | Nis_113
  | Nis_112
  | Nis_111
  | Nis_110
  | Nis_109
  | Nis_108
  | Nis_107
  | Nis_106
  | Nis_105
  | Nis_104
  | Nis_103
  | Nis_102
  | Nis_101
  | Nis_100
  | Nis_99
  | Nis_98
  | Nis_97
  | Nis_96
  | Nis_95
  | Nis_94
  | Nis_93
  | Nis_92
  | Nis_91
  | Nis_90
  | Nis_89
  | Nis_88
  | Nis_87
  | Nis_86
  | Nis_85
  | Nis_84
  | Nis_83
  | Nis_82
  | Nis_81
  | Nis_80
  | Nis_79
  | Nis_78
  | Nis_77
  | Nis_76
  | Nis_75
  | Nis_74
  | Nis_73
  | Nis_72
  | Nis_71
  | Nis_70
  | Nis_69
  | Nis_68
  | Nis_67
  | Nis_66
  | Nis_65
  | Nis_64
  | Nis_63
  | Nis_62
  | Nis_61
  | Nis_60
  | Nis_59
  | Nis_58
  | Nis_57
  | Nis_56
  | Nis_55
  | Nis_54
  | Nis_53
  | Nis_52
  | Nis_51
  | Nis_50
  | Nis_49
  | Nis_48
  | Nis_47
  | Nis_46
  | Nis_45
  | Nis_44
  | Nis_43
  | Nis_42
  | Nis_41
  | Nis_40
  | Nis_39
  | Nis_38
  | Nis_37
  | Nis_36
  | Nis_35
  | Nis_34
  | Nis_33
  | Nis_32
  | Nis_31
  | Nis_30
  | Nis_29
  | Nis_28
  | Nis_27
  | Nis_26
  | Nis_25
  | Nis_24
  | Nis_23
  | Nis_22
  | Nis_21
  | Nis_20
  | Nis_19
  | Nis_18
  | Nis_17
  | Nis_16
  | Nis_15
  | Nis_14
  | Nis_13
  | Nis_12
  | Nis_11
  | Nis_10
  | Nis_9
  | Nis_8
  | Nis_7
  | Nis_6
  | Nis_5
  | Nis_4
  | Nis_3
  | Nis_2
  | Nis_1
  
  (** val noninitstate'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> noninitstate' -> 'a1 **)
  
  let noninitstate'_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 f158 f159 f160 f161 f162 f163 f164 f165 f166 f167 f168 f169 f170 f171 f172 f173 f174 f175 f176 f177 f178 f179 f180 f181 f182 f183 f184 f185 f186 f187 f188 f189 f190 f191 f192 f193 f194 f195 f196 f197 f198 f199 f200 f201 f202 f203 f204 f205 f206 f207 f208 f209 f210 f211 f212 f213 f214 f215 f216 f217 f218 f219 f220 f221 f222 f223 f224 f225 f226 f227 f228 f229 f230 f231 f232 f233 f234 f235 f236 f237 f238 f239 f240 f241 f242 f243 f244 f245 f246 f247 f248 f249 f250 f251 f252 f253 f254 f255 f256 f257 f258 f259 f260 f261 f262 f263 f264 f265 f266 f267 f268 f269 f270 f271 f272 f273 f274 f275 f276 f277 f278 f279 f280 f281 f282 f283 f284 f285 f286 f287 f288 f289 f290 f291 f292 f293 f294 f295 f296 f297 f298 f299 f300 f301 f302 f303 f304 f305 f306 f307 f308 f309 f310 f311 f312 f313 f314 f315 f316 f317 f318 f319 f320 f321 f322 f323 f324 f325 f326 f327 f328 f329 f330 f331 f332 f333 f334 f335 f336 f337 f338 f339 f340 f341 f342 f343 f344 f345 f346 f347 f348 f349 f350 f351 f352 f353 f354 f355 f356 f357 f358 f359 f360 f361 f362 f363 f364 f365 f366 f367 f368 f369 f370 f371 f372 f373 f374 f375 f376 f377 f378 f379 f380 f381 f382 f383 f384 f385 f386 f387 f388 f389 f390 f391 f392 f393 f394 f395 f396 f397 f398 f399 f400 f401 f402 f403 f404 f405 f406 f407 f408 f409 f410 f411 f412 f413 f414 f415 f416 f417 f418 f419 f420 f421 f422 f423 f424 f425 f426 f427 f428 f429 f430 f431 f432 f433 f434 f435 f436 f437 f438 f439 f440 f441 f442 f443 f444 f445 f446 f447 f448 f449 f450 f451 f452 f453 f454 f455 f456 f457 f458 f459 f460 f461 f462 f463 f464 f465 f466 f467 f468 f469 f470 f471 f472 f473 f474 f475 f476 f477 f478 f479 f480 f481 f482 f483 f484 f485 f486 f487 f488 f489 f490 f491 f492 f493 f494 f495 f496 f497 f498 f499 f500 f501 f502 = function
  | Nis_504 -> f
  | Nis_503 -> f0
  | Nis_502 -> f1
  | Nis_501 -> f2
  | Nis_500 -> f3
  | Nis_499 -> f4
  | Nis_498 -> f5
  | Nis_497 -> f6
  | Nis_496 -> f7
  | Nis_495 -> f8
  | Nis_494 -> f9
  | Nis_493 -> f10
  | Nis_492 -> f11
  | Nis_491 -> f12
  | Nis_490 -> f13
  | Nis_489 -> f14
  | Nis_488 -> f15
  | Nis_487 -> f16
  | Nis_486 -> f17
  | Nis_485 -> f18
  | Nis_484 -> f19
  | Nis_483 -> f20
  | Nis_482 -> f21
  | Nis_481 -> f22
  | Nis_480 -> f23
  | Nis_479 -> f24
  | Nis_478 -> f25
  | Nis_477 -> f26
  | Nis_476 -> f27
  | Nis_475 -> f28
  | Nis_474 -> f29
  | Nis_473 -> f30
  | Nis_472 -> f31
  | Nis_471 -> f32
  | Nis_470 -> f33
  | Nis_469 -> f34
  | Nis_468 -> f35
  | Nis_467 -> f36
  | Nis_466 -> f37
  | Nis_465 -> f38
  | Nis_464 -> f39
  | Nis_463 -> f40
  | Nis_462 -> f41
  | Nis_461 -> f42
  | Nis_460 -> f43
  | Nis_459 -> f44
  | Nis_458 -> f45
  | Nis_457 -> f46
  | Nis_456 -> f47
  | Nis_455 -> f48
  | Nis_454 -> f49
  | Nis_453 -> f50
  | Nis_452 -> f51
  | Nis_451 -> f52
  | Nis_450 -> f53
  | Nis_449 -> f54
  | Nis_448 -> f55
  | Nis_447 -> f56
  | Nis_446 -> f57
  | Nis_445 -> f58
  | Nis_444 -> f59
  | Nis_443 -> f60
  | Nis_442 -> f61
  | Nis_441 -> f62
  | Nis_440 -> f63
  | Nis_439 -> f64
  | Nis_438 -> f65
  | Nis_437 -> f66
  | Nis_436 -> f67
  | Nis_435 -> f68
  | Nis_434 -> f69
  | Nis_433 -> f70
  | Nis_432 -> f71
  | Nis_431 -> f72
  | Nis_430 -> f73
  | Nis_429 -> f74
  | Nis_428 -> f75
  | Nis_427 -> f76
  | Nis_426 -> f77
  | Nis_425 -> f78
  | Nis_424 -> f79
  | Nis_423 -> f80
  | Nis_422 -> f81
  | Nis_421 -> f82
  | Nis_420 -> f83
  | Nis_419 -> f84
  | Nis_418 -> f85
  | Nis_417 -> f86
  | Nis_416 -> f87
  | Nis_415 -> f88
  | Nis_414 -> f89
  | Nis_413 -> f90
  | Nis_412 -> f91
  | Nis_411 -> f92
  | Nis_410 -> f93
  | Nis_409 -> f94
  | Nis_408 -> f95
  | Nis_407 -> f96
  | Nis_406 -> f97
  | Nis_405 -> f98
  | Nis_404 -> f99
  | Nis_403 -> f100
  | Nis_402 -> f101
  | Nis_401 -> f102
  | Nis_400 -> f103
  | Nis_399 -> f104
  | Nis_398 -> f105
  | Nis_397 -> f106
  | Nis_396 -> f107
  | Nis_395 -> f108
  | Nis_394 -> f109
  | Nis_393 -> f110
  | Nis_392 -> f111
  | Nis_391 -> f112
  | Nis_390 -> f113
  | Nis_389 -> f114
  | Nis_388 -> f115
  | Nis_387 -> f116
  | Nis_386 -> f117
  | Nis_385 -> f118
  | Nis_384 -> f119
  | Nis_383 -> f120
  | Nis_382 -> f121
  | Nis_381 -> f122
  | Nis_380 -> f123
  | Nis_379 -> f124
  | Nis_378 -> f125
  | Nis_377 -> f126
  | Nis_376 -> f127
  | Nis_375 -> f128
  | Nis_374 -> f129
  | Nis_373 -> f130
  | Nis_372 -> f131
  | Nis_371 -> f132
  | Nis_370 -> f133
  | Nis_369 -> f134
  | Nis_368 -> f135
  | Nis_367 -> f136
  | Nis_366 -> f137
  | Nis_365 -> f138
  | Nis_364 -> f139
  | Nis_363 -> f140
  | Nis_362 -> f141
  | Nis_361 -> f142
  | Nis_360 -> f143
  | Nis_359 -> f144
  | Nis_358 -> f145
  | Nis_357 -> f146
  | Nis_356 -> f147
  | Nis_355 -> f148
  | Nis_354 -> f149
  | Nis_353 -> f150
  | Nis_352 -> f151
  | Nis_351 -> f152
  | Nis_350 -> f153
  | Nis_349 -> f154
  | Nis_348 -> f155
  | Nis_347 -> f156
  | Nis_346 -> f157
  | Nis_345 -> f158
  | Nis_344 -> f159
  | Nis_343 -> f160
  | Nis_342 -> f161
  | Nis_341 -> f162
  | Nis_340 -> f163
  | Nis_339 -> f164
  | Nis_338 -> f165
  | Nis_337 -> f166
  | Nis_336 -> f167
  | Nis_335 -> f168
  | Nis_334 -> f169
  | Nis_333 -> f170
  | Nis_332 -> f171
  | Nis_331 -> f172
  | Nis_330 -> f173
  | Nis_329 -> f174
  | Nis_328 -> f175
  | Nis_327 -> f176
  | Nis_326 -> f177
  | Nis_325 -> f178
  | Nis_324 -> f179
  | Nis_323 -> f180
  | Nis_322 -> f181
  | Nis_321 -> f182
  | Nis_320 -> f183
  | Nis_319 -> f184
  | Nis_318 -> f185
  | Nis_317 -> f186
  | Nis_316 -> f187
  | Nis_315 -> f188
  | Nis_314 -> f189
  | Nis_313 -> f190
  | Nis_312 -> f191
  | Nis_311 -> f192
  | Nis_310 -> f193
  | Nis_309 -> f194
  | Nis_308 -> f195
  | Nis_307 -> f196
  | Nis_306 -> f197
  | Nis_305 -> f198
  | Nis_304 -> f199
  | Nis_303 -> f200
  | Nis_302 -> f201
  | Nis_301 -> f202
  | Nis_300 -> f203
  | Nis_299 -> f204
  | Nis_298 -> f205
  | Nis_297 -> f206
  | Nis_296 -> f207
  | Nis_295 -> f208
  | Nis_294 -> f209
  | Nis_293 -> f210
  | Nis_292 -> f211
  | Nis_291 -> f212
  | Nis_290 -> f213
  | Nis_289 -> f214
  | Nis_288 -> f215
  | Nis_287 -> f216
  | Nis_286 -> f217
  | Nis_285 -> f218
  | Nis_284 -> f219
  | Nis_283 -> f220
  | Nis_282 -> f221
  | Nis_281 -> f222
  | Nis_280 -> f223
  | Nis_279 -> f224
  | Nis_278 -> f225
  | Nis_277 -> f226
  | Nis_276 -> f227
  | Nis_275 -> f228
  | Nis_274 -> f229
  | Nis_273 -> f230
  | Nis_272 -> f231
  | Nis_271 -> f232
  | Nis_270 -> f233
  | Nis_269 -> f234
  | Nis_268 -> f235
  | Nis_267 -> f236
  | Nis_266 -> f237
  | Nis_265 -> f238
  | Nis_264 -> f239
  | Nis_263 -> f240
  | Nis_262 -> f241
  | Nis_261 -> f242
  | Nis_260 -> f243
  | Nis_259 -> f244
  | Nis_258 -> f245
  | Nis_257 -> f246
  | Nis_256 -> f247
  | Nis_255 -> f248
  | Nis_254 -> f249
  | Nis_253 -> f250
  | Nis_252 -> f251
  | Nis_251 -> f252
  | Nis_250 -> f253
  | Nis_249 -> f254
  | Nis_248 -> f255
  | Nis_247 -> f256
  | Nis_246 -> f257
  | Nis_245 -> f258
  | Nis_244 -> f259
  | Nis_243 -> f260
  | Nis_242 -> f261
  | Nis_241 -> f262
  | Nis_240 -> f263
  | Nis_239 -> f264
  | Nis_238 -> f265
  | Nis_237 -> f266
  | Nis_236 -> f267
  | Nis_235 -> f268
  | Nis_234 -> f269
  | Nis_233 -> f270
  | Nis_232 -> f271
  | Nis_231 -> f272
  | Nis_230 -> f273
  | Nis_229 -> f274
  | Nis_228 -> f275
  | Nis_227 -> f276
  | Nis_226 -> f277
  | Nis_225 -> f278
  | Nis_224 -> f279
  | Nis_223 -> f280
  | Nis_222 -> f281
  | Nis_221 -> f282
  | Nis_220 -> f283
  | Nis_219 -> f284
  | Nis_218 -> f285
  | Nis_217 -> f286
  | Nis_216 -> f287
  | Nis_215 -> f288
  | Nis_214 -> f289
  | Nis_213 -> f290
  | Nis_212 -> f291
  | Nis_211 -> f292
  | Nis_210 -> f293
  | Nis_209 -> f294
  | Nis_208 -> f295
  | Nis_207 -> f296
  | Nis_206 -> f297
  | Nis_205 -> f298
  | Nis_204 -> f299
  | Nis_203 -> f300
  | Nis_202 -> f301
  | Nis_201 -> f302
  | Nis_200 -> f303
  | Nis_199 -> f304
  | Nis_198 -> f305
  | Nis_197 -> f306
  | Nis_196 -> f307
  | Nis_195 -> f308
  | Nis_194 -> f309
  | Nis_193 -> f310
  | Nis_192 -> f311
  | Nis_191 -> f312
  | Nis_190 -> f313
  | Nis_189 -> f314
  | Nis_188 -> f315
  | Nis_187 -> f316
  | Nis_186 -> f317
  | Nis_185 -> f318
  | Nis_184 -> f319
  | Nis_183 -> f320
  | Nis_182 -> f321
  | Nis_181 -> f322
  | Nis_180 -> f323
  | Nis_179 -> f324
  | Nis_178 -> f325
  | Nis_177 -> f326
  | Nis_176 -> f327
  | Nis_175 -> f328
  | Nis_174 -> f329
  | Nis_173 -> f330
  | Nis_172 -> f331
  | Nis_171 -> f332
  | Nis_170 -> f333
  | Nis_169 -> f334
  | Nis_168 -> f335
  | Nis_167 -> f336
  | Nis_166 -> f337
  | Nis_165 -> f338
  | Nis_164 -> f339
  | Nis_163 -> f340
  | Nis_162 -> f341
  | Nis_161 -> f342
  | Nis_160 -> f343
  | Nis_159 -> f344
  | Nis_158 -> f345
  | Nis_157 -> f346
  | Nis_156 -> f347
  | Nis_155 -> f348
  | Nis_154 -> f349
  | Nis_153 -> f350
  | Nis_152 -> f351
  | Nis_151 -> f352
  | Nis_150 -> f353
  | Nis_149 -> f354
  | Nis_148 -> f355
  | Nis_147 -> f356
  | Nis_146 -> f357
  | Nis_145 -> f358
  | Nis_144 -> f359
  | Nis_143 -> f360
  | Nis_142 -> f361
  | Nis_141 -> f362
  | Nis_140 -> f363
  | Nis_139 -> f364
  | Nis_138 -> f365
  | Nis_137 -> f366
  | Nis_136 -> f367
  | Nis_135 -> f368
  | Nis_134 -> f369
  | Nis_133 -> f370
  | Nis_132 -> f371
  | Nis_131 -> f372
  | Nis_130 -> f373
  | Nis_129 -> f374
  | Nis_128 -> f375
  | Nis_127 -> f376
  | Nis_126 -> f377
  | Nis_125 -> f378
  | Nis_124 -> f379
  | Nis_123 -> f380
  | Nis_122 -> f381
  | Nis_121 -> f382
  | Nis_120 -> f383
  | Nis_119 -> f384
  | Nis_118 -> f385
  | Nis_117 -> f386
  | Nis_116 -> f387
  | Nis_115 -> f388
  | Nis_114 -> f389
  | Nis_113 -> f390
  | Nis_112 -> f391
  | Nis_111 -> f392
  | Nis_110 -> f393
  | Nis_109 -> f394
  | Nis_108 -> f395
  | Nis_107 -> f396
  | Nis_106 -> f397
  | Nis_105 -> f398
  | Nis_104 -> f399
  | Nis_103 -> f400
  | Nis_102 -> f401
  | Nis_101 -> f402
  | Nis_100 -> f403
  | Nis_99 -> f404
  | Nis_98 -> f405
  | Nis_97 -> f406
  | Nis_96 -> f407
  | Nis_95 -> f408
  | Nis_94 -> f409
  | Nis_93 -> f410
  | Nis_92 -> f411
  | Nis_91 -> f412
  | Nis_90 -> f413
  | Nis_89 -> f414
  | Nis_88 -> f415
  | Nis_87 -> f416
  | Nis_86 -> f417
  | Nis_85 -> f418
  | Nis_84 -> f419
  | Nis_83 -> f420
  | Nis_82 -> f421
  | Nis_81 -> f422
  | Nis_80 -> f423
  | Nis_79 -> f424
  | Nis_78 -> f425
  | Nis_77 -> f426
  | Nis_76 -> f427
  | Nis_75 -> f428
  | Nis_74 -> f429
  | Nis_73 -> f430
  | Nis_72 -> f431
  | Nis_71 -> f432
  | Nis_70 -> f433
  | Nis_69 -> f434
  | Nis_68 -> f435
  | Nis_67 -> f436
  | Nis_66 -> f437
  | Nis_65 -> f438
  | Nis_64 -> f439
  | Nis_63 -> f440
  | Nis_62 -> f441
  | Nis_61 -> f442
  | Nis_60 -> f443
  | Nis_59 -> f444
  | Nis_58 -> f445
  | Nis_57 -> f446
  | Nis_56 -> f447
  | Nis_55 -> f448
  | Nis_54 -> f449
  | Nis_53 -> f450
  | Nis_52 -> f451
  | Nis_51 -> f452
  | Nis_50 -> f453
  | Nis_49 -> f454
  | Nis_48 -> f455
  | Nis_47 -> f456
  | Nis_46 -> f457
  | Nis_45 -> f458
  | Nis_44 -> f459
  | Nis_43 -> f460
  | Nis_42 -> f461
  | Nis_41 -> f462
  | Nis_40 -> f463
  | Nis_39 -> f464
  | Nis_38 -> f465
  | Nis_37 -> f466
  | Nis_36 -> f467
  | Nis_35 -> f468
  | Nis_34 -> f469
  | Nis_33 -> f470
  | Nis_32 -> f471
  | Nis_31 -> f472
  | Nis_30 -> f473
  | Nis_29 -> f474
  | Nis_28 -> f475
  | Nis_27 -> f476
  | Nis_26 -> f477
  | Nis_25 -> f478
  | Nis_24 -> f479
  | Nis_23 -> f480
  | Nis_22 -> f481
  | Nis_21 -> f482
  | Nis_20 -> f483
  | Nis_19 -> f484
  | Nis_18 -> f485
  | Nis_17 -> f486
  | Nis_16 -> f487
  | Nis_15 -> f488
  | Nis_14 -> f489
  | Nis_13 -> f490
  | Nis_12 -> f491
  | Nis_11 -> f492
  | Nis_10 -> f493
  | Nis_9 -> f494
  | Nis_8 -> f495
  | Nis_7 -> f496
  | Nis_6 -> f497
  | Nis_5 -> f498
  | Nis_4 -> f499
  | Nis_3 -> f500
  | Nis_2 -> f501
  | Nis_1 -> f502
  
  (** val noninitstate'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> noninitstate' -> 'a1 **)
  
  let noninitstate'_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 f158 f159 f160 f161 f162 f163 f164 f165 f166 f167 f168 f169 f170 f171 f172 f173 f174 f175 f176 f177 f178 f179 f180 f181 f182 f183 f184 f185 f186 f187 f188 f189 f190 f191 f192 f193 f194 f195 f196 f197 f198 f199 f200 f201 f202 f203 f204 f205 f206 f207 f208 f209 f210 f211 f212 f213 f214 f215 f216 f217 f218 f219 f220 f221 f222 f223 f224 f225 f226 f227 f228 f229 f230 f231 f232 f233 f234 f235 f236 f237 f238 f239 f240 f241 f242 f243 f244 f245 f246 f247 f248 f249 f250 f251 f252 f253 f254 f255 f256 f257 f258 f259 f260 f261 f262 f263 f264 f265 f266 f267 f268 f269 f270 f271 f272 f273 f274 f275 f276 f277 f278 f279 f280 f281 f282 f283 f284 f285 f286 f287 f288 f289 f290 f291 f292 f293 f294 f295 f296 f297 f298 f299 f300 f301 f302 f303 f304 f305 f306 f307 f308 f309 f310 f311 f312 f313 f314 f315 f316 f317 f318 f319 f320 f321 f322 f323 f324 f325 f326 f327 f328 f329 f330 f331 f332 f333 f334 f335 f336 f337 f338 f339 f340 f341 f342 f343 f344 f345 f346 f347 f348 f349 f350 f351 f352 f353 f354 f355 f356 f357 f358 f359 f360 f361 f362 f363 f364 f365 f366 f367 f368 f369 f370 f371 f372 f373 f374 f375 f376 f377 f378 f379 f380 f381 f382 f383 f384 f385 f386 f387 f388 f389 f390 f391 f392 f393 f394 f395 f396 f397 f398 f399 f400 f401 f402 f403 f404 f405 f406 f407 f408 f409 f410 f411 f412 f413 f414 f415 f416 f417 f418 f419 f420 f421 f422 f423 f424 f425 f426 f427 f428 f429 f430 f431 f432 f433 f434 f435 f436 f437 f438 f439 f440 f441 f442 f443 f444 f445 f446 f447 f448 f449 f450 f451 f452 f453 f454 f455 f456 f457 f458 f459 f460 f461 f462 f463 f464 f465 f466 f467 f468 f469 f470 f471 f472 f473 f474 f475 f476 f477 f478 f479 f480 f481 f482 f483 f484 f485 f486 f487 f488 f489 f490 f491 f492 f493 f494 f495 f496 f497 f498 f499 f500 f501 f502 = function
  | Nis_504 -> f
  | Nis_503 -> f0
  | Nis_502 -> f1
  | Nis_501 -> f2
  | Nis_500 -> f3
  | Nis_499 -> f4
  | Nis_498 -> f5
  | Nis_497 -> f6
  | Nis_496 -> f7
  | Nis_495 -> f8
  | Nis_494 -> f9
  | Nis_493 -> f10
  | Nis_492 -> f11
  | Nis_491 -> f12
  | Nis_490 -> f13
  | Nis_489 -> f14
  | Nis_488 -> f15
  | Nis_487 -> f16
  | Nis_486 -> f17
  | Nis_485 -> f18
  | Nis_484 -> f19
  | Nis_483 -> f20
  | Nis_482 -> f21
  | Nis_481 -> f22
  | Nis_480 -> f23
  | Nis_479 -> f24
  | Nis_478 -> f25
  | Nis_477 -> f26
  | Nis_476 -> f27
  | Nis_475 -> f28
  | Nis_474 -> f29
  | Nis_473 -> f30
  | Nis_472 -> f31
  | Nis_471 -> f32
  | Nis_470 -> f33
  | Nis_469 -> f34
  | Nis_468 -> f35
  | Nis_467 -> f36
  | Nis_466 -> f37
  | Nis_465 -> f38
  | Nis_464 -> f39
  | Nis_463 -> f40
  | Nis_462 -> f41
  | Nis_461 -> f42
  | Nis_460 -> f43
  | Nis_459 -> f44
  | Nis_458 -> f45
  | Nis_457 -> f46
  | Nis_456 -> f47
  | Nis_455 -> f48
  | Nis_454 -> f49
  | Nis_453 -> f50
  | Nis_452 -> f51
  | Nis_451 -> f52
  | Nis_450 -> f53
  | Nis_449 -> f54
  | Nis_448 -> f55
  | Nis_447 -> f56
  | Nis_446 -> f57
  | Nis_445 -> f58
  | Nis_444 -> f59
  | Nis_443 -> f60
  | Nis_442 -> f61
  | Nis_441 -> f62
  | Nis_440 -> f63
  | Nis_439 -> f64
  | Nis_438 -> f65
  | Nis_437 -> f66
  | Nis_436 -> f67
  | Nis_435 -> f68
  | Nis_434 -> f69
  | Nis_433 -> f70
  | Nis_432 -> f71
  | Nis_431 -> f72
  | Nis_430 -> f73
  | Nis_429 -> f74
  | Nis_428 -> f75
  | Nis_427 -> f76
  | Nis_426 -> f77
  | Nis_425 -> f78
  | Nis_424 -> f79
  | Nis_423 -> f80
  | Nis_422 -> f81
  | Nis_421 -> f82
  | Nis_420 -> f83
  | Nis_419 -> f84
  | Nis_418 -> f85
  | Nis_417 -> f86
  | Nis_416 -> f87
  | Nis_415 -> f88
  | Nis_414 -> f89
  | Nis_413 -> f90
  | Nis_412 -> f91
  | Nis_411 -> f92
  | Nis_410 -> f93
  | Nis_409 -> f94
  | Nis_408 -> f95
  | Nis_407 -> f96
  | Nis_406 -> f97
  | Nis_405 -> f98
  | Nis_404 -> f99
  | Nis_403 -> f100
  | Nis_402 -> f101
  | Nis_401 -> f102
  | Nis_400 -> f103
  | Nis_399 -> f104
  | Nis_398 -> f105
  | Nis_397 -> f106
  | Nis_396 -> f107
  | Nis_395 -> f108
  | Nis_394 -> f109
  | Nis_393 -> f110
  | Nis_392 -> f111
  | Nis_391 -> f112
  | Nis_390 -> f113
  | Nis_389 -> f114
  | Nis_388 -> f115
  | Nis_387 -> f116
  | Nis_386 -> f117
  | Nis_385 -> f118
  | Nis_384 -> f119
  | Nis_383 -> f120
  | Nis_382 -> f121
  | Nis_381 -> f122
  | Nis_380 -> f123
  | Nis_379 -> f124
  | Nis_378 -> f125
  | Nis_377 -> f126
  | Nis_376 -> f127
  | Nis_375 -> f128
  | Nis_374 -> f129
  | Nis_373 -> f130
  | Nis_372 -> f131
  | Nis_371 -> f132
  | Nis_370 -> f133
  | Nis_369 -> f134
  | Nis_368 -> f135
  | Nis_367 -> f136
  | Nis_366 -> f137
  | Nis_365 -> f138
  | Nis_364 -> f139
  | Nis_363 -> f140
  | Nis_362 -> f141
  | Nis_361 -> f142
  | Nis_360 -> f143
  | Nis_359 -> f144
  | Nis_358 -> f145
  | Nis_357 -> f146
  | Nis_356 -> f147
  | Nis_355 -> f148
  | Nis_354 -> f149
  | Nis_353 -> f150
  | Nis_352 -> f151
  | Nis_351 -> f152
  | Nis_350 -> f153
  | Nis_349 -> f154
  | Nis_348 -> f155
  | Nis_347 -> f156
  | Nis_346 -> f157
  | Nis_345 -> f158
  | Nis_344 -> f159
  | Nis_343 -> f160
  | Nis_342 -> f161
  | Nis_341 -> f162
  | Nis_340 -> f163
  | Nis_339 -> f164
  | Nis_338 -> f165
  | Nis_337 -> f166
  | Nis_336 -> f167
  | Nis_335 -> f168
  | Nis_334 -> f169
  | Nis_333 -> f170
  | Nis_332 -> f171
  | Nis_331 -> f172
  | Nis_330 -> f173
  | Nis_329 -> f174
  | Nis_328 -> f175
  | Nis_327 -> f176
  | Nis_326 -> f177
  | Nis_325 -> f178
  | Nis_324 -> f179
  | Nis_323 -> f180
  | Nis_322 -> f181
  | Nis_321 -> f182
  | Nis_320 -> f183
  | Nis_319 -> f184
  | Nis_318 -> f185
  | Nis_317 -> f186
  | Nis_316 -> f187
  | Nis_315 -> f188
  | Nis_314 -> f189
  | Nis_313 -> f190
  | Nis_312 -> f191
  | Nis_311 -> f192
  | Nis_310 -> f193
  | Nis_309 -> f194
  | Nis_308 -> f195
  | Nis_307 -> f196
  | Nis_306 -> f197
  | Nis_305 -> f198
  | Nis_304 -> f199
  | Nis_303 -> f200
  | Nis_302 -> f201
  | Nis_301 -> f202
  | Nis_300 -> f203
  | Nis_299 -> f204
  | Nis_298 -> f205
  | Nis_297 -> f206
  | Nis_296 -> f207
  | Nis_295 -> f208
  | Nis_294 -> f209
  | Nis_293 -> f210
  | Nis_292 -> f211
  | Nis_291 -> f212
  | Nis_290 -> f213
  | Nis_289 -> f214
  | Nis_288 -> f215
  | Nis_287 -> f216
  | Nis_286 -> f217
  | Nis_285 -> f218
  | Nis_284 -> f219
  | Nis_283 -> f220
  | Nis_282 -> f221
  | Nis_281 -> f222
  | Nis_280 -> f223
  | Nis_279 -> f224
  | Nis_278 -> f225
  | Nis_277 -> f226
  | Nis_276 -> f227
  | Nis_275 -> f228
  | Nis_274 -> f229
  | Nis_273 -> f230
  | Nis_272 -> f231
  | Nis_271 -> f232
  | Nis_270 -> f233
  | Nis_269 -> f234
  | Nis_268 -> f235
  | Nis_267 -> f236
  | Nis_266 -> f237
  | Nis_265 -> f238
  | Nis_264 -> f239
  | Nis_263 -> f240
  | Nis_262 -> f241
  | Nis_261 -> f242
  | Nis_260 -> f243
  | Nis_259 -> f244
  | Nis_258 -> f245
  | Nis_257 -> f246
  | Nis_256 -> f247
  | Nis_255 -> f248
  | Nis_254 -> f249
  | Nis_253 -> f250
  | Nis_252 -> f251
  | Nis_251 -> f252
  | Nis_250 -> f253
  | Nis_249 -> f254
  | Nis_248 -> f255
  | Nis_247 -> f256
  | Nis_246 -> f257
  | Nis_245 -> f258
  | Nis_244 -> f259
  | Nis_243 -> f260
  | Nis_242 -> f261
  | Nis_241 -> f262
  | Nis_240 -> f263
  | Nis_239 -> f264
  | Nis_238 -> f265
  | Nis_237 -> f266
  | Nis_236 -> f267
  | Nis_235 -> f268
  | Nis_234 -> f269
  | Nis_233 -> f270
  | Nis_232 -> f271
  | Nis_231 -> f272
  | Nis_230 -> f273
  | Nis_229 -> f274
  | Nis_228 -> f275
  | Nis_227 -> f276
  | Nis_226 -> f277
  | Nis_225 -> f278
  | Nis_224 -> f279
  | Nis_223 -> f280
  | Nis_222 -> f281
  | Nis_221 -> f282
  | Nis_220 -> f283
  | Nis_219 -> f284
  | Nis_218 -> f285
  | Nis_217 -> f286
  | Nis_216 -> f287
  | Nis_215 -> f288
  | Nis_214 -> f289
  | Nis_213 -> f290
  | Nis_212 -> f291
  | Nis_211 -> f292
  | Nis_210 -> f293
  | Nis_209 -> f294
  | Nis_208 -> f295
  | Nis_207 -> f296
  | Nis_206 -> f297
  | Nis_205 -> f298
  | Nis_204 -> f299
  | Nis_203 -> f300
  | Nis_202 -> f301
  | Nis_201 -> f302
  | Nis_200 -> f303
  | Nis_199 -> f304
  | Nis_198 -> f305
  | Nis_197 -> f306
  | Nis_196 -> f307
  | Nis_195 -> f308
  | Nis_194 -> f309
  | Nis_193 -> f310
  | Nis_192 -> f311
  | Nis_191 -> f312
  | Nis_190 -> f313
  | Nis_189 -> f314
  | Nis_188 -> f315
  | Nis_187 -> f316
  | Nis_186 -> f317
  | Nis_185 -> f318
  | Nis_184 -> f319
  | Nis_183 -> f320
  | Nis_182 -> f321
  | Nis_181 -> f322
  | Nis_180 -> f323
  | Nis_179 -> f324
  | Nis_178 -> f325
  | Nis_177 -> f326
  | Nis_176 -> f327
  | Nis_175 -> f328
  | Nis_174 -> f329
  | Nis_173 -> f330
  | Nis_172 -> f331
  | Nis_171 -> f332
  | Nis_170 -> f333
  | Nis_169 -> f334
  | Nis_168 -> f335
  | Nis_167 -> f336
  | Nis_166 -> f337
  | Nis_165 -> f338
  | Nis_164 -> f339
  | Nis_163 -> f340
  | Nis_162 -> f341
  | Nis_161 -> f342
  | Nis_160 -> f343
  | Nis_159 -> f344
  | Nis_158 -> f345
  | Nis_157 -> f346
  | Nis_156 -> f347
  | Nis_155 -> f348
  | Nis_154 -> f349
  | Nis_153 -> f350
  | Nis_152 -> f351
  | Nis_151 -> f352
  | Nis_150 -> f353
  | Nis_149 -> f354
  | Nis_148 -> f355
  | Nis_147 -> f356
  | Nis_146 -> f357
  | Nis_145 -> f358
  | Nis_144 -> f359
  | Nis_143 -> f360
  | Nis_142 -> f361
  | Nis_141 -> f362
  | Nis_140 -> f363
  | Nis_139 -> f364
  | Nis_138 -> f365
  | Nis_137 -> f366
  | Nis_136 -> f367
  | Nis_135 -> f368
  | Nis_134 -> f369
  | Nis_133 -> f370
  | Nis_132 -> f371
  | Nis_131 -> f372
  | Nis_130 -> f373
  | Nis_129 -> f374
  | Nis_128 -> f375
  | Nis_127 -> f376
  | Nis_126 -> f377
  | Nis_125 -> f378
  | Nis_124 -> f379
  | Nis_123 -> f380
  | Nis_122 -> f381
  | Nis_121 -> f382
  | Nis_120 -> f383
  | Nis_119 -> f384
  | Nis_118 -> f385
  | Nis_117 -> f386
  | Nis_116 -> f387
  | Nis_115 -> f388
  | Nis_114 -> f389
  | Nis_113 -> f390
  | Nis_112 -> f391
  | Nis_111 -> f392
  | Nis_110 -> f393
  | Nis_109 -> f394
  | Nis_108 -> f395
  | Nis_107 -> f396
  | Nis_106 -> f397
  | Nis_105 -> f398
  | Nis_104 -> f399
  | Nis_103 -> f400
  | Nis_102 -> f401
  | Nis_101 -> f402
  | Nis_100 -> f403
  | Nis_99 -> f404
  | Nis_98 -> f405
  | Nis_97 -> f406
  | Nis_96 -> f407
  | Nis_95 -> f408
  | Nis_94 -> f409
  | Nis_93 -> f410
  | Nis_92 -> f411
  | Nis_91 -> f412
  | Nis_90 -> f413
  | Nis_89 -> f414
  | Nis_88 -> f415
  | Nis_87 -> f416
  | Nis_86 -> f417
  | Nis_85 -> f418
  | Nis_84 -> f419
  | Nis_83 -> f420
  | Nis_82 -> f421
  | Nis_81 -> f422
  | Nis_80 -> f423
  | Nis_79 -> f424
  | Nis_78 -> f425
  | Nis_77 -> f426
  | Nis_76 -> f427
  | Nis_75 -> f428
  | Nis_74 -> f429
  | Nis_73 -> f430
  | Nis_72 -> f431
  | Nis_71 -> f432
  | Nis_70 -> f433
  | Nis_69 -> f434
  | Nis_68 -> f435
  | Nis_67 -> f436
  | Nis_66 -> f437
  | Nis_65 -> f438
  | Nis_64 -> f439
  | Nis_63 -> f440
  | Nis_62 -> f441
  | Nis_61 -> f442
  | Nis_60 -> f443
  | Nis_59 -> f444
  | Nis_58 -> f445
  | Nis_57 -> f446
  | Nis_56 -> f447
  | Nis_55 -> f448
  | Nis_54 -> f449
  | Nis_53 -> f450
  | Nis_52 -> f451
  | Nis_51 -> f452
  | Nis_50 -> f453
  | Nis_49 -> f454
  | Nis_48 -> f455
  | Nis_47 -> f456
  | Nis_46 -> f457
  | Nis_45 -> f458
  | Nis_44 -> f459
  | Nis_43 -> f460
  | Nis_42 -> f461
  | Nis_41 -> f462
  | Nis_40 -> f463
  | Nis_39 -> f464
  | Nis_38 -> f465
  | Nis_37 -> f466
  | Nis_36 -> f467
  | Nis_35 -> f468
  | Nis_34 -> f469
  | Nis_33 -> f470
  | Nis_32 -> f471
  | Nis_31 -> f472
  | Nis_30 -> f473
  | Nis_29 -> f474
  | Nis_28 -> f475
  | Nis_27 -> f476
  | Nis_26 -> f477
  | Nis_25 -> f478
  | Nis_24 -> f479
  | Nis_23 -> f480
  | Nis_22 -> f481
  | Nis_21 -> f482
  | Nis_20 -> f483
  | Nis_19 -> f484
  | Nis_18 -> f485
  | Nis_17 -> f486
  | Nis_16 -> f487
  | Nis_15 -> f488
  | Nis_14 -> f489
  | Nis_13 -> f490
  | Nis_12 -> f491
  | Nis_11 -> f492
  | Nis_10 -> f493
  | Nis_9 -> f494
  | Nis_8 -> f495
  | Nis_7 -> f496
  | Nis_6 -> f497
  | Nis_5 -> f498
  | Nis_4 -> f499
  | Nis_3 -> f500
  | Nis_2 -> f501
  | Nis_1 -> f502
  
  type noninitstate = noninitstate'
  
  (** val noninitstateNum : noninitstate coq_Numbered **)
  
  let noninitstateNum =
    { injN = (fun x ->
      match x with
      | Nis_504 -> N0
      | Nis_503 -> Npos Coq_xH
      | Nis_502 -> Npos (Coq_xO Coq_xH)
      | Nis_501 -> Npos (Coq_xI Coq_xH)
      | Nis_500 -> Npos (Coq_xO (Coq_xO Coq_xH))
      | Nis_499 -> Npos (Coq_xI (Coq_xO Coq_xH))
      | Nis_498 -> Npos (Coq_xO (Coq_xI Coq_xH))
      | Nis_497 -> Npos (Coq_xI (Coq_xI Coq_xH))
      | Nis_496 -> Npos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))
      | Nis_495 -> Npos (Coq_xI (Coq_xO (Coq_xO Coq_xH)))
      | Nis_494 -> Npos (Coq_xO (Coq_xI (Coq_xO Coq_xH)))
      | Nis_493 -> Npos (Coq_xI (Coq_xI (Coq_xO Coq_xH)))
      | Nis_492 -> Npos (Coq_xO (Coq_xO (Coq_xI Coq_xH)))
      | Nis_491 -> Npos (Coq_xI (Coq_xO (Coq_xI Coq_xH)))
      | Nis_490 -> Npos (Coq_xO (Coq_xI (Coq_xI Coq_xH)))
      | Nis_489 -> Npos (Coq_xI (Coq_xI (Coq_xI Coq_xH)))
      | Nis_488 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Nis_487 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))
      | Nis_486 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Nis_485 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))
      | Nis_484 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Nis_483 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))
      | Nis_482 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Nis_481 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))
      | Nis_480 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Nis_479 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))
      | Nis_478 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Nis_477 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))
      | Nis_476 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Nis_475 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))
      | Nis_474 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Nis_473 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))
      | Nis_472 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_471 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_470 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_469 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_468 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_467 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_466 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_465 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH)))))
      | Nis_464 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_463 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_462 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_461 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_460 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_459 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_458 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_457 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH)))))
      | Nis_456 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_455 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_454 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_453 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_452 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_451 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_450 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_449 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))
      | Nis_448 -> Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_447 -> Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_446 -> Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_445 -> Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_444 -> Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_443 -> Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_442 -> Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_441 -> Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH)))))
      | Nis_440 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_439 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_438 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_437 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_436 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_435 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_434 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_433 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_432 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_431 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_430 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_429 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_428 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_427 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_426 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_425 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO Coq_xH))))))
      | Nis_424 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_423 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_422 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_421 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_420 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_419 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_418 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_417 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_416 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_415 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_414 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_413 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_412 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_411 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_410 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_409 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO Coq_xH))))))
      | Nis_408 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_407 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_406 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_405 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_404 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_403 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_402 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_401 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_400 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_399 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_398 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_397 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_396 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_395 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_394 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_393 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI Coq_xH))))))
      | Nis_392 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_391 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_390 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_389 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_388 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_387 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_386 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_385 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_384 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_383 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_382 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_381 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_380 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_379 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_378 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_377 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))
      | Nis_376 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_375 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_374 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_373 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_372 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_371 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_370 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_369 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_368 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_367 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_366 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_365 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_364 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_363 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_362 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_361 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_360 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_359 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_358 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_357 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_356 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_355 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_354 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_353 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_352 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_351 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_350 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_349 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_348 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_347 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_346 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_345 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH)))))))
      | Nis_344 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_343 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_342 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_341 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_340 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_339 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_338 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_337 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_336 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_335 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_334 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_333 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_332 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_331 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_330 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_329 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_328 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_327 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_326 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_325 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_324 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_323 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_322 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_321 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_320 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_319 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_318 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_317 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_316 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_315 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_314 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_313 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH)))))))
      | Nis_312 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_311 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_310 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_309 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_308 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_307 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_306 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_305 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_304 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_303 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_302 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_301 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_300 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_299 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_298 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_297 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_296 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_295 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_294 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_293 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_292 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_291 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_290 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_289 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_288 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_287 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_286 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_285 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_284 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_283 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_282 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_281 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH)))))))
      | Nis_280 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_279 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_278 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_277 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_276 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_275 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_274 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_273 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_272 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_271 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_270 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_269 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_268 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_267 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_266 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_265 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_264 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_263 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_262 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_261 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_260 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_259 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_258 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_257 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_256 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_255 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_254 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_253 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_252 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_251 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_250 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_249 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH)))))))
      | Nis_248 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_247 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_246 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_245 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_244 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_243 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_242 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_241 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_240 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_239 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_238 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_237 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_236 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_235 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_234 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_233 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_232 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_231 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_230 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_229 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_228 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_227 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_226 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_225 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_224 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_223 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_222 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_221 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_220 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_219 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_218 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_217 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_216 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_215 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_214 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_213 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_212 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_211 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_210 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_209 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_208 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_207 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_206 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_205 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_204 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_203 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_202 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_201 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_200 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_199 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_198 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_197 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_196 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_195 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_194 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_193 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_192 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_191 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_190 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_189 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_188 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_187 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_186 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_185 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO
          Coq_xH))))))))
      | Nis_184 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_183 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_182 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_181 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_180 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_179 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_178 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_177 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_176 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_175 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_174 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_173 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_172 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_171 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_170 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_169 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_168 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_167 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_166 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_165 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_164 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_163 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_162 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_161 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_160 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_159 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_158 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_157 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_156 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_155 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_154 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_153 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_152 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_151 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_150 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_149 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_148 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_147 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_146 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_145 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_144 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_143 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_142 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_141 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_140 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_139 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_138 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_137 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_136 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_135 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_134 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_133 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_132 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_131 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_130 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_129 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_128 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_127 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_126 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_125 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_124 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_123 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_122 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_121 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO
          Coq_xH))))))))
      | Nis_120 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_119 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_118 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_117 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_116 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_115 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_114 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_113 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_112 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_111 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_110 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_109 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_108 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_107 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_106 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_105 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_104 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_103 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_102 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_101 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_100 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_99 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_98 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_97 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_96 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_95 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_94 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_93 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_92 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_91 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_90 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_89 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_88 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_87 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_86 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_85 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_84 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_83 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_82 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_81 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_80 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_79 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_78 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_77 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_76 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_75 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_74 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_73 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_72 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_71 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_70 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_69 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_68 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_67 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_66 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_65 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_64 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_63 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_62 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_61 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_60 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_59 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_58 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_57 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI
          Coq_xH))))))))
      | Nis_56 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_55 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_54 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_53 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_52 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_51 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_50 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_49 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_48 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_47 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_46 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_45 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_44 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_43 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_42 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_41 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_40 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_39 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_38 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_37 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_36 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_35 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_34 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_33 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_32 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_31 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_30 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_29 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_28 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_27 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_26 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_25 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_24 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_23 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_22 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_21 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_20 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_19 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_18 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_17 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_16 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_15 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_14 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_13 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_12 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_11 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_10 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_9 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_8 ->
        Npos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_7 ->
        Npos (Coq_xI (Coq_xO (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_6 ->
        Npos (Coq_xO (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_5 ->
        Npos (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_4 ->
        Npos (Coq_xO (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_3 ->
        Npos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_2 ->
        Npos (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))
      | Nis_1 ->
        Npos (Coq_xI (Coq_xI (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xI (Coq_xI
          Coq_xH))))))))); surjN = (fun n ->
      match n with
      | N0 -> Nis_504
      | Npos p ->
        (match p with
         | Coq_xI p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_121
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_249)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_57
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_185
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_313)
                           | Coq_xH -> Nis_377)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_25
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_153
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_281)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_89
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_217
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_345)
                           | Coq_xH -> Nis_409)
                        | Coq_xH -> Nis_441)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_9
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_137
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_265)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_73
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_201
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_329)
                           | Coq_xH -> Nis_393)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_41
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_169
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_297)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_105
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_233
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_361)
                           | Coq_xH -> Nis_425)
                        | Coq_xH -> Nis_457)
                     | Coq_xH -> Nis_473)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_1
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_129
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_257)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_65
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_193
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_321)
                           | Coq_xH -> Nis_385)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_33
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_161
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_289)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_97
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_225
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_353)
                           | Coq_xH -> Nis_417)
                        | Coq_xH -> Nis_449)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_17
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_145
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_273)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_81
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_209
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_337)
                           | Coq_xH -> Nis_401)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_49
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_177
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_305)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_113
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_241
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_369)
                           | Coq_xH -> Nis_433)
                        | Coq_xH -> Nis_465)
                     | Coq_xH -> Nis_481)
                  | Coq_xH -> Nis_489)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_125
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_253)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_61
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_189
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_317)
                           | Coq_xH -> Nis_381)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_29
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_157
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_285)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_93
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_221
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_349)
                           | Coq_xH -> Nis_413)
                        | Coq_xH -> Nis_445)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_13
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_141
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_269)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_77
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_205
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_333)
                           | Coq_xH -> Nis_397)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_45
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_173
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_301)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_109
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_237
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_365)
                           | Coq_xH -> Nis_429)
                        | Coq_xH -> Nis_461)
                     | Coq_xH -> Nis_477)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_5
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_133
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_261)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_69
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_197
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_325)
                           | Coq_xH -> Nis_389)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_37
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_165
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_293)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_101
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_229
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_357)
                           | Coq_xH -> Nis_421)
                        | Coq_xH -> Nis_453)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_21
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_149
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_277)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_85
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_213
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_341)
                           | Coq_xH -> Nis_405)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_53
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_181
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_309)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_117
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_245
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_373)
                           | Coq_xH -> Nis_437)
                        | Coq_xH -> Nis_469)
                     | Coq_xH -> Nis_485)
                  | Coq_xH -> Nis_493)
               | Coq_xH -> Nis_497)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_123
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_251)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_59
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_187
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_315)
                           | Coq_xH -> Nis_379)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_27
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_155
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_283)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_91
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_219
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_347)
                           | Coq_xH -> Nis_411)
                        | Coq_xH -> Nis_443)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_11
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_139
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_267)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_75
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_203
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_331)
                           | Coq_xH -> Nis_395)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_43
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_171
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_299)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_107
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_235
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_363)
                           | Coq_xH -> Nis_427)
                        | Coq_xH -> Nis_459)
                     | Coq_xH -> Nis_475)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_3
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_131
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_259)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_67
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_195
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_323)
                           | Coq_xH -> Nis_387)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_35
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_163
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_291)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_99
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_227
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_355)
                           | Coq_xH -> Nis_419)
                        | Coq_xH -> Nis_451)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_19
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_147
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_275)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_83
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_211
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_339)
                           | Coq_xH -> Nis_403)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_51
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_179
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_307)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_115
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_243
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_371)
                           | Coq_xH -> Nis_435)
                        | Coq_xH -> Nis_467)
                     | Coq_xH -> Nis_483)
                  | Coq_xH -> Nis_491)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_127
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_255)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_63
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_191
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_319)
                           | Coq_xH -> Nis_383)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_31
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_159
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_287)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_95
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_223
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_351)
                           | Coq_xH -> Nis_415)
                        | Coq_xH -> Nis_447)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_15
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_143
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_271)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_79
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_207
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_335)
                           | Coq_xH -> Nis_399)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_47
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_175
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_303)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_111
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_239
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_367)
                           | Coq_xH -> Nis_431)
                        | Coq_xH -> Nis_463)
                     | Coq_xH -> Nis_479)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_7
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_135
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_263)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_71
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_199
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_327)
                           | Coq_xH -> Nis_391)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_39
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_167
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_295)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_103
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_231
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_359)
                           | Coq_xH -> Nis_423)
                        | Coq_xH -> Nis_455)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_23
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_151
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_279)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_87
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_215
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_343)
                           | Coq_xH -> Nis_407)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_55
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_183
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_311)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_119
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_247
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_375)
                           | Coq_xH -> Nis_439)
                        | Coq_xH -> Nis_471)
                     | Coq_xH -> Nis_487)
                  | Coq_xH -> Nis_495)
               | Coq_xH -> Nis_499)
            | Coq_xH -> Nis_501)
         | Coq_xO p0 ->
           (match p0 with
            | Coq_xI p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_122
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_250)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_58
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_186
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_314)
                           | Coq_xH -> Nis_378)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_26
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_154
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_282)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_90
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_218
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_346)
                           | Coq_xH -> Nis_410)
                        | Coq_xH -> Nis_442)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_10
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_138
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_266)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_74
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_202
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_330)
                           | Coq_xH -> Nis_394)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_42
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_170
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_298)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_106
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_234
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_362)
                           | Coq_xH -> Nis_426)
                        | Coq_xH -> Nis_458)
                     | Coq_xH -> Nis_474)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_2
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_130
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_258)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_66
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_194
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_322)
                           | Coq_xH -> Nis_386)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_34
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_162
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_290)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_98
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_226
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_354)
                           | Coq_xH -> Nis_418)
                        | Coq_xH -> Nis_450)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_18
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_146
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_274)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_82
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_210
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_338)
                           | Coq_xH -> Nis_402)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_50
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_178
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_306)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_114
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_242
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_370)
                           | Coq_xH -> Nis_434)
                        | Coq_xH -> Nis_466)
                     | Coq_xH -> Nis_482)
                  | Coq_xH -> Nis_490)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_126
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_254)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_62
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_190
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_318)
                           | Coq_xH -> Nis_382)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_30
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_158
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_286)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_94
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_222
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_350)
                           | Coq_xH -> Nis_414)
                        | Coq_xH -> Nis_446)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_14
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_142
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_270)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_78
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_206
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_334)
                           | Coq_xH -> Nis_398)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_46
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_174
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_302)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_110
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_238
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_366)
                           | Coq_xH -> Nis_430)
                        | Coq_xH -> Nis_462)
                     | Coq_xH -> Nis_478)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_6
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_134
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_262)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_70
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_198
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_326)
                           | Coq_xH -> Nis_390)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_38
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_166
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_294)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_102
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_230
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_358)
                           | Coq_xH -> Nis_422)
                        | Coq_xH -> Nis_454)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_22
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_150
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_278)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_86
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_214
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_342)
                           | Coq_xH -> Nis_406)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_54
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_182
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_310)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_118
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_246
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_374)
                           | Coq_xH -> Nis_438)
                        | Coq_xH -> Nis_470)
                     | Coq_xH -> Nis_486)
                  | Coq_xH -> Nis_494)
               | Coq_xH -> Nis_498)
            | Coq_xO p1 ->
              (match p1 with
               | Coq_xI p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_124
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_252)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_60
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_188
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_316)
                           | Coq_xH -> Nis_380)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_28
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_156
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_284)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_92
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_220
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_348)
                           | Coq_xH -> Nis_412)
                        | Coq_xH -> Nis_444)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_12
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_140
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_268)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_76
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_204
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_332)
                           | Coq_xH -> Nis_396)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_44
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_172
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_300)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_108
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_236
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_364)
                           | Coq_xH -> Nis_428)
                        | Coq_xH -> Nis_460)
                     | Coq_xH -> Nis_476)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_4
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_132
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_260)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_68
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_196
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_324)
                           | Coq_xH -> Nis_388)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_36
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_164
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_292)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_100
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_228
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_356)
                           | Coq_xH -> Nis_420)
                        | Coq_xH -> Nis_452)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_20
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_148
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_276)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_84
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_212
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_340)
                           | Coq_xH -> Nis_404)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_52
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_180
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_308)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_116
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_244
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_372)
                           | Coq_xH -> Nis_436)
                        | Coq_xH -> Nis_468)
                     | Coq_xH -> Nis_484)
                  | Coq_xH -> Nis_492)
               | Coq_xO p2 ->
                 (match p2 with
                  | Coq_xI p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 -> Nis_504
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_128
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_256)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_64
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_192
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_320)
                           | Coq_xH -> Nis_384)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_32
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_160
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_288)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_96
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_224
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_352)
                           | Coq_xH -> Nis_416)
                        | Coq_xH -> Nis_448)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_16
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_144
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_272)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_80
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_208
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_336)
                           | Coq_xH -> Nis_400)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_48
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_176
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_304)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_112
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_240
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_368)
                           | Coq_xH -> Nis_432)
                        | Coq_xH -> Nis_464)
                     | Coq_xH -> Nis_480)
                  | Coq_xO p3 ->
                    (match p3 with
                     | Coq_xI p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_8
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_136
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_264)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_72
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_200
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_328)
                           | Coq_xH -> Nis_392)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_40
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_168
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_296)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_104
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_232
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_360)
                           | Coq_xH -> Nis_424)
                        | Coq_xH -> Nis_456)
                     | Coq_xO p4 ->
                       (match p4 with
                        | Coq_xI p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_24
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_152
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_280)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_88
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_216
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_344)
                           | Coq_xH -> Nis_408)
                        | Coq_xO p5 ->
                          (match p5 with
                           | Coq_xI p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_56
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_184
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_312)
                           | Coq_xO p6 ->
                             (match p6 with
                              | Coq_xI p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_120
                                 | _ -> Nis_504)
                              | Coq_xO p7 ->
                                (match p7 with
                                 | Coq_xH -> Nis_248
                                 | _ -> Nis_504)
                              | Coq_xH -> Nis_376)
                           | Coq_xH -> Nis_440)
                        | Coq_xH -> Nis_472)
                     | Coq_xH -> Nis_488)
                  | Coq_xH -> Nis_496)
               | Coq_xH -> Nis_500)
            | Coq_xH -> Nis_502)
         | Coq_xH -> Nis_503)); injN_bound = (Npos (Coq_xO (Coq_xO (Coq_xO
      (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI Coq_xH))))))))) }
  
  (** val coq_NonInitStateAlph : noninitstate coq_Alphabet **)
  
  let coq_NonInitStateAlph =
    coq_NumberedAlphabet noninitstateNum
  
  (** val last_symb_of_non_init_state : noninitstate -> Coq__1.symbol **)
  
  let last_symb_of_non_init_state = function
  | Nis_504 -> Coq__1.NT Coq__1.Coq_external_declaration_nt
  | Nis_503 -> Coq__1.NT Coq__1.Coq_declaration_nt
  | Nis_502 -> Coq__1.NT Coq__1.Coq_compound_statement_nt
  | Nis_501 -> Coq__1.NT Coq__1.Coq_block_item_nt
  | Nis_500 -> Coq__1.NT Coq__1.Coq_block_item_nt
  | Nis_499 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_498 -> Coq__1.NT Coq__1.Coq_block_item_list_nt
  | Nis_497 -> Coq__1.NT Coq__1.Coq_declaration_nt
  | Nis_496 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_495 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_494 -> Coq__1.T Coq__1.ELSE_t
  | Nis_493 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_492 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_491 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_490 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_489 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_488 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_487 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_486 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_485 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_484 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_483 -> Coq__1.T Coq__1.ELSE_t
  | Nis_482 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_481 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_479 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_478 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_476 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_475 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_474 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_472 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_471 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_469 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_468 -> Coq__1.NT Coq__1.Coq_declaration_nt
  | Nis_467 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_465 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_464 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_462 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_461 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_460 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_458 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_457 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_455 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_454 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_453 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_452 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_450 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_449 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_447 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_446 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_445 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_443 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_442 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_441 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_440 -> Coq__1.NT Coq__1.Coq_compound_statement_nt
  | Nis_439 -> Coq__1.NT Coq__1.Coq_expression_statement_nt
  | Nis_438 -> Coq__1.NT Coq__1.Coq_iteration_statement_statement_safe__nt
  | Nis_437 -> Coq__1.NT Coq__1.Coq_jump_statement_nt
  | Nis_436 -> Coq__1.NT Coq__1.Coq_labeled_statement_statement_safe__nt
  | Nis_435 -> Coq__1.NT Coq__1.Coq_selection_statement_safe_nt
  | Nis_434 -> Coq__1.NT Coq__1.Coq_statement_safe_nt
  | Nis_433 -> Coq__1.T Coq__1.COLON_t
  | Nis_432 -> Coq__1.NT Coq__1.Coq_constant_expression_nt
  | Nis_431 -> Coq__1.T Coq__1.CASE_t
  | Nis_430 -> Coq__1.T Coq__1.COLON_t
  | Nis_429 -> Coq__1.T Coq__1.DEFAULT_t
  | Nis_428 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_426 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_425 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_424 -> Coq__1.T Coq__1.WHILE_t
  | Nis_423 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_422 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_420 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_419 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_417 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_416 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_415 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_413 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_412 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_410 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_409 -> Coq__1.NT Coq__1.Coq_declaration_nt
  | Nis_408 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_407 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_405 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_404 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_402 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_401 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_400 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_398 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_397 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_395 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_394 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_393 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_392 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_390 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_389 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_387 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_386 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_385 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_383 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_382 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_381 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_379 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_378 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_377 -> Coq__1.T Coq__1.WHILE_t
  | Nis_376 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_375 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_374 -> Coq__1.NT Coq__1.Coq_compound_statement_nt
  | Nis_373 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_372 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_371 -> Coq__1.NT Coq__1.Coq_expression_statement_nt
  | Nis_370 ->
    Coq__1.NT Coq__1.Coq_iteration_statement_statement_dangerous__nt
  | Nis_369 -> Coq__1.NT Coq__1.Coq_jump_statement_nt
  | Nis_368 -> Coq__1.NT Coq__1.Coq_labeled_statement_statement_dangerous__nt
  | Nis_367 -> Coq__1.NT Coq__1.Coq_selection_statement_dangerous_nt
  | Nis_366 -> Coq__1.NT Coq__1.Coq_statement_dangerous_nt
  | Nis_365 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_364 -> Coq__1.T Coq__1.BREAK_t
  | Nis_363 -> Coq__1.T Coq__1.COLON_t
  | Nis_362 -> Coq__1.NT Coq__1.Coq_constant_expression_nt
  | Nis_361 -> Coq__1.T Coq__1.CASE_t
  | Nis_360 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_359 -> Coq__1.T Coq__1.CONTINUE_t
  | Nis_358 -> Coq__1.T Coq__1.COLON_t
  | Nis_357 -> Coq__1.T Coq__1.DEFAULT_t
  | Nis_356 -> Coq__1.T Coq__1.DO_t
  | Nis_354 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_353 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_352 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_351 -> Coq__1.T Coq__1.FOR_t
  | Nis_350 -> Coq__1.T Coq__1.DO_t
  | Nis_348 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_347 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_346 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_345 -> Coq__1.T Coq__1.FOR_t
  | Nis_344 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_343 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_342 -> Coq__1.T Coq__1.GOTO_t
  | Nis_340 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_339 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_338 -> Coq__1.T Coq__1.IF_t
  | Nis_337 -> Coq__1.T Coq__1.COLON_t
  | Nis_336 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_334 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_333 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_332 -> Coq__1.T Coq__1.SWITCH_t
  | Nis_330 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_329 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_328 -> Coq__1.T Coq__1.WHILE_t
  | Nis_326 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_325 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_324 -> Coq__1.T Coq__1.IF_t
  | Nis_323 -> Coq__1.T Coq__1.COLON_t
  | Nis_322 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_321 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_320 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_319 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_318 -> Coq__1.T Coq__1.RETURN_t
  | Nis_317 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_315 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_314 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_313 -> Coq__1.T Coq__1.SWITCH_t
  | Nis_311 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_310 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_309 -> Coq__1.T Coq__1.WHILE_t
  | Nis_308 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_307 -> Coq__1.NT Coq__1.Coq_declarator_nt
  | Nis_306 -> Coq__1.NT Coq__1.Coq_init_declarator_nt
  | Nis_305 -> Coq__1.NT Coq__1.Coq_c_initializer_nt
  | Nis_304 -> Coq__1.T Coq__1.EQ_t
  | Nis_303 -> Coq__1.NT Coq__1.Coq_declarator_nt
  | Nis_302 -> Coq__1.NT Coq__1.Coq_init_declarator_nt
  | Nis_301 -> Coq__1.T Coq__1.COMMA_t
  | Nis_300 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_299 -> Coq__1.NT Coq__1.Coq_init_declarator_list_nt
  | Nis_298 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_297 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_296 -> Coq__1.NT Coq__1.Coq_external_declaration_nt
  | Nis_295 -> Coq__1.NT Coq__1.Coq_function_definition_nt
  | Nis_294 -> Coq__1.T Coq__1.EOF_t
  | Nis_293 -> Coq__1.NT Coq__1.Coq_translation_unit_nt
  | Nis_292 -> Coq__1.NT Coq__1.Coq_translation_unit_file_nt
  | Nis_291 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_290 -> Coq__1.T Coq__1.COMMA_t
  | Nis_289 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_288 -> Coq__1.NT Coq__1.Coq_enumerator_list_nt
  | Nis_287 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_286 -> Coq__1.NT Coq__1.Coq_enumerator_nt
  | Nis_285 -> Coq__1.NT Coq__1.Coq_constant_expression_nt
  | Nis_284 -> Coq__1.NT Coq__1.Coq_unary_expression_nt
  | Nis_282 -> Coq__1.NT Coq__1.Coq_type_name_nt
  | Nis_281 -> Coq__1.NT Coq__1.Coq_cast_expression_nt
  | Nis_279 -> Coq__1.NT Coq__1.Coq_type_name_nt
  | Nis_278 -> Coq__1.NT Coq__1.Coq_unary_expression_nt
  | Nis_276 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_275 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_274 -> Coq__1.T Coq__1.COMMA_t
  | Nis_273 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_272 -> Coq__1.NT Coq__1.Coq_initializer_list_nt
  | Nis_271 -> Coq__1.NT Coq__1.Coq_c_initializer_nt
  | Nis_270 -> Coq__1.NT Coq__1.Coq_c_initializer_nt
  | Nis_269 -> Coq__1.NT Coq__1.Coq_designation_nt
  | Nis_268 -> Coq__1.NT Coq__1.Coq_c_initializer_nt
  | Nis_267 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_266 -> Coq__1.NT Coq__1.Coq_c_initializer_nt
  | Nis_265 -> Coq__1.NT Coq__1.Coq_designation_nt
  | Nis_264 -> Coq__1.NT Coq__1.Coq_designator_nt
  | Nis_263 -> Coq__1.NT Coq__1.Coq_designator_nt
  | Nis_262 -> Coq__1.T Coq__1.EQ_t
  | Nis_261 -> Coq__1.NT Coq__1.Coq_designator_list_nt
  | Nis_260 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_259 -> Coq__1.T Coq__1.COMMA_t
  | Nis_258 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_257 -> Coq__1.NT Coq__1.Coq_initializer_list_nt
  | Nis_256 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_255 -> Coq__1.T Coq__1.DOT_t
  | Nis_254 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_253 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_252 -> Coq__1.NT Coq__1.Coq_constant_expression_nt
  | Nis_251 -> Coq__1.T Coq__1.LBRACK_t
  | Nis_250 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_248 -> Coq__1.NT Coq__1.Coq_type_name_nt
  | Nis_247 -> Coq__1.NT Coq__1.Coq_unary_expression_nt
  | Nis_246 -> Coq__1.NT Coq__1.Coq_abstract_declarator_nt
  | Nis_245 -> Coq__1.NT Coq__1.Coq_pointer_nt
  | Nis_244 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_243 -> Coq__1.NT Coq__1.Coq_specifier_qualifier_list_nt
  | Nis_241 -> Coq__1.NT Coq__1.Coq_type_name_nt
  | Nis_240 -> Coq__1.NT Coq__1.Coq_specifier_qualifier_list_nt
  | Nis_239 -> Coq__1.NT Coq__1.Coq_specifier_qualifier_list_nt
  | Nis_238 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_237 -> Coq__1.NT Coq__1.Coq_struct_declaration_list_nt
  | Nis_236 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_235 -> Coq__1.NT Coq__1.Coq_struct_declaration_nt
  | Nis_234 -> Coq__1.NT Coq__1.Coq_struct_declarator_nt
  | Nis_233 -> Coq__1.NT Coq__1.Coq_constant_expression_nt
  | Nis_232 -> Coq__1.T Coq__1.COLON_t
  | Nis_231 -> Coq__1.NT Coq__1.Coq_declarator_nt
  | Nis_230 -> Coq__1.NT Coq__1.Coq_struct_declarator_nt
  | Nis_229 -> Coq__1.T Coq__1.COMMA_t
  | Nis_228 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_227 -> Coq__1.NT Coq__1.Coq_struct_declarator_list_nt
  | Nis_226 -> Coq__1.NT Coq__1.Coq_conditional_expression_nt
  | Nis_225 -> Coq__1.NT Coq__1.Coq_constant_expression_nt
  | Nis_224 -> Coq__1.T Coq__1.COLON_t
  | Nis_223 -> Coq__1.NT Coq__1.Coq_abstract_declarator_nt
  | Nis_222 -> Coq__1.NT Coq__1.Coq_declarator_nt
  | Nis_220 -> Coq__1.NT Coq__1.Coq_abstract_declarator_nt
  | Nis_218 -> Coq__1.NT Coq__1.Coq_declarator_nt
  | Nis_217 -> Coq__1.NT Coq__1.Coq_direct_abstract_declarator_nt
  | Nis_216 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_215 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_214 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_213 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_212 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_211 -> Coq__1.NT Coq__1.Coq_type_qualifier_list_nt
  | Nis_210 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_209 -> Coq__1.T Coq__1.LBRACK_t
  | Nis_208 -> Coq__1.NT Coq__1.Coq_direct_declarator_nt
  | Nis_206 -> Coq__1.NT Coq__1.Coq_parameter_type_list_nt
  | Nis_205 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_204 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_203 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_202 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_201 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_200 -> Coq__1.NT Coq__1.Coq_type_qualifier_list_nt
  | Nis_199 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_198 -> Coq__1.T Coq__1.LBRACK_t
  | Nis_197 -> Coq__1.NT Coq__1.Coq_parameter_declaration_nt
  | Nis_195 -> Coq__1.NT Coq__1.Coq_parameter_type_list_nt
  | Nis_193 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_192 -> Coq__1.NT Coq__1.Coq_direct_abstract_declarator_nt
  | Nis_191 -> Coq__1.NT Coq__1.Coq_pointer_nt
  | Nis_190 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_189 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_188 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_187 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_186 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_185 -> Coq__1.NT Coq__1.Coq_type_qualifier_list_nt
  | Nis_184 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_183 -> Coq__1.T Coq__1.LBRACK_t
  | Nis_181 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_180 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_179 -> Coq__1.NT Coq__1.Coq_parameter_declaration_nt
  | Nis_178 -> Coq__1.T Coq__1.ELLIPSIS_t
  | Nis_177 -> Coq__1.T Coq__1.COMMA_t
  | Nis_176 -> Coq__1.NT Coq__1.Coq_parameter_list_nt
  | Nis_174 -> Coq__1.NT Coq__1.Coq_parameter_type_list_nt
  | Nis_173 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_172 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_171 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_170 -> Coq__1.NT Coq__1.Coq_declaration_specifiers_nt
  | Nis_169 -> Coq__1.NT Coq__1.Coq_enum_specifier_nt
  | Nis_168 -> Coq__1.NT Coq__1.Coq_function_specifier_nt
  | Nis_167 -> Coq__1.NT Coq__1.Coq_storage_class_specifier_nt
  | Nis_166 -> Coq__1.NT Coq__1.Coq_type_qualifier_nt
  | Nis_165 -> Coq__1.NT Coq__1.Coq_type_specifier_nt
  | Nis_164 -> Coq__1.T Coq__1.AUTO_t
  | Nis_162 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_161 -> Coq__1.NT Coq__1.Coq_direct_declarator_nt
  | Nis_160 -> Coq__1.NT Coq__1.Coq_pointer_nt
  | Nis_159 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_158 -> Coq__1.T Coq__1.SEMICOLON_t
  | Nis_157 -> Coq__1.NT Coq__1.Coq_pointer_nt
  | Nis_156 -> Coq__1.NT Coq__1.Coq_type_qualifier_nt
  | Nis_155 -> Coq__1.NT Coq__1.Coq_pointer_nt
  | Nis_154 -> Coq__1.NT Coq__1.Coq_type_qualifier_nt
  | Nis_153 -> Coq__1.NT Coq__1.Coq_type_qualifier_list_nt
  | Nis_152 -> Coq__1.T Coq__1.STAR_t
  | Nis_151 -> Coq__1.T Coq__1.VAR_NAME_t
  | Nis_150 -> Coq__1.NT Coq__1.Coq_specifier_qualifier_list_nt
  | Nis_149 -> Coq__1.NT Coq__1.Coq_struct_declaration_nt
  | Nis_148 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_147 -> Coq__1.NT Coq__1.Coq_struct_declaration_list_nt
  | Nis_146 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_145 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_144 -> Coq__1.NT Coq__1.Coq_struct_or_union_nt
  | Nis_143 -> Coq__1.NT Coq__1.Coq_struct_or_union_specifier_nt
  | Nis_142 -> Coq__1.NT Coq__1.Coq_type_qualifier_nt
  | Nis_141 -> Coq__1.NT Coq__1.Coq_type_specifier_nt
  | Nis_140 -> Coq__1.T Coq__1.BOOL_t
  | Nis_139 -> Coq__1.T Coq__1.CHAR_t
  | Nis_138 -> Coq__1.T Coq__1.CONST_t
  | Nis_137 -> Coq__1.T Coq__1.COMMA_t
  | Nis_136 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_135 -> Coq__1.NT Coq__1.Coq_cast_expression_nt
  | Nis_134 -> Coq__1.T Coq__1.DEC_t
  | Nis_133 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_132 -> Coq__1.T Coq__1.DOT_t
  | Nis_131 -> Coq__1.T Coq__1.INC_t
  | Nis_130 -> Coq__1.T Coq__1.RBRACK_t
  | Nis_129 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_128 -> Coq__1.T Coq__1.LBRACK_t
  | Nis_127 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_126 -> Coq__1.T Coq__1.COMMA_t
  | Nis_124 -> Coq__1.NT Coq__1.Coq_argument_expression_list_nt
  | Nis_123 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_122 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_121 -> Coq__1.NT Coq__1.Coq_logical_AND_expression_nt
  | Nis_120 -> Coq__1.T Coq__1.BARBAR_t
  | Nis_119 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_118 -> Coq__1.NT Coq__1.Coq_conditional_expression_nt
  | Nis_117 -> Coq__1.T Coq__1.COLON_t
  | Nis_116 -> Coq__1.NT Coq__1.Coq_assignment_expression_nt
  | Nis_115 -> Coq__1.NT Coq__1.Coq_conditional_expression_nt
  | Nis_114 -> Coq__1.T Coq__1.COMMA_t
  | Nis_113 -> Coq__1.NT Coq__1.Coq_expression_nt
  | Nis_112 -> Coq__1.NT Coq__1.Coq_inclusive_OR_expression_nt
  | Nis_111 -> Coq__1.NT Coq__1.Coq_exclusive_OR_expression_nt
  | Nis_110 -> Coq__1.NT Coq__1.AND_expression_nt
  | Nis_109 -> Coq__1.NT Coq__1.Coq_equality_expression_nt
  | Nis_108 -> Coq__1.T Coq__1.AND_t
  | Nis_107 -> Coq__1.NT Coq__1.AND_expression_nt
  | Nis_106 -> Coq__1.NT Coq__1.Coq_relational_expression_nt
  | Nis_105 -> Coq__1.T Coq__1.EQEQ_t
  | Nis_104 -> Coq__1.NT Coq__1.Coq_relational_expression_nt
  | Nis_103 -> Coq__1.T Coq__1.NEQ_t
  | Nis_102 -> Coq__1.NT Coq__1.Coq_equality_expression_nt
  | Nis_101 -> Coq__1.T Coq__1.HAT_t
  | Nis_100 -> Coq__1.NT Coq__1.Coq_exclusive_OR_expression_nt
  | Nis_99 -> Coq__1.T Coq__1.BAR_t
  | Nis_98 -> Coq__1.NT Coq__1.Coq_inclusive_OR_expression_nt
  | Nis_97 -> Coq__1.T Coq__1.ANDAND_t
  | Nis_96 -> Coq__1.NT Coq__1.Coq_logical_AND_expression_nt
  | Nis_95 -> Coq__1.T Coq__1.QUESTION_t
  | Nis_94 -> Coq__1.NT Coq__1.Coq_logical_OR_expression_nt
  | Nis_93 -> Coq__1.NT Coq__1.Coq_shift_expression_nt
  | Nis_92 -> Coq__1.T Coq__1.GEQ_t
  | Nis_91 -> Coq__1.NT Coq__1.Coq_shift_expression_nt
  | Nis_90 -> Coq__1.T Coq__1.GT_t
  | Nis_89 -> Coq__1.NT Coq__1.Coq_shift_expression_nt
  | Nis_88 -> Coq__1.T Coq__1.LEQ_t
  | Nis_87 -> Coq__1.NT Coq__1.Coq_additive_expression_nt
  | Nis_86 -> Coq__1.NT Coq__1.Coq_shift_expression_nt
  | Nis_85 -> Coq__1.T Coq__1.LT_t
  | Nis_84 -> Coq__1.NT Coq__1.Coq_relational_expression_nt
  | Nis_83 -> Coq__1.NT Coq__1.Coq_additive_expression_nt
  | Nis_82 -> Coq__1.T Coq__1.LEFT_t
  | Nis_81 -> Coq__1.NT Coq__1.Coq_multiplicative_expression_nt
  | Nis_80 -> Coq__1.T Coq__1.MINUS_t
  | Nis_79 -> Coq__1.NT Coq__1.Coq_multiplicative_expression_nt
  | Nis_78 -> Coq__1.T Coq__1.PLUS_t
  | Nis_77 -> Coq__1.NT Coq__1.Coq_additive_expression_nt
  | Nis_76 -> Coq__1.NT Coq__1.Coq_cast_expression_nt
  | Nis_75 -> Coq__1.NT Coq__1.Coq_cast_expression_nt
  | Nis_74 -> Coq__1.T Coq__1.PERCENT_t
  | Nis_73 -> Coq__1.NT Coq__1.Coq_cast_expression_nt
  | Nis_72 -> Coq__1.T Coq__1.SLASH_t
  | Nis_71 -> Coq__1.NT Coq__1.Coq_cast_expression_nt
  | Nis_70 -> Coq__1.T Coq__1.STAR_t
  | Nis_69 -> Coq__1.NT Coq__1.Coq_multiplicative_expression_nt
  | Nis_68 -> Coq__1.T Coq__1.RIGHT_t
  | Nis_67 -> Coq__1.NT Coq__1.Coq_shift_expression_nt
  | Nis_66 -> Coq__1.NT Coq__1.Coq_assignment_operator_nt
  | Nis_65 -> Coq__1.T Coq__1.ADD_ASSIGN_t
  | Nis_64 -> Coq__1.T Coq__1.AND_ASSIGN_t
  | Nis_63 -> Coq__1.T Coq__1.DIV_ASSIGN_t
  | Nis_62 -> Coq__1.T Coq__1.EQ_t
  | Nis_61 -> Coq__1.T Coq__1.LEFT_ASSIGN_t
  | Nis_60 -> Coq__1.T Coq__1.MOD_ASSIGN_t
  | Nis_59 -> Coq__1.T Coq__1.MUL_ASSIGN_t
  | Nis_58 -> Coq__1.T Coq__1.OR_ASSIGN_t
  | Nis_57 -> Coq__1.T Coq__1.RIGHT_ASSIGN_t
  | Nis_56 -> Coq__1.T Coq__1.SUB_ASSIGN_t
  | Nis_55 -> Coq__1.T Coq__1.XOR_ASSIGN_t
  | Nis_54 -> Coq__1.NT Coq__1.Coq_unary_expression_nt
  | Nis_52 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_51 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_50 -> Coq__1.T Coq__1.PTR_t
  | Nis_49 -> Coq__1.NT Coq__1.Coq_postfix_expression_nt
  | Nis_48 -> Coq__1.NT Coq__1.Coq_primary_expression_nt
  | Nis_47 -> Coq__1.NT Coq__1.Coq_unary_expression_nt
  | Nis_46 -> Coq__1.NT Coq__1.Coq_unary_operator_nt
  | Nis_45 -> Coq__1.T Coq__1.AND_t
  | Nis_44 -> Coq__1.T Coq__1.BANG_t
  | Nis_43 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_42 -> Coq__1.T Coq__1.BUILTIN_VA_ARG_t
  | Nis_41 -> Coq__1.T Coq__1.CONSTANT_t
  | Nis_40 -> Coq__1.T Coq__1.DEC_t
  | Nis_39 -> Coq__1.T Coq__1.DOUBLE_t
  | Nis_38 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_37 -> Coq__1.T Coq__1.INC_t
  | Nis_36 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_35 -> Coq__1.T Coq__1.LPAREN_t
  | Nis_34 -> Coq__1.T Coq__1.MINUS_t
  | Nis_33 -> Coq__1.T Coq__1.PLUS_t
  | Nis_32 -> Coq__1.T Coq__1.SIZEOF_t
  | Nis_31 -> Coq__1.T Coq__1.STAR_t
  | Nis_30 -> Coq__1.T Coq__1.TILDE_t
  | Nis_29 -> Coq__1.T Coq__1.VAR_NAME_t
  | Nis_28 -> Coq__1.T Coq__1.EQ_t
  | Nis_27 -> Coq__1.NT Coq__1.Coq_enumeration_constant_nt
  | Nis_26 -> Coq__1.NT Coq__1.Coq_enumerator_nt
  | Nis_25 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_24 -> Coq__1.T Coq__1.COMMA_t
  | Nis_23 -> Coq__1.T Coq__1.RBRACE_t
  | Nis_22 -> Coq__1.NT Coq__1.Coq_enumerator_list_nt
  | Nis_21 -> Coq__1.T Coq__1.VAR_NAME_t
  | Nis_20 -> Coq__1.T Coq__1.LBRACE_t
  | Nis_19 -> Coq__1.T Coq__1.OTHER_NAME_t
  | Nis_18 -> Coq__1.T Coq__1.ENUM_t
  | Nis_17 -> Coq__1.T Coq__1.EXTERN_t
  | Nis_16 -> Coq__1.T Coq__1.FLOAT_t
  | Nis_15 -> Coq__1.T Coq__1.INLINE_t
  | Nis_14 -> Coq__1.T Coq__1.INT_t
  | Nis_13 -> Coq__1.T Coq__1.LONG_t
  | Nis_12 -> Coq__1.T Coq__1.REGISTER_t
  | Nis_11 -> Coq__1.T Coq__1.RESTRICT_t
  | Nis_10 -> Coq__1.T Coq__1.SHORT_t
  | Nis_9 -> Coq__1.T Coq__1.SIGNED_t
  | Nis_8 -> Coq__1.T Coq__1.STATIC_t
  | Nis_7 -> Coq__1.T Coq__1.STRUCT_t
  | Nis_6 -> Coq__1.T Coq__1.TYPEDEF_t
  | Nis_5 -> Coq__1.T Coq__1.TYPEDEF_NAME_t
  | Nis_4 -> Coq__1.T Coq__1.UNION_t
  | Nis_3 -> Coq__1.T Coq__1.UNSIGNED_t
  | Nis_2 -> Coq__1.T Coq__1.VOID_t
  | Nis_1 -> Coq__1.T Coq__1.VOLATILE_t
  | _ -> Coq__1.T Coq__1.RPAREN_t
  
  type state =
  | Init
  | Ninit of noninitstate
  
  (** val state_rect : 'a1 -> (noninitstate -> 'a1) -> state -> 'a1 **)
  
  let state_rect f f0 = function
  | Init -> f
  | Ninit x -> f0 x
  
  (** val state_rec : 'a1 -> (noninitstate -> 'a1) -> state -> 'a1 **)
  
  let state_rec f f0 = function
  | Init -> f
  | Ninit x -> f0 x
  
  (** val coq_StateAlph : state coq_Alphabet **)
  
  let coq_StateAlph =
    { coq_AlphabetComparable = (fun x y ->
      match x with
      | Init ->
        (match y with
         | Init -> Eq
         | Ninit n -> Lt)
      | Ninit x0 ->
        (match y with
         | Init -> Gt
         | Ninit y0 ->
           compare coq_NonInitStateAlph.coq_AlphabetComparable x0 y0));
      coq_AlphabetFinite =
      (Init::(List0.map (fun x -> Ninit x)
               (all_list coq_NonInitStateAlph.coq_AlphabetFinite))) }
  
  type action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act
  
  (** val action_rect :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> action -> 'a1 **)
  
  let action_rect term f f0 f1 = function
  | Shift_act x -> f x __
  | Reduce_act x -> f0 x
  | Fail_act -> f1
  
  (** val action_rec :
      Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production ->
      'a1) -> 'a1 -> action -> 'a1 **)
  
  let action_rec term f f0 f1 = function
  | Shift_act x -> f x __
  | Reduce_act x -> f0 x
  | Fail_act -> f1
  
  type default_action =
  | Default_reduce_act of Gram.production
  | Accept_act
  
  (** val default_action_rect :
      (Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1 **)
  
  let default_action_rect f f0 = function
  | Default_reduce_act x -> f x
  | Accept_act -> f0
  
  (** val default_action_rec :
      (Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1 **)
  
  let default_action_rec f f0 = function
  | Default_reduce_act x -> f x
  | Accept_act -> f0
  
  type pseudoprod = Gram.production option
  
  type item = { pseudoprod_item : pseudoprod; dot_pos_item : nat;
                lookaheads_item : Gram.terminal list }
  
  (** val item_rect :
      (pseudoprod -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1 **)
  
  let item_rect f i =
    let { pseudoprod_item = x; dot_pos_item = x0; lookaheads_item = x1 } = i
    in
    f x x0 x1
  
  (** val item_rec :
      (pseudoprod -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1 **)
  
  let item_rec f i =
    let { pseudoprod_item = x; dot_pos_item = x0; lookaheads_item = x1 } = i
    in
    f x x0 x1
  
  (** val pseudoprod_item : item -> pseudoprod **)
  
  let pseudoprod_item x = x.pseudoprod_item
  
  (** val dot_pos_item : item -> nat **)
  
  let dot_pos_item x = x.dot_pos_item
  
  (** val lookaheads_item : item -> Gram.terminal list **)
  
  let lookaheads_item x = x.lookaheads_item
  
  (** val action_table :
      state -> (default_action, Coq__1.terminal -> action) sum **)
  
  let action_table = function
  | Init ->
    Coq_inr (fun terminal0 ->
      match terminal0 with
      | Coq__1.AUTO_t -> Shift_act Nis_164
      | Coq__1.BOOL_t -> Shift_act Nis_140
      | Coq__1.CHAR_t -> Shift_act Nis_139
      | Coq__1.CONST_t -> Shift_act Nis_138
      | Coq__1.DOUBLE_t -> Shift_act Nis_39
      | Coq__1.ENUM_t -> Shift_act Nis_18
      | Coq__1.EXTERN_t -> Shift_act Nis_17
      | Coq__1.FLOAT_t -> Shift_act Nis_16
      | Coq__1.INLINE_t -> Shift_act Nis_15
      | Coq__1.INT_t -> Shift_act Nis_14
      | Coq__1.LONG_t -> Shift_act Nis_13
      | Coq__1.REGISTER_t -> Shift_act Nis_12
      | Coq__1.RESTRICT_t -> Shift_act Nis_11
      | Coq__1.SHORT_t -> Shift_act Nis_10
      | Coq__1.SIGNED_t -> Shift_act Nis_9
      | Coq__1.STATIC_t -> Shift_act Nis_8
      | Coq__1.STRUCT_t -> Shift_act Nis_7
      | Coq__1.TYPEDEF_t -> Shift_act Nis_6
      | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
      | Coq__1.UNION_t -> Shift_act Nis_4
      | Coq__1.UNSIGNED_t -> Shift_act Nis_3
      | Coq__1.VOID_t -> Shift_act Nis_2
      | Coq__1.VOLATILE_t -> Shift_act Nis_1
      | _ -> Fail_act)
  | Ninit n ->
    (match n with
     | Nis_504 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_229))
     | Nis_503 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_96))
     | Nis_502 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_97))
     | Nis_501 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_26))
     | Nis_500 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_27))
     | Nis_499 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_33))
     | Nis_498 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACE_t -> Shift_act Nis_499
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_497 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_24))
     | Nis_496 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_25))
     | Nis_495 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_34))
     | Nis_494 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_493 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ELSE_t -> Shift_act Nis_494
         | _ -> Fail_act)
     | Nis_492 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_109))
     | Nis_491 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_123))
     | Nis_490 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_188))
     | Nis_489 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_190))
     | Nis_488 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_142))
     | Nis_487 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_145))
     | Nis_486 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_186))
     | Nis_485 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_187))
     | Nis_484 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_189))
     | Nis_483 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_482 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ELSE_t -> Shift_act Nis_483
         | _ -> Fail_act)
     | Nis_481 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_126))
     | Nis_480 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_479 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_480
         | _ -> Fail_act)
     | Nis_478 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_132))
     | Nis_477 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_476 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_477
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_475 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_476
         | _ -> Fail_act)
     | Nis_474 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_129))
     | Nis_473 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_472 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_473
         | _ -> Fail_act)
     | Nis_471 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_135))
     | Nis_470 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_469 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_470
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_468 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_469
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_467 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_125))
     | Nis_466 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_465 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_466
         | _ -> Fail_act)
     | Nis_464 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_131))
     | Nis_463 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_462 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_463
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_461 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_462
         | _ -> Fail_act)
     | Nis_460 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_128))
     | Nis_459 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_458 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_459
         | _ -> Fail_act)
     | Nis_457 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_134))
     | Nis_456 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_455 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_456
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_454 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_455
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_453 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_454
         | _ -> Fail_act)
     | Nis_452 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_127))
     | Nis_451 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_450 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_451
         | _ -> Fail_act)
     | Nis_449 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_133))
     | Nis_448 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_447 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_448
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_446 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_447
         | _ -> Fail_act)
     | Nis_445 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_130))
     | Nis_444 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_443 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_444
         | _ -> Fail_act)
     | Nis_442 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_136))
     | Nis_441 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_147))
     | Nis_440 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Fail_act
         | Coq__1.ANDAND_t -> Fail_act
         | Coq__1.AND_ASSIGN_t -> Fail_act
         | Coq__1.BAR_t -> Fail_act
         | Coq__1.BARBAR_t -> Fail_act
         | Coq__1.COLON_t -> Fail_act
         | Coq__1.COMMA_t -> Fail_act
         | Coq__1.DIV_ASSIGN_t -> Fail_act
         | Coq__1.DOT_t -> Fail_act
         | Coq__1.ELLIPSIS_t -> Fail_act
         | Coq__1.ELSE_t -> Reduce_act (Obj.magic Coq__1.Prod_205)
         | Coq__1.EOF_t -> Fail_act
         | Coq__1.EQ_t -> Fail_act
         | Coq__1.EQEQ_t -> Fail_act
         | Coq__1.GEQ_t -> Fail_act
         | Coq__1.GT_t -> Fail_act
         | Coq__1.HAT_t -> Fail_act
         | Coq__1.LBRACK_t -> Fail_act
         | Coq__1.LEFT_t -> Fail_act
         | Coq__1.LEFT_ASSIGN_t -> Fail_act
         | Coq__1.LEQ_t -> Fail_act
         | Coq__1.LT_t -> Fail_act
         | Coq__1.MOD_ASSIGN_t -> Fail_act
         | Coq__1.MUL_ASSIGN_t -> Fail_act
         | Coq__1.NEQ_t -> Fail_act
         | Coq__1.OR_ASSIGN_t -> Fail_act
         | Coq__1.PERCENT_t -> Fail_act
         | Coq__1.PTR_t -> Fail_act
         | Coq__1.QUESTION_t -> Fail_act
         | Coq__1.RBRACK_t -> Fail_act
         | Coq__1.RIGHT_t -> Fail_act
         | Coq__1.RIGHT_ASSIGN_t -> Fail_act
         | Coq__1.RPAREN_t -> Fail_act
         | Coq__1.SLASH_t -> Fail_act
         | Coq__1.SUB_ASSIGN_t -> Fail_act
         | Coq__1.XOR_ASSIGN_t -> Fail_act
         | _ -> Reduce_act (Obj.magic Coq__1.Prod_199))
     | Nis_439 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Fail_act
         | Coq__1.ANDAND_t -> Fail_act
         | Coq__1.AND_ASSIGN_t -> Fail_act
         | Coq__1.BAR_t -> Fail_act
         | Coq__1.BARBAR_t -> Fail_act
         | Coq__1.COLON_t -> Fail_act
         | Coq__1.COMMA_t -> Fail_act
         | Coq__1.DIV_ASSIGN_t -> Fail_act
         | Coq__1.DOT_t -> Fail_act
         | Coq__1.ELLIPSIS_t -> Fail_act
         | Coq__1.ELSE_t -> Reduce_act (Obj.magic Coq__1.Prod_206)
         | Coq__1.EOF_t -> Fail_act
         | Coq__1.EQ_t -> Fail_act
         | Coq__1.EQEQ_t -> Fail_act
         | Coq__1.GEQ_t -> Fail_act
         | Coq__1.GT_t -> Fail_act
         | Coq__1.HAT_t -> Fail_act
         | Coq__1.LBRACK_t -> Fail_act
         | Coq__1.LEFT_t -> Fail_act
         | Coq__1.LEFT_ASSIGN_t -> Fail_act
         | Coq__1.LEQ_t -> Fail_act
         | Coq__1.LT_t -> Fail_act
         | Coq__1.MOD_ASSIGN_t -> Fail_act
         | Coq__1.MUL_ASSIGN_t -> Fail_act
         | Coq__1.NEQ_t -> Fail_act
         | Coq__1.OR_ASSIGN_t -> Fail_act
         | Coq__1.PERCENT_t -> Fail_act
         | Coq__1.PTR_t -> Fail_act
         | Coq__1.QUESTION_t -> Fail_act
         | Coq__1.RBRACK_t -> Fail_act
         | Coq__1.RIGHT_t -> Fail_act
         | Coq__1.RIGHT_ASSIGN_t -> Fail_act
         | Coq__1.RPAREN_t -> Fail_act
         | Coq__1.SLASH_t -> Fail_act
         | Coq__1.SUB_ASSIGN_t -> Fail_act
         | Coq__1.XOR_ASSIGN_t -> Fail_act
         | _ -> Reduce_act (Obj.magic Coq__1.Prod_200))
     | Nis_438 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_208))
     | Nis_437 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Fail_act
         | Coq__1.ANDAND_t -> Fail_act
         | Coq__1.AND_ASSIGN_t -> Fail_act
         | Coq__1.BAR_t -> Fail_act
         | Coq__1.BARBAR_t -> Fail_act
         | Coq__1.COLON_t -> Fail_act
         | Coq__1.COMMA_t -> Fail_act
         | Coq__1.DIV_ASSIGN_t -> Fail_act
         | Coq__1.DOT_t -> Fail_act
         | Coq__1.ELLIPSIS_t -> Fail_act
         | Coq__1.ELSE_t -> Reduce_act (Obj.magic Coq__1.Prod_209)
         | Coq__1.EOF_t -> Fail_act
         | Coq__1.EQ_t -> Fail_act
         | Coq__1.EQEQ_t -> Fail_act
         | Coq__1.GEQ_t -> Fail_act
         | Coq__1.GT_t -> Fail_act
         | Coq__1.HAT_t -> Fail_act
         | Coq__1.LBRACK_t -> Fail_act
         | Coq__1.LEFT_t -> Fail_act
         | Coq__1.LEFT_ASSIGN_t -> Fail_act
         | Coq__1.LEQ_t -> Fail_act
         | Coq__1.LT_t -> Fail_act
         | Coq__1.MOD_ASSIGN_t -> Fail_act
         | Coq__1.MUL_ASSIGN_t -> Fail_act
         | Coq__1.NEQ_t -> Fail_act
         | Coq__1.OR_ASSIGN_t -> Fail_act
         | Coq__1.PERCENT_t -> Fail_act
         | Coq__1.PTR_t -> Fail_act
         | Coq__1.QUESTION_t -> Fail_act
         | Coq__1.RBRACK_t -> Fail_act
         | Coq__1.RIGHT_t -> Fail_act
         | Coq__1.RIGHT_ASSIGN_t -> Fail_act
         | Coq__1.RPAREN_t -> Fail_act
         | Coq__1.SLASH_t -> Fail_act
         | Coq__1.SUB_ASSIGN_t -> Fail_act
         | Coq__1.XOR_ASSIGN_t -> Fail_act
         | _ -> Reduce_act (Obj.magic Coq__1.Prod_203))
     | Nis_436 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_204))
     | Nis_435 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_207))
     | Nis_434 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_146))
     | Nis_433 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_432 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_433
         | _ -> Fail_act)
     | Nis_430 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_429 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_430
         | _ -> Fail_act)
     | Nis_428 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Fail_act
         | Coq__1.ANDAND_t -> Fail_act
         | Coq__1.AND_ASSIGN_t -> Fail_act
         | Coq__1.BAR_t -> Fail_act
         | Coq__1.BARBAR_t -> Fail_act
         | Coq__1.COLON_t -> Fail_act
         | Coq__1.COMMA_t -> Fail_act
         | Coq__1.DIV_ASSIGN_t -> Fail_act
         | Coq__1.DOT_t -> Fail_act
         | Coq__1.ELLIPSIS_t -> Fail_act
         | Coq__1.ELSE_t -> Reduce_act (Obj.magic Coq__1.Prod_124)
         | Coq__1.EOF_t -> Fail_act
         | Coq__1.EQ_t -> Fail_act
         | Coq__1.EQEQ_t -> Fail_act
         | Coq__1.GEQ_t -> Fail_act
         | Coq__1.GT_t -> Fail_act
         | Coq__1.HAT_t -> Fail_act
         | Coq__1.LBRACK_t -> Fail_act
         | Coq__1.LEFT_t -> Fail_act
         | Coq__1.LEFT_ASSIGN_t -> Fail_act
         | Coq__1.LEQ_t -> Fail_act
         | Coq__1.LT_t -> Fail_act
         | Coq__1.MOD_ASSIGN_t -> Fail_act
         | Coq__1.MUL_ASSIGN_t -> Fail_act
         | Coq__1.NEQ_t -> Fail_act
         | Coq__1.OR_ASSIGN_t -> Fail_act
         | Coq__1.PERCENT_t -> Fail_act
         | Coq__1.PTR_t -> Fail_act
         | Coq__1.QUESTION_t -> Fail_act
         | Coq__1.RBRACK_t -> Fail_act
         | Coq__1.RIGHT_t -> Fail_act
         | Coq__1.RIGHT_ASSIGN_t -> Fail_act
         | Coq__1.RPAREN_t -> Fail_act
         | Coq__1.SLASH_t -> Fail_act
         | Coq__1.SUB_ASSIGN_t -> Fail_act
         | Coq__1.XOR_ASSIGN_t -> Fail_act
         | _ -> Reduce_act (Obj.magic Coq__1.Prod_110))
     | Nis_427 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.SEMICOLON_t -> Shift_act Nis_428
         | _ -> Fail_act)
     | Nis_426 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_427
         | _ -> Fail_act)
     | Nis_424 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_425
         | _ -> Fail_act)
     | Nis_423 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.WHILE_t -> Shift_act Nis_424
         | _ -> Fail_act)
     | Nis_422 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_112))
     | Nis_421 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_420 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_421
         | _ -> Fail_act)
     | Nis_419 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_118))
     | Nis_418 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_417 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_418
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_416 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_417
         | _ -> Fail_act)
     | Nis_415 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_115))
     | Nis_414 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_413 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_414
         | _ -> Fail_act)
     | Nis_412 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_121))
     | Nis_411 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_410 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_411
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_409 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_410
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_408 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.SEMICOLON_t -> Shift_act Nis_298
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_407 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_111))
     | Nis_406 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_405 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_406
         | _ -> Fail_act)
     | Nis_404 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_117))
     | Nis_403 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_402 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_403
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_401 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_402
         | _ -> Fail_act)
     | Nis_400 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_114))
     | Nis_399 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_398 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_399
         | _ -> Fail_act)
     | Nis_397 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_120))
     | Nis_396 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_395 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_396
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_394 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_395
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_393 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_394
         | _ -> Fail_act)
     | Nis_392 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_113))
     | Nis_391 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_390 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_391
         | _ -> Fail_act)
     | Nis_389 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_119))
     | Nis_388 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_387 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_388
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_386 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_387
         | _ -> Fail_act)
     | Nis_385 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_116))
     | Nis_384 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_383 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_384
         | _ -> Fail_act)
     | Nis_382 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_122))
     | Nis_381 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_110))
     | Nis_380 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.SEMICOLON_t -> Shift_act Nis_381
         | _ -> Fail_act)
     | Nis_379 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_380
         | _ -> Fail_act)
     | Nis_377 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_378
         | _ -> Fail_act)
     | Nis_376 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.WHILE_t -> Shift_act Nis_377
         | _ -> Fail_act)
     | Nis_375 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_144))
     | Nis_374 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_199))
     | Nis_373 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_93))
     | Nis_372 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_373
         | _ -> Fail_act)
     | Nis_371 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_200))
     | Nis_370 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_202))
     | Nis_369 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_203))
     | Nis_368 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_198))
     | Nis_367 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_201))
     | Nis_366 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_143))
     | Nis_365 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_139))
     | Nis_364 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.SEMICOLON_t -> Shift_act Nis_365
         | _ -> Fail_act)
     | Nis_363 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_362 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_363
         | _ -> Fail_act)
     | Nis_360 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_138))
     | Nis_359 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.SEMICOLON_t -> Shift_act Nis_360
         | _ -> Fail_act)
     | Nis_358 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_357 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_358
         | _ -> Fail_act)
     | Nis_356 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_355 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_354 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_355
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_353 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_354
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_352 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SEMICOLON_t -> Shift_act Nis_353
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_351 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_352
         | _ -> Fail_act)
     | Nis_350 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_349 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_348 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_349
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_347 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_348
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_346 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SEMICOLON_t -> Shift_act Nis_347
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_345 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_346
         | _ -> Fail_act)
     | Nis_344 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_137))
     | Nis_343 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.SEMICOLON_t -> Shift_act Nis_344
         | _ -> Fail_act)
     | Nis_342 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_343
         | _ -> Fail_act)
     | Nis_341 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_340 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_341
         | _ -> Fail_act)
     | Nis_338 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_339
         | _ -> Fail_act)
     | Nis_337 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_336 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_337
         | _ -> Fail_act)
     | Nis_335 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_334 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_335
         | _ -> Fail_act)
     | Nis_332 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_333
         | _ -> Fail_act)
     | Nis_331 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_330 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_331
         | _ -> Fail_act)
     | Nis_328 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_329
         | _ -> Fail_act)
     | Nis_327 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_431
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_429
         | Coq__1.DO_t -> Shift_act Nis_350
         | Coq__1.FOR_t -> Shift_act Nis_345
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_338
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_336
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_332
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_328
         | _ -> Fail_act)
     | Nis_326 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_327
         | _ -> Fail_act)
     | Nis_324 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_325
         | _ -> Fail_act)
     | Nis_323 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_322 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_323
         | _ -> Fail_act)
     | Nis_321 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_140))
     | Nis_320 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.SEMICOLON_t -> Shift_act Nis_321
         | _ -> Fail_act)
     | Nis_319 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_141))
     | Nis_318 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SEMICOLON_t -> Shift_act Nis_319
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_317 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_94))
     | Nis_316 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_315 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_316
         | _ -> Fail_act)
     | Nis_313 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_314
         | _ -> Fail_act)
     | Nis_312 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_311 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_312
         | _ -> Fail_act)
     | Nis_309 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_310
         | _ -> Fail_act)
     | Nis_308 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BREAK_t -> Shift_act Nis_364
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CASE_t -> Shift_act Nis_361
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.CONTINUE_t -> Shift_act Nis_359
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DEFAULT_t -> Shift_act Nis_357
         | Coq__1.DO_t -> Shift_act Nis_356
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.FOR_t -> Shift_act Nis_351
         | Coq__1.GOTO_t -> Shift_act Nis_342
         | Coq__1.IF_t -> Shift_act Nis_324
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_322
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACE_t -> Shift_act Nis_495
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RETURN_t -> Shift_act Nis_318
         | Coq__1.SEMICOLON_t -> Shift_act Nis_317
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.SWITCH_t -> Shift_act Nis_313
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | Coq__1.WHILE_t -> Shift_act Nis_309
         | _ -> Fail_act)
     | Nis_307 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_101)
         | Coq__1.EQ_t -> Shift_act Nis_304
         | Coq__1.LBRACE_t -> Shift_act Nis_308
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_101)
         | _ -> Fail_act)
     | Nis_306 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_103))
     | Nis_305 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_102))
     | Nis_304 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_303 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_101)
         | Coq__1.EQ_t -> Shift_act Nis_304
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_101)
         | _ -> Fail_act)
     | Nis_302 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_104))
     | Nis_301 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_300 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_38))
     | Nis_299 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_301
         | Coq__1.SEMICOLON_t -> Shift_act Nis_300
         | _ -> Fail_act)
     | Nis_298 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_39))
     | Nis_297 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.SEMICOLON_t -> Shift_act Nis_298
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_296 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_230))
     | Nis_295 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_95))
     | Nis_294 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_231))
     | Nis_293 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EOF_t -> Shift_act Nis_294
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_292 -> Coq_inl Accept_act
     | Nis_291 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_79))
     | Nis_290 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACE_t -> Shift_act Nis_291
         | Coq__1.VAR_NAME_t -> Shift_act Nis_21
         | _ -> Fail_act)
     | Nis_289 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_77))
     | Nis_288 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_290
         | Coq__1.RBRACE_t -> Shift_act Nis_289
         | _ -> Fail_act)
     | Nis_287 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.VAR_NAME_t -> Shift_act Nis_21
         | _ -> Fail_act)
     | Nis_286 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_84))
     | Nis_285 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_83))
     | Nis_284 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_256))
     | Nis_283 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.AND_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.DIV_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.EQ_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.LBRACE_t -> Shift_act Nis_250
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.LEFT_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.MINUS_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.MOD_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.MUL_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.OR_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.PERCENT_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.PLUS_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.RIGHT_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.SLASH_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.SUB_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | Coq__1.XOR_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_257)
         | _ -> Fail_act)
     | Nis_282 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_283
         | _ -> Fail_act)
     | Nis_281 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_32))
     | Nis_280 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_250
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_279 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_280
         | _ -> Fail_act)
     | Nis_278 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_253))
     | Nis_277 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_180))
     | Nis_276 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RPAREN_t -> Shift_act Nis_277
         | _ -> Fail_act)
     | Nis_275 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_177))
     | Nis_274 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOT_t -> Shift_act Nis_255
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LBRACK_t -> Shift_act Nis_251
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACE_t -> Shift_act Nis_275
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_273 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_176))
     | Nis_272 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_274
         | Coq__1.RBRACE_t -> Shift_act Nis_273
         | _ -> Fail_act)
     | Nis_271 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_106))
     | Nis_270 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_105))
     | Nis_269 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_268 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_108))
     | Nis_267 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_28))
     | Nis_266 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_107))
     | Nis_265 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_264 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_53))
     | Nis_263 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_54))
     | Nis_262 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_50))
     | Nis_261 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.DOT_t -> Shift_act Nis_255
         | Coq__1.EQ_t -> Shift_act Nis_262
         | Coq__1.LBRACK_t -> Shift_act Nis_251
         | _ -> Fail_act)
     | Nis_260 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_30))
     | Nis_259 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOT_t -> Shift_act Nis_255
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LBRACK_t -> Shift_act Nis_251
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACE_t -> Shift_act Nis_260
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_258 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_29))
     | Nis_257 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_259
         | Coq__1.RBRACE_t -> Shift_act Nis_258
         | _ -> Fail_act)
     | Nis_256 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_52))
     | Nis_255 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_256
         | _ -> Fail_act)
     | Nis_254 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOT_t -> Shift_act Nis_255
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LBRACK_t -> Shift_act Nis_251
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_253 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_51))
     | Nis_252 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_253
         | _ -> Fail_act)
     | Nis_250 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOT_t -> Shift_act Nis_255
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LBRACE_t -> Shift_act Nis_254
         | Coq__1.LBRACK_t -> Shift_act Nis_251
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_249 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LBRACE_t -> Shift_act Nis_250
         | _ -> Fail_act)
     | Nis_248 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_249
         | _ -> Fail_act)
     | Nis_247 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_254))
     | Nis_246 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_233))
     | Nis_245 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LBRACK_t -> Shift_act Nis_183
         | Coq__1.LPAREN_t -> Shift_act Nis_244
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_3)
         | _ -> Fail_act)
     | Nis_244 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Shift_act Nis_183
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_244
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Shift_act Nis_182
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_243 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LBRACK_t -> Shift_act Nis_183
         | Coq__1.LPAREN_t -> Shift_act Nis_244
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_232)
         | Coq__1.STAR_t -> Shift_act Nis_152
         | _ -> Fail_act)
     | Nis_242 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_171))
     | Nis_241 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_242
         | _ -> Fail_act)
     | Nis_240 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_194))
     | Nis_239 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_196))
     | Nis_238 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_227))
     | Nis_237 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.RBRACE_t -> Shift_act Nis_238
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_236 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_235 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_217))
     | Nis_234 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_222))
     | Nis_233 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_220))
     | Nis_231 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_232
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_219)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_219)
         | _ -> Fail_act)
     | Nis_230 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_223))
     | Nis_229 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_224
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_228 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_215))
     | Nis_227 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_229
         | Coq__1.SEMICOLON_t -> Shift_act Nis_228
         | _ -> Fail_act)
     | Nis_226 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_37))
     | Nis_225 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_221))
     | Nis_223 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_157))
     | Nis_222 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_156))
     | Nis_221 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_55))
     | Nis_220 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_221
         | _ -> Fail_act)
     | Nis_219 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_69))
     | Nis_218 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_219
         | _ -> Fail_act)
     | Nis_217 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_5)
         | Coq__1.LBRACK_t -> Shift_act Nis_198
         | Coq__1.LPAREN_t -> Shift_act Nis_193
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_5)
         | _ -> Fail_act)
     | Nis_216 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_71))
     | Nis_215 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_216
         | _ -> Fail_act)
     | Nis_214 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_70))
     | Nis_213 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_214
         | _ -> Fail_act)
     | Nis_212 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_72))
     | Nis_211 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACK_t -> Shift_act Nis_212
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_210 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_73))
     | Nis_209 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACK_t -> Shift_act Nis_210
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_208 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_48)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_48)
         | Coq__1.EQ_t -> Reduce_act (Obj.magic Coq__1.Prod_48)
         | Coq__1.LBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_48)
         | Coq__1.LBRACK_t -> Shift_act Nis_209
         | Coq__1.LPAREN_t -> Shift_act Nis_162
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_48)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_48)
         | _ -> Fail_act)
     | Nis_207 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_65))
     | Nis_206 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_207
         | _ -> Fail_act)
     | Nis_205 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_58))
     | Nis_204 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_205
         | _ -> Fail_act)
     | Nis_203 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_56))
     | Nis_202 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_203
         | _ -> Fail_act)
     | Nis_201 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_60))
     | Nis_200 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACK_t -> Shift_act Nis_201
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_199 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_62))
     | Nis_198 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACK_t -> Shift_act Nis_199
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_197 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_159))
     | Nis_196 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_64))
     | Nis_195 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_196
         | _ -> Fail_act)
     | Nis_194 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_66))
     | Nis_193 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Shift_act Nis_194
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_192 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_4)
         | Coq__1.LBRACK_t -> Shift_act Nis_198
         | Coq__1.LPAREN_t -> Shift_act Nis_193
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_4)
         | _ -> Fail_act)
     | Nis_191 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_3)
         | Coq__1.LBRACK_t -> Shift_act Nis_183
         | Coq__1.LPAREN_t -> Shift_act Nis_181
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_3)
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_190 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_59))
     | Nis_189 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_190
         | _ -> Fail_act)
     | Nis_188 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_57))
     | Nis_187 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACK_t -> Shift_act Nis_188
         | _ -> Fail_act)
     | Nis_186 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_61))
     | Nis_185 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACK_t -> Shift_act Nis_186
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_184 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_63))
     | Nis_183 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RBRACK_t -> Shift_act Nis_184
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_182 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_67))
     | Nis_181 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Shift_act Nis_183
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_181
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Shift_act Nis_182
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_180 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_158)
         | Coq__1.LBRACK_t -> Shift_act Nis_183
         | Coq__1.LPAREN_t -> Shift_act Nis_181
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_158)
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_179 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_160))
     | Nis_178 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_162))
     | Nis_177 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ELLIPSIS_t -> Shift_act Nis_178
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_176 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_177
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_161)
         | _ -> Fail_act)
     | Nis_175 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_74))
     | Nis_174 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RPAREN_t -> Shift_act Nis_175
         | _ -> Fail_act)
     | Nis_173 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_42))
     | Nis_172 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_44))
     | Nis_171 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_40))
     | Nis_170 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_46))
     | Nis_169 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_250))
     | Nis_168 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_47)
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_167 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_41)
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_166 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_45)
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_165 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_43)
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_164 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_213))
     | Nis_163 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_75))
     | Nis_162 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Shift_act Nis_164
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.EXTERN_t -> Shift_act Nis_17
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INLINE_t -> Shift_act Nis_15
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.REGISTER_t -> Shift_act Nis_12
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Shift_act Nis_163
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STATIC_t -> Shift_act Nis_8
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_t -> Shift_act Nis_6
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_161 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_49)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_49)
         | Coq__1.EQ_t -> Reduce_act (Obj.magic Coq__1.Prod_49)
         | Coq__1.LBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_49)
         | Coq__1.LBRACK_t -> Shift_act Nis_209
         | Coq__1.LPAREN_t -> Shift_act Nis_162
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_49)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_49)
         | _ -> Fail_act)
     | Nis_160 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_159 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_158 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_216))
     | Nis_157 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_165))
     | Nis_156 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_237))
     | Nis_155 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_166))
     | Nis_154 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_238))
     | Nis_153 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_164)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_164)
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_164)
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_164)
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_164)
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_152 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_163)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_163)
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_163)
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_163)
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_163)
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_151 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_68))
     | Nis_150 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_224
         | Coq__1.LPAREN_t -> Shift_act Nis_159
         | Coq__1.SEMICOLON_t -> Shift_act Nis_158
         | Coq__1.STAR_t -> Shift_act Nis_152
         | Coq__1.VAR_NAME_t -> Shift_act Nis_151
         | _ -> Fail_act)
     | Nis_149 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_218))
     | Nis_148 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_226))
     | Nis_147 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.RBRACE_t -> Shift_act Nis_148
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_146 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_145 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.BOOL_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.CHAR_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.CONST_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.DOUBLE_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.ENUM_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.EXTERN_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.FLOAT_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.INLINE_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.INT_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.LBRACE_t -> Shift_act Nis_146
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.LONG_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.REGISTER_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.RESTRICT_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.SHORT_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.SIGNED_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.STATIC_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.STRUCT_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.TYPEDEF_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.TYPEDEF_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.UNION_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.UNSIGNED_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.VOID_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | Coq__1.VOLATILE_t -> Reduce_act (Obj.magic Coq__1.Prod_228)
         | _ -> Fail_act)
     | Nis_144 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LBRACE_t -> Shift_act Nis_236
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_145
         | _ -> Fail_act)
     | Nis_143 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_249))
     | Nis_142 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_197)
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_141 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_195)
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_140 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_248))
     | Nis_139 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_240))
     | Nis_138 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_234))
     | Nis_137 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_136 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_137
         | _ -> Fail_act)
     | Nis_135 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_255))
     | Nis_134 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_175))
     | Nis_133 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_172))
     | Nis_132 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_133
         | _ -> Fail_act)
     | Nis_131 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_174))
     | Nis_130 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_168))
     | Nis_129 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | Coq__1.RBRACK_t -> Shift_act Nis_130
         | _ -> Fail_act)
     | Nis_127 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_10))
     | Nis_125 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_169))
     | Nis_124 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_126
         | Coq__1.RPAREN_t -> Shift_act Nis_125
         | _ -> Fail_act)
     | Nis_123 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_9))
     | Nis_122 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_12))
     | Nis_121 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ANDAND_t -> Shift_act Nis_97
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_151)
         | _ -> Fail_act)
     | Nis_119 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_91))
     | Nis_118 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_36))
     | Nis_116 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_92))
     | Nis_115 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_11))
     | Nis_113 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COLON_t -> Shift_act Nis_117
         | Coq__1.COMMA_t -> Shift_act Nis_114
         | _ -> Fail_act)
     | Nis_112 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.BAR_t -> Shift_act Nis_99
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_148)
         | _ -> Fail_act)
     | Nis_111 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.HAT_t -> Shift_act Nis_101
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_99)
         | _ -> Fail_act)
     | Nis_110 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_108
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_89)
         | _ -> Fail_act)
     | Nis_109 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.EQEQ_t -> Shift_act Nis_105
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.NEQ_t -> Shift_act Nis_103
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_2)
         | _ -> Fail_act)
     | Nis_107 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_108
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_90)
         | _ -> Fail_act)
     | Nis_106 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.GEQ_t -> Shift_act Nis_92
         | Coq__1.GT_t -> Shift_act Nis_90
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.LEQ_t -> Shift_act Nis_88
         | Coq__1.LT_t -> Shift_act Nis_85
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_87)
         | _ -> Fail_act)
     | Nis_104 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.GEQ_t -> Shift_act Nis_92
         | Coq__1.GT_t -> Shift_act Nis_90
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.LEQ_t -> Shift_act Nis_88
         | Coq__1.LT_t -> Shift_act Nis_85
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_88)
         | _ -> Fail_act)
     | Nis_102 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.EQEQ_t -> Shift_act Nis_105
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.NEQ_t -> Shift_act Nis_103
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_1)
         | _ -> Fail_act)
     | Nis_100 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.HAT_t -> Shift_act Nis_101
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_100)
         | _ -> Fail_act)
     | Nis_98 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.BAR_t -> Shift_act Nis_99
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_149)
         | _ -> Fail_act)
     | Nis_96 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ANDAND_t -> Shift_act Nis_97
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_150)
         | _ -> Fail_act)
     | Nis_94 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.BARBAR_t -> Shift_act Nis_120
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_35)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_35)
         | Coq__1.QUESTION_t -> Shift_act Nis_95
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_35)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_35)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_35)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_35)
         | _ -> Fail_act)
     | Nis_93 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.LEFT_t -> Shift_act Nis_82
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.RIGHT_t -> Shift_act Nis_68
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_185)
         | _ -> Fail_act)
     | Nis_91 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.LEFT_t -> Shift_act Nis_82
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.RIGHT_t -> Shift_act Nis_68
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_183)
         | _ -> Fail_act)
     | Nis_89 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.LEFT_t -> Shift_act Nis_82
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.RIGHT_t -> Shift_act Nis_68
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_184)
         | _ -> Fail_act)
     | Nis_87 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.MINUS_t -> Shift_act Nis_80
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.PLUS_t -> Shift_act Nis_78
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_191)
         | _ -> Fail_act)
     | Nis_86 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.LEFT_t -> Shift_act Nis_82
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.RIGHT_t -> Shift_act Nis_68
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_182)
         | _ -> Fail_act)
     | Nis_84 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.GEQ_t -> Shift_act Nis_92
         | Coq__1.GT_t -> Shift_act Nis_90
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.LEQ_t -> Shift_act Nis_88
         | Coq__1.LT_t -> Shift_act Nis_85
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_86)
         | _ -> Fail_act)
     | Nis_83 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.MINUS_t -> Shift_act Nis_80
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.PLUS_t -> Shift_act Nis_78
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_192)
         | _ -> Fail_act)
     | Nis_81 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.MINUS_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.PERCENT_t -> Shift_act Nis_74
         | Coq__1.PLUS_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_8)
         | Coq__1.SLASH_t -> Shift_act Nis_72
         | Coq__1.STAR_t -> Shift_act Nis_70
         | _ -> Fail_act)
     | Nis_79 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.MINUS_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.PERCENT_t -> Shift_act Nis_74
         | Coq__1.PLUS_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_7)
         | Coq__1.SLASH_t -> Shift_act Nis_72
         | Coq__1.STAR_t -> Shift_act Nis_70
         | _ -> Fail_act)
     | Nis_77 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.MINUS_t -> Shift_act Nis_80
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.PLUS_t -> Shift_act Nis_78
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_193)
         | _ -> Fail_act)
     | Nis_76 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_152))
     | Nis_75 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_155))
     | Nis_73 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_154))
     | Nis_71 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_153))
     | Nis_69 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.MINUS_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.PERCENT_t -> Shift_act Nis_74
         | Coq__1.PLUS_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_6)
         | Coq__1.SLASH_t -> Shift_act Nis_72
         | Coq__1.STAR_t -> Shift_act Nis_70
         | _ -> Fail_act)
     | Nis_67 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.LEFT_t -> Shift_act Nis_82
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.RIGHT_t -> Shift_act Nis_68
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_181)
         | _ -> Fail_act)
     | Nis_65 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_17))
     | Nis_64 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_23))
     | Nis_63 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_15))
     | Nis_62 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_13))
     | Nis_61 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_19))
     | Nis_60 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_16))
     | Nis_59 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_14))
     | Nis_58 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_22))
     | Nis_57 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_20))
     | Nis_56 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_18))
     | Nis_55 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_21))
     | Nis_54 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Shift_act Nis_65
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.AND_ASSIGN_t -> Shift_act Nis_64
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.DIV_ASSIGN_t -> Shift_act Nis_63
         | Coq__1.EQ_t -> Shift_act Nis_62
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.LEFT_ASSIGN_t -> Shift_act Nis_61
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.MINUS_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.MOD_ASSIGN_t -> Shift_act Nis_60
         | Coq__1.MUL_ASSIGN_t -> Shift_act Nis_59
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.OR_ASSIGN_t -> Shift_act Nis_58
         | Coq__1.PERCENT_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.PLUS_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.RIGHT_ASSIGN_t -> Shift_act Nis_57
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.SLASH_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_31)
         | Coq__1.SUB_ASSIGN_t -> Shift_act Nis_56
         | Coq__1.XOR_ASSIGN_t -> Shift_act Nis_55
         | _ -> Fail_act)
     | Nis_53 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_170))
     | Nis_52 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RPAREN_t -> Shift_act Nis_53
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_51 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_173))
     | Nis_50 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_51
         | _ -> Fail_act)
     | Nis_49 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.ADD_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.AND_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.ANDAND_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.AND_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.BAR_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.BARBAR_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.DEC_t -> Shift_act Nis_134
         | Coq__1.DIV_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.DOT_t -> Shift_act Nis_132
         | Coq__1.EQ_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.EQEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.GEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.GT_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.HAT_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.INC_t -> Shift_act Nis_131
         | Coq__1.LBRACK_t -> Shift_act Nis_128
         | Coq__1.LEFT_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.LEFT_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.LEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.LPAREN_t -> Shift_act Nis_52
         | Coq__1.LT_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.MINUS_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.MOD_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.MUL_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.NEQ_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.OR_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.PERCENT_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.PLUS_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.PTR_t -> Shift_act Nis_50
         | Coq__1.QUESTION_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.RBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.RIGHT_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.RIGHT_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.SLASH_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.SUB_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | Coq__1.XOR_ASSIGN_t -> Reduce_act (Obj.magic Coq__1.Prod_252)
         | _ -> Fail_act)
     | Nis_48 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_167))
     | Nis_47 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_31))
     | Nis_45 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_258))
     | Nis_44 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_263))
     | Nis_42 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LPAREN_t -> Shift_act Nis_43
         | _ -> Fail_act)
     | Nis_41 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_179))
     | Nis_40 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_38
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_39 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_245))
     | Nis_38 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_37 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_38
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_36 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_35 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BOOL_t -> Shift_act Nis_140
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CHAR_t -> Shift_act Nis_139
         | Coq__1.CONST_t -> Shift_act Nis_138
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.DOUBLE_t -> Shift_act Nis_39
         | Coq__1.ENUM_t -> Shift_act Nis_18
         | Coq__1.FLOAT_t -> Shift_act Nis_16
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.INT_t -> Shift_act Nis_14
         | Coq__1.LONG_t -> Shift_act Nis_13
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.RESTRICT_t -> Shift_act Nis_11
         | Coq__1.SHORT_t -> Shift_act Nis_10
         | Coq__1.SIGNED_t -> Shift_act Nis_9
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.STRUCT_t -> Shift_act Nis_7
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.TYPEDEF_NAME_t -> Shift_act Nis_5
         | Coq__1.UNION_t -> Shift_act Nis_4
         | Coq__1.UNSIGNED_t -> Shift_act Nis_3
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | Coq__1.VOID_t -> Shift_act Nis_2
         | Coq__1.VOLATILE_t -> Shift_act Nis_1
         | _ -> Fail_act)
     | Nis_34 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_261))
     | Nis_33 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_260))
     | Nis_32 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_35
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act)
     | Nis_31 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_259))
     | Nis_30 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_262))
     | Nis_29 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_178))
     | Nis_27 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_82)
         | Coq__1.EQ_t -> Shift_act Nis_28
         | Coq__1.RBRACE_t -> Reduce_act (Obj.magic Coq__1.Prod_82)
         | _ -> Fail_act)
     | Nis_26 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_85))
     | Nis_25 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_78))
     | Nis_24 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.RBRACE_t -> Shift_act Nis_25
         | Coq__1.VAR_NAME_t -> Shift_act Nis_21
         | _ -> Fail_act)
     | Nis_23 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_76))
     | Nis_22 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.COMMA_t -> Shift_act Nis_24
         | Coq__1.RBRACE_t -> Shift_act Nis_23
         | _ -> Fail_act)
     | Nis_21 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_81))
     | Nis_20 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.VAR_NAME_t -> Shift_act Nis_21
         | _ -> Fail_act)
     | Nis_19 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AUTO_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.BOOL_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.CHAR_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.COLON_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.COMMA_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.CONST_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.DOUBLE_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.ENUM_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.EXTERN_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.FLOAT_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.INLINE_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.INT_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.LBRACE_t -> Shift_act Nis_20
         | Coq__1.LBRACK_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.LONG_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.LPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.REGISTER_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.RESTRICT_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.RPAREN_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.SEMICOLON_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.SHORT_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.SIGNED_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.STAR_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.STATIC_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.STRUCT_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.TYPEDEF_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.TYPEDEF_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.UNION_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.UNSIGNED_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.VAR_NAME_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.VOID_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | Coq__1.VOLATILE_t -> Reduce_act (Obj.magic Coq__1.Prod_80)
         | _ -> Fail_act)
     | Nis_18 ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.LBRACE_t -> Shift_act Nis_287
         | Coq__1.OTHER_NAME_t -> Shift_act Nis_19
         | _ -> Fail_act)
     | Nis_17 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_211))
     | Nis_16 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_244))
     | Nis_15 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_98))
     | Nis_14 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_242))
     | Nis_13 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_243))
     | Nis_12 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_214))
     | Nis_11 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_235))
     | Nis_10 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_241))
     | Nis_9 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_246))
     | Nis_8 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_212))
     | Nis_7 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_224))
     | Nis_6 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_210))
     | Nis_5 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_251))
     | Nis_4 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_225))
     | Nis_3 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_247))
     | Nis_2 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_239))
     | Nis_1 -> Coq_inl (Default_reduce_act (Obj.magic Coq__1.Prod_236))
     | _ ->
       Coq_inr (fun terminal0 ->
         match terminal0 with
         | Coq__1.AND_t -> Shift_act Nis_45
         | Coq__1.BANG_t -> Shift_act Nis_44
         | Coq__1.BUILTIN_VA_ARG_t -> Shift_act Nis_42
         | Coq__1.CONSTANT_t -> Shift_act Nis_41
         | Coq__1.DEC_t -> Shift_act Nis_40
         | Coq__1.INC_t -> Shift_act Nis_37
         | Coq__1.LPAREN_t -> Shift_act Nis_36
         | Coq__1.MINUS_t -> Shift_act Nis_34
         | Coq__1.PLUS_t -> Shift_act Nis_33
         | Coq__1.SIZEOF_t -> Shift_act Nis_32
         | Coq__1.STAR_t -> Shift_act Nis_31
         | Coq__1.TILDE_t -> Shift_act Nis_30
         | Coq__1.VAR_NAME_t -> Shift_act Nis_29
         | _ -> Fail_act))
  
  (** val goto_table : state -> Coq__1.nonterminal -> noninitstate option **)
  
  let goto_table state0 nt =
    match state0 with
    | Init ->
      (match nt with
       | Coq__1.Coq_declaration_nt -> Some Nis_503
       | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_297
       | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
       | Coq__1.Coq_external_declaration_nt -> Some Nis_504
       | Coq__1.Coq_function_definition_nt -> Some Nis_295
       | Coq__1.Coq_function_specifier_nt -> Some Nis_168
       | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
       | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
       | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
       | Coq__1.Coq_translation_unit_nt -> Some Nis_293
       | Coq__1.Coq_translation_unit_file_nt -> Some Nis_292
       | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
       | Coq__1.Coq_type_specifier_nt -> Some Nis_165
       | _ -> None)
    | Ninit n ->
      (match n with
       | Nis_498 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_block_item_nt -> Some Nis_500
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_declaration_nt -> Some Nis_497
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_408
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_496
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_494 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_485
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_483 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_485
          | Coq__1.Coq_statement_safe_nt -> Some Nis_484
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_480 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_422
          | Coq__1.Coq_statement_safe_nt -> Some Nis_481
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_477 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_419
          | Coq__1.Coq_statement_safe_nt -> Some Nis_478
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_476 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_479
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_473 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_415
          | Coq__1.Coq_statement_safe_nt -> Some Nis_474
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_470 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_412
          | Coq__1.Coq_statement_safe_nt -> Some Nis_471
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_469 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_472
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_468 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_475
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_466 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_407
          | Coq__1.Coq_statement_safe_nt -> Some Nis_467
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_463 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_404
          | Coq__1.Coq_statement_safe_nt -> Some Nis_464
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_462 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_465
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_459 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_400
          | Coq__1.Coq_statement_safe_nt -> Some Nis_460
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_456 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_397
          | Coq__1.Coq_statement_safe_nt -> Some Nis_457
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_455 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_458
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_454 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_461
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_451 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_392
          | Coq__1.Coq_statement_safe_nt -> Some Nis_452
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_448 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_389
          | Coq__1.Coq_statement_safe_nt -> Some Nis_449
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_447 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_450
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_444 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_385
          | Coq__1.Coq_statement_safe_nt -> Some Nis_445
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_433 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_366
          | Coq__1.Coq_statement_safe_nt -> Some Nis_434
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_431 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_226
          | Coq__1.Coq_constant_expression_nt -> Some Nis_432
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_430 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_375
          | Coq__1.Coq_statement_safe_nt -> Some Nis_441
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_425 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_426
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_421 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_422
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_418 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_419
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_417 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_420
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_414 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_415
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_411 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_412
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_410 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_413
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_409 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_416
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_408 ->
         (match nt with
          | Coq__1.Coq_declarator_nt -> Some Nis_303
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_init_declarator_nt -> Some Nis_306
          | Coq__1.Coq_init_declarator_list_nt -> Some Nis_299
          | Coq__1.Coq_pointer_nt -> Some Nis_160
          | _ -> None)
       | Nis_406 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_407
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_403 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_404
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_402 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_405
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_399 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_400
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_396 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_397
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_395 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_398
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_394 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_401
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_391 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_392
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_388 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_389
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_387 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_390
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_384 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_385
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_378 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_379
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_363 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_366
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_361 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_226
          | Coq__1.Coq_constant_expression_nt -> Some Nis_362
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_358 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_375
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_356 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_376
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_355 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_382
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_354 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_383
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_353 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_386
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_352 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_declaration_nt -> Some Nis_409
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_408
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_393
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_350 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_423
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_349 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_382
          | Coq__1.Coq_statement_safe_nt -> Some Nis_442
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_348 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_443
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_347 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_446
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_346 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_declaration_nt -> Some Nis_468
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_408
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_453
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_341 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_486
          | Coq__1.Coq_statement_safe_nt -> Some Nis_482
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_339 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_340
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_337 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_488
          | Coq__1.Coq_statement_safe_nt -> Some Nis_487
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_335 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_490
          | Coq__1.Coq_statement_safe_nt -> Some Nis_489
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_333 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_334
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_331 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_492
          | Coq__1.Coq_statement_safe_nt -> Some Nis_491
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_329 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_330
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_327 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_440
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_439
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_iteration_statement_statement_safe__nt -> Some Nis_438
          | Coq__1.Coq_jump_statement_nt -> Some Nis_437
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_labeled_statement_statement_safe__nt -> Some Nis_436
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_selection_statement_safe_nt -> Some Nis_435
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_486
          | Coq__1.Coq_statement_safe_nt -> Some Nis_493
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_325 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_326
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_323 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_488
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_318 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_320
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_316 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_490
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_314 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_315
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_312 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_492
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_310 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_311
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_308 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_block_item_nt -> Some Nis_501
          | Coq__1.Coq_block_item_list_nt -> Some Nis_498
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_compound_statement_nt -> Some Nis_374
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_declaration_nt -> Some Nis_497
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_408
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_372
          | Coq__1.Coq_expression_statement_nt -> Some Nis_371
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_iteration_statement_statement_dangerous__nt ->
            Some Nis_370
          | Coq__1.Coq_jump_statement_nt -> Some Nis_369
          | Coq__1.Coq_labeled_statement_statement_dangerous__nt ->
            Some Nis_368
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_selection_statement_dangerous_nt -> Some Nis_367
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_statement_dangerous_nt -> Some Nis_496
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_307 ->
         (match nt with
          | Coq__1.Coq_compound_statement_nt -> Some Nis_502
          | _ -> None)
       | Nis_304 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_305
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_301 ->
         (match nt with
          | Coq__1.Coq_declarator_nt -> Some Nis_303
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_init_declarator_nt -> Some Nis_302
          | Coq__1.Coq_pointer_nt -> Some Nis_160
          | _ -> None)
       | Nis_297 ->
         (match nt with
          | Coq__1.Coq_declarator_nt -> Some Nis_307
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_init_declarator_nt -> Some Nis_306
          | Coq__1.Coq_init_declarator_list_nt -> Some Nis_299
          | Coq__1.Coq_pointer_nt -> Some Nis_160
          | _ -> None)
       | Nis_293 ->
         (match nt with
          | Coq__1.Coq_declaration_nt -> Some Nis_503
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_297
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_external_declaration_nt -> Some Nis_296
          | Coq__1.Coq_function_definition_nt -> Some Nis_295
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_290 ->
         (match nt with
          | Coq__1.Coq_enumeration_constant_nt -> Some Nis_27
          | Coq__1.Coq_enumerator_nt -> Some Nis_26
          | _ -> None)
       | Nis_287 ->
         (match nt with
          | Coq__1.Coq_enumeration_constant_nt -> Some Nis_27
          | Coq__1.Coq_enumerator_nt -> Some Nis_286
          | Coq__1.Coq_enumerator_list_nt -> Some Nis_288
          | _ -> None)
       | Nis_280 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_281
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_274 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_268
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_designation_nt -> Some Nis_265
          | Coq__1.Coq_designator_nt -> Some Nis_264
          | Coq__1.Coq_designator_list_nt -> Some Nis_261
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_269 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_270
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_265 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_266
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_261 ->
         (match nt with
          | Coq__1.Coq_designator_nt -> Some Nis_263
          | _ -> None)
       | Nis_259 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_268
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_designation_nt -> Some Nis_265
          | Coq__1.Coq_designator_nt -> Some Nis_264
          | Coq__1.Coq_designator_list_nt -> Some Nis_261
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_254 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_271
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_designation_nt -> Some Nis_269
          | Coq__1.Coq_designator_nt -> Some Nis_264
          | Coq__1.Coq_designator_list_nt -> Some Nis_261
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_initializer_list_nt -> Some Nis_257
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_251 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_226
          | Coq__1.Coq_constant_expression_nt -> Some Nis_252
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_250 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_267
          | Coq__1.Coq_c_initializer_nt -> Some Nis_271
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_designation_nt -> Some Nis_269
          | Coq__1.Coq_designator_nt -> Some Nis_264
          | Coq__1.Coq_designator_list_nt -> Some Nis_261
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_initializer_list_nt -> Some Nis_272
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_245 ->
         (match nt with
          | Coq__1.Coq_direct_abstract_declarator_nt -> Some Nis_192
          | _ -> None)
       | Nis_244 ->
         (match nt with
          | Coq__1.Coq_abstract_declarator_nt -> Some Nis_220
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_180
          | Coq__1.Coq_direct_abstract_declarator_nt -> Some Nis_217
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_parameter_declaration_nt -> Some Nis_197
          | Coq__1.Coq_parameter_list_nt -> Some Nis_176
          | Coq__1.Coq_parameter_type_list_nt -> Some Nis_206
          | Coq__1.Coq_pointer_nt -> Some Nis_245
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_243 ->
         (match nt with
          | Coq__1.Coq_abstract_declarator_nt -> Some Nis_246
          | Coq__1.Coq_direct_abstract_declarator_nt -> Some Nis_217
          | Coq__1.Coq_pointer_nt -> Some Nis_245
          | _ -> None)
       | Nis_237 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_150
          | Coq__1.Coq_struct_declaration_nt -> Some Nis_149
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_236 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_150
          | Coq__1.Coq_struct_declaration_nt -> Some Nis_235
          | Coq__1.Coq_struct_declaration_list_nt -> Some Nis_237
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_232 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_226
          | Coq__1.Coq_constant_expression_nt -> Some Nis_233
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_229 ->
         (match nt with
          | Coq__1.Coq_declarator_nt -> Some Nis_231
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_pointer_nt -> Some Nis_160
          | Coq__1.Coq_struct_declarator_nt -> Some Nis_230
          | _ -> None)
       | Nis_224 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_226
          | Coq__1.Coq_constant_expression_nt -> Some Nis_225
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_211 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_213
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_154
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_209 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_215
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_156
          | Coq__1.Coq_type_qualifier_list_nt -> Some Nis_211
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_200 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_202
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_154
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_198 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_204
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_156
          | Coq__1.Coq_type_qualifier_list_nt -> Some Nis_200
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_193 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_180
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_parameter_declaration_nt -> Some Nis_197
          | Coq__1.Coq_parameter_list_nt -> Some Nis_176
          | Coq__1.Coq_parameter_type_list_nt -> Some Nis_195
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_191 ->
         (match nt with
          | Coq__1.Coq_direct_abstract_declarator_nt -> Some Nis_192
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_161
          | _ -> None)
       | Nis_185 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_187
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_154
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_183 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_189
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_156
          | Coq__1.Coq_type_qualifier_list_nt -> Some Nis_185
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_181 ->
         (match nt with
          | Coq__1.Coq_abstract_declarator_nt -> Some Nis_220
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_180
          | Coq__1.Coq_declarator_nt -> Some Nis_218
          | Coq__1.Coq_direct_abstract_declarator_nt -> Some Nis_217
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_parameter_declaration_nt -> Some Nis_197
          | Coq__1.Coq_parameter_list_nt -> Some Nis_176
          | Coq__1.Coq_parameter_type_list_nt -> Some Nis_206
          | Coq__1.Coq_pointer_nt -> Some Nis_191
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_180 ->
         (match nt with
          | Coq__1.Coq_abstract_declarator_nt -> Some Nis_223
          | Coq__1.Coq_declarator_nt -> Some Nis_222
          | Coq__1.Coq_direct_abstract_declarator_nt -> Some Nis_217
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_pointer_nt -> Some Nis_191
          | _ -> None)
       | Nis_177 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_180
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_parameter_declaration_nt -> Some Nis_179
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_168 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_170
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_167 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_171
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_166 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_172
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_165 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_173
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_162 ->
         (match nt with
          | Coq__1.Coq_declaration_specifiers_nt -> Some Nis_180
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_function_specifier_nt -> Some Nis_168
          | Coq__1.Coq_parameter_declaration_nt -> Some Nis_197
          | Coq__1.Coq_parameter_list_nt -> Some Nis_176
          | Coq__1.Coq_parameter_type_list_nt -> Some Nis_174
          | Coq__1.Coq_storage_class_specifier_nt -> Some Nis_167
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_166
          | Coq__1.Coq_type_specifier_nt -> Some Nis_165
          | _ -> None)
       | Nis_160 ->
         (match nt with
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_161
          | _ -> None)
       | Nis_159 ->
         (match nt with
          | Coq__1.Coq_declarator_nt -> Some Nis_218
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_pointer_nt -> Some Nis_160
          | _ -> None)
       | Nis_153 ->
         (match nt with
          | Coq__1.Coq_pointer_nt -> Some Nis_155
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_154
          | _ -> None)
       | Nis_152 ->
         (match nt with
          | Coq__1.Coq_pointer_nt -> Some Nis_157
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_156
          | Coq__1.Coq_type_qualifier_list_nt -> Some Nis_153
          | _ -> None)
       | Nis_150 ->
         (match nt with
          | Coq__1.Coq_declarator_nt -> Some Nis_231
          | Coq__1.Coq_direct_declarator_nt -> Some Nis_208
          | Coq__1.Coq_pointer_nt -> Some Nis_160
          | Coq__1.Coq_struct_declarator_nt -> Some Nis_234
          | Coq__1.Coq_struct_declarator_list_nt -> Some Nis_227
          | _ -> None)
       | Nis_147 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_150
          | Coq__1.Coq_struct_declaration_nt -> Some Nis_149
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_146 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_150
          | Coq__1.Coq_struct_declaration_nt -> Some Nis_235
          | Coq__1.Coq_struct_declaration_list_nt -> Some Nis_147
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_142 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_239
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_141 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_240
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_137 ->
         (match nt with
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_243
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_name_nt -> Some Nis_241
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | _ -> None)
       | Nis_128 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_129
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_126 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_127
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_120 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_121
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_117 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_118
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_114 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_116
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_108 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_equality_expression_nt -> Some Nis_109
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_105 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_106
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_103 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_104
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_101 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_107
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_99 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_100
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_97 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_98
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_95 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_113
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_92 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_shift_expression_nt -> Some Nis_93
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_90 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_shift_expression_nt -> Some Nis_91
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_88 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_shift_expression_nt -> Some Nis_89
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_85 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_shift_expression_nt -> Some Nis_86
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_82 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_83
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_80 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_81
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_78 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_79
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_74 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_75
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_72 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_73
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_70 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_71
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_68 ->
         (match nt with
          | Coq__1.Coq_additive_expression_nt -> Some Nis_77
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_66 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_122
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_54 ->
         (match nt with
          | Coq__1.Coq_assignment_operator_nt -> Some Nis_66
          | _ -> None)
       | Nis_52 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_argument_expression_list_nt -> Some Nis_124
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_123
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_46 ->
         (match nt with
          | Coq__1.Coq_cast_expression_nt -> Some Nis_135
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_43 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_136
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_40 ->
         (match nt with
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_247
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_38 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_276
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_243
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_name_nt -> Some Nis_248
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_37 ->
         (match nt with
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_278
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_36 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_276
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_243
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_name_nt -> Some Nis_279
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_35 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_assignment_expression_nt -> Some Nis_119
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_115
          | Coq__1.Coq_enum_specifier_nt -> Some Nis_169
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_expression_nt -> Some Nis_276
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_specifier_qualifier_list_nt -> Some Nis_243
          | Coq__1.Coq_struct_or_union_nt -> Some Nis_144
          | Coq__1.Coq_struct_or_union_specifier_nt -> Some Nis_143
          | Coq__1.Coq_type_name_nt -> Some Nis_282
          | Coq__1.Coq_type_qualifier_nt -> Some Nis_142
          | Coq__1.Coq_type_specifier_nt -> Some Nis_141
          | Coq__1.Coq_unary_expression_nt -> Some Nis_54
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_32 ->
         (match nt with
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_unary_expression_nt -> Some Nis_284
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_28 ->
         (match nt with
          | Coq__1.AND_expression_nt -> Some Nis_110
          | Coq__1.Coq_additive_expression_nt -> Some Nis_87
          | Coq__1.Coq_cast_expression_nt -> Some Nis_76
          | Coq__1.Coq_conditional_expression_nt -> Some Nis_226
          | Coq__1.Coq_constant_expression_nt -> Some Nis_285
          | Coq__1.Coq_equality_expression_nt -> Some Nis_102
          | Coq__1.Coq_exclusive_OR_expression_nt -> Some Nis_111
          | Coq__1.Coq_inclusive_OR_expression_nt -> Some Nis_112
          | Coq__1.Coq_logical_AND_expression_nt -> Some Nis_96
          | Coq__1.Coq_logical_OR_expression_nt -> Some Nis_94
          | Coq__1.Coq_multiplicative_expression_nt -> Some Nis_69
          | Coq__1.Coq_postfix_expression_nt -> Some Nis_49
          | Coq__1.Coq_primary_expression_nt -> Some Nis_48
          | Coq__1.Coq_relational_expression_nt -> Some Nis_84
          | Coq__1.Coq_shift_expression_nt -> Some Nis_67
          | Coq__1.Coq_unary_expression_nt -> Some Nis_47
          | Coq__1.Coq_unary_operator_nt -> Some Nis_46
          | _ -> None)
       | Nis_24 ->
         (match nt with
          | Coq__1.Coq_enumeration_constant_nt -> Some Nis_27
          | Coq__1.Coq_enumerator_nt -> Some Nis_26
          | _ -> None)
       | Nis_20 ->
         (match nt with
          | Coq__1.Coq_enumeration_constant_nt -> Some Nis_27
          | Coq__1.Coq_enumerator_nt -> Some Nis_286
          | Coq__1.Coq_enumerator_list_nt -> Some Nis_22
          | _ -> None)
       | _ -> None)
  
  (** val past_symb_of_non_init_state :
      noninitstate -> Coq__1.symbol list **)
  
  let past_symb_of_non_init_state = fun _ -> []
  
  (** val past_state_of_non_init_state :
      noninitstate -> (state -> bool) list **)
  
  let past_state_of_non_init_state = fun _ -> []
  
  (** val items_of_state : state -> item list **)
  
  let items_of_state = fun _ -> []
 end

module Parser = Make(Aut)

(** val parse :
    nat -> Aut.GramDefs.token coq_Stream -> Parser.Inter.parse_result **)

let parse =
  Parser.parse

