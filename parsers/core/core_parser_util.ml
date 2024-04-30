open Cerb_frontend

type _sym =
  string * (Lexing.position * Lexing.position)

let _sym_compare (str1, _) (str2, _) =
  compare str1 str2

type mode =
  | StdMode
  | ImplORFileMode

type parsed_core_file =
  Symbol.sym (* main symbol *) *
  (Symbol.sym * (Core.core_base_type * Ctype.ctype) * unit Core.expr) list (* globals *) *
  unit Core.fun_map (* fun map *) *
  (Symbol.sym, Cerb_location.t * Ctype.tag_definition) Pmap.map (* tagDefs *)

(* Type of Core parser outputs *)
type result =
  | Rfile of parsed_core_file
  | Rstd  of (string, Symbol.sym) Pmap.map (* Map of ailnames *) * unit Core.fun_map
  | Rimpl of Core.impl (* * unit Core.fun_map *)

exception Core_error of (Cerb_location.t * Errors.core_parser_cause)

type token =
  | CONST
  | SHORT
  | INT
  | LONG
  | LONG_LONG
  | BOOL
  | SIGNED
  | UNSIGNED
  | FLOAT
  | DOUBLE
  | LONG_DOUBLE
  | CHAR
  | ICHAR
  | VOID
  
  | INT8_T
  | INT16_T
  | INT32_T
  | INT64_T
  | UINT8_T
  | UINT16_T
  | UINT32_T
  | UINT64_T

  | INTPTR_T
  | INTMAX_T
  | UINTPTR_T
  | UINTMAX_T
  
  | SIZE_T
  | PTRDIFF_T
  | IVMAX_ALIGNMENT
  
  | ATOMIC
  | STRUCT (* TODO *)
  | UNION (* TODO *)
(*  | ENUM (* TODO *) *)
(*  | WCHAR_T (* TODO *) *)
(*  | CHAR16_T (* TODO *) *)
(*  | CHAR32_T (* TODO *) *)
  | INTEGER
  | FLOATING
  | BOOLEAN
  | POINTER
  | CTYPE
  | CFUNCTION
  | UNIT
  | UNIT_VALUE
  | EFF
  | TRUE
  | FALSE
  | NOT
  | UNDEF
  | ERROR
  | LET
  | IN
  | IF
  | THEN
  | ELSE
  | UNSEQ
  | WEAK
  | STRONG
  | SAVE (* TODO *)
  | RUN (* TODO *)
(*
  | TRY
  | WITH
*)

  | BOUND
  | CREATE
  | CREATE_READONLY
  | ALLOC
  | FREE
  | KILL
  | STORE
  | STORE_LOCK
  | LOAD
  | SEQ_RMW
  | SEQ_RMW_WITH_FORWARD
  | RMW
  | FENCE
(*  | COMPARE_EXCHANGE_STRONG *)
  | DEF
  | GLOB
  | FUN
  | PROC
  | END
  | SEQ_CST
  | RELAXED
  | RELEASE
  | ACQUIRE
  | CONSUME
  | ACQ_REL
  | IS_SCALAR
  | IS_INTEGER
  | IS_SIGNED
  | IS_UNSIGNED
  | ARE_COMPATIBLE
  | UNSPECIFIED
  
  | STRING of string
  | CSTRING of string
  
  | SYM of _sym
  | IMPL of Implementation.implementation_constant
  | UB of Undefined.undefined_behaviour
  | INT_CONST of Nat_big_num.num
  
  | SQUOTE
  
  | CASE
  | OF
  
  | EQ_GT

  | PLUS
  | MINUS
  | STAR
  | SLASH
  | REM_T
  | REM_F
  | CARET
  | EQ
  | GT
  | LT
  | GE
  | LE
  | SLASH_BACKSLASH
  | BACKSLASH_SLASH
  | NEG
  | UNDERSCORE
  | PIPE
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LBRACE
  | RBRACE
  | DOT
  | DOTS
  | SEMICOLON
  | COMMA
  | COLON
  | COLON_EQ
  | EOF
  
  | PAR
  | ND
  | ARRAY_SHIFT
  | MEMBER_SHIFT
  
  (* integer values *)
  | IVMAX
  | IVMIN
  | IVSIZEOF
  | IVALIGNOF
  | IVCOMPL
  | IVAND
  | IVOR
  | IVXOR
  | CCALL
  | PCALL
  | CFUNCTION_VALUE
  | ARRAYCTOR

  | COLON_COLON
  | BRACKETS
  | ARRAY
  | LOADED
  | STORABLE
  | SPECIFIED
  
  | PURE
  
  | MEMOP
  | PURE_MEMOP_OP of Mem_common.pure_memop
  | MEMOP_OP of _sym Mem_common.generic_memop
  | PTRMEMBERSHIFT
  
  | AILNAME

  | AILCTYPE
  
  | FVFROMINT
  | IVFROMFLOAT
  | NULL
  | BUILTIN
  | CONV_INT
  | WRAPI of Core.iop
  | CATCH_EXCEPTIONAL_CONDITION of Core.iop
