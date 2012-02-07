(*
 * Copyright (c) 2001-2002,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(** This file was originally part of Hugues Casee's frontc 2.0, and has been
* * extensively changed since.
**
** 1.0	3.22.99	Hugues Cassé	First version.
** 2.0  George Necula 12/12/00: Many extensions
**)

(*
** Types
*)

type cabsloc = {
  lineno : int;
  filename: string;
  byteno: int;
  ident : int
}


type location = Position.t

type storage_class =
  | AUTO
  | STATIC
  | EXTERN
  | REGISTER

type qualifier =
  | CONST

type specifier =
  | VOID
  | CHAR
  | SHORT
  | INT
  | LONG
  | SIGNED
  | UNSIGNED
  | BOOL

type specifiers = specifier CpMultiSet.t
type qualifiers = qualifier BatSet.t

(* Expressions *)
type sequential_operator =
  | COMMA
  | AND
  | OR

type arithmetic_operator =
  | ADD
  | SUB
  | MUL
  | DIV
  | MOD
  | BAND
  | BOR
  | XOR
  | SHL
  | SHR

type relational_operator =
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

type binary_operator =
  | ARITHMETIC of arithmetic_operator
  | SEQUENTIAL of sequential_operator
  | RELATIONAL of relational_operator

type unary_operator =
  | MINUS
  | PLUS
  | NOT
  | BNOT
  | ADDRESS
  | INDIRECTION
  | PREFIX_INCR
  | PREFIX_DECR
  | POSTFIX_INCR
  | POSTFIX_DECR

type suffix =
  | SUFFIX_UNSIGNED
  | SUFFIX_UNSIGNED_LONG
  | SUFFIX_UNSIGNED_LONG_LONG
  | SUFFIX_LONG
  | SUFFIX_LONG_LONG

type integer_constant = BatBig_int.t * suffix option

type constant =
  | CONST_INT of integer_constant
(*
  | CONST_FLOAT of string (* the textual representaton *)
  | CONST_CHAR of int64 list
  | CONST_WCHAR of int64 list
  | CONST_STRING of string
*)

type c_type =
  | BASE of qualifiers * specifiers
  | ARRAY of qualifiers * c_type * exp_l option
  | POINTER of qualifiers * c_type
  | FUNCTION of c_type * decl_l list

(* Declaration *)
and declaration = string * c_type * storage_class list
and decl_l = declaration * location
and definition = decl_l * exp_l option
and defn_l = definition * location

and expression =
  | UNARY of unary_operator * exp_l
  | BINARY of binary_operator * exp_l * exp_l 
  | ASSIGN of arithmetic_operator option * exp_l * exp_l
  | QUESTION of exp_l * exp_l * exp_l
(*
  | COMPOUND_LITERAL of (specifier * c_type) * init_expression
*)
  | CAST of c_type * exp_l
  | CALL of exp_l * exp_l list
  | CONSTANT of constant
  | VARIABLE of string
  | TYPE_SIZEOF of c_type
  | TYPE_ALIGNOF of c_type
  | INDEX of exp_l * exp_l

and exp_l = expression * location

(* Statements *)

type statement =
  | SKIP
  | EXPRESSION of exp_l
  | BLOCK of stmt_l list
  | IF of exp_l * stmt_l * stmt_l option
  | WHILE of exp_l * stmt_l
  | DO of exp_l * stmt_l
  | FOR_EXP of exp_l option * exp_l option * exp_l option * stmt_l
  | FOR_DECL of defn_l list * exp_l option * exp_l option * stmt_l
  | BREAK
  | CONTINUE
  | RETURN of exp_l option
  | SWITCH of exp_l * stmt_l
  | CASE of exp_l * stmt_l
  | DEFAULT of stmt_l
  | LABEL of string * stmt_l
  | GOTO of string
  | DECLARATION of defn_l list

and stmt_l = statement * location

type global_definition =
  | FUNCTION_DEFINITION of decl_l * stmt_l
  | EXTERNAL_DECLARATION of defn_l list

type g_defn_l = global_definition * location

(* the string is a file name, and then the list of toplevel forms *)
type file = string * g_defn_l list
