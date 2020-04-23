open Utils
open List
open Printf
open Sym
open Sexplib
open Except
module Loc=Location

type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  | List of t
  | Tuple of t list
  | Struct of Sym.t

let rec pp = function
  | Unit -> "unit" 
  | Bool -> "bool"
  | Int -> "int"
  | Loc -> "loc"
  | Array -> "array"
  | List bt -> sprintf "(list %s)" (pp bt)
  | Tuple bts -> sprintf "(tuple (%s))" (String.concat " " (map pp bts))
  | Struct id -> sprintf "(struct %s)" (Sym.pp id)

let rec parse_sexp loc (names : namemap) sx = 
  match sx with
  | Sexp.Atom "unit" -> 
     return Unit
  | Sexp.Atom "bool" -> 
     return Bool
  | Sexp.Atom "int" -> 
     return Int
  | Sexp.Atom "loc" -> 
     return Loc
  | Sexp.Atom "array" -> 
     return Array
  | Sexp.List [Sexp.Atom "list"; bt] -> 
     parse_sexp loc names bt >>= fun bt -> 
     return (List bt)
  | Sexp.List [Sexp.Atom "tuple"; Sexp.List bts] -> 
     mapM (parse_sexp loc names) bts >>= fun bts ->
     return (Tuple bts)
  | Sexp.List [Sexp.Atom "struct"; Sexp.Atom id] -> 
     Sym.parse loc names id >>= fun sym ->
     return (Struct sym)
  | a -> parse_error "base type" a loc

let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst _sym _sym' bt = bt


