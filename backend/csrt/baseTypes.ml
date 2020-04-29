open Utils
open List
open PPrint
open Sexplib
open Except
module Loc=Location

type t =
  | Unit 
  | Bool
  | Int
  | Loc
  | Array
  (* | List of t *)
  | Tuple of (Sym.t * t) list
  | Struct of Sym.t

let rec pp = function
  | Unit -> !^ "unit"
  | Bool -> !^ "bool"
  | Int -> !^ "int"
  | Loc -> !^ "loc"
  | Array -> !^ "array"
  (* | List bt -> parens ((!^ "list") ^^^ pp bt) *)
  | Tuple nbts -> parens (separate (break 1) (map pp_tuple_item nbts))
  | Struct id -> parens (!^ "struct" ^^ Sym.pp id)

and pp_tuple_item (sym, bt) = 
  parens (Sym.pp sym ^^ space ^^ colon ^^ space ^^ pp bt)

let rec parse_sexp loc (names : NameMap.t) sx = 
  match sx with
  | Sexp.Atom "unit" -> 
     return (Unit,names)
  | Sexp.Atom "bool" -> 
     return (Bool,names)
  | Sexp.Atom "int" -> 
     return (Int,names)
  | Sexp.Atom "loc" -> 
     return (Loc,names)
  | Sexp.Atom "array" -> 
     return (Array,names)
  (* | Sexp.List [Sexp.Atom "list"; bt] -> 
   *    parse_sexp loc names bt >>= fun bt -> 
   *    return (List bt) *)
  | Sexp.List [Sexp.Atom "struct"; Sexp.Atom id] -> 
     NameMap.sym_of loc id names >>= fun sym ->
     return (Struct sym, names)
  | Sexp.List tuple_items -> 
     fold_leftM (parse_tuple_item loc) ([],names) tuple_items >>= fun (nbts,names) ->
     return (Tuple nbts,names)
  | a -> parse_error loc "base type" a

and parse_tuple_item loc (components, names) s = 
  match s with
  | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; bt] ->
     let name = Sym.fresh_pretty id in
     let names = NameMap.record loc id name names in
     parse_sexp loc names bt >>= fun (bt,names) ->
     return (components @ [name,bt], names)
     
  | a -> parse_error loc "base type" a


let type_equal t1 t2 = t1 = t2

let types_equal ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

let subst _sym _sym' bt = bt


