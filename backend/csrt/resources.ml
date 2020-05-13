open Option
open List
open PPrint
open Pp_tools
module Loc=Locations
module IT=IndexTerms

type t = 
  | Block of Sym.t * IT.t (* size *)
  (* | Uninitialised of IndexTerms.t * Ctype.ctype *)
  | Points of Sym.t * Sym.t * IT.t
  | Struct of Sym.t

let pp = function
  | Block (it1,it2) -> 
     parens (!^"block" ^^^ Sym.pp it1 ^^^ IndexTerms.pp it2)
  (* | Uninitialised (it, ct) ->
   *    parens (!^"uninit" ^^^ IndexTerms.pp it ^^^ squotes (Pp_core_ctype.pp_ctype ct) *)
  | Points (it1,it2,it3) ->     (* it2: what it points to, it3: size *)
     parens (!^"points" ^^^ Sym.pp it1 ^^^ Sym.pp it2 ^^^ IndexTerms.pp it3)
  | Struct sym ->
     Colour.pp_ansi_format [Red;Bold] (parens (!^"struct" ^^^ Sym.pp sym))




let subst sym with_it t = 
  match t with
  | Block (it, it') -> 
     Block (Sym.subst sym with_it it, 
             IndexTerms.subst sym with_it it')
  (* | Uninitialised (it,ct) ->
   *    Uninitialised (IndexTerms.subst sym with_it it, ct) *)
  | Points (it, it', it'') -> 
     Points (Sym.subst sym with_it it, 
             Sym.subst sym with_it it',
             IndexTerms.subst sym with_it it'')
  | Struct s ->
     Struct (Sym.subst sym with_it s)

let type_equal env t1 t2 = 
  t1 = t2                       (* todo: maybe up to variable
                                   instantiation, etc. *)

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)

let unify r1 r2 res = 
  match r1, r2 with
  | Points (it1, it2, it3), Points (it1', it2', it3') ->
     Sym.unify it1 it1' res >>= fun res ->
     Sym.unify it2 it2' res >>= fun res ->
     IndexTerms.unify it3 it3' res
  | Block (it1, it2), Block (it1', it2') ->
     Sym.unify it1 it1' res >>= fun res ->
     IndexTerms.unify it2 it2' res
  | Struct sym, Struct sym' ->
     Sym.unify sym sym' res
  | _ -> fail


let associated = function
  | Points (v, _, _) -> v
  | Block (v, _) -> v
  | Struct v -> v

let footprint = function
  | Points (v, _, size) -> Some (v,size)
  | Block (v, size) -> Some (v,size)
  | Struct v -> None

(* let owned = function
 *   | Points (_, v, _) -> [v]
 *   | Struct _ -> []
 *   | Block _ -> [] *)


