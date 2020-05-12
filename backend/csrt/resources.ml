open Option
open List
open PPrint
open Pp_tools
module Loc=Locations


type t = 
  | Block of IndexTerms.t * IndexTerms.t (* size *)
  (* | Uninitialised of IndexTerms.t * Ctype.ctype *)
  | Points of IndexTerms.t * IndexTerms.t * IndexTerms.t
  | Struct of Sym.t

let pp = function
  | Block (it1,it2) -> 
     parens (!^"block" ^^^ IndexTerms.pp it1 ^^^ IndexTerms.pp it2)
  (* | Uninitialised (it, ct) ->
   *    parens (!^"uninit" ^^^ IndexTerms.pp it ^^^ squotes (Pp_core_ctype.pp_ctype ct) *)
  | Points (it1,it2,it3) ->     (* it2: what it points to, it3: size *)
     parens (!^"points" ^^^ IndexTerms.pp it1 ^^^ IndexTerms.pp it2 ^^^ IndexTerms.pp it3)
  | Struct sym ->
     Colour.pp_ansi_format [Red;Bold] (parens (!^"struct" ^^^ Sym.pp sym))




let subst sym with_it t = 
  match t with
  | Block (it, it') -> 
     Block (IndexTerms.subst sym with_it it, 
             IndexTerms.subst sym with_it it')
  (* | Uninitialised (it,ct) ->
   *    Uninitialised (IndexTerms.subst sym with_it it, ct) *)
  | Points (it, it', it'') -> 
     Points (IndexTerms.subst sym with_it it, 
             IndexTerms.subst sym with_it it',
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
     IndexTerms.unify it1 it1' res >>= fun res ->
     IndexTerms.unify it2 it2' res >>= fun res ->
     IndexTerms.unify it3 it3' res
  | Block (it1, it2), Block (it1', it2') ->
     IndexTerms.unify it1 it1' res >>= fun res ->
     IndexTerms.unify it2 it2' res

  | Struct (sym), Struct (sym') when sym = sym' ->
     return res

  | Struct sym, Struct sym' ->
     begin match SymMap.find_opt sym res with
     | None -> fail
     | Some uni ->
        match uni.resolved with
        | Some s when s = sym' -> return res 
        | Some it -> fail
        | None -> 
           let uni = { uni with resolved = Some sym' } in
           return (SymMap.add sym uni res)
     end
  | _ -> fail


let owner = function
  | Points (S (v,_), _, _) -> Some v
  | Block (S (v,_), _) -> Some v
  | Struct s -> Some s
  | _ -> None

let owned = function
  | Points (_, S (v,_), _) -> [v]
  | Points (_, _, _) -> []
  | Struct _ -> []
  | Block _ -> []


