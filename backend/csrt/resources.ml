open Option
open List
open PPrint
open Pp_tools
module Loc=Locations
module IT=IndexTerms



type field_names = (Sym.t * Sym.t) list

type t = 
  | Block of Sym.t * Utils.num (* size *)
  (* | Uninitialised of IndexTerms.t * Ctype.ctype *)
  | Points of Sym.t * Sym.t * Utils.num
  | PackedStruct of Sym.t
  | OpenedStruct of Sym.t * field_names

let pp = function
  | Block (it1,it2) -> 
     parens (!^"block" ^^^ Sym.pp it1 ^^^ pp_num it2)
  (* | Uninitialised (it, ct) ->
   *    parens (!^"uninit" ^^^ IndexTerms.pp it ^^^ squotes (Pp_core_ctype.pp_ctype ct) *)
  | Points (it1,it2,it3) ->     (* it2: what it points to, it3: size *)
     parens (!^"points" ^^^ Sym.pp it1 ^^^ Sym.pp it2 ^^^ pp_num it3)
  | PackedStruct sym ->
     (parens (!^"packed struct" ^^^ Sym.pp sym))
  | OpenedStruct (sym_val, field_names) ->
     let pp_field_names =
       flow_map (comma ^^ break 1) 
         (fun (s1,s2) -> parens (Sym.pp s1 ^^^ arrow ^^^ Sym.pp s2)) 
         field_names
     in
     Colour.pp_ansi_format [Red;Bold] 
       (parens (!^"opened struct" ^^^ Sym.pp sym_val ^^^ parens pp_field_names))




let subst sym with_it t = 
  match t with
  | Block (it, it') -> 
     Block (Sym.subst sym with_it it, it') 
             (* IndexTerms.subst sym with_it it') *)
  | Points (it, it', it'') -> 
     Points (Sym.subst sym with_it it, 
             Sym.subst sym with_it it',
             it'')
             (* IndexTerms.subst sym with_it it'') *)
  | PackedStruct s ->
     PackedStruct (Sym.subst sym with_it s)
  | OpenedStruct (s1, field_names) ->
     let field_names' = 
       List.map (fun (s,s') -> (Sym.subst sym with_it s,Sym.subst sym with_it s'))
         field_names in
     OpenedStruct (Sym.subst sym with_it s1, field_names')

let type_equal env t1 t2 = 
  t1 = t2                       (* todo: maybe up to variable
                                   instantiation, etc. *)

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)


let rec unify_field_names field_names field_names' res = 
  match field_names, field_names' with
  | [], [] -> return res
  | (s1,s2) :: field_names, (s1',s2') :: field_names' ->
     Sym.unify s1 s1' res >>= fun res ->
     Sym.unify s2 s2' res >>= fun res ->
     unify_field_names field_names field_names' res
  | _, _ -> fail


let unify r1 r2 res = 
  match r1, r2 with
  | Points (it1, it2, it3), Points (it1', it2', it3') 
       when Nat_big_num.equal it3 it3' ->
     Sym.unify it1 it1' res >>= fun res ->
     Sym.unify it2 it2' res >>= fun res ->
     return res
     (* IndexTerms.unify it3 it3' res *)
  | Block (it1, it2), Block (it1', it2')
       when Nat_big_num.equal it2 it2' ->
     Sym.unify it1 it1' res >>= fun res ->
     return res
     (* IndexTerms.unify it2 it2' res *)
  | PackedStruct sym, PackedStruct (sym') ->
     Sym.unify sym sym' res
  | OpenedStruct (sym1, field_names),
    OpenedStruct (sym1', field_names')  ->
     Sym.unify sym1 sym1' res >>= fun res ->
     unify_field_names field_names field_names' res
  | _ -> fail


let associated = function
  | Points (v, _, _) -> v
  | Block (v, _) -> v
  | PackedStruct v -> v
  | OpenedStruct (v,_) -> v

let footprint = function
  | Points (v, _, size) -> Some (v,size)
  | Block (v, size) -> Some (v,size)
  | PackedStruct _ -> None
  | OpenedStruct _ -> None

(* let owned = function
 *   | Points (_, v, _) -> [v]
 *   | Struct _ -> []
 *   | Block _ -> [] *)


