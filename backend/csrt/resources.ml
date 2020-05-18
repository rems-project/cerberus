open Utils
open Cerb_frontend
open Option
open List
open PPrint
open Pp_tools
module Loc=Locations
module IT=IndexTerms



type points_to = 
  {pointer: Sym.t; 
   pointee: Sym.t option; 
   typ: Cerb_frontend.Ctype.ctype;
   size: num}

type t = 
  (* | Block of {loc: Sym.t; size : num} *)
  | Points of points_to

let pp = function
  (* | Block b -> 
   *    parens (!^"block" ^^^ Sym.pp b.loc ^^^ pp_num b.size) *)
  | Points p ->
     begin match p.pointee with
     | Some s ->
        parens (!^"points" ^^^ Sym.pp p.pointer ^^^ Sym.pp s ^^^ 
                  Cerb_frontend.Pp_core_ctype.pp_ctype p.typ)
     | None ->
        parens (!^"points" ^^^ Sym.pp p.pointer ^^^ !^"uninitialised" ^^^
                  Cerb_frontend.Pp_core_ctype.pp_ctype p.typ)
     end

let subst sym with_it t = 
  match t with
  (* | Block b -> 
   *    Block {loc = Sym.subst sym with_it b.loc;
   *           size = b.size}  *)
  | Points p -> 
     Points 
       {p with pointer = Sym.subst sym with_it p.pointer;
               pointee = match p.pointee with
                         | Some s -> Some (Sym.subst sym with_it s)
                         | None -> None}


let type_equal env t1 t2 = 
  t1 = t2                       (* todo: maybe up to variable
                                   instantiation, etc. *)

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)


let rec unify_field_names field_names field_names' res = 
  match field_names, field_names' with
  | [], [] -> return res
  | f :: field_names, f' :: field_names' ->
     Sym.unify (fst f) (snd f') res >>= fun res ->
     unify_field_names field_names field_names' res
  | _, _ -> fail


let unify r1 r2 res = 
  match r1, r2 with
  | Points p, Points p' when Ctype.ctypeEqual p.typ p'.typ ->
     Sym.unify p.pointer p'.pointer res >>= fun res ->
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> Sym.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end >>= fun res ->
     return res
  (* | Block b, Block b' when Nat_big_num.equal b.size b'.size ->
   *    Sym.unify b.loc b.loc res *)
  (* | PackedStruct s, PackedStruct s' ->
   *    Sym.unify s.sym s'.sym res *)
  | _ -> fail


let associated = function
  | Points p -> p.pointer
  (* | Block b -> b.loc *)
  (* | PackedStruct s -> s.sym *)

let footprint = function
  | Points p -> Some (p.pointer,p.size)
  (* | Block b -> Some (b.loc,b.size) *)
  (* | PackedStruct s -> None *)

(* let owned = function
 *   | Points (_, v, _) -> [v]
 *   | Struct _ -> []
 *   | Block _ -> [] *)


