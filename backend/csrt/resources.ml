open Utils
open Cerb_frontend
open Pp_core_ctype
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
  | Points of points_to

let pp = function
  | Points {pointer; pointee = Some s ; typ; size} ->
     parens (!^"points" ^^^ parens (pp_ctype typ) ^^^ Sym.pp pointer ^^^ Sym.pp s)
  | Points {pointer; pointee = None ; typ; size} ->
     parens (Sym.pp pointer ^^^ !^"uninit" ^^^ pp_ctype typ)


let subst_var sym with_it = function
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (Sym.subst sym with_it s)
       | None -> None
     in
     let pointer = Sym.subst sym with_it p.pointer in
     Points {p with pointer; pointee}


let type_equal env t1 t2 = t1 = t2

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)


let unify r1 r2 res = 
  match r1, r2 with
  | Points p, Points p' when Ctype.ctypeEqual p.typ p'.typ ->
     Sym.unify p.pointer p'.pointer res >>= fun res ->
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> Sym.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | _ -> fail


let associated = function
  | Points p -> p.pointer




