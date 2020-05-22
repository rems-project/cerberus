open Option
open Cerb_frontend
open Pp_core_ctype
open List
open PPrint
open Pp_tools
module Loc=Locations
module IT=IndexTerms


type offset = Num.t

type points_to = 
  {pointer: Sym.t; 
   offset: offset;
   pointee: Sym.t option; 
   typ: Cerb_frontend.Ctype.ctype;
   size: Num.t}





type t = Points of points_to

let pp_pointer_and_offset pointer offset = 
  if Num.equal offset Num.zero then Sym.pp pointer 
  else Sym.pp pointer ^^ plus ^^ !^(Num.to_string offset)


let pp atomic = 
  let mparens pped = if atomic then parens pped else pped in
  function
  | Points {pointer; offset; pointee = Some s ; typ; size} ->
     mparens (pp_pointer_and_offset pointer offset ^^
                parens (pp_ctype typ) ^^^ arrow ^^^ Sym.pp s)
  | Points {pointer; offset; pointee = None ; typ; size} ->
     mparens (pp_pointer_and_offset pointer offset ^^
                parens (pp_ctype typ) ^^^ !^"uninit")




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




let associated = function
  | Points p -> p.pointer





let unify r1 r2 res = 
  match r1, r2 with
  | Points p, Points p' when 
         Num.equal p.offset p'.offset &&
         Ctype.ctypeEqual p.typ p'.typ &&
         Num.equal p.size p'.size ->

     Sym.unify p.pointer p'.pointer res >>= fun res ->
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> Sym.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | _ -> fail
