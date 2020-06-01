open Option
open Pp
open List
module Loc = Locations
module IT = IndexTerms
module CF = Cerb_frontend




type points = 
  { pointer: Sym.t; 
    pointee: Sym.t option; 
    typ: CF.Ctype.ctype;
    size: Num.t 
  }



type t = Points of points

let pp atomic resource = 
  let mparens pp = if atomic then parens pp else pp in
  match resource with
  | Points {pointer; pointee = Some v; typ; size} ->
     mparens (!^"Points" ^^ parens (pp_ctype typ) ^^^ Sym.pp pointer ^^^ Sym.pp v)
  | Points {pointer; pointee = None; typ; size} ->
     mparens (!^"Points" ^^ parens (pp_ctype typ) ^^^ Sym.pp pointer ^^^ !^"uninit")




let subst_var subst = function
  | Points p -> 
     let pointee = match p.pointee with
       | Some s -> Some (Sym.subst subst s)
       | None -> None
     in
     let pointer = Sym.subst subst p.pointer in
     Points {p with pointer; pointee}

let subst_vars = Subst.make_substs subst_var



let type_equal env t1 t2 = t1 = t2

let types_equal env ts1 ts2 = 
  for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)




let associated = function
  | Points p -> p.pointer





let unify r1 r2 res = 
  match r1, r2 with
  | Points p, Points p' when
         CF.Ctype.ctypeEqual p.typ p'.typ && Num.equal p.size p'.size ->

     let* res = Sym.unify p.pointer p'.pointer res in
     begin match p.pointee, p'.pointee with
     | Some s, Some s' -> Sym.unify s s' res
     | None, None -> return res
     | _, _ -> fail
     end
  | _ -> fail
