module CF = Cerb_frontend

(* copying subset of Ctype.ctype *)


type t =
  | Void
  | Integer of CF.Ctype.integerType
  | Pointer of CF.Ctype.qualifiers * t
  | Struct of Sym.t




let rec to_ctype = function
  | Void -> CF.Ctype.Ctype ([], Void)
  | Integer it -> CF.Ctype.Ctype ([], Basic (Integer it))
  | Pointer (q,t) -> CF.Ctype.Ctype ([], Pointer (q, to_ctype t))
  | Struct t -> CF.Ctype.Ctype ([], Struct t)


let rec of_ctype (CF.Ctype.Ctype (_,ct_)) =
  let open Option in
  match ct_ with
  | CF.Ctype.Void -> 
     Some Void
  | CF.Ctype.Basic (Integer it) -> 
     Some (Integer it)
  | CF.Ctype.Basic (Floating it) -> 
     None
  | CF.Ctype.Array _ -> 
     None
  | CF.Ctype.Function _ -> 
     None
  | CF.Ctype.Pointer (qualifiers,ctype) -> 
     let* t = of_ctype ctype in
     Some (Pointer (qualifiers, t))
  | CF.Ctype.Atomic _ ->
     None
  | CF.Ctype.Struct s ->
     Some (Struct s)
  | Union _ ->
     None



let equal t1 t2 = 
  CF.Ctype.ctypeEqual (to_ctype t1) (to_ctype t2)

let pp t = 
  CF.Pp_core_ctype.pp_ctype (to_ctype t)


