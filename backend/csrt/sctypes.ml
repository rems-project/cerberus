module CF = Cerb_frontend

(* copying subset of Ctype.ctype *)


type t_ =
  | Void
  | Integer of CF.Ctype.integerType
  | Pointer of CF.Ctype.qualifiers * t
  | Struct of Sym.t

and t = 
  Sctype of CF.Annot.annot list * t_




let rec to_ctype : t -> CF.Ctype.ctype = 
  fun (Sctype (annots, sct_)) ->
  let ct_ = match sct_ with
    | Void -> CF.Ctype.Void
    | Integer it -> Basic (Integer it)
    | Pointer (q,t) -> Pointer (q, to_ctype t)
    | Struct t -> Struct t
  in
  Ctype (annots, ct_)


let rec of_ctype : CF.Ctype.ctype -> t option =
  fun (CF.Ctype.Ctype (annots,ct_)) ->
  let open Option in
  match ct_ with
  | CF.Ctype.Void -> 
     (Some (Sctype (annots, Void)) : t option)
  | CF.Ctype.Basic (Integer it) -> 
     (Some (Sctype (annots, Integer it)) : t option)
  | CF.Ctype.Basic (Floating it) -> 
     None
  | CF.Ctype.Array _ -> 
     None
  | CF.Ctype.Function _ -> 
     None
  | CF.Ctype.Pointer (qualifiers,ctype) -> 
     let* t = of_ctype ctype in
     Some (Sctype (annots, Pointer (qualifiers, t)))
  | CF.Ctype.Atomic _ ->
     None
  | CF.Ctype.Struct s ->
     Some (Sctype (annots, Struct s))
  | Union _ ->
     None




let equal t1 t2 = 
  CF.Ctype.ctypeEqual (to_ctype t1) (to_ctype t2)

let pp t = 
  CF.Pp_core_ctype.pp_ctype (to_ctype t)


