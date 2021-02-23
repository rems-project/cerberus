open Cerb_frontend

(* copying subset of Ctype.ctype *)


type t_ =
  | Void
  | Integer of Ctype.integerType
  | Pointer of Ctype.qualifiers * t
  | Struct of Sym.t
  | Function of (* has_proto *)bool * (Ctype.qualifiers * t)
                * (Ctype.qualifiers * t * (* is_register *)bool) list
                * (* is_variadic *)bool


and t = 
  Sctype of Annot.annot list * t_

let pointer_sct sct = 
  Sctype ([], Pointer (Ctype.no_qualifiers, sct))


let rec to_ctype : t -> Ctype.ctype = 
  fun (Sctype (annots, sct_)) ->
  let ct_ = match sct_ with
    | Void -> Ctype.Void
    | Integer it -> Basic (Integer it)
    | Pointer (q,t) -> Pointer (q, to_ctype t)
    | Struct t -> Struct t
    | Function (has_proto, (ret_q,ret_ct), args, variadic) ->
       let args = 
         List.map (fun (arg_q, arg_ct, is_reg) -> (arg_q, to_ctype arg_ct, is_reg))
           args
       in
       let ret_ct = to_ctype ret_ct in
       Function (has_proto, (ret_q, ret_ct), args, variadic)
  in
  Ctype (annots, ct_)


let rec of_ctype : Ctype.ctype -> t option =
  fun (Ctype.Ctype (annots,ct_)) ->
  let open Option in
  match ct_ with
  | Ctype.Void -> 
     (Some (Sctype (annots, Void)) : t option)
  | Ctype.Basic (Integer it) -> 
     (Some (Sctype (annots, Integer it)) : t option)
  | Ctype.Basic (Floating it) -> 
     None
  | Ctype.Array _ -> 
     None
  | Ctype.Function (has_proto, (ret_q,ret_ct), args, variadic) ->
     let* args = 
       ListM.mapM (fun (arg_q, arg_ct, is_reg) -> 
           let* arg_ct = of_ctype arg_ct in
           return (arg_q, arg_ct, is_reg)
         ) args
     in
     let* ret_ct = of_ctype ret_ct in
     Some (Sctype (annots, Function (has_proto, (ret_q, ret_ct), args, variadic)))
  | Ctype.Pointer (qualifiers,ctype) -> 
     let* t = of_ctype ctype in
     Some (Sctype (annots, Pointer (qualifiers, t)))
  | Ctype.Atomic _ ->
     None
  | Ctype.Struct s ->
     Some (Sctype (annots, Struct s))
  | Union _ ->
     None




let equal t1 t2 = 
  Ctype.ctypeEqual (to_ctype t1) (to_ctype t2)

let pp t = 
  Pp_core_ctype.pp_ctype (to_ctype t)


