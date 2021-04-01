open Cerb_frontend

(* copying subset of Ctype.ctype *)



type t = 
  Sctype of Annot.annot list * t_

and t_ =
  | Void
  | Integer of Ctype.integerType
  | Array of t * int option
  | Pointer of Ctype.qualifiers * t
  | Struct of Sym.t
  | Function of (* has_proto *)bool * (Ctype.qualifiers * t)
                * (Ctype.qualifiers * t * (* is_register *)bool) list
                * (* is_variadic *)bool


let is_unsigned_integer_type = function
  | Sctype (_, Integer ty) ->
     AilTypesAux.is_unsigned_integer_type 
       (Ctype ([], Ctype.Basic (Ctype.Integer ty)))
  | _ -> false
     


let pointer_sct sct = 
  Sctype ([], Pointer (Ctype.no_qualifiers, sct))


let rec to_ctype (Sctype (annots, ct_)) =
  let ct_ = match ct_ with
    | Void -> 
       Ctype.Void
    | Integer it -> 
       Basic (Integer it)
    | Array (t, oi) ->
       Array (to_ctype t, Option.map Z.of_int oi)
    | Pointer (q,t) -> 
       Pointer (q, to_ctype t)
    | Struct t -> 
       Struct t
    | Function (has_proto, (ret_q,ret_ct), args, variadic) ->
       let args = 
         List.map (fun (arg_q, arg_ct, is_reg) -> 
             (arg_q, to_ctype arg_ct, is_reg)
           ) args
       in
       let ret_ct = to_ctype ret_ct in
       Function (has_proto, (ret_q, ret_ct), args, variadic)
  in
  Ctype (annots, ct_)


let rec of_ctype (Ctype.Ctype (annots,ct_)) =
  let open Option in
  let@ ct_ = match ct_ with
  | Ctype.Void -> 
     return Void
  | Ctype.Basic (Integer it) -> 
     return (Integer it)
  | Ctype.Basic (Floating it) -> 
     fail
  | Ctype.Array _ -> 
     fail
  | Ctype.Function (has_proto, (ret_q,ret_ct), args, variadic) ->
     let@ args = 
       ListM.mapM (fun (arg_q, arg_ct, is_reg) -> 
           let@ arg_ct = of_ctype arg_ct in
           return (arg_q, arg_ct, is_reg)
         ) args
     in
     let@ ret_ct = of_ctype ret_ct in
     return (Function (has_proto, (ret_q, ret_ct), args, variadic))
  | Ctype.Pointer (qualifiers,ctype) -> 
     let@ t = of_ctype ctype in
     return (Pointer (qualifiers, t))
  | Ctype.Atomic _ ->
     None
  | Ctype.Struct s ->
     return (Struct s)
  | Union _ ->
     fail
  in
  return (Sctype (annots, ct_))



let rec equal (Sctype (_, ct1_)) (Sctype (_, ct2_)) =
  match ct1_, ct2_ with
  | Void, Void -> 
     true
  | Integer it1, Integer it2 -> 
     Ctype.integerTypeEqual it1 it2
  | Array (t1, oi1), Array (t2, oi2) ->
     equal t1 t2 && Option.equal (=) oi1 oi2
  | Pointer (qs1, ct1), Pointer (qs2, ct2) ->
     equal ct1 ct2 &&
     Ctype.qualifiersEqual qs1 qs2
  | Struct s1, Struct s2 ->
     Sym.equal s1 s2
  | Function (has_proto1, (qs1, ret1), args1, is_variadic1),
    Function (has_proto2, (qs2, ret2), args2, is_variadic2) ->
     has_proto1 = has_proto2 &&
     Ctype.qualifiersEqual qs1 qs2 &&
     equal ret1 ret2 &&
     List.equal (fun (aqs1,act1,areg1) (aqs2,act2,areg2) ->
         Ctype.qualifiersEqual aqs1 aqs2 &&
         equal act1 act2 &&
         areg1 = areg2
       ) args1 args2 &&
     is_variadic1 = is_variadic2

  | Void, _
  | Integer _, _
  | Array _, _
  | Pointer _, _
  | Struct _, _
  | Function _, _ 
    -> 
     false



let pp t = 
  Pp_core_ctype.pp_ctype (to_ctype t)


