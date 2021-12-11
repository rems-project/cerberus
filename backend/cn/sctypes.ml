open Cerb_frontend

(* copying subset of Ctype.ctype *)



type integerType = Ctype.integerType
let integerTypeEqual = Ctype.integerTypeEqual
let pp_integerType = Pp_core_ctype.pp_integer_ctype

type t =
  | Void
  | Integer of integerType
  | Array of t * int option
  | Pointer of t
  | Struct of Sym.t
  | Function of (* has_proto *)bool * (Ctype.qualifiers * t)
                * (t * (* is_register *)bool) list
                * (* is_variadic *)bool


let is_unsigned_integer_type ty =
  AilTypesAux.is_unsigned_integer_type 
    (Ctype ([], Ctype.Basic (Ctype.Integer ty)))


let is_unsigned_integer_ctype = function
  | Integer ty ->
     AilTypesAux.is_unsigned_integer_type 
       (Ctype ([], Ctype.Basic (Ctype.Integer ty)))
  | _ -> false
     


let void_ct = 
  Void

let integer_ct it = 
  Integer it

let array_ct ct olength = 
  Array (ct, olength)

let pointer_ct ct = 
  Pointer ct

let struct_ct tag = 
  Struct tag

let char_ct = 
  Integer Char




let rec to_ctype ct_ =
  let ct_ = match ct_ with
    | Void -> 
       Ctype.Void
    | Integer it -> 
       Basic (Integer it)
    | Array (t, oi) ->
       Array (to_ctype t, Option.map Z.of_int oi)
    | Pointer t -> 
       Pointer (Ctype.no_qualifiers, to_ctype t)
    | Struct t -> 
       Struct t
    | Function (has_proto, (ret_q,ret_ct), args, variadic) ->
       let args = 
         List.map (fun (arg_ct, is_reg) -> 
             (Ctype.no_qualifiers, to_ctype arg_ct, is_reg)
           ) args
       in
       let ret_ct = to_ctype ret_ct in
       Function (has_proto, (ret_q, ret_ct), args, variadic)
  in
  Ctype ([], ct_)


let rec of_ctype (Ctype.Ctype (_,ct_)) =
  let open Option in
  match ct_ with
  | Ctype.Void -> 
     return Void
  | Ctype.Basic (Integer it) -> 
     return (Integer it)
  | Ctype.Basic (Floating it) -> 
     fail
  | Ctype.Array (ct,nopt) -> 
     let@ ct = of_ctype ct in
     return (Array (ct, Option.map Z.to_int nopt))
  | Ctype.Function (has_proto, (ret_q,ret_ct), args, variadic) ->
     let@ args = 
       ListM.mapM (fun (_arg_q, arg_ct, is_reg) -> 
           let@ arg_ct = of_ctype arg_ct in
           return (arg_ct, is_reg)
         ) args
     in
     let@ ret_ct = of_ctype ret_ct in
     return (Function (has_proto, (ret_q, ret_ct), args, variadic))
  | Ctype.FunctionNoParams _ ->
      fail
  | Ctype.Pointer (qualifiers,ctype) -> 
     let@ t = of_ctype ctype in
     return (Pointer t)
  | Ctype.Atomic _ ->
     None
  | Ctype.Struct s ->
     return (Struct s)
  | Union _ ->
     fail



let equal =
  let rec aux ct1_ ct2_ =
    match ct1_, ct2_ with
    | Void, Void -> 
       true
    | Integer it1, Integer it2 -> 
       Ctype.integerTypeEqual it1 it2
    | Array (t1, oi1), Array (t2, oi2) ->
       aux t1 t2 && Option.equal (=) oi1 oi2
    | Pointer ct1, Pointer ct2 ->
       aux ct1 ct2
       (* && (ignore_qualifiers || Ctype.qualifiersEqual qs1 qs2) *)
    | Struct s1, Struct s2 ->
       Sym.equal s1 s2
    | Function (has_proto1, (qs1, ret1), args1, is_variadic1),
      Function (has_proto2, (qs2, ret2), args2, is_variadic2) ->
       has_proto1 = has_proto2
       (* && (ignore_qualifiers || Ctype.qualifiersEqual qs1 qs2) *)
       && aux ret1 ret2
       && List.equal (fun (act1,areg1) (act2,areg2) ->
              (* (ignore_qualifiers || Ctype.qualifiersEqual aqs1 aqs2) *)
              aux act1 act2 &&
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
  in
  aux



let pp t = 
  Pp_core_ctype.pp_ctype (to_ctype t)


