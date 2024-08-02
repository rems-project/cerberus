open Cerb_frontend

(* copying some things over from frontend/model/ctype.lem *)
(* copying subset of Ctype.ctype *)

module IntegerBaseTypes = struct
  type integerBaseType = Ctype.integerBaseType =
    | Ichar
    | Short
    | Int_
    | Long
    | LongLong
    (* Things defined in the standard libraries *)
    | IntN_t of int
    | Int_leastN_t of int
    | Int_fastN_t of int
    | Intmax_t
    | Intptr_t
  [@@deriving eq, ord]

  type t = integerBaseType

  let equal = equal_integerBaseType

  let compare = compare_integerBaseType
end

open IntegerBaseTypes

module IntegerTypes = struct
  type integerType = Ctype.integerType =
    | Char
    | Bool
    | Signed of integerBaseType
    | Unsigned of integerBaseType
    | Enum of Symbol.sym
    (* Things defined in the standard libraries *)
    | Wchar_t
    | Wint_t
    | Size_t
    | Ptrdiff_t
    | Ptraddr_t
  [@@deriving eq, ord]

  type t = integerType

  let equal = equal_integerType

  let compare = compare_integerType

  let pp = Pp_core_ctype.pp_integer_ctype
end

open IntegerTypes

module Qualifiers = struct
  type qualifiers = Ctype.qualifiers =
    { const : bool;
      restrict : bool;
      volatile : bool
    }
  [@@deriving eq, ord]

  type t = qualifiers

  let equal = equal_qualifiers

  let compare = compare_qualifiers
end

open Qualifiers

type ctype =
  | Void
  | Integer of integerType
  | Array of ctype * int option
  | Pointer of ctype
  | Struct of Sym.t
  | Function of
      (qualifiers * ctype)
      * (ctype * (* is_register *) bool) list
      * (* is_variadic *) bool
[@@deriving eq, ord]

type t = ctype

let equal = equal_ctype

let compare = compare_ctype

type c_concrete_sig =
  { sig_return_ty : Ctype.ctype;
    sig_arg_tys : Ctype.ctype list;
    sig_variadic : bool;
    sig_has_proto : bool
  }

let rec subtype ct ct' =
  match (ct, ct') with
  | Void, Void -> true
  | Integer it, Integer it' -> IntegerTypes.equal it it'
  | Array (ct, _length_opt), Array (ct', None) -> subtype ct ct'
  | Array (ct, length_opt), Array (ct', length_opt') ->
    subtype ct ct' && Option.equal Int.equal length_opt length_opt'
  | Pointer ct, Pointer ct' -> subtype ct ct'
  | Struct tag, Struct tag' -> Sym.equal tag tag'
  | Function _, Function _ -> equal_ctype ct ct'
  | _, _ -> false


let is_unsigned_integer_type ty =
  AilTypesAux.is_unsigned_integer_type Ctype.(Ctype ([], Basic (Integer ty)))


let is_unsigned_integer_ctype = function
  | Integer ty ->
    AilTypesAux.is_unsigned_integer_type Ctype.(Ctype ([], Basic (Integer ty)))
  | _ -> false


let is_struct_ctype = function Struct tag -> Some tag | _ -> None

let void_ct = Void

let integer_ct it = Integer it

let array_ct ct olength = Array (ct, olength)

let pointer_ct ct = Pointer ct

let struct_ct tag = Struct tag

let char_ct = Integer Char

let rec to_ctype (ct_ : ctype) =
  let ct_ =
    match ct_ with
    | Void -> Ctype.Void
    | Integer it -> Basic (Integer it)
    | Array (t, oi) -> Array (to_ctype t, Option.map Z.of_int oi)
    | Pointer t -> Pointer (Ctype.no_qualifiers, to_ctype t)
    | Struct t -> Struct t
    | Function ((ret_q, ret_ct), args, variadic) ->
      let args =
        List.map
          (fun (arg_ct, is_reg) -> (Ctype.no_qualifiers, to_ctype arg_ct, is_reg))
          args
      in
      let ret_ct = to_ctype ret_ct in
      Function ((ret_q, ret_ct), args, variadic)
  in
  Ctype ([], ct_)


let rec of_ctype (Ctype.Ctype (_, ct_)) =
  let open Option in
  match ct_ with
  | Ctype.Void -> return Void
  | Ctype.Basic (Integer it) -> return (Integer it)
  | Ctype.Basic (Floating _) -> fail
  | Ctype.Array (ct, nopt) ->
    let@ ct = of_ctype ct in
    return (Array (ct, Option.map Z.to_int nopt))
  | Ctype.Function ((ret_q, ret_ct), args, variadic) ->
    let@ args =
      ListM.mapM
        (fun (_arg_q, arg_ct, is_reg) ->
          let@ arg_ct = of_ctype arg_ct in
          return (arg_ct, is_reg))
        args
    in
    let@ ret_ct = of_ctype ret_ct in
    return (Function ((ret_q, ret_ct), args, variadic))

  (* The meaning of a function with no parameters depends on the version of C,
     but here we treat it as if it really has no parameter (i.e., like `void`)
     which is what more recent versions of the standard do. *)
  | Ctype.FunctionNoParams (ret_q, ret_ct) ->
    let@ ret_ct = of_ctype ret_ct in
    return (Function ((ret_q, ret_ct), [], false))

  | Ctype.Pointer (_qualifiers, ctype) ->
    let@ t = of_ctype ctype in
    return (Pointer t)
  | Ctype.Atomic _ -> None
  | Ctype.Struct s -> return (Struct s)
  | Union _ -> fail


let of_ctype_unsafe loc ct =
  let open Cerb_pp_prelude in
  match of_ctype ct with
  | Some ct -> ct
  | None -> Tools.unsupported loc (!^"YAV C-type" ^^^ Cerb_frontend.Pp_core_ctype.pp_ctype ct)


let pp t = Pp_core_ctype.pp_ctype (to_ctype t)

let is_integer_type = function Integer it -> Some it | _ -> None
