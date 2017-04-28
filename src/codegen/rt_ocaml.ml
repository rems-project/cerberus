(* Created by Victor Gomes 2017-03-10 *)

open Util
module M = Mem
module T = AilTypes
module C = Core_ctype

exception Undefined of string
exception Error of string
exception No_value

let (>>=) = M.bind0
let (>>) x y = x >>= fun _ -> y
let return = M.return0

(* init/set globals before calling main *)

let set_global (f, x) =
  f return () >>= fun y -> x := y; return ()

let init_globals glbs =
  List.fold_left (fun acc (f, x) -> acc >> set_global (f, x)) (return ()) glbs

let null_ptr = M.null_ptrval C.Void0

(* Non deterministic choice *)

let nd n xs =
  Random.self_init ();
  Random.int n |> List.nth xs

(* IV min/max wraps *)

let ivctor memf errmsg = function
  | C.Basic0 (T.Integer it) -> memf it
  | _ -> raise (Error errmsg)

let ivmin = ivctor M.min_ival "ivmin"

let ivmax = ivctor M.max_ival "ivmax"

(* Ail types *)

let ail_qualifier (c, r, v, a) =
  { AilTypes.const = c;
    AilTypes.restrict = r;
    AilTypes.volatile = v;
    AilTypes.atomic = a;
  }

let is_scalar ty =
  AilTypesAux.is_scalar (Core_aux.unproj_ctype ty)

let is_integer ty =
  AilTypesAux.is_integer (Core_aux.unproj_ctype ty)

let is_signed ty =
  AilTypesAux.is_signed_integer_type (Core_aux.unproj_ctype ty)

let is_unsigned ty =
  AilTypesAux.is_unsigned_integer_type (Core_aux.unproj_ctype ty)

(* Loaded - Specified and unspecified values *)

type 'a loaded =
  | Specified of 'a
  | Unspecified of C.ctype0

let specified x = Specified x
let unspecified x = Unspecified x

exception Label of string * (M.integer_value) loaded

(* Cast from memory values *)

let get_integer m =
  let terr _ _ = raise (Error "Type mismatch, expecting integer values.") in
  M.case_mem_value m unspecified (fun _ -> specified) terr terr (terr()) terr terr

let get_pointer m =
  let terr _ _ = raise (Error "Type mismatch, expecting pointer values.") in
  M.case_mem_value m unspecified terr terr (fun _ p -> specified p)
    (terr()) terr terr

(* Cast to memory values *)

let mk_int s = M.integer_ival (Nat_big_num.of_string s)

(* Binary operations wrap *)

let add = M.op_ival M.IntAdd
let sub = M.op_ival M.IntSub
let mul = M.op_ival M.IntMul
let div = M.op_ival M.IntDiv
let remt = M.op_ival M.IntRem_t
let remf = M.op_ival M.IntRem_f
let exp = M.op_ival M.IntExp

let eq n m = Option.get (M.eq_ival (Some M.initial_mem_state) n m)
let lt n m = Option.get (M.lt_ival (Some M.initial_mem_state) n m)
let gt n m = Option.get (M.lt_ival (Some M.initial_mem_state) m n)
let le n m = Option.get (M.le_ival (Some M.initial_mem_state) n m)
let ge n m = Option.get (M.le_ival (Some M.initial_mem_state) m n)

let eq_ptrval p q = M.eq_ptrval p q
let ne_ptrval p q = M.ne_ptrval p q
let ge_ptrval p q = M.ge_ptrval p q
let lt_ptrval p q = M.lt_ptrval p q
let gt_ptrval p q = M.gt_ptrval p q
let le_ptrval p q = M.le_ptrval p q
let diff_ptrval p q = M.diff_ptrval p q

(* Memory actions wrap *)

let create pre al ty = M.allocate_static 0 pre al ty

let alloc pre al n = M.allocate_dynamic 0 pre al n

let load_integer ity e = M.load (C.Basic0 (T.Integer ity)) e
  >>= return % get_integer % snd

let load_pointer q cty e = M.load (C.Pointer0 (q, cty)) e
  >>= return % get_pointer % snd

let store f ty e1 e2 =
  let e = match e2 with
    | Specified e -> f e
    | Unspecified ty -> M.unspecified_mval ty
  in M.store ty e1 e

let store_integer ity =
  store (M.integer_value_mval ity) (C.Basic0 (T.Integer ity))

let store_pointer q cty =
  store (M.pointer_mval cty) (C.Pointer0 (q, cty))

(* TODO: it only support array of int *)

(*
let store_array cty size =
  let mk_array = match cty with
    | C.Void0 -> raise (Error "store array: not expecting void type")
    | C.Basic0 (T.Integer ity) -> List.map (M.integer_value_mval ity)
    | C.Basic0 (T.Floating fty) -> List.map (M.floating_value_mval fty)
                                    (*
    | C.Array0 of C.ctype0 * Nat_big_num.num option
    | C.Function0 of C.ctype0 * (AilTypes.qualifiers * C.ctype0) list * bool
    | C.Pointer0 of AilTypes.qualifiers * C.ctype0
    | C.Atomic0 of C.ctype0
    | C.Struct0 of C.struct_tag
    | C.Union0 of C.union_tag
    | C.Builtin0 of string *)
  in
  store (fun e -> M.array_mval (mk_array e)) (C.Array0 (cty, size))
*)
let store_array cty size e1 le2 =
  M.store (C.Array0 (cty, size)) e1 (
    match le2 with
    | Specified e2 ->
      begin match cty with
        | C.Basic0 (T.Integer ity) -> M.array_mval (List.map (M.integer_value_mval ity) e2)
        | _ -> raise (Error "excepting an array of integers")
      end
    | Unspecified ty -> M.unspecified_mval ty
  )

(* Printf wrap *)

let printf (conv : C.ctype0 -> M.integer_value -> M.integer_value)
    (xs:M.integer_value list)
    (args:(C.ctype0 * M.pointer_value) list) =
  let encode ival = match Mem_aux.integerFromIntegerValue ival with
    | Some n -> Decode_ocaml.encode_character_constant n
    | None -> Debug_ocaml.error
                "Printf: one of the element of the format array was invalid"
  in
  let eval_conv cty x =
    let throw_error _ = raise (Error "Rt_ocaml.printf: expecting an integer") in
    let n = M.case_mem_value x
        throw_error
        (fun _ v -> conv cty v)
        (fun _ -> throw_error)
        (fun _ -> throw_error)
        throw_error
        (fun _ -> throw_error)
        (fun _ -> throw_error)
    in Either.Right (Undefined.Defined0 (Core.Vspecified (Core.OVinteger n)))
  in
  Output.printf eval_conv (List.rev (List.map encode xs)) args
  >>= begin function
    | Either.Right (Undefined.Defined0 xs) ->
      let n = List.length xs in
      print_string (String.init n (List.nth xs));
      return (M.integer_ival (Nat_big_num.of_int n))
    | Either.Right (Undefined.Undef (_, xs) ) ->
      raise (Error (String.concat "," 
                      (List.map Undefined.stringFromUndefined_behaviour xs)))
    | Either.Right (Undefined.Error (_, m) ) -> raise (Error m)
    | Either.Left z -> raise (Error (Pp_errors.to_string z))
  end

(* Exit continuation *)

exception Exit of (M.integer_value loaded)



let print_exit_value n =
  let pp n = Printf.printf
      "Defined {value: \"Specified(%s)\", stdout: \"\", blocked: \"false\"}\nCONSTRS ==> []\nLog[0]\n\nEnd[0]\n" n in
  try
    ignore (Sys.getenv "CERBOUTPUT");
    pp (Nat_big_num.to_string n); n
    (*
    Nat_big_num.to_string n |> print_string; n*)
  with Not_found -> n

let quit f =
  try
    let _ = M.runMem (f (fun x -> raise (Exit x)) ()) M.initial_mem_state in
    raise (Error "continuation not raised")
  with
  | Exit x ->
    (match x with
     | Specified x -> M.eval_integer_value x
                      |> Option.get
                      |> print_exit_value
                      |> Nat_big_num.to_int
                      |> exit
     | Unspecified _ -> print_string "Unspecified"; exit(-1)
    )

let run globals main =
  begin fun cont args ->
    globals
    |> init_globals
    >> main cont args
  end |> quit
