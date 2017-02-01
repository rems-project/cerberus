(* Created by Victor Gomes 2016-02-02 *)

open Util
open Continuation

module M = Mem
module I = Mem.Impl
module T = AilTypes
module C = Core_ctype
module O = Util.Option

exception Undefined of string
exception Error of string
exception No_value

let cons x l = x :: l

(* IV min/max wraps *)

let ivctor memf errmsg = function
  | C.Basic0 (T.Integer it) -> memf it
  | _ -> raise (Error errmsg)

let ivmin = ivctor M.min_ival0 "ivmin"

let ivmax = ivctor M.max_ival0 "ivmax"

(* Loaded - Specified and unspecified values *)

type 'a loaded =
  | Specified of 'a
  | Unspecified of C.ctype0

let specified x = Specified x

(* Cast from memory values *)

let mv_to_integer_loaded mv =
  match mv with
  | I.MVinteger (at, iv) ->
    if M.is_specified_ival0 iv then
      Specified iv
    else
      Unspecified (C.Basic0 (T.Integer at))
  | _ -> raise (Error "type mismatch")

let mv_to_pointer mv =
  match mv with
  | I.MVpointer (cy, pt) -> pt
  | _ -> raise (Error "type mismatch")


(* Cast to memory values *)

let mv_from_integer at iv =
  match iv with
    | I.IV (_, _) -> I.MVinteger (at, iv)


let mk_int s = I.IV (I.Prov_none, I.IVconcrete (Nat_big_num.of_string s))

(* Binary operations wrap *)

let eq n m = O.get (M.eq_ival0 M.initial_mem_state0 Symbolic.Constraints_TODO n m)
let lt n m = O.get (M.lt_ival0 Symbolic.Constraints_TODO n m)
let gt n m = O.get (M.lt_ival0 Symbolic.Constraints_TODO m n)
let le n m = O.get (M.le_ival0 Symbolic.Constraints_TODO n m)
let ge n m = O.get (M.le_ival0 Symbolic.Constraints_TODO m n)

(* Memory actions wrap *)

let create pre al ty = lift $ M.allocate_static0 0 pre al ty

let alloc pre al n = lift $ M.allocate_dynamic0 0 pre al n

let load_integer ity e = lift $ M.bind3 (M.load0 (C.Basic0 (T.Integer ity)) e)
                           (M.return3 % mv_to_integer_loaded % snd)

let load_pointer q cty e = lift $ M.bind3 (M.load0 (C.Pointer0 (q, cty)) e) (M.return3 % specified % mv_to_pointer % snd)

let store ty e1 e2 = lift $ M.store0 ty e1 e2

let store_integer ity e1 le2 =
  lift $ M.store0 (C.Basic0 (T.Integer ity)) e1 (
    match le2 with
    | Specified e2 -> M.integer_value_mval0 ity e2
    | Unspecified ty -> M.unspecified_mval0 ty
  )

let store_pointer q cty e1 le2 =
  lift $ M.store0 (C.Pointer0 (q, cty)) e1 (
    match le2 with
    | Specified e2 -> M.pointer_mval0 cty e2
    | Unspecified ty -> M.unspecified_mval0 ty
  )


(* Cast types functions *)

let pointer_from_integer_value = function
  | I.IV (p, ivb) -> I.PV (p, I.PVfromint ivb, [])

(* Get values from memeory monad result *)

let get_first_value mv =
  match mv with
    | [Either.Left _] -> raise (Error "Returning error...")
    | [Either.Right (res, _)] -> res
    | _ -> raise (Error "Too many results...")

(* Exit continuation *)

let value = return

let exit f =
  match get_first_value (run f) with
  | Specified iv -> M.eval_integer_value0 iv |> O.get |> Nat_big_num.to_int |>
                    (fun res -> print_int res; exit res)
  | Unspecified _ -> print_string "Unspecified value"
