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

let mv_to_integer mv =
  match mv with
    | I.MVinteger (at, iv) -> iv
    | _ -> raise (Error "type mismatch")

let mv_to_pointer mv =
  match mv with
    | I.MVpointer (cy, pt) -> pt
    | _ -> raise (Error "type mismatch")


(* Cast to memory values *)

let mv_from_integer at iv =
  match iv with
    | I.IV (_, _) -> I.MVinteger (at, iv)

(* Memory actions wrap *)

let create pre al ty = lift $ M.allocate_static0 0 pre al ty

let alloc pre al n = lift $ M.allocate_dynamic0 0 pre al n

let load_integer ty e = lift $ M.bind1 (M.load0 ty e) (M.return1 % specified % mv_to_integer % snd)

let load_pointer ty e = lift $ M.bind1 (M.load0 ty e) (M.return1 % specified % mv_to_pointer % snd)

let store ty e1 e2 = lift $ M.store0 ty e1 e2

(* Cast types functions *)

let int_of_integer_value (Specified iv) = M.eval_integer_value0 iv |> O.get |> Nat_big_num.to_int

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

let exit f = let res = run f |> get_first_value |> int_of_integer_value
             in print_int res; exit res
