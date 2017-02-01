(* Created by Victor Gomes 2016-02-08 *)
(* Instance of the continuation monad transformer for the memory state monad. *)

open Util

open Mem

(* A CPS computation that produces an intermediate result of type 'a whose
   final result type is 'b memM0 *)
type ('a, 'b) t = ContT of (('a -> 'b memM0) -> 'b memM0)

let contT c = ContT c

let runContT (ContT c) k = c k

let mapContT f (ContT c) = ContT (f % c)

let withContT f (ContT c) = ContT (c % f)

let return x = contT $ fun k -> k x

let bind (ContT c) f = contT $ fun k -> c (fun x -> runContT (f x) k)

let (>>=) = bind

let callCC f =
  contT $ fun k ->
    let ret x = contT $ fun _ -> k x in
    runContT (f ret) k

(* It runs the continuation monad with calcc and the state memory one *)
let run f =
  apply f
  |> callCC
  |> (flip runContT) return3
  |> (flip runMem0) initial_mem_state0

let evalContT m = runContT m return3

let lift m = ContT (bind3 m)
