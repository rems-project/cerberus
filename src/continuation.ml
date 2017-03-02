(* Created by Victor Gomes 2016-02-08 *)
(* Instance of the continuation monad transformer for the memory state monad. *)

open Util

open Mem

(* A CPS computation that produces an intermediate result of type 'a whose
   final result type is 'b memM0 *)
type ('a, 'b) t = ContT of (('a -> 'b memM) -> 'b memM)

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
let run_callcc f =
  apply f
  |> callCC
  |> (flip runContT) return2
  |> (flip runMem) initial_mem_state

let run f =
  runContT f return2
  |> (flip runMem) initial_mem_state

let evalContT m = runContT m return2

let lift m = ContT (bind2 m)

let reset e = ContT (fun k -> bind2 (runContT e return2) k)

let shift e =
  ContT (fun k -> runContT (e (fun v -> ContT (fun c -> bind2 (k v) c))) return2)
(*
let try_catch a h = (reset (let x = a in (fun _ -> x))) h
let throw e = shift (fun _ -> (fun h -> h e))
*)
