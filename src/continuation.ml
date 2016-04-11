(* Created by Victor Gomes 2016-02-08 *)
(* Instance of the continuation monad transformer for the memory state monad. *)

open Util

open Mem

type ('a, 'b) t = ContT of (('a -> 'b memM0) -> 'b memM0)

let contT c = ContT c

let runContT (ContT c) k = c k

let return x = contT $ fun k -> k x

let bind (ContT c) f = contT $ fun k -> c (fun x -> runContT (f x) k)

let (>>=) = bind

let callCC f = contT $ fun k -> let ret x = contT $ fun _ -> k x in
                                  runContT (f ret) k

(* It runs the continuation monad with calcc and the state memory one *)
let run f = runMem0 (runContT (callCC (fun ret -> f ret)) return1) initial_mem_state0

let evalContT m = runContT m return1

let lift m = ContT (bind1 m)
(*
let reset = lift % evalContT

let shift f = ContT (evalContT % f)
*)
