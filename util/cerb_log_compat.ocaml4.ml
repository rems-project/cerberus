(* Follow Stdlib.Mutex.protect (introduced in OCaml 5.1). Keep the handler
   immediately after acquisition, without allocating a finally closure while
   holding the lock. Inlining could let Flambda move allocations into that gap.
   OCaml 4.14's Mutex.unlock does not poll for asynchronous exceptions. *)
external reraise : exn -> 'a = "%reraise"

let[@inline never] protect mutex f =
  Mutex.lock mutex;
  match f () with
  | result -> Mutex.unlock mutex; result
  | exception exn -> Mutex.unlock mutex; reraise exn

(* String.hash is available only since OCaml 5. Hashtbl.hash gives the same
   result, without needing another runtime primitive in the backport. *)
module String_key = struct
  type t = string
  let equal = String.equal
  let hash = Hashtbl.hash
end
