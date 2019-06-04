module type MONAD = sig
  type ('a, 'b) t
  val return: 'b -> ('a, 'b) t
  val bind: ('a, 'b) t -> ('b -> ('a, 'c) t) -> ('a, 'c) t
  val (>>=): ('a, 'b) t -> ('b -> ('a, 'c) t) -> ('a, 'c) t
  val (>>): ('a, 'b) t -> ('a, 'c) t -> ('a, 'c) t
end

module type STATE_MONAD = sig
  type 'a state
  include MONAD
  val run: ('a, 'b) t -> 'a state -> 'b * 'a state
  val mapM: ('b -> ('a, 'c) t) -> 'b list -> ('a, 'c list) t
  val get: ('a, 'a state) t
  val put: 'a state -> ('a, unit) t
  val update: ('a state -> 'a state) -> ('a, unit) t
  val modify: ('a state -> 'b * 'a state) -> ('a, 'b) t
  val whenM: ('a, bool) t -> (unit -> ('a, unit) t) -> ('a, unit) t
  val ifM: ('a, bool) t -> (unit -> ('a, 'b) t) -> (unit -> ('a, 'b) t) ->
    ('a, 'b) t
end

module Option: MONAD with type ('a, 'b) t = 'b option = struct
  type ('a, 'b) t = 'b option
  let return x = Some x
  let bind m f =
    match m with
    | Some x -> f x
    | None -> None
  let (>>=) = bind
  let (>>) m1 m2 = m1 >>= fun _ -> m2
end

module Make(S: sig type 'a t end): STATE_MONAD with type 'a state = 'a S.t =
struct
  type 'a state = 'a S.t
  type ('a, 'b) t = 'a state -> 'b * 'a state
  let return x = fun s -> (x, s)
  let bind m f = fun s ->
    let (x, s') = m s in f x s'
  let (>>=) = bind
  let (>>) m n = m >>= fun _ -> n
  let run m = m
  let sequence ms =
    let m =
      List.fold_left (fun acc m ->
          m   >>= fun x ->
          acc >>= fun xs ->
          return (x::xs)
        ) (return []) ms
    in fun s ->
      let (xs, s') = m s in
      (List.rev xs, s')
  let mapM f xs = sequence (List.map f xs)
  let get = fun s -> (s, s)
  let put s = fun _ -> ((), s)
  let update f = fun s -> ((), f s)
  let modify f = fun s -> f s
  let whenM bM f = bM >>= fun b -> if b then f () else return ()
  let ifM bM f g = bM >>= fun b -> if b then f () else g ()
end
