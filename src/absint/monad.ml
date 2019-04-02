module type MONAD = sig
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
  val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  val (>>): 'a t -> 'b t -> 'b t
end

module type STATE_MONAD = sig
  type state
  include MONAD
  val run: 'a t -> state -> 'a * state
  val mapM: ('a -> 'b t) -> 'a list -> ('b list) t
  val get: state t
  val put: state -> unit t
  val update: (state -> state) -> unit t
  val modify: (state -> 'a * state) -> 'a t
  val whenM: bool t -> (unit -> unit t) -> unit t
  val ifM: bool t -> (unit -> 'a t) -> (unit -> 'a t) -> 'a t
end

module Option: MONAD with type 'a t = 'a option = struct
  type 'a t = 'a option
  let return x = Some x
  let bind m f =
    match m with
    | Some x -> f x
    | None -> None
  let (>>=) = bind
  let (>>) m1 m2 = m1 >>= fun _ -> m2
end

module Make(S: sig type t end): STATE_MONAD with type state = S.t = struct
  type state = S.t
  type 'a t = state -> 'a * state
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
