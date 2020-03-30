(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Short name for the type of a comparison function. *)
type 'a cmp = 'a -> 'a -> int

module Int =
  struct
    type t = int
    let compare = (-)
  end

module Option =
  struct
    type 'a t = 'a option

    let map : ('a -> 'b) -> 'a t -> 'b t = fun f o ->
      match o with
      | None    -> None
      | Some(e) -> Some(f e)

    let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b = fun f d o ->
      match o with
      | None    -> d
      | Some(e) -> f e

    let iter : ('a -> unit) -> 'a t -> unit = fun f o ->
      match o with
      | None    -> ()
      | Some(e) -> f e

    let get : 'a -> 'a option -> 'a = fun d o ->
      match o with
      | None    -> d
      | Some(e) -> e

    let equal : 'a eq -> 'a option eq = fun eq o1 o2 ->
      match (o1, o2) with
      | (None    , None    ) -> true
      | (Some(e1), Some(e2)) -> eq e1 e2
      | (_       , _       ) -> false

    let pp : 'a pp -> 'a option pp = fun pp_elt oc o ->
      match o with
      | None   -> ()
      | Some e -> pp_elt oc e
  end

module Filename =
  struct
    include Filename

    (** [realpath path] returns the absolute canonical path to file [path]. If
        [path] is invalid (i.e., it does not describe an existing file),  then
        the exception [Invalid_argument] is raised. *)
    external realpath : string -> string = "c_realpath"
  end

module SMap = Map.Make(String)
module IMap = Map.Make(Int)
