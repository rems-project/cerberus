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

module List =
  struct
    include List

    (** [filter_map f l] applies function [f] to the elements of [l], and then
        filters out then [None]. *)
    let rec filter_map : ('a -> 'b option) -> 'a list -> 'b list = fun f l ->
      match l with
      | []     -> []
      | h :: t ->
          match f h with
          | Some(x) -> x :: filter_map f t
          | None    -> filter_map f t

    let find_index : ('a -> bool) -> 'a list -> int = fun p l ->
      let rec find i l =
        match l with
        | []     -> raise Not_found
        | x :: l -> if p x then i else find (i+1) l
      in
      find 0 l
  end

module Buffer =
  struct
    include Buffer

    let add_full_channel : t -> in_channel -> unit = fun buf ic ->
      try
        while true do
          add_char buf (input_char ic)
        done
      with End_of_file -> ()

    let add_file : t -> string -> unit = fun buf fname ->
      let ic = open_in fname in
      add_full_channel buf ic;
      close_in ic

    let from_file : string -> t = fun fname ->
      let buf = create 4096 in
      add_file buf fname; buf

    let to_file : string -> t -> unit = fun fname buf ->
      let oc = open_out fname in
      output_buffer oc buf;
      close_out oc
  end

module String =
  struct
    include String

    let for_all : (char -> bool) -> string -> bool = fun p s ->
      try iter (fun c -> if not (p c) then raise Exit) s; true
      with Exit -> false
  end

(** [outut_lines oc ls] prints the lines [ls] to the output channel [oc] while
    inserting newlines according to [String.split_on_char]. *)
let output_lines : out_channel -> string list -> unit = fun oc ls ->
  match ls with
  | []      -> ()
  | l :: ls -> output_string oc l; List.iter (Printf.fprintf oc "\n%s") ls
