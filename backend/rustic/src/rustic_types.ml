open Cerb_frontend

(* TODO: move some of that out, and share with BMC *)
module Ord_pair (X : Set.OrderedType) (Y : Set.OrderedType) : Set.OrderedType with type t = X.t * Y.t = struct
    type t = X.t * Y.t
    let compare ((x1, x2) : t) (y1, y2) =
        match X.compare x1 y1 with
        | 0 -> Y.compare x2 y2
        | v -> v
end

module Map_of_list (X : Map.S) = struct
  let of_list (l : 'a) =
    List.fold_left
      (fun mo (x, v) ->
        match mo with
        | None -> None
        | Some m ->
          (match X.find_opt x m with
          | None -> Some (X.add x v m)
          | Some _ -> None))
      (Some X.empty)
      l
end

let rec map_option_aux f acc = function
  | [] -> List.rev acc
  | x :: xs ->
    (match f x with
     | None -> map_option_aux f acc xs
     | Some y -> map_option_aux f (y :: acc) xs)

let map_option f xs = map_option_aux f [] xs

module Option_map (X : Map.S) = struct
  module Z = Map_of_list(X)

  let map (f : X.key -> 'a -> 'b option) (s : 'a X.t) =
    let m = Z.of_list (map_option (fun (k, v) -> match f k v with None -> None | Some v' -> Some (k, v')) (X.bindings s)) in
    match m with
    | None -> (* it came from a map, and entries can only be deleted, so it is still functional *) assert false
    | Some m' -> m'
end

module String_map = Map.Make(String)
module String_map_aux = Map_of_list(String_map)
module String_option_map = Option_map(String_map)

(*
type rc_ownership =
| RC_read
| RC_write
| RC_zap
| RC_bad

let string_of_rc_ownership = function
| RC_read -> "read"
| RC_write -> "write"
| RC_zap -> "zap"
| RC_bad -> "BAD"
*)

type rc_scoping =
| RCS_scoped of string
| RCS_unscoped

type rc_type =
| RC_placeholder of string
| RC_uninit
| RC_scalar
| RC_ptr of rc_type * rc_scoping
| RC_struct of Symbol.sym (* * rc_ownership
| RC_atomic of rc_type*)

module RC_type = struct
  type t = rc_type
  let compare (x : t) y = Stdlib.compare x y (* yuck *)
end

module RC_type_pair = Ord_pair(RC_type)(RC_type)

type rc_change =
| RC_unchanged
| RC_changed of rc_type

(* TODO: this is super brittle, but I don't know how else to do it *)
let string_of_sym (Symbol.Symbol (_, _, id_opt)) =
  match id_opt with Symbol.SD_Id id -> id | _ -> assert false (* FIXME? *)

let string_of_scoping = function
| RCS_scoped s -> s
| RCS_unscoped -> "all"

let rec string_of_rc_type = function
| RC_placeholder s -> "?" ^ s
| RC_scalar -> "scalar"
| RC_uninit -> "uninit"
| RC_ptr (t, s) -> "ptr@" ^ string_of_scoping s ^ "[" ^ string_of_rc_type t ^ "]"
| RC_struct s -> failwith "TODO: struct"
(*| RC_ptr (o, t) -> "ptr[" ^ string_of_rc_ownership o ^ "](" ^ string_of_rc_type t ^ ")"*)
(*| RC_struct (id, o) -> "struct " ^ string_of_sym id ^ "[" ^ string_of_rc_ownership o ^ "]"
| RC_atomic t -> "atomic " ^ string_of_rc_type t*)

type ('b) gamma_ty = (rc_type String_map.t) list
