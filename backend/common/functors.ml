(* functors.ml *)
(* (C) J Pichon 2019 *)

module type Thing = sig
  type t
end

module type Showable = sig
  type t
  val string_of : t -> string
end

let option_map f xs =
  let rec g l = function
  | [] -> List.rev l
  | x :: xs ->
    let l' = (match f x with None -> l | Some y -> y :: l) in
    g l' xs in
  g [] xs

module Ord_pair (X : Set.OrderedType) (Y : Set.OrderedType) : Set.OrderedType with type t = X.t * Y.t = struct
  type t = X.t * Y.t
  let compare ((x1, x2) : t) (y1, y2) =
    match X.compare x1 y1 with
    | 0 -> Y.compare x2 y2
    | v -> v
end

let pair_compare f1 f2 (a1, b1) (a2, b2) =
  match f1 a1 a2 with
  | 0 -> f2 b1 b2
  | v -> v

module Ord_triple (X : Set.OrderedType) (Y : Set.OrderedType) (Z : Set.OrderedType) : Set.OrderedType with type t = X.t * Y.t * Z.t = struct
  type t = X.t * Y.t * Z.t
  let compare ((x1, x2, x3) : t) (y1, y2, y3) =
    match X.compare x1 y1 with
    | 0 ->
      (match Y.compare x2 y2 with
      | 0 -> Z.compare x3 y3
      | v -> v)
    | v -> v
end

let rec list_compare f xs ys =
  match (xs, ys) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs', y :: ys' ->
    (match f x y with
    | 0 -> list_compare f xs' ys'
    | v -> v)

module Ord_list (X : Set.OrderedType) : Set.OrderedType with type t = X.t list = struct
  type t = X.t list
  let rec compare (xs : t) (ys) =
    list_compare X.compare xs ys
end


module Real_map (X : Set.S) (Y : Set.S) = struct
  let map (f : X.elt -> Y.elt) (s : X.t) =
    X.fold (fun x s' -> Y.add (f x) s') s Y.empty
end

module Set_union (X : Set.S) = struct
  let union (xs : X.t list) =
    List.fold_left X.union X.empty xs
end

module Powerset_bind (X : Set.S) (Y : Set.S) : sig val bind : (X.elt -> Y.t) -> X.t -> Y.t end = struct
  module U = Set_union(Y)

  let bind (f : X.elt -> Y.t) (s : X.t) =
    U.union (List.map f (X.elements s))
end

module Option_set_bind (X : Set.S) (Y : Set.S) = struct

  let bind (f : X.elt -> Y.elt option) (s : X.t) =
    Y.of_list (option_map f (X.elements s))
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

module Collect_in_map (X : Map.S) (Y : Set.S) = struct
  let collect index_of set =
    Y.fold
      (fun a m ->
        let ix = index_of a in
        match X.find_opt ix m with
        | None -> X.add ix (Y.singleton a) m
        | Some s -> X.add ix (Y.add a s) m)
      set
      X.empty
end

module Collect_in_map_fun (X : Map.S) (Y : Set.S) (Z : Set.S) = struct
  let set_map_of f s =
    Y.fold
      (fun x map ->
        let (k, v) = f x in
        match X.find_opt k map with
        | None -> X.add k (Z.singleton v) map
        | Some acts -> X.add k (Z.add v acts) map)
      s
      X.empty
end

module Transitive_reduction (X : Set.OrderedType) (S : Set.S with type elt := X.t * X.t) = struct
let transitive_reduction s =
  S.filter
    (fun (n, n'') ->
      not (S.exists (fun (n1, n2) ->
        X.compare n n1 = 0 &&
        S.exists (fun (n3, n4) -> X.compare n2 n3 = 0 && X.compare n4 n'' = 0) s) s))
    s

let transitive_reduction_over_right s link =
  S.filter
    (fun (s_src, s_tgt) ->
      not (S.exists (fun (s'_src, s'_tgt) ->
        X.compare s_src s'_src = 0 &&
        S.exists (fun (l_src, l_tgt) -> X.compare s'_tgt l_src = 0 && X.compare l_tgt s_tgt = 0) link) s))
    s

let transitive_reduction_over_left s link =
  S.filter
    (fun (s_src, s_tgt) ->
      not (S.exists (fun (s'_src, s'_tgt) ->
        X.compare s_tgt s'_tgt = 0 &&
        S.exists (fun (l_src, l_tgt) -> X.compare s'_src l_tgt = 0 && X.compare l_src s_src = 0) link) s))
    s

let transitive_reduction_over s link =
  transitive_reduction_over_left (transitive_reduction_over_right s link) link
end