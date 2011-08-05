module A = CpArray.Growable

module type UNION_FIND = sig
  type t = {rank : int A.t; mutable parents : int A.t}

  type hint = Less of int * int | Equal

  val create : int -> t
  val find : t -> int -> int
  val union : t -> int -> int -> t
  val union_hint : t -> int -> int -> t * hint
end

module UnionFind = struct
  type hint = Less of int * int | Equal
  type t = {rank : int A.t; mutable parents : int A.t}

  let create size = {
    rank = A.create size 0;
    parents = A.init size (fun i -> i)
  }

  let find t e =
    let rec find_helper ps x cont =
      let p = A.get ps x in
      if p = x then cont (ps, x)
      else find_helper ps p (fun (ps', r) -> cont (A.set ps' x r, r)) in
    let ps, r = find_helper t.parents e (fun x -> x) in
    t.parents <- ps; r

  let union t x y =
    let dx = find t x in
    let dy = find t y in
    if dx <> dy then begin
      let rx = A.get t.parents dx in
      let ry = A.get t.parents dy in
      if rx < ry then
        {t with parents = A.set t.parents dx dy}
      else if rx > ry then
        {t with parents = A.set t.parents dy dx}
      else {
        rank    = A.set t.rank dx (rx + 1);
        parents = A.set t.parents dy dx
      }
    end else t

  let union_hint t x y =
    let dx = find t x in
    let dy = find t y in
    if dx <> dy then begin
      let rx = A.get t.parents dx in
      let ry = A.get t.parents dy in
      if rx < ry then
        {t with parents = A.set t.parents dx dy}, Less (rx, ry)
      else if rx > ry then
        {t with parents = A.set t.parents dy dx}, Less (ry, rx)
      else {
        rank    = A.set t.rank dx (rx + 1);
        parents = A.set t.parents dy dx
      }, Equal
    end else t, Equal
end

module MakeGrowable = functor (UF : UNION_FIND) ->
struct
  type hint = Less of int * int | Equal
  type t = UF.t * int

  let to_hint = function
    | UF.Equal -> Equal
    | UF.Less (r1, r2) -> Less (r1, r2)

  let create size = UF.create size, size
  let find (t, s) e = UF.find t e
  let union (t, s) x y = UF.union t x y, s
  let union_hint (t, s) x y =
    let t', o = UF.union_hint t x y in
    (t', s), to_hint o
  let grow ({UF.rank; parents}, s) n = {
    UF.rank = A.grow rank    n (fun _ -> 0);
    parents = A.grow parents n (fun i -> s + i)}, s + n
end

module Growable = MakeGrowable(UnionFind)

include UnionFind
