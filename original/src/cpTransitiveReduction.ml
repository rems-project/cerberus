module S = BatSet
module M = BatMap

module R = struct
  type 'a t = ('a, 'a BatSet.t) BatMap.t

  let empty = M.empty

  let add (v1, v2) t =
    try
      let from_v1 = M.find v1 t in
      M.add v1 (S.add v2 from_v1) t
    with Not_found ->
      M.add v1 (S.singleton v2) t

  let reachable v1 v2 t = try S.mem v2 (M.find v1 t) with Not_found -> false

  let reachable_set v1 t = try M.find v1 t with Not_found -> S.empty
end

let reduce edges =
  let r = S.fold (fun e r -> R.add e r) edges R.empty in
  let f (v1, v2) =
    S.exists (fun v -> R.reachable v v2 r) (R.reachable_set v1 r) in
  S.fold (fun e c -> if f e then c else S.add e c) edges S.empty
