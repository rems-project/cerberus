module A = CpArray.Growable
module M = BatMap
module U = CpUnionFind.Growable

type constant = int
type apply = constant * constant
type term =
  | Constant of constant
  | Apply of apply

type t = {
  delta : U.t;
  use : (apply * constant) list A.t;
  congr : (constant * constant, constant) M.t;
  pending : (constant * constant) list;
  size : int
}

let create size = {
  delta = U.create size;
  use = A.create size [];
  congr = M.empty;
  pending = [];
  size = size
}

let find cc c = U.find cc.delta c
let union cc c1 c2 =
  let delta, hint = U.union_hint cc.delta c1 c2 in
  {cc with delta = delta}, hint
let find_congr cc r1 r2 = M.find (r1, r2) cc.congr
let add_pending cc eq = {cc with pending = eq :: cc.pending}

let propagate cc =
  let rec fold f cc =
    match cc.pending with
    | [] -> cc
    | eq :: rest -> fold f (f {cc with pending = rest} eq) in
  let process cc (c1, c2) =
    let cc, hint = union cc c1 c2 in
    match hint with
    | U.Equal -> cc
    | U.Less (r1, r2) ->
        List.fold_left 
          (fun cc ((c1, c2) as f, c) ->
            let c1' = find cc c1 in
            let c2' = find cc c2 in
            try
              add_pending cc (c, find_congr cc c1' c2')
            with Not_found ->
              {cc with
                use = A.update cc.use r2 (BatList.cons (f, c));
                congr = M.add (c1', c2') c cc.congr
              }
          )
          {cc with use = A.set cc.use r1 []}
          (A.get cc.use r1) in
  fold process cc

let merge cc t c =
  match t with
  | Constant c' -> propagate (add_pending cc (c', c))
  | Apply ((c1, c2) as f) ->
      let r1 = find cc c1 in
      let r2 = find cc c2 in
      try
        propagate (add_pending cc (c, find_congr cc r1 r2))
      with Not_found ->
        let add r a = A.update a r (BatList.cons (f, c)) in
        {cc with
          use = add r2 (add r1 cc.use);
          congr = M.add (r1, r2) c cc.congr
        }

let merge_constants cc c c' = propagate (add_pending cc (c', c))

let rec normalise cc t =
  match t with
  | Constant c -> Constant (find cc c)
  | Apply (c1, c2) ->
      let u1 = normalise cc (Constant c1) in
      let u2 = normalise cc (Constant c2) in
      match u1, u2 with
      | Constant r1, Constant r2 ->
          begin
            try
              Constant (find cc (find_congr cc r1 r2))
            with Not_found ->
              Apply (r1, r2)
          end
      | _ -> assert (false)

let normalise_constant cc c = find cc c

let congruent cc t1 t2 = (normalise cc t1) = (normalise cc t2)

let congruent_constants cc c1 c2 =
  (normalise_constant cc c1) = (normalise_constant cc c2)

let grow cc n = {cc with
  delta = U.grow cc.delta n;
  use = A.grow cc.use n (fun _ -> []);
  size = cc.size + n
}
let size cc = cc.size 
