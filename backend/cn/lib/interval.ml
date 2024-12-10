let both f a b = match (a, b) with Some x, Some y -> Some (f x y) | _ -> None

let either f a b =
  match (a, b) with None, _ -> b | _, None -> a | Some x, Some y -> Some (f x y)


(* Single continuous interval *)
module Interval = struct
  (* Closed below (unless no lower bound), open above *)
  type t =
    { lower : Z.t option;
      upper : Z.t option
    }
  [@@deriving eq, ord]

  let empty = { lower = Some Z.zero; upper = Some Z.zero }

  let is_empty i =
    match (i.lower, i.upper) with Some x, Some y -> Z.geq x y | _ -> false


  let is_const i =
    match (i.lower, i.upper) with
    | Some x, Some y when Z.equal (Z.succ x) y -> Some x
    | _ -> None


  let to_string i =
    if is_empty i then
      "[]"
    else (
      match is_const i with
      | Some i -> "[" ^ Z.to_string i ^ "]"
      | None ->
        let left = match i.lower with None -> "(-inf" | Some i -> "[" ^ Z.to_string i in
        let right = match i.upper with None -> "inf" | Some i -> Z.to_string i in
        left ^ "," ^ right ^ ")")


  (* Is the first interval completely below the second one *)
  let is_known_below i j = Option.value (both Z.leq i.upper j.lower) ~default:false

  let combine i j =
    if is_empty i || is_empty j then
      (empty, empty, empty)
    else if is_known_below i j then
      (i, empty, j)
    else if is_known_below j i then
      (j, empty, i)
    else (
      let il = either Z.max i.lower j.lower in
      (* lower bound of intersection *)
      let left =
        match il with
        | None -> empty
        | Some u -> { lower = both Z.min i.lower j.lower; upper = Some u }
      in
      let iu = either Z.min i.upper j.upper in
      (* upper bound of intersection *)
      let right =
        match iu with
        | None -> empty
        | Some l -> { lower = Some l; upper = both Z.max i.upper j.upper }
      in
      (left, { lower = il; upper = iu }, right))


  let const k = { lower = Some k; upper = Some (Z.succ k) }

  let int = { lower = None; upper = None }

  let nat = { lower = Some Z.zero; upper = None }

  let uint n = { lower = Some Z.zero; upper = Some (Z.shift_left Z.one n) }

  let sint n =
    let u = Z.shift_left Z.one (n - 1) in
    { lower = Some (Z.neg u); upper = Some u }


  let lt i = { lower = None; upper = Some i }

  let gt i = { lower = Some (Z.succ i); upper = None }

  let leq i = { lower = None; upper = Some (Z.succ i) }

  let geq i = { lower = Some i; upper = None }

  let range i j = { lower = Some i; upper = Some j }

  let minimum i : Z.t option = i.lower

  let maximum i : Z.t option = Option.map (fun n -> Z.sub n Z.one) i.upper
end

module Intervals = struct
  (* Separated, sorted from smallest integers to largest. *)
  type t = Interval.t list [@@deriving eq, ord]

  let to_intervals t = t

  let of_interval i = [ i ]

  let rec to_string is =
    match is with
    | [] -> "[]"
    | [ i ] -> Interval.to_string i
    | i :: more -> Interval.to_string i ^ " || " ^ to_string more


  let rec intersect is js =
    match (is, js) with
    | [], _ -> []
    | _, [] -> []
    | i :: is1, j :: js1 ->
      let _below, common, above = Interval.combine i j in
      let is2, js2 =
        if Interval.is_empty above then
          (is1, js1)
        else if Interval.is_known_below i above then
          (is1, above :: js1)
        else
          (above :: is, js1)
      in
      if Interval.is_empty common then
        intersect is2 js2
      else
        common :: intersect is2 js2


  let rec union is js =
    match (is, js) with
    | [], _ -> js
    | _, [] -> is
    | i :: is1, j :: js1 ->
      let below, common, above = Interval.combine i j in
      let is2, js2 =
        if Interval.is_empty above then
          (is1, js1)
        else if Interval.is_known_below i above then
          (is1, above :: js1)
        else
          (above :: is1, js1)
      in
      let cons x xs =
        if Interval.is_empty x then
          xs
        else (
          match xs with
          | [] -> [ x ]
          | y :: ys ->
            (match (x.upper, y.lower) with
             | Some u, Some l when Z.equal u l ->
               { lower = x.lower; upper = y.upper } :: ys
             | _ -> x :: xs))
      in
      cons below (cons common (union is2 js2))


  let complement (is : t) : t =
    let rec loop (from : Z.t option) (next : t) : t =
      match next with
      | [] -> [ { lower = from; upper = None } ]
      | i :: is ->
        let rest = match i.upper with None -> [] | u -> loop u is in
        (match i.lower with None -> rest | l -> { lower = from; upper = l } :: rest)
    in
    loop None is


  let is_const (is : t) : Z.t option =
    match is with [ i ] -> Interval.is_const i | _ -> None


  let is_empty (is : t) : bool = List.is_empty is

  let minimum (is : t) : Z.t option =
    match is with i :: _ -> Interval.minimum i | [] -> None


  let rec maximum (is : t) : Z.t option =
    match is with [ i ] -> Interval.maximum i | _ :: is' -> maximum is' | [] -> None
end

module Solver = struct
  module IT = IndexTerms
  module RT = ResourceTypes
  open Terms
  open BaseTypes

  let interval_for (eval : IT.t -> IT.t option) q tyi =
    let is_q i = match IT.term i with Sym y -> Sym.equal q y | _ -> false in
    let eval_k e =
      if Sym.Set.mem q (IT.free_vars e) then
        None
      else
        Option.bind (eval e) (fun v ->
          match IT.term v with
          | Const (Z z) -> Some z
          | Const (Bits (_, z)) -> Some z
          | _ -> None)
    in
    let mkI i = Intervals.intersect tyi i in
    let var_k f x y =
      let mk b v = mkI (Intervals.of_interval (f b v)) in
      match () with
      | _ when is_q x -> Option.map (mk false) (eval_k y)
      | _ when is_q y -> Option.map (mk true) (eval_k x)
      | _ -> None
    in
    let do_eq = var_k (fun _ -> Interval.const) in
    let do_lt = var_k (fun swap -> if swap then Interval.gt else Interval.lt) in
    let do_le = var_k (fun swap -> if swap then Interval.geq else Interval.leq) in
    let do_compl i = mkI (Intervals.complement i) in
    let do_impl i j = Intervals.union (do_compl i) j in
    let rec interval p =
      match IT.term p with
      | Const (Bool true) -> Some tyi
      | Const (Bool false) -> Some (Intervals.of_interval Interval.empty)
      | Unop (Not, term) -> Option.map do_compl (interval term)
      | Binop (And, lhs, rhs) -> both Intervals.intersect (interval lhs) (interval rhs)
      | Binop (Or, lhs, rhs) -> both Intervals.union (interval lhs) (interval rhs)
      | Binop (Implies, lhs, rhs) ->
        (match eval lhs with
         | None -> both do_impl (interval lhs) (interval rhs)
         | Some (IT (Const (Bool b), _, _)) -> if b then interval rhs else Some tyi
         | _ -> None)
      | Binop (EQ, lhs, rhs) -> do_eq lhs rhs
      | Binop (LT, lhs, rhs) -> do_lt lhs rhs
      | Binop (LE, lhs, rhs) -> do_le lhs rhs
      | _ -> None
    in
    interval


  let supported_type loc ty : (Interval.t * (Z.t -> IT.t)) option =
    let yes i k = Some (i, fun v -> IT (Const (k v), ty, loc)) in
    match ty with
    | Integer -> yes Interval.int (fun v -> Z v)
    | Bits (sign, w) ->
      (match sign with
       | Signed -> yes (Interval.sint w) (fun v -> Bits ((sign, w), v))
       | Unsigned -> yes (Interval.uint w) (fun v -> Bits ((sign, w), v)))
    | _ -> None


  let simp_rt eval (rt : RT.t) : RT.t =
    match rt with
    | RT.P _ -> rt
    | RT.Q qpred ->
      let x, t = qpred.q in
      let loc = IT.loc qpred.permission in
      (match supported_type loc t with
       | None -> rt
       | Some (tyi, k) ->
         let xt = IT.sym_ (x, t, loc) in
         let interval_to_term i =
           match Interval.is_const i with
           | Some v -> IT.eq_ (xt, k v) loc
           | None ->
             let has_lower =
               Option.bind i.lower (fun l ->
                 match tyi.lower with
                 | Some tl when Z.equal l tl -> None
                 | _ -> Some (IT.le_ (k l, xt) loc))
             in
             let has_upper =
               Option.bind i.upper (fun u ->
                 match tyi.upper with
                 | Some tu when Z.equal u tu -> None
                 | _ -> Some (IT.lt_ (xt, k u) loc))
             in
             (match (has_lower, has_upper) with
              | Some l, Some u -> IT.and2_ (l, u) loc
              | None, Some u -> u
              | Some l, None -> l
              | None, None -> IT.bool_ true loc)
         in
         (match interval_for eval x (Intervals.of_interval tyi) qpred.permission with
          | None -> rt
          | Some is ->
            let ps = List.map interval_to_term (Intervals.to_intervals is) in
            RT.Q { qpred with permission = IT.or_ ps loc }))
end
