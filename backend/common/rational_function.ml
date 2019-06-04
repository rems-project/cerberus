(* rational_function.ml - rational functions *)
(* TODO: not as general as it ought to *)
(* (C) J Pichon 2019 *)

let option_map f xs =
  let rec g l = function
  | [] -> List.rev l
  | x :: xs ->
    let l' = (match f x with None -> l | Some y -> y :: l) in
    g l' xs in
  g [] xs

module type S = sig
  type var (* variables *)
  type t =
  | F_var of var
  | F_const of Rational_ml.t
  | F_plus of t list
  | F_minus of t * t
  | F_times of t * t
  | F_div of t * t
  val compare : t -> t -> int
  val simplify_formula : t -> t
  val derivative : var -> t -> t
end

module Make (V : Functors.Thing) = struct

type var = V.t

type t =
  | F_var of var
  | F_const of Rational_ml.t
  | F_plus of t list
  | F_minus of t * t
  | F_times of t * t
  | F_div of t * t

  let formula_compare (x : t) y = Pervasives.compare x y
  let compare (x : t) y = formula_compare x y

  let rec simplify_formula = function
| F_var x -> F_var x
| F_const (n, d) -> if n = 0 then F_const (0, 1) else F_const (n, d)
| F_plus fs ->
  let fs = List.map simplify_formula fs in
  let const_part = Rational_ml.addn (option_map (function F_const (n, d) -> Some (n, d) | _ -> None) fs) in
  let non_consts = option_map (function F_const _ -> None | f -> Some f) fs in
  (match const_part with
  | (0, _) -> (match non_consts with [] -> F_const (0, 1) | [f] -> f | _ -> F_plus non_consts)
  | _ ->
    let f = F_const const_part in
    (match non_consts with [] -> f | _ -> F_plus (non_consts @ [f])))
| F_minus (f1, f2) ->
  let f1 = simplify_formula f1 in
  let f2 = simplify_formula f2 in
  if formula_compare f1 f2 = 0 then F_const (0, 1)
  else
    (match f1, f2 with
    | _, F_const (0, _) -> f1
    | F_const r1, F_const r2 -> F_const (Rational_ml.sub r1 r2)
    | _ -> F_minus (f1, f2))
| F_times (f1, f2) ->
  let f1 = simplify_formula f1 in
  let f2 = simplify_formula f2 in
  (match f1, f2 with
  | F_const (0, _), _ -> F_const (0, 1)
  | _, F_const (0, _) -> F_const (0, 1)
  | F_const (1, _), _ -> f2
  | _, F_const (1, _) -> f1
  | _, _ -> F_times (f1, f2))
| F_div (f1, f2) ->
  let f1 = simplify_formula f1 in
  let f2 = simplify_formula f2 in
  (match f1, f2 with
  | F_const (0, _), _ -> F_const (0, 1)
  | _, F_const (1, _) -> f1
  | _, _ -> F_div (f1, f2))

let rec derivative x = function
| F_var y -> if x = y then F_const (1, 1) else F_const (0, 1)
| F_const _ -> F_const (0, 1)
| F_plus fs -> F_plus (List.map (derivative x) fs)
| F_minus (f1, f2) -> F_minus (derivative x f1, derivative x f2)
| F_times (f1, f2) -> F_plus [F_times (derivative x f1, f2); F_times (f1, derivative x f2)]
| F_div (f1, f2) -> F_div (F_minus (F_times (derivative x f1, f2), F_times (f1, derivative x f2)), F_times (f2, f2))

let f_square f = F_times (f, f)

end

module Make_showable (V : Functors.Showable) (R : S with type var = V.t) = struct

 let rec string_of_formula_aux = function
  | R.F_var x -> (V.string_of x, true)
  | R.F_const r -> (Rational_ml.string_of r, true)
  | R.F_plus fs ->
    (match fs with
    | [] -> ("0", true)
    | [f] -> string_of_formula_aux f
    | _ -> (String.concat " + " (List.map string_of_formula_protected fs), false))
  | R.F_minus (f1, f2) ->
     (string_of_formula_protected f1 ^ " - " ^ string_of_formula_protected f2 , false)
  | R.F_times (f1, f2) ->
    (string_of_formula_protected f1 ^ " * " ^ string_of_formula_protected f2 , false)
  | R.F_div (f1, f2) ->
    (string_of_formula_protected f1 ^ " / " ^ string_of_formula_protected f2 , false)
  and string_of_formula_protected f =
    let (s, str) = string_of_formula_aux f in
    if str then s else "(" ^ s ^ ")"
  let string_of f =
    let (s, _) = string_of_formula_aux f in s

end

module Make_evaluator (R : S) (M : Map.S with type key = R.var) = struct

let rec evaluate map x = function
| R.F_var x -> M.find x map
| R.F_const c -> c
| R.F_plus fs -> Rational_ml.addn (List.map (evaluate map x) fs)
| R.F_minus (f1, f2) -> Rational_ml.sub (evaluate map x f1) (evaluate map x f2)
| R.F_times (f1, f2) -> Rational_ml.mult (evaluate map x f1) (evaluate map x f2)
| R.F_div (f1, f2) -> Rational_ml.div (evaluate map x f1) (evaluate map x f2)

end