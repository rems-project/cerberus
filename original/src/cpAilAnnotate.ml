module A = CpAil
module AT = CpAilTypes

class annotate_position (p : Position.t) = object
  method position = p
end

class annotate_type p (t : A.type_class) = object
  inherit annotate_position p
  method type_class = t
end

let a_pos p = new annotate_position p
let a_type p t = new annotate_type p t

let pos_of  (a, _) = a#position
let type_of (a, _) = a#type_class
let exp_of  (_, e) = e

let exp_type_of e =
  let t = match type_of e with
    | A.Exp    t -> t
    | A.Lvalue t -> AT.lvalue_convert t in
  AT.pointer_convert t

let lvalue_type_of e =
  match type_of e with
  | A.Lvalue t -> AT.pointer_convert t
  | A.Exp    _ -> invalid_arg "Not an lvalue."

let ctype_of e =
  match type_of e with
  | A.Exp    t -> t
  | A.Lvalue t -> t
