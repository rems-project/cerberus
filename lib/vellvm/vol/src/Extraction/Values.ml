open AST
open BinInt
open Compare_dec
open Coqlib
open Datatypes
open DepElim
open Floats
open FunctionalInduction
open Integers
open Peano_dec

type block = coq_Z

(** val eq_block : coq_Z -> coq_Z -> bool **)

let eq_block =
  zeq

type coq_val =
  | Vundef
  | Vint of nat * Int.int
  | Vfloat of float
  | Vptr of block * Int.int
  | Vinttoptr of Int.int

(** val val_rect :
    'a1 -> (nat -> Int.int -> 'a1) -> (float -> 'a1) -> (block -> Int.int ->
    'a1) -> (Int.int -> 'a1) -> coq_val -> 'a1 **)

let val_rect f f0 f1 f2 f3 = function
  | Vundef -> f
  | Vint (x, x0) -> f0 x x0
  | Vfloat x -> f1 x
  | Vptr (x, x0) -> f2 x x0
  | Vinttoptr x -> f3 x

(** val val_rec :
    'a1 -> (nat -> Int.int -> 'a1) -> (float -> 'a1) -> (block -> Int.int ->
    'a1) -> (Int.int -> 'a1) -> coq_val -> 'a1 **)

let val_rec f f0 f1 f2 f3 = function
  | Vundef -> f
  | Vint (x, x0) -> f0 x x0
  | Vfloat x -> f1 x
  | Vptr (x, x0) -> f2 x x0
  | Vinttoptr x -> f3 x

(** val zero : nat -> Int.int **)

let zero wz =
  Int.zero wz

(** val one : nat -> Int.int **)

let one wz =
  Int.one wz

(** val mone : nat -> Int.int **)

let mone wz =
  Int.mone wz

(** val coq_Vzero : nat -> coq_val **)

let coq_Vzero wz =
  Vint (wz, (zero wz))

(** val coq_Vone : nat -> coq_val **)

let coq_Vone wz =
  Vint (wz, (one wz))

(** val coq_Vmone : nat -> coq_val **)

let coq_Vmone wz =
  Vint (wz, (mone wz))

(** val coq_Vtrue : coq_val **)

let coq_Vtrue =
  coq_Vone O

(** val coq_Vfalse : coq_val **)

let coq_Vfalse =
  coq_Vzero O

module Val = 
 struct 
  (** val eq : coq_val -> coq_val -> bool **)
  
  let eq v1 v2 =
    match v1 with
      | Vundef -> false
      | Vint (wz1, i1) ->
          (match v2 with
             | Vint (wz2, i2) ->
                 proj_sumbool
                   (zeq (Int.unsigned wz1 i1) (Int.unsigned wz2 i2))
             | Vfloat f2 ->
                 proj_sumbool
                   (zeq (Int.unsigned wz1 i1)
                     (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))
                       (Float.intuoffloat f2)))
             | _ -> false)
      | Vfloat f1 ->
          (match v2 with
             | Vint (wz2, i2) ->
                 proj_sumbool
                   (zeq
                     (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O)))))))))))))))))))))))))))))))
                       (Float.intuoffloat f1)) (Int.unsigned wz2 i2))
             | Vfloat f2 -> if Float.eq_dec f1 f2 then true else false
             | _ -> false)
      | Vptr (b1, o1) ->
          (match v2 with
             | Vptr (b2, o2) ->
                 if proj_sumbool (eq_block b1 b2)
                 then proj_sumbool
                        (zeq
                          (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S O))))))))))))))))))))))))))))))) o1)
                          (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S O))))))))))))))))))))))))))))))) o2))
                 else false
             | _ -> false)
      | Vinttoptr i1 ->
          (match v2 with
             | Vinttoptr i2 ->
                 proj_sumbool
                   (zeq
                     (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))))))))))))))))))) i1)
                     (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))))))))))))))))))) i2))
             | _ -> false)
  
  (** val get_wordsize : coq_val -> nat option **)
  
  let get_wordsize = function
    | Vint (wz, i) -> Some wz
    | Vptr (b, i) -> Some (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))
    | Vinttoptr i -> Some (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))
    | _ -> None
  
  (** val of_bool : bool -> coq_val **)
  
  let of_bool = function
    | true -> coq_Vtrue
    | false -> coq_Vfalse
  
  (** val neg : coq_val -> coq_val **)
  
  let neg = function
    | Vint (wz, n) -> Vint (wz, (Int.neg wz n))
    | _ -> Vundef
  
  (** val negf : coq_val -> coq_val **)
  
  let negf = function
    | Vfloat f -> Vfloat (Float.neg f)
    | _ -> Vundef
  
  (** val absf : coq_val -> coq_val **)
  
  let absf = function
    | Vfloat f -> Vfloat (Float.abs f)
    | _ -> Vundef
  
  (** val trunc : coq_val -> nat -> coq_val **)
  
  let trunc v wz' =
    match v with
      | Vint (wz, n) ->
          if le_lt_dec wz wz'
          then Vundef
          else Vint (wz', (Int.repr wz' (Int.unsigned wz n)))
      | _ -> Vundef
  
  (** val ftrunc : coq_val -> coq_val **)
  
  let ftrunc v = match v with
    | Vfloat f -> v
    | _ -> Vundef
  
  (** val intoffloat : coq_val -> coq_val **)
  
  let intoffloat = function
    | Vfloat f -> Vint ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))), (Float.intoffloat f))
    | _ -> Vundef
  
  (** val intuoffloat : coq_val -> coq_val **)
  
  let intuoffloat = function
    | Vfloat f -> Vint ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))), (Float.intuoffloat f))
    | _ -> Vundef
  
  (** val floatofint : coq_val -> coq_val **)
  
  let floatofint = function
    | Vint (wz, n) ->
        (match wz with
           | O -> Vundef
           | S n0 ->
               (match n0 with
                  | O -> Vundef
                  | S n1 ->
                      (match n1 with
                         | O -> Vundef
                         | S n2 ->
                             (match n2 with
                                | O -> Vundef
                                | S n3 ->
                                    (match n3 with
                                       | O -> Vundef
                                       | S n4 ->
                                           (match n4 with
                                              | O -> Vundef
                                              | S n5 ->
                                                  (
                                                  match n5 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n6 ->
                                                  (match n6 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n7 ->
                                                  (match n7 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n8 ->
                                                  (match n8 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n9 ->
                                                  (match n9 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n10 ->
                                                  (match n10 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n11 ->
                                                  (match n11 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n12 ->
                                                  (match n12 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n13 ->
                                                  (match n13 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n14 ->
                                                  (match n14 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n15 ->
                                                  (match n15 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n16 ->
                                                  (match n16 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n17 ->
                                                  (match n17 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n18 ->
                                                  (match n18 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n19 ->
                                                  (match n19 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n20 ->
                                                  (match n20 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n21 ->
                                                  (match n21 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n22 ->
                                                  (match n22 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n23 ->
                                                  (match n23 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n24 ->
                                                  (match n24 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n25 ->
                                                  (match n25 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n26 ->
                                                  (match n26 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n27 ->
                                                  (match n27 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n28 ->
                                                  (match n28 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n29 ->
                                                  (match n29 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n30 ->
                                                  (match n30 with
                                                    | 
                                                  O -> Vfloat
                                                  (Float.floatofint n)
                                                    | 
                                                  S n31 -> Vundef))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val floatofintu : coq_val -> coq_val **)
  
  let floatofintu = function
    | Vint (wz, n) ->
        (match wz with
           | O -> Vundef
           | S n0 ->
               (match n0 with
                  | O -> Vundef
                  | S n1 ->
                      (match n1 with
                         | O -> Vundef
                         | S n2 ->
                             (match n2 with
                                | O -> Vundef
                                | S n3 ->
                                    (match n3 with
                                       | O -> Vundef
                                       | S n4 ->
                                           (match n4 with
                                              | O -> Vundef
                                              | S n5 ->
                                                  (
                                                  match n5 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n6 ->
                                                  (match n6 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n7 ->
                                                  (match n7 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n8 ->
                                                  (match n8 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n9 ->
                                                  (match n9 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n10 ->
                                                  (match n10 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n11 ->
                                                  (match n11 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n12 ->
                                                  (match n12 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n13 ->
                                                  (match n13 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n14 ->
                                                  (match n14 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n15 ->
                                                  (match n15 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n16 ->
                                                  (match n16 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n17 ->
                                                  (match n17 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n18 ->
                                                  (match n18 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n19 ->
                                                  (match n19 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n20 ->
                                                  (match n20 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n21 ->
                                                  (match n21 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n22 ->
                                                  (match n22 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n23 ->
                                                  (match n23 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n24 ->
                                                  (match n24 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n25 ->
                                                  (match n25 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n26 ->
                                                  (match n26 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n27 ->
                                                  (match n27 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n28 ->
                                                  (match n28 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n29 ->
                                                  (match n29 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n30 ->
                                                  (match n30 with
                                                    | 
                                                  O -> Vfloat
                                                  (Float.floatofintu n)
                                                    | 
                                                  S n31 -> Vundef))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val floatofwords : coq_val -> coq_val -> coq_val **)
  
  let floatofwords v1 v2 =
    match v1 with
      | Vint (wz, n1) ->
          (match wz with
             | O -> Vundef
             | S n ->
                 (match n with
                    | O -> Vundef
                    | S n0 ->
                        (match n0 with
                           | O -> Vundef
                           | S n2 ->
                               (match n2 with
                                  | O -> Vundef
                                  | S n3 ->
                                      (match n3 with
                                         | O -> Vundef
                                         | S n4 ->
                                             (match n4 with
                                                | O -> Vundef
                                                | S n5 ->
                                                  (match n5 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n6 ->
                                                  (match n6 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n7 ->
                                                  (match n7 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n8 ->
                                                  (match n8 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n9 ->
                                                  (match n9 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n10 ->
                                                  (match n10 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n11 ->
                                                  (match n11 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n12 ->
                                                  (match n12 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n13 ->
                                                  (match n13 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n14 ->
                                                  (match n14 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n15 ->
                                                  (match n15 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n16 ->
                                                  (match n16 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n17 ->
                                                  (match n17 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n18 ->
                                                  (match n18 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n19 ->
                                                  (match n19 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n20 ->
                                                  (match n20 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n21 ->
                                                  (match n21 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n22 ->
                                                  (match n22 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n23 ->
                                                  (match n23 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n24 ->
                                                  (match n24 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n25 ->
                                                  (match n25 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n26 ->
                                                  (match n26 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n27 ->
                                                  (match n27 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n28 ->
                                                  (match n28 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n29 ->
                                                  (match n29 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n30 ->
                                                  (match n30 with
                                                    | 
                                                  O ->
                                                  (match v2 with
                                                    | 
                                                  Vint (
                                                  wz0, n31) ->
                                                  (match wz0 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n32 ->
                                                  (match n32 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n33 ->
                                                  (match n33 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n34 ->
                                                  (match n34 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n35 ->
                                                  (match n35 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n36 ->
                                                  (match n36 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n37 ->
                                                  (match n37 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n38 ->
                                                  (match n38 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n39 ->
                                                  (match n39 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n40 ->
                                                  (match n40 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n41 ->
                                                  (match n41 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n42 ->
                                                  (match n42 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n43 ->
                                                  (match n43 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n44 ->
                                                  (match n44 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n45 ->
                                                  (match n45 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n46 ->
                                                  (match n46 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n47 ->
                                                  (match n47 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n48 ->
                                                  (match n48 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n49 ->
                                                  (match n49 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n50 ->
                                                  (match n50 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n51 ->
                                                  (match n51 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n52 ->
                                                  (match n52 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n53 ->
                                                  (match n53 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n54 ->
                                                  (match n54 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n55 ->
                                                  (match n55 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n56 ->
                                                  (match n56 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n57 ->
                                                  (match n57 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n58 ->
                                                  (match n58 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n59 ->
                                                  (match n59 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n60 ->
                                                  (match n60 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n61 ->
                                                  (match n61 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n62 ->
                                                  (match n62 with
                                                    | 
                                                  O -> Vfloat
                                                  (Float.from_words n1 n31)
                                                    | 
                                                  S n63 -> Vundef))))))))))))))))))))))))))))))))
                                                    | 
                                                  _ -> Vundef)
                                                    | 
                                                  S n31 -> Vundef))))))))))))))))))))))))))))))))
      | _ -> Vundef
  
  (** val notint : coq_val -> coq_val **)
  
  let notint = function
    | Vint (wz, n) -> Vint (wz, (Int.xor wz n (Int.mone wz)))
    | _ -> Vundef
  
  (** val notbool : coq_val -> coq_val **)
  
  let notbool = function
    | Vundef -> Vundef
    | Vint (wz, n) -> of_bool (Int.eq wz n (zero wz))
    | Vfloat f -> Vundef
    | _ -> coq_Vfalse
  
  (** val zero_ext : coq_Z -> coq_val -> coq_val **)
  
  let zero_ext nbits = function
    | Vint (wz, n) -> Vint (wz, (Int.zero_ext wz nbits n))
    | _ -> Vundef
  
  (** val sign_ext : coq_Z -> coq_val -> coq_val **)
  
  let sign_ext nbits = function
    | Vint (wz, n) -> Vint (wz, (Int.sign_ext wz nbits n))
    | _ -> Vundef
  
  (** val singleoffloat : coq_val -> coq_val **)
  
  let singleoffloat = function
    | Vfloat f -> Vfloat (Float.singleoffloat f)
    | _ -> Vundef
  
  type add_comp = coq_val
  
  (** val add_comp_proj : coq_val -> coq_val -> add_comp -> add_comp **)
  
  let add_comp_proj v1 v2 comp =
    comp
  
  (** val add_obligation_1 : nat -> Int.int -> nat -> Int.int -> add_comp **)
  
  let add_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> Vint (wz0, (Int.add wz0 i1 i2))) wz i i0
  
  (** val add_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> add_comp **)
  
  let add_obligation_2 wz i wz0 i0 = function
    | true -> add_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val add_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> add_comp **)
  
  let add_obligation_3 =
    add_obligation_2
  
  (** val add_obligation_4 :
      nat -> Int.int -> block -> Int.int -> add_comp **)
  
  let add_obligation_4 wz i b i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 b0 i2 -> Vptr (b0,
      (Int.add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i2 i1)))
      wz i b i0
  
  (** val add_obligation_5 :
      nat -> Int.int -> block -> Int.int -> bool -> add_comp **)
  
  let add_obligation_5 wz i b i0 = function
    | true -> add_obligation_4 wz i b i0
    | false -> Vundef
  
  (** val add_obligation_6 :
      nat -> Int.int -> block -> Int.int -> bool -> add_comp **)
  
  let add_obligation_6 =
    add_obligation_5
  
  (** val add_obligation_7 : nat -> Int.int -> Int.int -> add_comp **)
  
  let add_obligation_7 wz i i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 i2 -> Vinttoptr
      (Int.add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i1 i2))
      wz i i0
  
  (** val add_obligation_8 :
      nat -> Int.int -> Int.int -> bool -> add_comp **)
  
  let add_obligation_8 wz i i0 = function
    | true -> add_obligation_7 wz i i0
    | false -> Vundef
  
  (** val add_obligation_9 :
      nat -> Int.int -> Int.int -> bool -> add_comp **)
  
  let add_obligation_9 =
    add_obligation_8
  
  (** val add_obligation_10 : nat -> Int.int -> coq_val -> add_comp **)
  
  let add_obligation_10 wz i = function
    | Vint (wz0, i0) -> add_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | Vptr (b, i0) ->
        add_obligation_6 wz i b i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vinttoptr i0 ->
        add_obligation_9 wz i i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val add_obligation_11 :
      block -> Int.int -> nat -> Int.int -> add_comp **)
  
  let add_obligation_11 b i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 -> Vptr (b,
      (Int.add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i i1)))
      wz i0
  
  (** val add_obligation_12 :
      block -> Int.int -> nat -> Int.int -> bool -> add_comp **)
  
  let add_obligation_12 b i wz i0 = function
    | true -> add_obligation_11 b i wz i0
    | false -> Vundef
  
  (** val add_obligation_13 :
      block -> Int.int -> nat -> Int.int -> bool -> add_comp **)
  
  let add_obligation_13 =
    add_obligation_12
  
  (** val add_obligation_14 : block -> Int.int -> coq_val -> add_comp **)
  
  let add_obligation_14 b i = function
    | Vint (wz, i0) ->
        add_obligation_13 b i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val add_obligation_15 : Int.int -> nat -> Int.int -> add_comp **)
  
  let add_obligation_15 i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 -> Vinttoptr
      (Int.add (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i i1))
      wz i0
  
  (** val add_obligation_16 :
      Int.int -> nat -> Int.int -> bool -> add_comp **)
  
  let add_obligation_16 i wz i0 = function
    | true -> add_obligation_15 i wz i0
    | false -> Vundef
  
  (** val add_obligation_17 :
      Int.int -> nat -> Int.int -> bool -> add_comp **)
  
  let add_obligation_17 =
    add_obligation_16
  
  (** val add_obligation_18 : Int.int -> coq_val -> add_comp **)
  
  let add_obligation_18 i = function
    | Vint (wz, i0) ->
        add_obligation_17 i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val add_obligation_19 : coq_val -> coq_val -> add_comp **)
  
  let add_obligation_19 = function
    | Vint (wz, i) -> add_obligation_10 wz i
    | Vptr (b, i) -> add_obligation_14 b i
    | Vinttoptr i -> add_obligation_18 i
    | _ -> (fun v2 -> Vundef)
  
  (** val add : coq_val -> coq_val -> add_comp **)
  
  let add =
    add_obligation_19
  
  (** val coq_FunctionalInduction_add :
      (coq_val -> coq_val -> add_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_add =
    Build_FunctionalInduction
  
  type sub_comp = coq_val
  
  (** val sub_comp_proj : coq_val -> coq_val -> sub_comp -> sub_comp **)
  
  let sub_comp_proj v1 v2 comp =
    comp
  
  (** val sub_obligation_1 : nat -> Int.int -> nat -> Int.int -> sub_comp **)
  
  let sub_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> Vint (wz0, (Int.sub wz0 i1 i2))) wz i i0
  
  (** val sub_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> sub_comp **)
  
  let sub_obligation_2 wz i wz0 i0 = function
    | true -> sub_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val sub_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> sub_comp **)
  
  let sub_obligation_3 =
    sub_obligation_2
  
  (** val sub_obligation_4 : nat -> Int.int -> coq_val -> sub_comp **)
  
  let sub_obligation_4 wz i = function
    | Vint (wz0, i0) -> sub_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val sub_obligation_5 :
      block -> Int.int -> nat -> Int.int -> sub_comp **)
  
  let sub_obligation_5 b i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 -> Vptr (b,
      (Int.sub (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i i1)))
      wz i0
  
  (** val sub_obligation_6 :
      block -> Int.int -> nat -> Int.int -> bool -> sub_comp **)
  
  let sub_obligation_6 b i wz i0 = function
    | true -> sub_obligation_5 b i wz i0
    | false -> Vundef
  
  (** val sub_obligation_7 :
      block -> Int.int -> nat -> Int.int -> bool -> sub_comp **)
  
  let sub_obligation_7 =
    sub_obligation_6
  
  (** val sub_obligation_8 : block -> Int.int -> coq_val -> sub_comp **)
  
  let sub_obligation_8 b i = function
    | Vint (wz, i0) ->
        sub_obligation_7 b i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vptr (b0, i0) ->
        if zeq b b0
        then Vint ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               (S (S (S (S (S (S (S (S (S (S (S (S
               O))))))))))))))))))))))))))))))),
               (Int.sub (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O))))))))))))))))))))))))))))))) i i0))
        else Vundef
    | _ -> Vundef
  
  (** val sub_obligation_9 : Int.int -> nat -> Int.int -> sub_comp **)
  
  let sub_obligation_9 i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 -> Vinttoptr
      (Int.sub (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i i1))
      wz i0
  
  (** val sub_obligation_10 :
      Int.int -> nat -> Int.int -> bool -> sub_comp **)
  
  let sub_obligation_10 i wz i0 = function
    | true -> sub_obligation_9 i wz i0
    | false -> Vundef
  
  (** val sub_obligation_11 :
      Int.int -> nat -> Int.int -> bool -> sub_comp **)
  
  let sub_obligation_11 =
    sub_obligation_10
  
  (** val sub_obligation_12 : Int.int -> coq_val -> sub_comp **)
  
  let sub_obligation_12 i = function
    | Vint (wz, i0) ->
        sub_obligation_11 i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vinttoptr i0 -> Vint ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))),
        (Int.sub (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i
          i0))
    | _ -> Vundef
  
  (** val sub_obligation_13 : coq_val -> coq_val -> sub_comp **)
  
  let sub_obligation_13 = function
    | Vint (wz, i) -> sub_obligation_4 wz i
    | Vptr (b, i) -> sub_obligation_8 b i
    | Vinttoptr i -> sub_obligation_12 i
    | _ -> (fun v2 -> Vundef)
  
  (** val sub : coq_val -> coq_val -> sub_comp **)
  
  let sub =
    sub_obligation_13
  
  (** val coq_FunctionalInduction_sub :
      (coq_val -> coq_val -> sub_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_sub =
    Build_FunctionalInduction
  
  type mul_comp = coq_val
  
  (** val mul_comp_proj : coq_val -> coq_val -> mul_comp -> mul_comp **)
  
  let mul_comp_proj v1 v2 comp =
    comp
  
  (** val mul_obligation_1 : nat -> Int.int -> nat -> Int.int -> mul_comp **)
  
  let mul_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> Vint (wz0, (Int.mul wz0 i1 i2))) wz i i0
  
  (** val mul_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> mul_comp **)
  
  let mul_obligation_2 wz i wz0 i0 = function
    | true -> mul_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val mul_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> mul_comp **)
  
  let mul_obligation_3 =
    mul_obligation_2
  
  (** val mul_obligation_4 : nat -> Int.int -> coq_val -> mul_comp **)
  
  let mul_obligation_4 wz i = function
    | Vint (wz0, i0) -> mul_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val mul_obligation_5 : coq_val -> coq_val -> mul_comp **)
  
  let mul_obligation_5 = function
    | Vint (wz, i) -> mul_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val mul : coq_val -> coq_val -> mul_comp **)
  
  let mul =
    mul_obligation_5
  
  (** val coq_FunctionalInduction_mul :
      (coq_val -> coq_val -> mul_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_mul =
    Build_FunctionalInduction
  
  type divs_comp = coq_val
  
  (** val divs_comp_proj : coq_val -> coq_val -> divs_comp -> divs_comp **)
  
  let divs_comp_proj v1 v2 comp =
    comp
  
  (** val divs_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> divs_comp **)
  
  let divs_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.eq wz0 i2 (Int.zero wz0)
      then Vundef
      else Vint (wz0, (Int.divs wz0 i1 i2))) wz i i0
  
  (** val divs_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> divs_comp **)
  
  let divs_obligation_2 wz i wz0 i0 = function
    | true -> divs_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val divs_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> divs_comp **)
  
  let divs_obligation_3 =
    divs_obligation_2
  
  (** val divs_obligation_4 : nat -> Int.int -> coq_val -> divs_comp **)
  
  let divs_obligation_4 wz i = function
    | Vint (wz0, i0) -> divs_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val divs_obligation_5 : coq_val -> coq_val -> divs_comp **)
  
  let divs_obligation_5 = function
    | Vint (wz, i) -> divs_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val divs : coq_val -> coq_val -> divs_comp **)
  
  let divs =
    divs_obligation_5
  
  (** val coq_FunctionalInduction_divs :
      (coq_val -> coq_val -> divs_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_divs =
    Build_FunctionalInduction
  
  type mods_comp = coq_val
  
  (** val mods_comp_proj : coq_val -> coq_val -> mods_comp -> mods_comp **)
  
  let mods_comp_proj v1 v2 comp =
    comp
  
  (** val mods_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> mods_comp **)
  
  let mods_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.eq wz0 i2 (Int.zero wz0)
      then Vundef
      else Vint (wz0, (Int.mods wz0 i1 i2))) wz i i0
  
  (** val mods_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> mods_comp **)
  
  let mods_obligation_2 wz i wz0 i0 = function
    | true -> mods_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val mods_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> mods_comp **)
  
  let mods_obligation_3 =
    mods_obligation_2
  
  (** val mods_obligation_4 : nat -> Int.int -> coq_val -> mods_comp **)
  
  let mods_obligation_4 wz i = function
    | Vint (wz0, i0) -> mods_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val mods_obligation_5 : coq_val -> coq_val -> mods_comp **)
  
  let mods_obligation_5 = function
    | Vint (wz, i) -> mods_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val mods : coq_val -> coq_val -> mods_comp **)
  
  let mods =
    mods_obligation_5
  
  (** val coq_FunctionalInduction_mods :
      (coq_val -> coq_val -> mods_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_mods =
    Build_FunctionalInduction
  
  type divu_comp = coq_val
  
  (** val divu_comp_proj : coq_val -> coq_val -> divu_comp -> divu_comp **)
  
  let divu_comp_proj v1 v2 comp =
    comp
  
  (** val divu_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> divu_comp **)
  
  let divu_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.eq wz0 i2 (Int.zero wz0)
      then Vundef
      else Vint (wz0, (Int.divu wz0 i1 i2))) wz i i0
  
  (** val divu_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> divu_comp **)
  
  let divu_obligation_2 wz i wz0 i0 = function
    | true -> divu_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val divu_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> divu_comp **)
  
  let divu_obligation_3 =
    divu_obligation_2
  
  (** val divu_obligation_4 : nat -> Int.int -> coq_val -> divu_comp **)
  
  let divu_obligation_4 wz i = function
    | Vint (wz0, i0) -> divu_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val divu_obligation_5 : coq_val -> coq_val -> divu_comp **)
  
  let divu_obligation_5 = function
    | Vint (wz, i) -> divu_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val divu : coq_val -> coq_val -> divu_comp **)
  
  let divu =
    divu_obligation_5
  
  (** val coq_FunctionalInduction_divu :
      (coq_val -> coq_val -> divu_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_divu =
    Build_FunctionalInduction
  
  type modu_comp = coq_val
  
  (** val modu_comp_proj : coq_val -> coq_val -> modu_comp -> modu_comp **)
  
  let modu_comp_proj v1 v2 comp =
    comp
  
  (** val modu_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> modu_comp **)
  
  let modu_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.eq wz0 i2 (Int.zero wz0)
      then Vundef
      else Vint (wz0, (Int.modu wz0 i1 i2))) wz i i0
  
  (** val modu_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> modu_comp **)
  
  let modu_obligation_2 wz i wz0 i0 = function
    | true -> modu_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val modu_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> modu_comp **)
  
  let modu_obligation_3 =
    modu_obligation_2
  
  (** val modu_obligation_4 : nat -> Int.int -> coq_val -> modu_comp **)
  
  let modu_obligation_4 wz i = function
    | Vint (wz0, i0) -> modu_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val modu_obligation_5 : coq_val -> coq_val -> modu_comp **)
  
  let modu_obligation_5 = function
    | Vint (wz, i) -> modu_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val modu : coq_val -> coq_val -> modu_comp **)
  
  let modu =
    modu_obligation_5
  
  (** val coq_FunctionalInduction_modu :
      (coq_val -> coq_val -> modu_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_modu =
    Build_FunctionalInduction
  
  type and_comp = coq_val
  
  (** val and_comp_proj : coq_val -> coq_val -> and_comp -> and_comp **)
  
  let and_comp_proj v1 v2 comp =
    comp
  
  (** val and_obligation_1 : nat -> Int.int -> nat -> Int.int -> and_comp **)
  
  let and_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> Vint (wz0, (Int.coq_and wz0 i1 i2))) wz i
      i0
  
  (** val and_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> and_comp **)
  
  let and_obligation_2 wz i wz0 i0 = function
    | true -> and_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val and_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> and_comp **)
  
  let and_obligation_3 =
    and_obligation_2
  
  (** val and_obligation_4 : nat -> Int.int -> coq_val -> and_comp **)
  
  let and_obligation_4 wz i = function
    | Vint (wz0, i0) -> and_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val and_obligation_5 : coq_val -> coq_val -> and_comp **)
  
  let and_obligation_5 = function
    | Vint (wz, i) -> and_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val coq_and : coq_val -> coq_val -> and_comp **)
  
  let coq_and =
    and_obligation_5
  
  (** val coq_FunctionalInduction_and :
      (coq_val -> coq_val -> and_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_and =
    Build_FunctionalInduction
  
  type or_comp = coq_val
  
  (** val or_comp_proj : coq_val -> coq_val -> or_comp -> or_comp **)
  
  let or_comp_proj v1 v2 comp =
    comp
  
  (** val or_obligation_1 : nat -> Int.int -> nat -> Int.int -> or_comp **)
  
  let or_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> Vint (wz0, (Int.coq_or wz0 i1 i2))) wz i
      i0
  
  (** val or_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> or_comp **)
  
  let or_obligation_2 wz i wz0 i0 = function
    | true -> or_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val or_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> or_comp **)
  
  let or_obligation_3 =
    or_obligation_2
  
  (** val or_obligation_4 : nat -> Int.int -> coq_val -> or_comp **)
  
  let or_obligation_4 wz i = function
    | Vint (wz0, i0) -> or_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val or_obligation_5 : coq_val -> coq_val -> or_comp **)
  
  let or_obligation_5 = function
    | Vint (wz, i) -> or_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val coq_or : coq_val -> coq_val -> or_comp **)
  
  let coq_or =
    or_obligation_5
  
  (** val coq_FunctionalInduction_or :
      (coq_val -> coq_val -> or_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_or =
    Build_FunctionalInduction
  
  type xor_comp = coq_val
  
  (** val xor_comp_proj : coq_val -> coq_val -> xor_comp -> xor_comp **)
  
  let xor_comp_proj v1 v2 comp =
    comp
  
  (** val xor_obligation_1 : nat -> Int.int -> nat -> Int.int -> xor_comp **)
  
  let xor_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> Vint (wz0, (Int.xor wz0 i1 i2))) wz i i0
  
  (** val xor_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> xor_comp **)
  
  let xor_obligation_2 wz i wz0 i0 = function
    | true -> xor_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val xor_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> xor_comp **)
  
  let xor_obligation_3 =
    xor_obligation_2
  
  (** val xor_obligation_4 : nat -> Int.int -> coq_val -> xor_comp **)
  
  let xor_obligation_4 wz i = function
    | Vint (wz0, i0) -> xor_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val xor_obligation_5 : coq_val -> coq_val -> xor_comp **)
  
  let xor_obligation_5 = function
    | Vint (wz, i) -> xor_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val xor : coq_val -> coq_val -> xor_comp **)
  
  let xor =
    xor_obligation_5
  
  (** val coq_FunctionalInduction_xor :
      (coq_val -> coq_val -> xor_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_xor =
    Build_FunctionalInduction
  
  type shl_comp = coq_val
  
  (** val shl_comp_proj : coq_val -> coq_val -> shl_comp -> shl_comp **)
  
  let shl_comp_proj v1 v2 comp =
    comp
  
  (** val shl_obligation_1 : nat -> Int.int -> nat -> Int.int -> shl_comp **)
  
  let shl_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.ltu wz0 i2 (Int.iwordsize wz0)
      then Vint (wz0, (Int.shl wz0 i1 i2))
      else Vundef) wz i i0
  
  (** val shl_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> shl_comp **)
  
  let shl_obligation_2 wz i wz0 i0 = function
    | true -> shl_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val shl_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> shl_comp **)
  
  let shl_obligation_3 =
    shl_obligation_2
  
  (** val shl_obligation_4 : nat -> Int.int -> coq_val -> shl_comp **)
  
  let shl_obligation_4 wz i = function
    | Vint (wz0, i0) -> shl_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val shl_obligation_5 : coq_val -> coq_val -> shl_comp **)
  
  let shl_obligation_5 = function
    | Vint (wz, i) -> shl_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val shl : coq_val -> coq_val -> shl_comp **)
  
  let shl =
    shl_obligation_5
  
  (** val coq_FunctionalInduction_shl :
      (coq_val -> coq_val -> shl_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_shl =
    Build_FunctionalInduction
  
  type shr_comp = coq_val
  
  (** val shr_comp_proj : coq_val -> coq_val -> shr_comp -> shr_comp **)
  
  let shr_comp_proj v1 v2 comp =
    comp
  
  (** val shr_obligation_1 : nat -> Int.int -> nat -> Int.int -> shr_comp **)
  
  let shr_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.ltu wz0 i2 (Int.iwordsize wz0)
      then Vint (wz0, (Int.shr wz0 i1 i2))
      else Vundef) wz i i0
  
  (** val shr_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> shr_comp **)
  
  let shr_obligation_2 wz i wz0 i0 = function
    | true -> shr_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val shr_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> shr_comp **)
  
  let shr_obligation_3 =
    shr_obligation_2
  
  (** val shr_obligation_4 : nat -> Int.int -> coq_val -> shr_comp **)
  
  let shr_obligation_4 wz i = function
    | Vint (wz0, i0) -> shr_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val shr_obligation_5 : coq_val -> coq_val -> shr_comp **)
  
  let shr_obligation_5 = function
    | Vint (wz, i) -> shr_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val shr : coq_val -> coq_val -> shr_comp **)
  
  let shr =
    shr_obligation_5
  
  (** val coq_FunctionalInduction_shr :
      (coq_val -> coq_val -> shr_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_shr =
    Build_FunctionalInduction
  
  type shr_carry_comp = coq_val
  
  (** val shr_carry_comp_proj :
      coq_val -> coq_val -> shr_carry_comp -> shr_carry_comp **)
  
  let shr_carry_comp_proj v1 v2 comp =
    comp
  
  (** val shr_carry_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> shr_carry_comp **)
  
  let shr_carry_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.ltu wz0 i2 (Int.iwordsize wz0)
      then Vint (wz0, (Int.shr_carry wz0 i1 i2))
      else Vundef) wz i i0
  
  (** val shr_carry_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> shr_carry_comp **)
  
  let shr_carry_obligation_2 wz i wz0 i0 = function
    | true -> shr_carry_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val shr_carry_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> shr_carry_comp **)
  
  let shr_carry_obligation_3 =
    shr_carry_obligation_2
  
  (** val shr_carry_obligation_4 :
      nat -> Int.int -> coq_val -> shr_carry_comp **)
  
  let shr_carry_obligation_4 wz i = function
    | Vint (wz0, i0) ->
        shr_carry_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val shr_carry_obligation_5 : coq_val -> coq_val -> shr_carry_comp **)
  
  let shr_carry_obligation_5 = function
    | Vint (wz, i) -> shr_carry_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val shr_carry : coq_val -> coq_val -> shr_carry_comp **)
  
  let shr_carry =
    shr_carry_obligation_5
  
  (** val coq_FunctionalInduction_shr_carry :
      (coq_val -> coq_val -> shr_carry_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_shr_carry =
    Build_FunctionalInduction
  
  type shrx_comp = coq_val
  
  (** val shrx_comp_proj : coq_val -> coq_val -> shrx_comp -> shrx_comp **)
  
  let shrx_comp_proj v1 v2 comp =
    comp
  
  (** val shrx_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> shrx_comp **)
  
  let shrx_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.ltu wz0 i2 (Int.iwordsize wz0)
      then Vint (wz0, (Int.shrx wz0 i1 i2))
      else Vundef) wz i i0
  
  (** val shrx_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> shrx_comp **)
  
  let shrx_obligation_2 wz i wz0 i0 = function
    | true -> shrx_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val shrx_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> shrx_comp **)
  
  let shrx_obligation_3 =
    shrx_obligation_2
  
  (** val shrx_obligation_4 : nat -> Int.int -> coq_val -> shrx_comp **)
  
  let shrx_obligation_4 wz i = function
    | Vint (wz0, i0) -> shrx_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val shrx_obligation_5 : coq_val -> coq_val -> shrx_comp **)
  
  let shrx_obligation_5 = function
    | Vint (wz, i) -> shrx_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val shrx : coq_val -> coq_val -> shrx_comp **)
  
  let shrx =
    shrx_obligation_5
  
  (** val coq_FunctionalInduction_shrx :
      (coq_val -> coq_val -> shrx_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_shrx =
    Build_FunctionalInduction
  
  type shru_comp = coq_val
  
  (** val shru_comp_proj : coq_val -> coq_val -> shru_comp -> shru_comp **)
  
  let shru_comp_proj v1 v2 comp =
    comp
  
  (** val shru_obligation_1 :
      nat -> Int.int -> nat -> Int.int -> shru_comp **)
  
  let shru_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.ltu wz0 i2 (Int.iwordsize wz0)
      then Vint (wz0, (Int.shru wz0 i1 i2))
      else Vundef) wz i i0
  
  (** val shru_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> shru_comp **)
  
  let shru_obligation_2 wz i wz0 i0 = function
    | true -> shru_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val shru_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> shru_comp **)
  
  let shru_obligation_3 =
    shru_obligation_2
  
  (** val shru_obligation_4 : nat -> Int.int -> coq_val -> shru_comp **)
  
  let shru_obligation_4 wz i = function
    | Vint (wz0, i0) -> shru_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val shru_obligation_5 : coq_val -> coq_val -> shru_comp **)
  
  let shru_obligation_5 = function
    | Vint (wz, i) -> shru_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val shru : coq_val -> coq_val -> shru_comp **)
  
  let shru =
    shru_obligation_5
  
  (** val coq_FunctionalInduction_shru :
      (coq_val -> coq_val -> shru_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_shru =
    Build_FunctionalInduction
  
  (** val rolm : coq_val -> Int.int -> Int.int -> coq_val **)
  
  let rolm v amount mask =
    match v with
      | Vint (wz, n) ->
          (match wz with
             | O -> Vundef
             | S n0 ->
                 (match n0 with
                    | O -> Vundef
                    | S n1 ->
                        (match n1 with
                           | O -> Vundef
                           | S n2 ->
                               (match n2 with
                                  | O -> Vundef
                                  | S n3 ->
                                      (match n3 with
                                         | O -> Vundef
                                         | S n4 ->
                                             (match n4 with
                                                | O -> Vundef
                                                | S n5 ->
                                                  (match n5 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n6 ->
                                                  (match n6 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n7 ->
                                                  (match n7 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n8 ->
                                                  (match n8 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n9 ->
                                                  (match n9 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n10 ->
                                                  (match n10 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n11 ->
                                                  (match n11 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n12 ->
                                                  (match n12 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n13 ->
                                                  (match n13 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n14 ->
                                                  (match n14 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n15 ->
                                                  (match n15 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n16 ->
                                                  (match n16 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n17 ->
                                                  (match n17 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n18 ->
                                                  (match n18 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n19 ->
                                                  (match n19 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n20 ->
                                                  (match n20 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n21 ->
                                                  (match n21 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n22 ->
                                                  (match n22 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n23 ->
                                                  (match n23 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n24 ->
                                                  (match n24 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n25 ->
                                                  (match n25 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n26 ->
                                                  (match n26 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n27 ->
                                                  (match n27 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n28 ->
                                                  (match n28 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n29 ->
                                                  (match n29 with
                                                    | 
                                                  O -> Vundef
                                                    | 
                                                  S n30 ->
                                                  (match n30 with
                                                    | 
                                                  O -> Vint ((S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S
                                                  O))))))))))))))))))))))))))))))),
                                                  (Int.rolm (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S
                                                  O)))))))))))))))))))))))))))))))
                                                  n amount mask))
                                                    | 
                                                  S n31 -> Vundef))))))))))))))))))))))))))))))))
      | _ -> Vundef
  
  type ror_comp = coq_val
  
  (** val ror_comp_proj : coq_val -> coq_val -> ror_comp -> ror_comp **)
  
  let ror_comp_proj v1 v2 comp =
    comp
  
  (** val ror_obligation_1 : nat -> Int.int -> nat -> Int.int -> ror_comp **)
  
  let ror_obligation_1 wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 ->
      if Int.ltu wz0 i2 (Int.iwordsize wz0)
      then Vint (wz0, (Int.ror wz0 i1 i2))
      else Vundef) wz i i0
  
  (** val ror_obligation_2 :
      nat -> Int.int -> nat -> Int.int -> bool -> ror_comp **)
  
  let ror_obligation_2 wz i wz0 i0 = function
    | true -> ror_obligation_1 wz i wz0 i0
    | false -> Vundef
  
  (** val ror_obligation_3 :
      nat -> Int.int -> nat -> Int.int -> bool -> ror_comp **)
  
  let ror_obligation_3 =
    ror_obligation_2
  
  (** val ror_obligation_4 : nat -> Int.int -> coq_val -> ror_comp **)
  
  let ror_obligation_4 wz i = function
    | Vint (wz0, i0) -> ror_obligation_3 wz i wz0 i0 (eq_nat_dec wz wz0)
    | _ -> Vundef
  
  (** val ror_obligation_5 : coq_val -> coq_val -> ror_comp **)
  
  let ror_obligation_5 = function
    | Vint (wz, i) -> ror_obligation_4 wz i
    | _ -> (fun v2 -> Vundef)
  
  (** val ror : coq_val -> coq_val -> ror_comp **)
  
  let ror =
    ror_obligation_5
  
  (** val coq_FunctionalInduction_ror :
      (coq_val -> coq_val -> ror_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_ror =
    Build_FunctionalInduction
  
  (** val addf : coq_val -> coq_val -> coq_val **)
  
  let addf v1 v2 =
    match v1 with
      | Vfloat f1 ->
          (match v2 with
             | Vfloat f2 -> Vfloat (Float.add f1 f2)
             | _ -> Vundef)
      | _ -> Vundef
  
  (** val subf : coq_val -> coq_val -> coq_val **)
  
  let subf v1 v2 =
    match v1 with
      | Vfloat f1 ->
          (match v2 with
             | Vfloat f2 -> Vfloat (Float.sub f1 f2)
             | _ -> Vundef)
      | _ -> Vundef
  
  (** val mulf : coq_val -> coq_val -> coq_val **)
  
  let mulf v1 v2 =
    match v1 with
      | Vfloat f1 ->
          (match v2 with
             | Vfloat f2 -> Vfloat (Float.mul f1 f2)
             | _ -> Vundef)
      | _ -> Vundef
  
  (** val divf : coq_val -> coq_val -> coq_val **)
  
  let divf v1 v2 =
    match v1 with
      | Vfloat f1 ->
          (match v2 with
             | Vfloat f2 -> Vfloat (Float.div f1 f2)
             | _ -> Vundef)
      | _ -> Vundef
  
  (** val modf : coq_val -> coq_val -> coq_val **)
  
  let modf v1 v2 =
    match v1 with
      | Vfloat f1 ->
          (match v2 with
             | Vfloat f2 -> Vfloat (Float.rem f1 f2)
             | _ -> Vundef)
      | _ -> Vundef
  
  (** val cmp_mismatch : comparison -> coq_val **)
  
  let cmp_mismatch = function
    | Ceq -> coq_Vfalse
    | Cne -> coq_Vtrue
    | _ -> Vundef
  
  type cmp_comp = coq_val
  
  (** val cmp_comp_proj :
      comparison -> coq_val -> coq_val -> cmp_comp -> cmp_comp **)
  
  let cmp_comp_proj c v1 v2 comp =
    comp
  
  (** val cmp_obligation_1 :
      comparison -> nat -> Int.int -> nat -> Int.int -> cmp_comp **)
  
  let cmp_obligation_1 c wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> of_bool (Int.cmp wz0 c i1 i2)) wz i i0
  
  (** val cmp_obligation_2 :
      comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_2 c wz i wz0 i0 = function
    | true -> cmp_obligation_1 c wz i wz0 i0
    | false -> Vundef
  
  (** val cmp_obligation_3 :
      comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_3 =
    cmp_obligation_2
  
  (** val cmp_obligation_4 :
      comparison -> nat -> Int.int -> block -> Int.int -> cmp_comp **)
  
  let cmp_obligation_4 c wz i b i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 b0 i2 ->
      if Int.eq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
           i1
           (Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))
      then cmp_mismatch c
      else Vundef) wz i b i0
  
  (** val cmp_obligation_5 :
      comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_5 c wz i b i0 = function
    | true -> cmp_obligation_4 c wz i b i0
    | false -> Vundef
  
  (** val cmp_obligation_6 :
      comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_6 =
    cmp_obligation_5
  
  (** val cmp_obligation_7 :
      comparison -> nat -> Int.int -> Int.int -> cmp_comp **)
  
  let cmp_obligation_7 c wz i i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 i2 -> Vundef) wz i i0
  
  (** val cmp_obligation_8 :
      comparison -> nat -> Int.int -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_8 c wz i i0 = function
    | true -> cmp_obligation_7 c wz i i0
    | false -> Vundef
  
  (** val cmp_obligation_9 :
      comparison -> nat -> Int.int -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_9 =
    cmp_obligation_8
  
  (** val cmp_obligation_10 :
      comparison -> nat -> Int.int -> coq_val -> cmp_comp **)
  
  let cmp_obligation_10 c wz i = function
    | Vint (wz0, i0) -> cmp_obligation_3 c wz i wz0 i0 (eq_nat_dec wz wz0)
    | Vptr (b, i0) ->
        cmp_obligation_6 c wz i b i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vinttoptr i0 ->
        cmp_obligation_9 c wz i i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val cmp_obligation_11 :
      comparison -> block -> Int.int -> nat -> Int.int -> cmp_comp **)
  
  let cmp_obligation_11 c b i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 ->
      if Int.eq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
           i1
           (Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))
      then cmp_mismatch c
      else Vundef) wz i0
  
  (** val cmp_obligation_12 :
      comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_12 c b i wz i0 = function
    | true -> cmp_obligation_11 c b i wz i0
    | false -> Vundef
  
  (** val cmp_obligation_13 :
      comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_13 =
    cmp_obligation_12
  
  (** val cmp_obligation_14 :
      comparison -> block -> Int.int -> coq_val -> cmp_comp **)
  
  let cmp_obligation_14 c b i = function
    | Vint (wz, i0) ->
        cmp_obligation_13 c b i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vptr (b0, i0) ->
        if zeq b b0
        then of_bool
               (Int.cmp (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O))))))))))))))))))))))))))))))) c i i0)
        else cmp_mismatch c
    | _ -> Vundef
  
  (** val cmp_obligation_15 :
      comparison -> Int.int -> nat -> Int.int -> cmp_comp **)
  
  let cmp_obligation_15 c i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 -> Vundef) wz i0
  
  (** val cmp_obligation_16 :
      comparison -> Int.int -> nat -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_16 c i wz i0 = function
    | true -> cmp_obligation_15 c i wz i0
    | false -> Vundef
  
  (** val cmp_obligation_17 :
      comparison -> Int.int -> nat -> Int.int -> bool -> cmp_comp **)
  
  let cmp_obligation_17 =
    cmp_obligation_16
  
  (** val cmp_obligation_18 :
      comparison -> Int.int -> coq_val -> cmp_comp **)
  
  let cmp_obligation_18 c i = function
    | Vint (wz, i0) ->
        cmp_obligation_17 c i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vinttoptr i0 ->
        of_bool
          (Int.cmp (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) c i i0)
    | _ -> Vundef
  
  (** val cmp_obligation_19 :
      comparison -> coq_val -> coq_val -> cmp_comp **)
  
  let cmp_obligation_19 c = function
    | Vint (wz, i) -> cmp_obligation_10 c wz i
    | Vptr (b, i) -> cmp_obligation_14 c b i
    | Vinttoptr i -> cmp_obligation_18 c i
    | _ -> (fun v2 -> Vundef)
  
  (** val cmp : comparison -> coq_val -> coq_val -> cmp_comp **)
  
  let cmp =
    cmp_obligation_19
  
  (** val coq_FunctionalInduction_cmp :
      (comparison -> coq_val -> coq_val -> cmp_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_cmp =
    Build_FunctionalInduction
  
  type cmpu_comp = coq_val
  
  (** val cmpu_comp_proj :
      comparison -> coq_val -> coq_val -> cmpu_comp -> cmpu_comp **)
  
  let cmpu_comp_proj c v1 v2 comp =
    comp
  
  (** val cmpu_obligation_1 :
      comparison -> nat -> Int.int -> nat -> Int.int -> cmpu_comp **)
  
  let cmpu_obligation_1 c wz i wz0 i0 =
    solution_left wz0 (fun i1 i2 -> of_bool (Int.cmpu wz0 c i1 i2)) wz i i0
  
  (** val cmpu_obligation_2 :
      comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_2 c wz i wz0 i0 = function
    | true -> cmpu_obligation_1 c wz i wz0 i0
    | false -> Vundef
  
  (** val cmpu_obligation_3 :
      comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_3 =
    cmpu_obligation_2
  
  (** val cmpu_obligation_4 :
      comparison -> nat -> Int.int -> block -> Int.int -> cmpu_comp **)
  
  let cmpu_obligation_4 c wz i b i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 b0 i2 ->
      if Int.eq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
           i1
           (Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))
      then cmp_mismatch c
      else Vundef) wz i b i0
  
  (** val cmpu_obligation_5 :
      comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_5 c wz i b i0 = function
    | true -> cmpu_obligation_4 c wz i b i0
    | false -> Vundef
  
  (** val cmpu_obligation_6 :
      comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_6 =
    cmpu_obligation_5
  
  (** val cmpu_obligation_7 :
      comparison -> nat -> Int.int -> Int.int -> cmpu_comp **)
  
  let cmpu_obligation_7 c wz i i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 i2 -> Vundef) wz i i0
  
  (** val cmpu_obligation_8 :
      comparison -> nat -> Int.int -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_8 c wz i i0 = function
    | true -> cmpu_obligation_7 c wz i i0
    | false -> Vundef
  
  (** val cmpu_obligation_9 :
      comparison -> nat -> Int.int -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_9 =
    cmpu_obligation_8
  
  (** val cmpu_obligation_10 :
      comparison -> nat -> Int.int -> coq_val -> cmpu_comp **)
  
  let cmpu_obligation_10 c wz i = function
    | Vint (wz0, i0) -> cmpu_obligation_3 c wz i wz0 i0 (eq_nat_dec wz wz0)
    | Vptr (b, i0) ->
        cmpu_obligation_6 c wz i b i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vinttoptr i0 ->
        cmpu_obligation_9 c wz i i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | _ -> Vundef
  
  (** val cmpu_obligation_11 :
      comparison -> block -> Int.int -> nat -> Int.int -> cmpu_comp **)
  
  let cmpu_obligation_11 c b i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 ->
      if Int.eq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
           i1
           (Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))
      then cmp_mismatch c
      else Vundef) wz i0
  
  (** val cmpu_obligation_12 :
      comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_12 c b i wz i0 = function
    | true -> cmpu_obligation_11 c b i wz i0
    | false -> Vundef
  
  (** val cmpu_obligation_13 :
      comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_13 =
    cmpu_obligation_12
  
  (** val cmpu_obligation_14 :
      comparison -> block -> Int.int -> coq_val -> cmpu_comp **)
  
  let cmpu_obligation_14 c b i = function
    | Vint (wz, i0) ->
        cmpu_obligation_13 c b i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vptr (b0, i0) ->
        if zeq b b0
        then of_bool
               (Int.cmpu (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 O))))))))))))))))))))))))))))))) c i i0)
        else cmp_mismatch c
    | _ -> Vundef
  
  (** val cmpu_obligation_15 :
      comparison -> Int.int -> nat -> Int.int -> cmpu_comp **)
  
  let cmpu_obligation_15 c i wz i0 =
    solution_left (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (fun i1 -> Vundef) wz i0
  
  (** val cmpu_obligation_16 :
      comparison -> Int.int -> nat -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_16 c i wz i0 = function
    | true -> cmpu_obligation_15 c i wz i0
    | false -> Vundef
  
  (** val cmpu_obligation_17 :
      comparison -> Int.int -> nat -> Int.int -> bool -> cmpu_comp **)
  
  let cmpu_obligation_17 =
    cmpu_obligation_16
  
  (** val cmpu_obligation_18 :
      comparison -> Int.int -> coq_val -> cmpu_comp **)
  
  let cmpu_obligation_18 c i = function
    | Vint (wz, i0) ->
        cmpu_obligation_17 c i wz i0
          (eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))
    | Vinttoptr i0 ->
        of_bool
          (Int.cmpu (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) c i i0)
    | _ -> Vundef
  
  (** val cmpu_obligation_19 :
      comparison -> coq_val -> coq_val -> cmpu_comp **)
  
  let cmpu_obligation_19 c = function
    | Vint (wz, i) -> cmpu_obligation_10 c wz i
    | Vptr (b, i) -> cmpu_obligation_14 c b i
    | Vinttoptr i -> cmpu_obligation_18 c i
    | _ -> (fun v2 -> Vundef)
  
  (** val cmpu : comparison -> coq_val -> coq_val -> cmpu_comp **)
  
  let cmpu =
    cmpu_obligation_19
  
  (** val coq_FunctionalInduction_cmpu :
      (comparison -> coq_val -> coq_val -> cmpu_comp) coq_FunctionalInduction **)
  
  let coq_FunctionalInduction_cmpu =
    Build_FunctionalInduction
  
  (** val cmpf : comparison -> coq_val -> coq_val -> coq_val **)
  
  let cmpf c v1 v2 =
    match v1 with
      | Vfloat f1 ->
          (match v2 with
             | Vfloat f2 -> of_bool (Float.cmp c f1 f2)
             | _ -> Vundef)
      | _ -> Vundef
  
  (** val load_result : memory_chunk -> coq_val -> coq_val **)
  
  let load_result chunk v =
    match chunk with
      | Mint wz ->
          (match v with
             | Vundef -> Vundef
             | Vint (wz2, n) -> Vint (wz, (Int.repr wz (Int.unsigned wz2 n)))
             | Vfloat f -> Vundef
             | x ->
                 if eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O)))))))))))))))))))))))))))))))
                 then x
                 else Vundef)
      | Mfloat32 ->
          (match v with
             | Vfloat f -> Vfloat (Float.singleoffloat f)
             | _ -> Vundef)
      | Mfloat64 -> (match v with
                       | Vfloat f -> Vfloat f
                       | _ -> Vundef)
  
  (** val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)
  
  let eq_rew_r_dep x y hC =
    hC
  
  (** val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2 **)
  
  let eq_rew_dep x f y =
    f
 end

type meminj = block -> (block*coq_Z) option

