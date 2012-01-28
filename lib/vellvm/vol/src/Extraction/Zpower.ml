open BinInt
open BinPos
open Datatypes
open Wf_nat
open Zmisc

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Zpower_nat : coq_Z -> nat -> coq_Z **)

let coq_Zpower_nat z n =
  iter_nat n (fun x -> coq_Zmult z x) (Zpos Coq_xH)

(** val shift_nat : nat -> positive -> positive **)

let shift_nat n z =
  iter_nat n (fun x -> Coq_xO x) z

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n z =
  iter_pos n (fun x -> Coq_xO x) z

(** val shift : coq_Z -> positive -> positive **)

let shift n z =
  match n with
    | Zpos p -> iter_pos p (fun x -> Coq_xO x) z
    | _ -> z

(** val two_power_nat : nat -> coq_Z **)

let two_power_nat n =
  Zpos (shift_nat n Coq_xH)

(** val two_power_pos : positive -> coq_Z **)

let two_power_pos x =
  Zpos (shift_pos x Coq_xH)

(** val two_p : coq_Z -> coq_Z **)

let two_p = function
  | Z0 -> Zpos Coq_xH
  | Zpos y -> two_power_pos y
  | Zneg y -> Z0

(** val coq_Zdiv_rest_aux : ((coq_Z*coq_Z)*coq_Z) -> (coq_Z*coq_Z)*coq_Z **)

let coq_Zdiv_rest_aux = function
  | qr,d ->
      let q,r = qr in
      (match q with
         | Z0 -> Z0,r
         | Zpos p ->
             (match p with
                | Coq_xI n -> (Zpos n),(coq_Zplus d r)
                | Coq_xO n -> (Zpos n),r
                | Coq_xH -> Z0,(coq_Zplus d r))
         | Zneg p ->
             (match p with
                | Coq_xI n ->
                    (coq_Zminus (Zneg n) (Zpos Coq_xH)),
                    (coq_Zplus d r)
                | Coq_xO n -> (Zneg n),r
                | Coq_xH -> (Zneg Coq_xH),(coq_Zplus d r))),
      (coq_Zmult (Zpos (Coq_xO Coq_xH)) d)

(** val coq_Zdiv_rest : coq_Z -> positive -> coq_Z*coq_Z **)

let coq_Zdiv_rest x p =
  let qr,d = iter_pos p coq_Zdiv_rest_aux ((x,Z0),(Zpos Coq_xH)) in qr

type coq_Zdiv_rest_proofs =
  | Zdiv_rest_proof of coq_Z * coq_Z

(** val coq_Zdiv_rest_proofs_rect :
    coq_Z -> positive -> (coq_Z -> coq_Z -> __ -> __ -> __ -> 'a1) ->
    coq_Zdiv_rest_proofs -> 'a1 **)

let coq_Zdiv_rest_proofs_rect x p f = function
  | Zdiv_rest_proof (x0, x1) -> f x0 x1 __ __ __

(** val coq_Zdiv_rest_proofs_rec :
    coq_Z -> positive -> (coq_Z -> coq_Z -> __ -> __ -> __ -> 'a1) ->
    coq_Zdiv_rest_proofs -> 'a1 **)

let coq_Zdiv_rest_proofs_rec x p f = function
  | Zdiv_rest_proof (x0, x1) -> f x0 x1 __ __ __

(** val coq_Zdiv_rest_correct : coq_Z -> positive -> coq_Zdiv_rest_proofs **)

let coq_Zdiv_rest_correct x p =
  let x0,x1 = iter_pos p coq_Zdiv_rest_aux ((x,Z0),(Zpos Coq_xH)) in
  let x2,x3 = x0 in Zdiv_rest_proof (x2, x3)

