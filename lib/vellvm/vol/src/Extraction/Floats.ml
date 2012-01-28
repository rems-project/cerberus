open BinInt
open BinPos
open Datatypes
open Integers

module Float = 
 struct 
  (** val zero : float **)
  
  let zero = 0.
  
  (** val eq_dec : float -> float -> bool **)
  
  let eq_dec = fun (x: float) (y: float) -> x = y
  
  (** val neg : float -> float **)
  
  let neg = ( ~-. )
  
  (** val abs : float -> float **)
  
  let abs = abs_float
  
  (** val singleoffloat : float -> float **)
  
  let singleoffloat = Floataux.singleoffloat
  
  (** val intoffloat : float -> Int.int **)
  
  let intoffloat = Floataux.intoffloat
  
  (** val intuoffloat : float -> Int.int **)
  
  let intuoffloat = Floataux.intuoffloat
  
  (** val floatofint : Int.int -> float **)
  
  let floatofint = Floataux.floatofint
  
  (** val floatofintu : Int.int -> float **)
  
  let floatofintu = Floataux.floatofintu
  
  (** val add : float -> float -> float **)
  
  let add = ( +. )
  
  (** val sub : float -> float -> float **)
  
  let sub = ( -. )
  
  (** val mul : float -> float -> float **)
  
  let mul = ( *. )
  
  (** val div : float -> float -> float **)
  
  let div = ( /. )
  
  (** val rem : float -> float -> float **)
  
  let rem = mod_float
  
  (** val cmp : comparison -> float -> float -> bool **)
  
  let cmp = Floataux.cmp
  
  (** val bits_of_double : float -> Int.int **)
  
  let bits_of_double = Floataux.bits_of_double
  
  (** val double_of_bits : Int.int -> float **)
  
  let double_of_bits = Floataux.double_of_bits
  
  (** val bits_of_single : float -> Int.int **)
  
  let bits_of_single = Floataux.bits_of_single
  
  (** val single_of_bits : Int.int -> float **)
  
  let single_of_bits = Floataux.single_of_bits
  
  (** val from_words : Int.int -> Int.int -> float **)
  
  let from_words hi lo =
    double_of_bits
      (Int.coq_or (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (Int.shl (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))) hi))
          (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))
        (Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (Int.unsigned (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) lo)))
  
  (** val ox8000_0000 : Int.int **)
  
  let ox8000_0000 =
    Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
      (Int.half_modulus (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))
  
  (** val ox4330_0000 : Int.int **)
  
  let ox4330_0000 =
    Int.repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) (Zpos
      (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
      (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO (Coq_xI (Coq_xI (Coq_xO
      (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))))))))))))))))))))))))
 end

