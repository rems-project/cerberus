open BinInt
open BinPos
open Coqlib
open Datatypes
open List0
open Zdiv
open Zpower

type __ = Obj.t

type comparison =
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge

val comparison_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1

val comparison_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> comparison -> 'a1

val negate_comparison : comparison -> comparison

val swap_comparison : comparison -> comparison

module Int : 
 sig 
  val wordsize : nat -> nat
  
  val modulus : nat -> coq_Z
  
  val half_modulus : nat -> coq_Z
  
  val max_unsigned : nat -> coq_Z
  
  val max_signed : nat -> coq_Z
  
  val min_signed : nat -> coq_Z
  
  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)
  
  val int_rect : nat -> (coq_Z -> __ -> 'a1) -> int -> 'a1
  
  val int_rec : nat -> (coq_Z -> __ -> 'a1) -> int -> 'a1
  
  val intval : nat -> int -> coq_Z
  
  val unsigned : nat -> int -> coq_Z
  
  val signed : nat -> int -> coq_Z
  
  val repr : nat -> coq_Z -> int
  
  val zero : nat -> int
  
  val one : nat -> int
  
  val mone : nat -> int
  
  val iwordsize : nat -> int
  
  val eq_dec : nat -> int -> int -> bool
  
  val eq : nat -> int -> int -> bool
  
  val lt : nat -> int -> int -> bool
  
  val ltu : nat -> int -> int -> bool
  
  val neg : nat -> int -> int
  
  val add : nat -> int -> int -> int
  
  val sub : nat -> int -> int -> int
  
  val mul : nat -> int -> int -> int
  
  val coq_Zdiv_round : coq_Z -> coq_Z -> coq_Z
  
  val coq_Zmod_round : coq_Z -> coq_Z -> coq_Z
  
  val divs : nat -> int -> int -> int
  
  val mods : nat -> int -> int -> int
  
  val divu : nat -> int -> int -> int
  
  val modu : nat -> int -> int -> int
  
  val coq_Z_shift_add : bool -> coq_Z -> coq_Z
  
  val coq_Z_bin_decomp : coq_Z -> bool*coq_Z
  
  val bits_of_Z : nat -> coq_Z -> coq_Z -> bool
  
  val coq_Z_of_bits : nat -> (coq_Z -> bool) -> coq_Z -> coq_Z
  
  val bitwise_binop : nat -> (bool -> bool -> bool) -> int -> int -> int
  
  val coq_and : nat -> int -> int -> int
  
  val coq_or : nat -> int -> int -> int
  
  val xor : nat -> int -> int -> int
  
  val not : nat -> int -> int
  
  val shl : nat -> int -> int -> int
  
  val shru : nat -> int -> int -> int
  
  val shr : nat -> int -> int -> int
  
  val shrx : nat -> int -> int -> int
  
  val shr_carry : nat -> int -> int -> int
  
  val rol : nat -> int -> int -> int
  
  val ror : nat -> int -> int -> int
  
  val rolm : nat -> int -> int -> int -> int
  
  val zero_ext : nat -> coq_Z -> int -> int
  
  val sign_ext : nat -> coq_Z -> int -> int
  
  val coq_Z_one_bits : nat -> coq_Z -> coq_Z -> coq_Z list
  
  val one_bits : nat -> int -> int list
  
  val is_power2 : nat -> int -> int option
  
  val cmp : nat -> comparison -> int -> int -> bool
  
  val cmpu : nat -> comparison -> int -> int -> bool
  
  val notbool : nat -> int -> int
  
  val powerserie : coq_Z list -> coq_Z
  
  val int_of_one_bits : nat -> int list -> int
 end

