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

val eq_block : coq_Z -> coq_Z -> bool

type coq_val =
  | Vundef
  | Vint of nat * Int.int
  | Vfloat of float
  | Vptr of block * Int.int
  | Vinttoptr of Int.int

val val_rect :
  'a1 -> (nat -> Int.int -> 'a1) -> (float -> 'a1) -> (block -> Int.int ->
  'a1) -> (Int.int -> 'a1) -> coq_val -> 'a1

val val_rec :
  'a1 -> (nat -> Int.int -> 'a1) -> (float -> 'a1) -> (block -> Int.int ->
  'a1) -> (Int.int -> 'a1) -> coq_val -> 'a1

val zero : nat -> Int.int

val one : nat -> Int.int

val mone : nat -> Int.int

val coq_Vzero : nat -> coq_val

val coq_Vone : nat -> coq_val

val coq_Vmone : nat -> coq_val

val coq_Vtrue : coq_val

val coq_Vfalse : coq_val

module Val : 
 sig 
  val eq : coq_val -> coq_val -> bool
  
  val get_wordsize : coq_val -> nat option
  
  val of_bool : bool -> coq_val
  
  val neg : coq_val -> coq_val
  
  val negf : coq_val -> coq_val
  
  val absf : coq_val -> coq_val
  
  val trunc : coq_val -> nat -> coq_val
  
  val ftrunc : coq_val -> coq_val
  
  val intoffloat : coq_val -> coq_val
  
  val intuoffloat : coq_val -> coq_val
  
  val floatofint : coq_val -> coq_val
  
  val floatofintu : coq_val -> coq_val
  
  val floatofwords : coq_val -> coq_val -> coq_val
  
  val notint : coq_val -> coq_val
  
  val notbool : coq_val -> coq_val
  
  val zero_ext : coq_Z -> coq_val -> coq_val
  
  val sign_ext : coq_Z -> coq_val -> coq_val
  
  val singleoffloat : coq_val -> coq_val
  
  type add_comp = coq_val
  
  val add_comp_proj : coq_val -> coq_val -> add_comp -> add_comp
  
  val add_obligation_1 : nat -> Int.int -> nat -> Int.int -> add_comp
  
  val add_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> add_comp
  
  val add_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> add_comp
  
  val add_obligation_4 : nat -> Int.int -> block -> Int.int -> add_comp
  
  val add_obligation_5 :
    nat -> Int.int -> block -> Int.int -> bool -> add_comp
  
  val add_obligation_6 :
    nat -> Int.int -> block -> Int.int -> bool -> add_comp
  
  val add_obligation_7 : nat -> Int.int -> Int.int -> add_comp
  
  val add_obligation_8 : nat -> Int.int -> Int.int -> bool -> add_comp
  
  val add_obligation_9 : nat -> Int.int -> Int.int -> bool -> add_comp
  
  val add_obligation_10 : nat -> Int.int -> coq_val -> add_comp
  
  val add_obligation_11 : block -> Int.int -> nat -> Int.int -> add_comp
  
  val add_obligation_12 :
    block -> Int.int -> nat -> Int.int -> bool -> add_comp
  
  val add_obligation_13 :
    block -> Int.int -> nat -> Int.int -> bool -> add_comp
  
  val add_obligation_14 : block -> Int.int -> coq_val -> add_comp
  
  val add_obligation_15 : Int.int -> nat -> Int.int -> add_comp
  
  val add_obligation_16 : Int.int -> nat -> Int.int -> bool -> add_comp
  
  val add_obligation_17 : Int.int -> nat -> Int.int -> bool -> add_comp
  
  val add_obligation_18 : Int.int -> coq_val -> add_comp
  
  val add_obligation_19 : coq_val -> coq_val -> add_comp
  
  val add : coq_val -> coq_val -> add_comp
  
  val coq_FunctionalInduction_add :
    (coq_val -> coq_val -> add_comp) coq_FunctionalInduction
  
  type sub_comp = coq_val
  
  val sub_comp_proj : coq_val -> coq_val -> sub_comp -> sub_comp
  
  val sub_obligation_1 : nat -> Int.int -> nat -> Int.int -> sub_comp
  
  val sub_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> sub_comp
  
  val sub_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> sub_comp
  
  val sub_obligation_4 : nat -> Int.int -> coq_val -> sub_comp
  
  val sub_obligation_5 : block -> Int.int -> nat -> Int.int -> sub_comp
  
  val sub_obligation_6 :
    block -> Int.int -> nat -> Int.int -> bool -> sub_comp
  
  val sub_obligation_7 :
    block -> Int.int -> nat -> Int.int -> bool -> sub_comp
  
  val sub_obligation_8 : block -> Int.int -> coq_val -> sub_comp
  
  val sub_obligation_9 : Int.int -> nat -> Int.int -> sub_comp
  
  val sub_obligation_10 : Int.int -> nat -> Int.int -> bool -> sub_comp
  
  val sub_obligation_11 : Int.int -> nat -> Int.int -> bool -> sub_comp
  
  val sub_obligation_12 : Int.int -> coq_val -> sub_comp
  
  val sub_obligation_13 : coq_val -> coq_val -> sub_comp
  
  val sub : coq_val -> coq_val -> sub_comp
  
  val coq_FunctionalInduction_sub :
    (coq_val -> coq_val -> sub_comp) coq_FunctionalInduction
  
  type mul_comp = coq_val
  
  val mul_comp_proj : coq_val -> coq_val -> mul_comp -> mul_comp
  
  val mul_obligation_1 : nat -> Int.int -> nat -> Int.int -> mul_comp
  
  val mul_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> mul_comp
  
  val mul_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> mul_comp
  
  val mul_obligation_4 : nat -> Int.int -> coq_val -> mul_comp
  
  val mul_obligation_5 : coq_val -> coq_val -> mul_comp
  
  val mul : coq_val -> coq_val -> mul_comp
  
  val coq_FunctionalInduction_mul :
    (coq_val -> coq_val -> mul_comp) coq_FunctionalInduction
  
  type divs_comp = coq_val
  
  val divs_comp_proj : coq_val -> coq_val -> divs_comp -> divs_comp
  
  val divs_obligation_1 : nat -> Int.int -> nat -> Int.int -> divs_comp
  
  val divs_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> divs_comp
  
  val divs_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> divs_comp
  
  val divs_obligation_4 : nat -> Int.int -> coq_val -> divs_comp
  
  val divs_obligation_5 : coq_val -> coq_val -> divs_comp
  
  val divs : coq_val -> coq_val -> divs_comp
  
  val coq_FunctionalInduction_divs :
    (coq_val -> coq_val -> divs_comp) coq_FunctionalInduction
  
  type mods_comp = coq_val
  
  val mods_comp_proj : coq_val -> coq_val -> mods_comp -> mods_comp
  
  val mods_obligation_1 : nat -> Int.int -> nat -> Int.int -> mods_comp
  
  val mods_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> mods_comp
  
  val mods_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> mods_comp
  
  val mods_obligation_4 : nat -> Int.int -> coq_val -> mods_comp
  
  val mods_obligation_5 : coq_val -> coq_val -> mods_comp
  
  val mods : coq_val -> coq_val -> mods_comp
  
  val coq_FunctionalInduction_mods :
    (coq_val -> coq_val -> mods_comp) coq_FunctionalInduction
  
  type divu_comp = coq_val
  
  val divu_comp_proj : coq_val -> coq_val -> divu_comp -> divu_comp
  
  val divu_obligation_1 : nat -> Int.int -> nat -> Int.int -> divu_comp
  
  val divu_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> divu_comp
  
  val divu_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> divu_comp
  
  val divu_obligation_4 : nat -> Int.int -> coq_val -> divu_comp
  
  val divu_obligation_5 : coq_val -> coq_val -> divu_comp
  
  val divu : coq_val -> coq_val -> divu_comp
  
  val coq_FunctionalInduction_divu :
    (coq_val -> coq_val -> divu_comp) coq_FunctionalInduction
  
  type modu_comp = coq_val
  
  val modu_comp_proj : coq_val -> coq_val -> modu_comp -> modu_comp
  
  val modu_obligation_1 : nat -> Int.int -> nat -> Int.int -> modu_comp
  
  val modu_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> modu_comp
  
  val modu_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> modu_comp
  
  val modu_obligation_4 : nat -> Int.int -> coq_val -> modu_comp
  
  val modu_obligation_5 : coq_val -> coq_val -> modu_comp
  
  val modu : coq_val -> coq_val -> modu_comp
  
  val coq_FunctionalInduction_modu :
    (coq_val -> coq_val -> modu_comp) coq_FunctionalInduction
  
  type and_comp = coq_val
  
  val and_comp_proj : coq_val -> coq_val -> and_comp -> and_comp
  
  val and_obligation_1 : nat -> Int.int -> nat -> Int.int -> and_comp
  
  val and_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> and_comp
  
  val and_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> and_comp
  
  val and_obligation_4 : nat -> Int.int -> coq_val -> and_comp
  
  val and_obligation_5 : coq_val -> coq_val -> and_comp
  
  val coq_and : coq_val -> coq_val -> and_comp
  
  val coq_FunctionalInduction_and :
    (coq_val -> coq_val -> and_comp) coq_FunctionalInduction
  
  type or_comp = coq_val
  
  val or_comp_proj : coq_val -> coq_val -> or_comp -> or_comp
  
  val or_obligation_1 : nat -> Int.int -> nat -> Int.int -> or_comp
  
  val or_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> or_comp
  
  val or_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> or_comp
  
  val or_obligation_4 : nat -> Int.int -> coq_val -> or_comp
  
  val or_obligation_5 : coq_val -> coq_val -> or_comp
  
  val coq_or : coq_val -> coq_val -> or_comp
  
  val coq_FunctionalInduction_or :
    (coq_val -> coq_val -> or_comp) coq_FunctionalInduction
  
  type xor_comp = coq_val
  
  val xor_comp_proj : coq_val -> coq_val -> xor_comp -> xor_comp
  
  val xor_obligation_1 : nat -> Int.int -> nat -> Int.int -> xor_comp
  
  val xor_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> xor_comp
  
  val xor_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> xor_comp
  
  val xor_obligation_4 : nat -> Int.int -> coq_val -> xor_comp
  
  val xor_obligation_5 : coq_val -> coq_val -> xor_comp
  
  val xor : coq_val -> coq_val -> xor_comp
  
  val coq_FunctionalInduction_xor :
    (coq_val -> coq_val -> xor_comp) coq_FunctionalInduction
  
  type shl_comp = coq_val
  
  val shl_comp_proj : coq_val -> coq_val -> shl_comp -> shl_comp
  
  val shl_obligation_1 : nat -> Int.int -> nat -> Int.int -> shl_comp
  
  val shl_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> shl_comp
  
  val shl_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> shl_comp
  
  val shl_obligation_4 : nat -> Int.int -> coq_val -> shl_comp
  
  val shl_obligation_5 : coq_val -> coq_val -> shl_comp
  
  val shl : coq_val -> coq_val -> shl_comp
  
  val coq_FunctionalInduction_shl :
    (coq_val -> coq_val -> shl_comp) coq_FunctionalInduction
  
  type shr_comp = coq_val
  
  val shr_comp_proj : coq_val -> coq_val -> shr_comp -> shr_comp
  
  val shr_obligation_1 : nat -> Int.int -> nat -> Int.int -> shr_comp
  
  val shr_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> shr_comp
  
  val shr_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> shr_comp
  
  val shr_obligation_4 : nat -> Int.int -> coq_val -> shr_comp
  
  val shr_obligation_5 : coq_val -> coq_val -> shr_comp
  
  val shr : coq_val -> coq_val -> shr_comp
  
  val coq_FunctionalInduction_shr :
    (coq_val -> coq_val -> shr_comp) coq_FunctionalInduction
  
  type shr_carry_comp = coq_val
  
  val shr_carry_comp_proj :
    coq_val -> coq_val -> shr_carry_comp -> shr_carry_comp
  
  val shr_carry_obligation_1 :
    nat -> Int.int -> nat -> Int.int -> shr_carry_comp
  
  val shr_carry_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> shr_carry_comp
  
  val shr_carry_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> shr_carry_comp
  
  val shr_carry_obligation_4 : nat -> Int.int -> coq_val -> shr_carry_comp
  
  val shr_carry_obligation_5 : coq_val -> coq_val -> shr_carry_comp
  
  val shr_carry : coq_val -> coq_val -> shr_carry_comp
  
  val coq_FunctionalInduction_shr_carry :
    (coq_val -> coq_val -> shr_carry_comp) coq_FunctionalInduction
  
  type shrx_comp = coq_val
  
  val shrx_comp_proj : coq_val -> coq_val -> shrx_comp -> shrx_comp
  
  val shrx_obligation_1 : nat -> Int.int -> nat -> Int.int -> shrx_comp
  
  val shrx_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> shrx_comp
  
  val shrx_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> shrx_comp
  
  val shrx_obligation_4 : nat -> Int.int -> coq_val -> shrx_comp
  
  val shrx_obligation_5 : coq_val -> coq_val -> shrx_comp
  
  val shrx : coq_val -> coq_val -> shrx_comp
  
  val coq_FunctionalInduction_shrx :
    (coq_val -> coq_val -> shrx_comp) coq_FunctionalInduction
  
  type shru_comp = coq_val
  
  val shru_comp_proj : coq_val -> coq_val -> shru_comp -> shru_comp
  
  val shru_obligation_1 : nat -> Int.int -> nat -> Int.int -> shru_comp
  
  val shru_obligation_2 :
    nat -> Int.int -> nat -> Int.int -> bool -> shru_comp
  
  val shru_obligation_3 :
    nat -> Int.int -> nat -> Int.int -> bool -> shru_comp
  
  val shru_obligation_4 : nat -> Int.int -> coq_val -> shru_comp
  
  val shru_obligation_5 : coq_val -> coq_val -> shru_comp
  
  val shru : coq_val -> coq_val -> shru_comp
  
  val coq_FunctionalInduction_shru :
    (coq_val -> coq_val -> shru_comp) coq_FunctionalInduction
  
  val rolm : coq_val -> Int.int -> Int.int -> coq_val
  
  type ror_comp = coq_val
  
  val ror_comp_proj : coq_val -> coq_val -> ror_comp -> ror_comp
  
  val ror_obligation_1 : nat -> Int.int -> nat -> Int.int -> ror_comp
  
  val ror_obligation_2 : nat -> Int.int -> nat -> Int.int -> bool -> ror_comp
  
  val ror_obligation_3 : nat -> Int.int -> nat -> Int.int -> bool -> ror_comp
  
  val ror_obligation_4 : nat -> Int.int -> coq_val -> ror_comp
  
  val ror_obligation_5 : coq_val -> coq_val -> ror_comp
  
  val ror : coq_val -> coq_val -> ror_comp
  
  val coq_FunctionalInduction_ror :
    (coq_val -> coq_val -> ror_comp) coq_FunctionalInduction
  
  val addf : coq_val -> coq_val -> coq_val
  
  val subf : coq_val -> coq_val -> coq_val
  
  val mulf : coq_val -> coq_val -> coq_val
  
  val divf : coq_val -> coq_val -> coq_val
  
  val modf : coq_val -> coq_val -> coq_val
  
  val cmp_mismatch : comparison -> coq_val
  
  type cmp_comp = coq_val
  
  val cmp_comp_proj :
    comparison -> coq_val -> coq_val -> cmp_comp -> cmp_comp
  
  val cmp_obligation_1 :
    comparison -> nat -> Int.int -> nat -> Int.int -> cmp_comp
  
  val cmp_obligation_2 :
    comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_3 :
    comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_4 :
    comparison -> nat -> Int.int -> block -> Int.int -> cmp_comp
  
  val cmp_obligation_5 :
    comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_6 :
    comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_7 : comparison -> nat -> Int.int -> Int.int -> cmp_comp
  
  val cmp_obligation_8 :
    comparison -> nat -> Int.int -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_9 :
    comparison -> nat -> Int.int -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_10 : comparison -> nat -> Int.int -> coq_val -> cmp_comp
  
  val cmp_obligation_11 :
    comparison -> block -> Int.int -> nat -> Int.int -> cmp_comp
  
  val cmp_obligation_12 :
    comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_13 :
    comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_14 :
    comparison -> block -> Int.int -> coq_val -> cmp_comp
  
  val cmp_obligation_15 : comparison -> Int.int -> nat -> Int.int -> cmp_comp
  
  val cmp_obligation_16 :
    comparison -> Int.int -> nat -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_17 :
    comparison -> Int.int -> nat -> Int.int -> bool -> cmp_comp
  
  val cmp_obligation_18 : comparison -> Int.int -> coq_val -> cmp_comp
  
  val cmp_obligation_19 : comparison -> coq_val -> coq_val -> cmp_comp
  
  val cmp : comparison -> coq_val -> coq_val -> cmp_comp
  
  val coq_FunctionalInduction_cmp :
    (comparison -> coq_val -> coq_val -> cmp_comp) coq_FunctionalInduction
  
  type cmpu_comp = coq_val
  
  val cmpu_comp_proj :
    comparison -> coq_val -> coq_val -> cmpu_comp -> cmpu_comp
  
  val cmpu_obligation_1 :
    comparison -> nat -> Int.int -> nat -> Int.int -> cmpu_comp
  
  val cmpu_obligation_2 :
    comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_3 :
    comparison -> nat -> Int.int -> nat -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_4 :
    comparison -> nat -> Int.int -> block -> Int.int -> cmpu_comp
  
  val cmpu_obligation_5 :
    comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_6 :
    comparison -> nat -> Int.int -> block -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_7 :
    comparison -> nat -> Int.int -> Int.int -> cmpu_comp
  
  val cmpu_obligation_8 :
    comparison -> nat -> Int.int -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_9 :
    comparison -> nat -> Int.int -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_10 :
    comparison -> nat -> Int.int -> coq_val -> cmpu_comp
  
  val cmpu_obligation_11 :
    comparison -> block -> Int.int -> nat -> Int.int -> cmpu_comp
  
  val cmpu_obligation_12 :
    comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_13 :
    comparison -> block -> Int.int -> nat -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_14 :
    comparison -> block -> Int.int -> coq_val -> cmpu_comp
  
  val cmpu_obligation_15 :
    comparison -> Int.int -> nat -> Int.int -> cmpu_comp
  
  val cmpu_obligation_16 :
    comparison -> Int.int -> nat -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_17 :
    comparison -> Int.int -> nat -> Int.int -> bool -> cmpu_comp
  
  val cmpu_obligation_18 : comparison -> Int.int -> coq_val -> cmpu_comp
  
  val cmpu_obligation_19 : comparison -> coq_val -> coq_val -> cmpu_comp
  
  val cmpu : comparison -> coq_val -> coq_val -> cmpu_comp
  
  val coq_FunctionalInduction_cmpu :
    (comparison -> coq_val -> coq_val -> cmpu_comp) coq_FunctionalInduction
  
  val cmpf : comparison -> coq_val -> coq_val -> coq_val
  
  val load_result : memory_chunk -> coq_val -> coq_val
  
  val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2
  
  val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
 end

type meminj = block -> (block*coq_Z) option

