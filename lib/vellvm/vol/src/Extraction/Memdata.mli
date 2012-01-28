open AST
open BinInt
open BinPos
open Compare_dec
open Coqlib
open Datatypes
open EqNat
open Integers
open List0
open Peano_dec
open Values
open Zdiv

val coq_Mint32 : memory_chunk

val bytesize_chunk : nat -> coq_Z

val bytesize_chunk_nat : nat -> nat

val size_chunk : memory_chunk -> coq_Z

val size_chunk_nat : memory_chunk -> nat

val align_chunk : memory_chunk -> coq_Z

type memval =
  | Undef
  | Byte of nat * Int.int
  | Pointer of block * Int.int * nat
  | IPointer of Int.int * nat

val memval_rect :
  'a1 -> (nat -> Int.int -> 'a1) -> (block -> Int.int -> nat -> 'a1) ->
  (Int.int -> nat -> 'a1) -> memval -> 'a1

val memval_rec :
  'a1 -> (nat -> Int.int -> 'a1) -> (block -> Int.int -> nat -> 'a1) ->
  (Int.int -> nat -> 'a1) -> memval -> 'a1

val bytes_of_int : nat -> coq_Z -> Int.int list

val int_of_bytes : Int.int list -> coq_Z

val big_endian : bool

val rev_if_be : 'a1 list -> 'a1 list

val encode_int : memory_chunk -> nat -> Int.int -> Int.int list

val decode_int : nat -> Int.int list -> Int.int

val decode_float32 : Int.int list -> Int.int

val decode_float64 : Int.int list -> Int.int

val encode_float : memory_chunk -> float -> Int.int list

val decode_float : memory_chunk -> Int.int list -> float

val inj_bytes : nat -> Int.int list -> memval list

val proj_bytes : nat -> memval list -> Int.int list option

val inj_pointer : nat -> block -> Int.int -> memval list

val check_pointer : nat -> block -> Int.int -> memval list -> bool

val proj_pointer : memval list -> coq_val

val inj_ipointer : nat -> Int.int -> memval list

val check_ipointer : nat -> Int.int -> memval list -> bool

val proj_ipointer : memval list -> coq_val

val wz_of_chunk : memory_chunk -> nat

val encode_val : memory_chunk -> coq_val -> memval list

val decode_val : memory_chunk -> memval list -> coq_val

val inject_id : meminj

