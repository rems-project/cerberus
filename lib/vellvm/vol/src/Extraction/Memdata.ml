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

(** val coq_Mint32 : memory_chunk **)

let coq_Mint32 =
  Mint (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

(** val bytesize_chunk : nat -> coq_Z **)

let bytesize_chunk wz =
  coq_ZRdiv (coq_Z_of_nat (S wz)) (Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH))))

(** val bytesize_chunk_nat : nat -> nat **)

let bytesize_chunk_nat wz =
  nat_of_Z (bytesize_chunk wz)

(** val size_chunk : memory_chunk -> coq_Z **)

let size_chunk = function
  | Mint wz -> bytesize_chunk wz
  | Mfloat32 -> Zpos (Coq_xO (Coq_xO Coq_xH))
  | Mfloat64 -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))

(** val size_chunk_nat : memory_chunk -> nat **)

let size_chunk_nat chunk =
  nat_of_Z (size_chunk chunk)

(** val align_chunk : memory_chunk -> coq_Z **)

let align_chunk = function
  | Mint wz ->
      if le_lt_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))
      then bytesize_chunk wz
      else if zeq (bytesize_chunk wz) (Zpos (Coq_xO (Coq_xO (Coq_xO
                Coq_xH))))
           then Zpos (Coq_xO (Coq_xO Coq_xH))
           else Zpos Coq_xH
  | _ -> Zpos (Coq_xO (Coq_xO Coq_xH))

type memval =
  | Undef
  | Byte of nat * Int.int
  | Pointer of block * Int.int * nat
  | IPointer of Int.int * nat

(** val memval_rect :
    'a1 -> (nat -> Int.int -> 'a1) -> (block -> Int.int -> nat -> 'a1) ->
    (Int.int -> nat -> 'a1) -> memval -> 'a1 **)

let memval_rect f f0 f1 f2 = function
  | Undef -> f
  | Byte (x, x0) -> f0 x x0
  | Pointer (x, x0, x1) -> f1 x x0 x1
  | IPointer (x, x0) -> f2 x x0

(** val memval_rec :
    'a1 -> (nat -> Int.int -> 'a1) -> (block -> Int.int -> nat -> 'a1) ->
    (Int.int -> nat -> 'a1) -> memval -> 'a1 **)

let memval_rec f f0 f1 f2 = function
  | Undef -> f
  | Byte (x, x0) -> f0 x x0
  | Pointer (x, x0, x1) -> f1 x x0 x1
  | IPointer (x, x0) -> f2 x x0

(** val bytes_of_int : nat -> coq_Z -> Int.int list **)

let rec bytes_of_int n x =
  match n with
    | O -> []
    | S m ->
        (Int.repr (S (S (S (S (S (S (S O))))))) x)::
        (bytes_of_int m
          (coq_Zdiv x (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
            (Coq_xO (Coq_xO Coq_xH)))))))))))

(** val int_of_bytes : Int.int list -> coq_Z **)

let rec int_of_bytes = function
  | [] -> Z0
  | b::l' ->
      coq_Zplus (Int.unsigned (S (S (S (S (S (S (S O))))))) b)
        (coq_Zmult (int_of_bytes l') (Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))))))

(** val big_endian : bool **)

let big_endian = Memdataaux.big_endian

(** val rev_if_be : 'a1 list -> 'a1 list **)

let rev_if_be l =
  if big_endian then rev l else l

(** val encode_int : memory_chunk -> nat -> Int.int -> Int.int list **)

let encode_int c wz x =
  let n = Int.unsigned wz x in
  rev_if_be
    (match c with
       | Mint wz0 -> bytes_of_int (nat_of_Z (bytesize_chunk wz0)) n
       | Mfloat32 -> bytes_of_int (S (S (S (S O)))) Z0
       | Mfloat64 -> bytes_of_int (S (S (S (S (S (S (S (S O)))))))) Z0)

(** val decode_int : nat -> Int.int list -> Int.int **)

let decode_int wz b =
  let b' = rev_if_be b in Int.repr wz (int_of_bytes b')

(** val decode_float32 : Int.int list -> Int.int **)

let decode_float32 b =
  Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))

(** val decode_float64 : Int.int list -> Int.int **)

let decode_float64 b =
  Int.zero (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val encode_float : memory_chunk -> float -> Int.int list **)

let encode_float = Memdataaux.encode_float

(** val decode_float : memory_chunk -> Int.int list -> float **)

let decode_float = Memdataaux.decode_float

(** val inj_bytes : nat -> Int.int list -> memval list **)

let inj_bytes wz bl =
  map (fun x -> Byte (wz, x)) bl

(** val proj_bytes : nat -> memval list -> Int.int list option **)

let rec proj_bytes wz = function
  | [] -> Some []
  | m::vl' ->
      (match m with
         | Byte (wz0, b) ->
             if eq_nat_dec wz0 wz
             then (match proj_bytes wz vl' with
                     | Some bl -> Some (b::bl)
                     | None -> None)
             else None
         | _ -> None)

(** val inj_pointer : nat -> block -> Int.int -> memval list **)

let rec inj_pointer n b ofs =
  match n with
    | O -> []
    | S m -> (Pointer (b, ofs, m))::(inj_pointer m b ofs)

(** val check_pointer : nat -> block -> Int.int -> memval list -> bool **)

let rec check_pointer n b ofs vl =
  match n with
    | O -> (match vl with
              | [] -> true
              | m::l -> false)
    | S m ->
        (match vl with
           | [] -> false
           | m0::vl' ->
               (match m0 with
                  | Pointer (b', ofs', m') ->
                      if if if proj_sumbool (eq_block b b')
                            then proj_sumbool
                                   (Int.eq_dec (S (S (S (S (S (S (S (S (S (S
                                     (S (S (S (S (S (S (S (S (S (S (S (S (S
                                     (S (S (S (S (S (S (S (S
                                     O))))))))))))))))))))))))))))))) ofs
                                     ofs')
                            else false
                         then beq_nat m m'
                         else false
                      then check_pointer m b ofs vl'
                      else false
                  | _ -> false))

(** val proj_pointer : memval list -> coq_val **)

let proj_pointer vl = match vl with
  | [] -> Vundef
  | m::vl' ->
      (match m with
         | Pointer (b, ofs, n) ->
             if check_pointer (size_chunk_nat coq_Mint32) b ofs vl
             then Vptr (b, ofs)
             else Vundef
         | _ -> Vundef)

(** val inj_ipointer : nat -> Int.int -> memval list **)

let rec inj_ipointer n i =
  match n with
    | O -> []
    | S m -> (IPointer (i, m))::(inj_ipointer m i)

(** val check_ipointer : nat -> Int.int -> memval list -> bool **)

let rec check_ipointer n i vl =
  match n with
    | O -> (match vl with
              | [] -> true
              | m::l -> false)
    | S m ->
        (match vl with
           | [] -> false
           | m0::vl' ->
               (match m0 with
                  | IPointer (i', m') ->
                      if if proj_sumbool
                              (Int.eq_dec (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S O)))))))))))))))))))))))))))))))
                                i i')
                         then beq_nat m m'
                         else false
                      then check_ipointer m i vl'
                      else false
                  | _ -> false))

(** val proj_ipointer : memval list -> coq_val **)

let proj_ipointer vl = match vl with
  | [] -> Vundef
  | m::vl' ->
      (match m with
         | IPointer (i, n) ->
             if check_ipointer (size_chunk_nat coq_Mint32) i vl
             then Vinttoptr i
             else Vundef
         | _ -> Vundef)

(** val wz_of_chunk : memory_chunk -> nat **)

let wz_of_chunk = function
  | Mint wz -> wz
  | Mfloat32 -> S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))
  | Mfloat64 -> S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val encode_val : memory_chunk -> coq_val -> memval list **)

let encode_val chunk = function
  | Vundef -> list_repeat (size_chunk_nat chunk) Undef
  | Vint (wz, n) -> inj_bytes (wz_of_chunk chunk) (encode_int chunk wz n)
  | Vfloat f -> inj_bytes (wz_of_chunk chunk) (encode_float chunk f)
  | Vptr (b, ofs) ->
      (match chunk with
         | Mint wz ->
             if eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))
             then inj_pointer (size_chunk_nat coq_Mint32) b ofs
             else list_repeat (size_chunk_nat chunk) Undef
         | _ -> list_repeat (size_chunk_nat chunk) Undef)
  | Vinttoptr i ->
      (match chunk with
         | Mint wz ->
             if eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))
             then inj_ipointer (size_chunk_nat (Mint wz)) i
             else list_repeat (size_chunk_nat chunk) Undef
         | _ -> list_repeat (size_chunk_nat chunk) Undef)

(** val decode_val : memory_chunk -> memval list -> coq_val **)

let decode_val chunk vl =
  match proj_bytes (wz_of_chunk chunk) vl with
    | Some bl ->
        (match chunk with
           | Mint n -> Vint ((wz_of_chunk chunk),
               (decode_int (wz_of_chunk chunk) bl))
           | _ -> Vfloat (decode_float chunk bl))
    | None ->
        (match chunk with
           | Mint wz ->
               if eq_nat_dec wz (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))
               then (match proj_pointer vl with
                       | Vundef -> proj_ipointer vl
                       | x -> x)
               else Vundef
           | _ -> Vundef)

(** val inject_id : meminj **)

let inject_id b =
  Some (b,Z0)

