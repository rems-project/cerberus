open Ascii
open BinInt
open BinPos
open Coqlib
open Datatypes
open EqNat
open Errors
open Integers
open List0
open String0

type ident = positive

val ident_eq : positive -> positive -> bool

type typ =
  | Tint
  | Tfloat

val typ_rect : 'a1 -> 'a1 -> typ -> 'a1

val typ_rec : 'a1 -> 'a1 -> typ -> 'a1

val typesize : typ -> coq_Z

val typ_eq : typ -> typ -> bool

val opt_typ_eq : typ option -> typ option -> bool

type signature = { sig_args : typ list; sig_res : typ option }

val signature_rect : (typ list -> typ option -> 'a1) -> signature -> 'a1

val signature_rec : (typ list -> typ option -> 'a1) -> signature -> 'a1

val sig_args : signature -> typ list

val sig_res : signature -> typ option

val proj_sig_res : signature -> typ

type memory_chunk =
  | Mint of nat
  | Mfloat32
  | Mfloat64

val memory_chunk_rect : (nat -> 'a1) -> 'a1 -> 'a1 -> memory_chunk -> 'a1

val memory_chunk_rec : (nat -> 'a1) -> 'a1 -> 'a1 -> memory_chunk -> 'a1

val memory_chunk_eq : memory_chunk -> memory_chunk -> bool

val type_of_chunk : memory_chunk -> typ

type init_data =
  | Init_int8 of Int.int
  | Init_int16 of Int.int
  | Init_int32 of Int.int
  | Init_float32 of float
  | Init_float64 of float
  | Init_space of coq_Z
  | Init_addrof of ident * Int.int

val init_data_rect :
  (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int.int -> 'a1) -> (float -> 'a1)
  -> (float -> 'a1) -> (coq_Z -> 'a1) -> (ident -> Int.int -> 'a1) ->
  init_data -> 'a1

val init_data_rec :
  (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int.int -> 'a1) -> (float -> 'a1)
  -> (float -> 'a1) -> (coq_Z -> 'a1) -> (ident -> Int.int -> 'a1) ->
  init_data -> 'a1

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : 
                    bool }

val globvar_rect :
  ('a1 -> init_data list -> bool -> bool -> 'a2) -> 'a1 globvar -> 'a2

val globvar_rec :
  ('a1 -> init_data list -> bool -> bool -> 'a2) -> 'a1 globvar -> 'a2

val gvar_info : 'a1 globvar -> 'a1

val gvar_init : 'a1 globvar -> init_data list

val gvar_readonly : 'a1 globvar -> bool

val gvar_volatile : 'a1 globvar -> bool

type ('f, 'v) program = { prog_funct : (ident*'f) list; prog_main : 
                          ident; prog_vars : (ident*'v globvar) list }

val program_rect :
  ((ident*'a1) list -> ident -> (ident*'a2 globvar) list -> 'a3) -> ('a1,
  'a2) program -> 'a3

val program_rec :
  ((ident*'a1) list -> ident -> (ident*'a2 globvar) list -> 'a3) -> ('a1,
  'a2) program -> 'a3

val prog_funct : ('a1, 'a2) program -> (ident*'a1) list

val prog_main : ('a1, 'a2) program -> ident

val prog_vars : ('a1, 'a2) program -> (ident*'a2 globvar) list

val prog_funct_names : ('a1, 'a2) program -> ident list

val prog_var_names : ('a1, 'a2) program -> ident list

val transf_program : ('a1 -> 'a2) -> (ident*'a1) list -> (ident*'a2) list

val transform_program :
  ('a1 -> 'a2) -> ('a1, 'a3) program -> ('a2, 'a3) program

val map_partial :
  ('a1 -> errmsg) -> ('a2 -> 'a3 res) -> ('a1*'a2) list -> ('a1*'a3) list res

val prefix_name : ident -> errmsg

val transform_partial_program :
  ('a1 -> 'a2 res) -> ('a1, 'a3) program -> ('a2, 'a3) program res

val transf_globvar : ('a1 -> 'a2 res) -> 'a1 globvar -> 'a2 globvar res

val transform_partial_program2 :
  ('a1 -> 'a2 res) -> ('a3 -> 'a4 res) -> ('a1, 'a3) program -> ('a2, 'a4)
  program res

type external_function = { ef_id : ident; ef_sig : 
                           signature; ef_inline : bool }

val external_function_rect :
  (ident -> signature -> bool -> 'a1) -> external_function -> 'a1

val external_function_rec :
  (ident -> signature -> bool -> 'a1) -> external_function -> 'a1

val ef_id : external_function -> ident

val ef_sig : external_function -> signature

val ef_inline : external_function -> bool

type 'f fundef =
  | Internal of 'f
  | External of external_function

val fundef_rect :
  ('a1 -> 'a2) -> (external_function -> 'a2) -> 'a1 fundef -> 'a2

val fundef_rec :
  ('a1 -> 'a2) -> (external_function -> 'a2) -> 'a1 fundef -> 'a2

val transf_fundef : ('a1 -> 'a2) -> 'a1 fundef -> 'a2 fundef

val transf_partial_fundef : ('a1 -> 'a2 res) -> 'a1 fundef -> 'a2 fundef res

