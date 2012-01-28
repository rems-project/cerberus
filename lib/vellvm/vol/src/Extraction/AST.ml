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

(** val ident_eq : positive -> positive -> bool **)

let ident_eq =
  peq

type typ =
  | Tint
  | Tfloat

(** val typ_rect : 'a1 -> 'a1 -> typ -> 'a1 **)

let typ_rect f f0 = function
  | Tint -> f
  | Tfloat -> f0

(** val typ_rec : 'a1 -> 'a1 -> typ -> 'a1 **)

let typ_rec f f0 = function
  | Tint -> f
  | Tfloat -> f0

(** val typesize : typ -> coq_Z **)

let typesize = function
  | Tint -> Zpos (Coq_xO (Coq_xO Coq_xH))
  | Tfloat -> Zpos (Coq_xO (Coq_xO (Coq_xO Coq_xH)))

(** val typ_eq : typ -> typ -> bool **)

let typ_eq t1 t2 =
  match t1 with
    | Tint -> (match t2 with
                 | Tint -> true
                 | Tfloat -> false)
    | Tfloat -> (match t2 with
                   | Tint -> false
                   | Tfloat -> true)

(** val opt_typ_eq : typ option -> typ option -> bool **)

let opt_typ_eq t1 t2 =
  match t1 with
    | Some x -> (match t2 with
                   | Some t -> typ_eq x t
                   | None -> false)
    | None -> (match t2 with
                 | Some t -> false
                 | None -> true)

type signature = { sig_args : typ list; sig_res : typ option }

(** val signature_rect :
    (typ list -> typ option -> 'a1) -> signature -> 'a1 **)

let signature_rect f s =
  let { sig_args = x; sig_res = x0 } = s in f x x0

(** val signature_rec :
    (typ list -> typ option -> 'a1) -> signature -> 'a1 **)

let signature_rec f s =
  let { sig_args = x; sig_res = x0 } = s in f x x0

(** val sig_args : signature -> typ list **)

let sig_args x = x.sig_args

(** val sig_res : signature -> typ option **)

let sig_res x = x.sig_res

(** val proj_sig_res : signature -> typ **)

let proj_sig_res s =
  match s.sig_res with
    | Some t -> t
    | None -> Tint

type memory_chunk =
  | Mint of nat
  | Mfloat32
  | Mfloat64

(** val memory_chunk_rect :
    (nat -> 'a1) -> 'a1 -> 'a1 -> memory_chunk -> 'a1 **)

let memory_chunk_rect f f0 f1 = function
  | Mint x -> f x
  | Mfloat32 -> f0
  | Mfloat64 -> f1

(** val memory_chunk_rec :
    (nat -> 'a1) -> 'a1 -> 'a1 -> memory_chunk -> 'a1 **)

let memory_chunk_rec f f0 f1 = function
  | Mint x -> f x
  | Mfloat32 -> f0
  | Mfloat64 -> f1

(** val memory_chunk_eq : memory_chunk -> memory_chunk -> bool **)

let memory_chunk_eq c1 c2 =
  match c1 with
    | Mint n1 -> (match c2 with
                    | Mint n2 -> beq_nat n1 n2
                    | _ -> false)
    | Mfloat32 -> (match c2 with
                     | Mfloat32 -> true
                     | _ -> false)
    | Mfloat64 -> (match c2 with
                     | Mfloat64 -> true
                     | _ -> false)

(** val type_of_chunk : memory_chunk -> typ **)

let type_of_chunk = function
  | Mint n -> Tint
  | _ -> Tfloat

type init_data =
  | Init_int8 of Int.int
  | Init_int16 of Int.int
  | Init_int32 of Int.int
  | Init_float32 of float
  | Init_float64 of float
  | Init_space of coq_Z
  | Init_addrof of ident * Int.int

(** val init_data_rect :
    (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int.int -> 'a1) -> (float ->
    'a1) -> (float -> 'a1) -> (coq_Z -> 'a1) -> (ident -> Int.int -> 'a1) ->
    init_data -> 'a1 **)

let init_data_rect f f0 f1 f2 f3 f4 f5 = function
  | Init_int8 x -> f x
  | Init_int16 x -> f0 x
  | Init_int32 x -> f1 x
  | Init_float32 x -> f2 x
  | Init_float64 x -> f3 x
  | Init_space x -> f4 x
  | Init_addrof (x, x0) -> f5 x x0

(** val init_data_rec :
    (Int.int -> 'a1) -> (Int.int -> 'a1) -> (Int.int -> 'a1) -> (float ->
    'a1) -> (float -> 'a1) -> (coq_Z -> 'a1) -> (ident -> Int.int -> 'a1) ->
    init_data -> 'a1 **)

let init_data_rec f f0 f1 f2 f3 f4 f5 = function
  | Init_int8 x -> f x
  | Init_int16 x -> f0 x
  | Init_int32 x -> f1 x
  | Init_float32 x -> f2 x
  | Init_float64 x -> f3 x
  | Init_space x -> f4 x
  | Init_addrof (x, x0) -> f5 x x0

type 'v globvar = { gvar_info : 'v; gvar_init : init_data list;
                    gvar_readonly : bool; gvar_volatile : 
                    bool }

(** val globvar_rect :
    ('a1 -> init_data list -> bool -> bool -> 'a2) -> 'a1 globvar -> 'a2 **)

let globvar_rect f g =
  let { gvar_info = x; gvar_init = x0; gvar_readonly = x1; gvar_volatile =
    x2 } = g
  in
  f x x0 x1 x2

(** val globvar_rec :
    ('a1 -> init_data list -> bool -> bool -> 'a2) -> 'a1 globvar -> 'a2 **)

let globvar_rec f g =
  let { gvar_info = x; gvar_init = x0; gvar_readonly = x1; gvar_volatile =
    x2 } = g
  in
  f x x0 x1 x2

(** val gvar_info : 'a1 globvar -> 'a1 **)

let gvar_info x = x.gvar_info

(** val gvar_init : 'a1 globvar -> init_data list **)

let gvar_init x = x.gvar_init

(** val gvar_readonly : 'a1 globvar -> bool **)

let gvar_readonly x = x.gvar_readonly

(** val gvar_volatile : 'a1 globvar -> bool **)

let gvar_volatile x = x.gvar_volatile

type ('f, 'v) program = { prog_funct : (ident*'f) list; prog_main : 
                          ident; prog_vars : (ident*'v globvar) list }

(** val program_rect :
    ((ident*'a1) list -> ident -> (ident*'a2 globvar) list -> 'a3) -> ('a1,
    'a2) program -> 'a3 **)

let program_rect f p =
  let { prog_funct = x; prog_main = x0; prog_vars = x1 } = p in f x x0 x1

(** val program_rec :
    ((ident*'a1) list -> ident -> (ident*'a2 globvar) list -> 'a3) -> ('a1,
    'a2) program -> 'a3 **)

let program_rec f p =
  let { prog_funct = x; prog_main = x0; prog_vars = x1 } = p in f x x0 x1

(** val prog_funct : ('a1, 'a2) program -> (ident*'a1) list **)

let prog_funct x = x.prog_funct

(** val prog_main : ('a1, 'a2) program -> ident **)

let prog_main x = x.prog_main

(** val prog_vars : ('a1, 'a2) program -> (ident*'a2 globvar) list **)

let prog_vars x = x.prog_vars

(** val prog_funct_names : ('a1, 'a2) program -> ident list **)

let prog_funct_names p =
  map fst p.prog_funct

(** val prog_var_names : ('a1, 'a2) program -> ident list **)

let prog_var_names p =
  map fst p.prog_vars

(** val transf_program :
    ('a1 -> 'a2) -> (ident*'a1) list -> (ident*'a2) list **)

let transf_program transf l =
  map (fun id_fn -> (fst id_fn),(transf (snd id_fn))) l

(** val transform_program :
    ('a1 -> 'a2) -> ('a1, 'a3) program -> ('a2, 'a3) program **)

let transform_program transf p =
  { prog_funct = (transf_program transf p.prog_funct); prog_main =
    p.prog_main; prog_vars = p.prog_vars }

(** val map_partial :
    ('a1 -> errmsg) -> ('a2 -> 'a3 res) -> ('a1*'a2) list -> ('a1*'a3) list
    res **)

let rec map_partial prefix_errmsg f = function
  | [] -> OK []
  | p::rem ->
      let a,b = p in
      (match f b with
         | OK c ->
             bind (map_partial prefix_errmsg f rem) (fun rem' -> OK
               ((a,c)::rem'))
         | Error msg -> Error (app (prefix_errmsg a) msg))

(** val prefix_name : ident -> errmsg **)

let prefix_name id =
  (MSG (String ((Ascii (true, false, false, true, false, false, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), (String ((Ascii (false, true, true, false, false, true, true,
    false)), (String ((Ascii (true, false, true, false, true, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (true, true, false, false, false, true, true,
    false)), (String ((Ascii (false, false, true, false, true, true, true,
    false)), (String ((Ascii (true, false, false, true, false, true, true,
    false)), (String ((Ascii (true, true, true, true, false, true, true,
    false)), (String ((Ascii (false, true, true, true, false, true, true,
    false)), (String ((Ascii (false, false, false, false, false, true, false,
    false)), EmptyString)))))))))))))))))))))))))::((CTX id)::((MSG (String
    ((Ascii (false, true, false, true, true, true, false, false)), (String
    ((Ascii (false, false, false, false, false, true, false, false)),
    EmptyString)))))::[]))

(** val transform_partial_program :
    ('a1 -> 'a2 res) -> ('a1, 'a3) program -> ('a2, 'a3) program res **)

let transform_partial_program transf_partial p =
  bind (map_partial prefix_name transf_partial p.prog_funct) (fun fl -> OK
    { prog_funct = fl; prog_main = p.prog_main; prog_vars = p.prog_vars })

(** val transf_globvar :
    ('a1 -> 'a2 res) -> 'a1 globvar -> 'a2 globvar res **)

let transf_globvar transf_partial_variable g =
  bind (transf_partial_variable g.gvar_info) (fun info' -> OK { gvar_info =
    info'; gvar_init = g.gvar_init; gvar_readonly = g.gvar_readonly;
    gvar_volatile = g.gvar_volatile })

(** val transform_partial_program2 :
    ('a1 -> 'a2 res) -> ('a3 -> 'a4 res) -> ('a1, 'a3) program -> ('a2, 'a4)
    program res **)

let transform_partial_program2 transf_partial_function transf_partial_variable p =
  bind (map_partial prefix_name transf_partial_function p.prog_funct)
    (fun fl ->
    bind
      (map_partial prefix_name (transf_globvar transf_partial_variable)
        p.prog_vars) (fun vl -> OK { prog_funct = fl; prog_main =
      p.prog_main; prog_vars = vl }))

type external_function = { ef_id : ident; ef_sig : 
                           signature; ef_inline : bool }

(** val external_function_rect :
    (ident -> signature -> bool -> 'a1) -> external_function -> 'a1 **)

let external_function_rect f e =
  let { ef_id = x; ef_sig = x0; ef_inline = x1 } = e in f x x0 x1

(** val external_function_rec :
    (ident -> signature -> bool -> 'a1) -> external_function -> 'a1 **)

let external_function_rec f e =
  let { ef_id = x; ef_sig = x0; ef_inline = x1 } = e in f x x0 x1

(** val ef_id : external_function -> ident **)

let ef_id x = x.ef_id

(** val ef_sig : external_function -> signature **)

let ef_sig x = x.ef_sig

(** val ef_inline : external_function -> bool **)

let ef_inline x = x.ef_inline

type 'f fundef =
  | Internal of 'f
  | External of external_function

(** val fundef_rect :
    ('a1 -> 'a2) -> (external_function -> 'a2) -> 'a1 fundef -> 'a2 **)

let fundef_rect f f0 = function
  | Internal x -> f x
  | External x -> f0 x

(** val fundef_rec :
    ('a1 -> 'a2) -> (external_function -> 'a2) -> 'a1 fundef -> 'a2 **)

let fundef_rec f f0 = function
  | Internal x -> f x
  | External x -> f0 x

(** val transf_fundef : ('a1 -> 'a2) -> 'a1 fundef -> 'a2 fundef **)

let transf_fundef transf = function
  | Internal f -> Internal (transf f)
  | External ef -> External ef

(** val transf_partial_fundef :
    ('a1 -> 'a2 res) -> 'a1 fundef -> 'a2 fundef res **)

let transf_partial_fundef transf_partial = function
  | Internal f -> bind (transf_partial f) (fun f' -> OK (Internal f'))
  | External ef -> OK (External ef)

