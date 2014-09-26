val ($): ('a -> 'b) -> 'a -> 'b
(* val (|-): ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c *)
val (-|): ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c
(* let (>?>) x b f g = if b then f x else g x *)


(*
(* Requires ocaml at least 4.00.0 *)
(* let (|>) x f = f x *)
external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply"
*)


type execution_mode =
  | Interactive
  | Exhaustive
  | Random

(* val string_of_execution_mode: execution_mode -> string *)

type language =
  | Cabs
  | Ail
  | Core

(* val string_of_language: language -> string *)


type cerberus_conf = {
  cpp_cmd:       string;
  pps:           language list;
  core_stdlib:   unit Core.fun_map;
  core_impl:     unit Core.impl;
  core_parser:   Input.t -> (Core_parser_util.result, Errors.t9) Exception.t2;
  exec_mode_opt: execution_mode option;
  progress:      bool
}

val (!!): (unit -> 'a) ref -> 'a

val cerb_conf: (unit -> cerberus_conf) ref

val set_cerb_conf:
    string ->
    language list ->
    unit Core.fun_map ->
    unit Core.impl ->
    bool ->
    execution_mode ->
    (Input.t -> (Core_parser_util.result, Errors.t9) Exception.t2) ->
    bool ->
    unit

(* print an error fatal message and exit with a given code (default is 1) *)
val error: ?code:int -> string -> 'a

val debug_level: int ref
val progress_sofar: int ref


val print_success: string -> unit
val print_debug: int -> string -> unit

(* val print_deubg2: string -> 'a -> 'a *)

val output_string2: string -> unit (* TODO: rename *)


(* let pass_through        f = Exception.fmap (fun v ->           f v        ; v) *)
val pass_through_test: bool -> ('a -> unit) -> ('a, 'msg) Exception.t2 -> ('a, 'msg) Exception.t2
val pass_message: string -> ('a, 'msg) Exception.t2 -> ('a, 'msg) Exception.t2
(* let return_none m         = Exception.bind0 m (fun _ -> Exception.return0 None) *)
(* let return_empty m        = Exception.bind0 m (fun _ -> Exception.return0 []) *)

(* let return_value m        = Exception.bind0 m (fun _ -> Exception.return0 []) *)
