open Cerb_frontend

type 'a cn_injection =
  { filename : string; (** The file we are going to be injecting into *)
    program : 'a AilSyntax.ail_program;
    (** The processed form of the program in [filename].
        This is used to find the locations of the symbols in [pre_post]. *)
    pre_post : (Symbol.sym * (string list * string list)) list;
    (** Pre- and post-condition checks to inject for the given symbols.
        The locations of the symbols are found by consulting [program]. *)
    in_stmt : (Cerb_location.t * string list) list;
    (** Additional statement injections to insert at the given locations. *)
    returns : (Cerb_location.t * 'a AilSyntax.expression option * string list) list;
    (** Injections to add when a function returns. *)
    inject_in_preproc : bool
    (** Should we inject using pre-processed locations (true) or not (false). *)
  }

(** [output_injections oc inj] performs the injections specified by [inj]
    and outputs them to channel [oc] *)
val output_injections
  :  Stdlib.out_channel ->
  'a cn_injection ->
  (unit, string) Result.result
