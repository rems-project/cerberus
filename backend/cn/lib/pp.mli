(* Module Pp -- Pretty printing *)

(* TODO: BCP: This file could still use some thinning and reorganization! *)
(* TODO: DCM: I suspect one way to proceed might be to have pp.ml be just include PPrint
   (or delete it and get users to rename it wherever it is used). Everything else that's
   currently in pp.ml could be turned into pp_utils.ml *)

type document = PPrint.document

module Infix : sig
  val ( ^^ ) : document -> document -> document

  val ( !^ ) : string -> document

  val ( ^/^ ) : document -> document -> document

  val ( ^//^ ) : document -> document -> document

  val ( ^^^ ) : document -> document -> document
end

val empty : document

val char : char -> document

val string : string -> document

val substring : string -> int -> int -> document

val fancystring : string -> int -> document

val fancysubstring : string -> int -> int -> int -> document

val utf8string : string -> document

val utf8format : ('a, unit, string, document) format4 -> 'a

val hardline : document

val blank : int -> document

val space : document

val break : int -> document

val ( ^^ ) : document -> document -> document

val group : document -> document

val ifflat : document -> document -> document

val nest : int -> document -> document

val align : document -> document

val is_empty : document -> bool

type point = int * int

type range = point * point

val range : (range -> unit) -> document -> document

val lparen : document

val rparen : document

val lbrace : document

val rbrace : document

val lbracket : document

val rbracket : document

val squote : document

val dquote : document

val bquote : document

val semi : document

val colon : document

val comma : document

val dot : document

val sharp : document

val slash : document

val backslash : document

val equals : document

val qmark : document

val tilde : document

val at : document

val percent : document

val dollar : document

val caret : document

val ampersand : document

val star : document

val plus : document

val minus : document

val underscore : document

val bang : document

val bar : document

val precede : document -> document -> document

val terminate : document -> document -> document

val enclose : document -> document -> document -> document

val squotes : document -> document

val dquotes : document -> document

val bquotes : document -> document

val braces : document -> document

val parens : document -> document

val brackets : document -> document

val twice : document -> document

val repeat : int -> document -> document

val concat : document list -> document

val separate : document -> document list -> document

val concat_map : ('a -> document) -> 'a list -> document

val separate_map : document -> ('a -> document) -> 'a list -> document

val separate2 : document -> document -> document list -> document

val optional : ('a -> document) -> 'a option -> document

val lines : string -> document list

val arbitrary_string : string -> document

val words : string -> document list

val split : (char -> bool) -> string -> document list

val flow : document -> document list -> document

val flow_map : document -> ('a -> document) -> 'a list -> document

val url : string -> document

val hang : int -> document -> document

val prefix : int -> int -> document -> document -> document

val jump : int -> int -> document -> document

val infix : int -> int -> document -> document -> document -> document

val surround : int -> int -> document -> document -> document -> document

val soft_surround : int -> int -> document -> document -> document -> document

val surround_separate
  :  int ->
  int ->
  document ->
  document ->
  document ->
  document ->
  document list ->
  document

val surround_separate_map
  :  int ->
  int ->
  document ->
  document ->
  document ->
  document ->
  ('a -> document) ->
  'a list ->
  document

val ( !^ ) : string -> document

val ( ^/^ ) : document -> document -> document

val ( ^//^ ) : document -> document -> document

module OCaml = PPrint.OCaml

val term_col : int

val int : int -> document

val z : Z.t -> document

val bool : bool -> document

val html_escapes : bool ref

val unicode : bool ref

val print_level : int ref

val print_timestamps : bool ref

val html_langle : document

val html_rangle : document

val langle : unit -> document

val rangle : unit -> document

val angles : document -> document

val times : (out_channel * string * int) option ref

val wrap : string -> string

val write_time_log_start : string -> string -> unit

val write_time_log_end : float option -> unit

val write_time_log_final : unit -> unit

val maybe_open_times_channel : (string * String.t) option -> unit

val maybe_close_times_channel : unit -> unit

val print : PPrint.ToChannel.channel -> document -> unit

val print_file : string -> document -> unit

val plain : ?rfrac:float -> ?width:int -> PPrint.ToBuffer.document -> string

val ( ^^^ )
  :  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document

val format_string : Cerb_colour.ansi_format -> string -> string

val format : Cerb_colour.ansi_format -> string -> document

val uformat : Cerb_colour.ansi_format -> string -> int -> document

type alignment =
  | L
  | R

val pad_ : alignment -> int -> int -> document -> document

val pad : alignment -> int -> document -> document

val pad_string_ : alignment -> int -> int -> string -> string

val pad_string : alignment -> int -> string -> string

val list : ('a -> document) -> 'a list -> document

val list_filtered : ('a -> document option) -> 'a list -> document

val option : ('a -> document) -> string -> 'a option -> document

val typ
  :  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document

val infix_arrow
  :  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document

val item : string -> document -> document

val c_comment : document -> document

val c_app : document -> document list -> document

val ineq
  :  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document ->
  Cerb_pp_prelude.P.document

val headline : string -> document

val bold : string -> document

val action : string -> document

val debug : int -> document Lazy.t -> unit

val warn_noloc : Cerb_pp_prelude.P.document -> unit

val time_f_elapsed : ('a -> 'b) -> 'a -> float * 'b

val time_f_debug : int -> string -> ('a -> 'b) -> 'a -> 'b

val time_log_start : string -> string -> float

val time_log_end : float -> unit

val time_f_logs : Locations.t -> int -> string -> ('a -> 'b) -> 'a -> 'b

val error : Locations.t -> document -> document list -> unit

val warn : Locations.t -> Cerb_pp_prelude.P.document -> unit

val loc_headline : Locations.t -> Cerb_pp_prelude.P.document -> Cerb_pp_prelude.P.document

type loc_pp =
  | Hex
  | Dec

val loc_pp : loc_pp ref

val maybe_open_json_output : string option -> unit

val maybe_close_json_output : unit -> unit

val print_json : Yojson.Safe.t Lazy.t -> unit

val progress_simple : string -> string -> unit

val of_total : int -> int -> string
