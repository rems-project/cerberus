module Identifier : sig
  type t = { loc : Cerb_location.t; str : string; }
  val mk : Cerb_location.t -> string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
  val get_loc : t -> Cerb_location.t
  val freshify : t -> int -> t
end

module Sym : sig
  type description =
    | SD_None
    | SD_unnamed_tag of Cerb_location.t
    | SD_Id of string
    | SD_CN_Id of string
    | SD_ObjectAddress of string
    | SD_Return
    | SD_FunArgValue of string
    | SD_FunArg of Cerb_location.t * int

  val show_description : description -> string

  type t = {
    tunit: string;
    id: int;
    desc: description;
  }

  val mk : string -> int -> description -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int

  val show : t -> string
  val show_raw : t -> string

  val match_id : t -> string option

  val get_desc : t -> description
  val set_desc : t -> description -> t

  val from_same_translation_unit : t -> t -> bool

  val fresh : unit -> t
  val fresh_pretty : string -> t
  val fresh_cn : string -> t
  val fresh_pretty_with_id : (int -> string) -> t
  val fresh_funarg : Cerb_location.t -> int -> t
  val fresh_with_description : description -> t
  val fresh_object_address : string -> t
  val fresh_unnamed_tag : Cerb_location.t -> t

  val empty_pmap : (t, 'a) Pmap.map
  end

type prefix =
  | PrefSource of Cerb_location.t * Sym.t list
  | PrefFunArg of Cerb_location.t * string * int
  | PrefStringLiteral of Cerb_location.t * string
  | PrefCompoundLiteral of Cerb_location.t * string
  | PrefMalloc
  | PrefTemporaryLifetime of Cerb_location.t * string
  | PrefOther of string

val mk_funarg_prefix : Cerb_location.t -> int -> prefix
val compound_literal_prefix : Cerb_location.t -> Sym.t -> prefix
val source_prefix : Cerb_location.t -> Sym.t list -> prefix
val temporary_lifetime_prefix : Cerb_location.t -> Sym.t -> prefix
val string_literal_prefix : Cerb_location.t -> Sym.t -> prefix
val other_prefix : string -> prefix
