module type Config = sig
  val warn_extra_semicolon : bool
  val cerb_conf : Cerb_frontend.Config.config
end

module Make(Conf: Config) : sig
  (** Parse a C translation unit from a file.
  The first argument is the name of the file to parse. *)
  val parse_from_channel :
    string ->
    ( Cerb_frontend.Cabs.translation_unit
    , Cerb_location.t * Cerb_frontend.Errors.cause ) Result.t

  (** Parse a C translation unit from the given string.
  When working with a pre-processed file, the name should be the name of the
  preprocessed file.  The original source name can be recovered from the
  pre-processing annotations. *)
  val parse_from_string :
    filename:string ->
    string ->
    ( Cerb_frontend.Cabs.translation_unit
    , Cerb_location.t * Cerb_frontend.Errors.cause ) Result.t
end