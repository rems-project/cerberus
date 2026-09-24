include Lem_errors

type cause =
  | CPP of string (* NOTE: this is an empty string when piping to stderr *) (* BACKEND ONLY *)
  | CPARSER of cparser_cause (* BACKEND ONLY *)
  | EXTENSION of extension_cause
  | DESUGAR of desugar_cause
  | AIL_TYPING of TypingError.typing_error
  | CORE_PARSER of core_parser_cause (* BACKEND ONLY *)
  | CORE_TYPING of core_typing_cause
  | CORE_LINKING of core_linking_cause
  | CORE_RUN of core_run_cause
  | DRIVER of driver_cause (* BACKEND ONLY *)
  | UNSUPPORTED of string (* BACKEND ONLY *)
  | INTERNAL_ERROR of internal_error

type error = Cerb_location.t * cause

let extension_error loc cause = (loc, EXTENSION cause)
let desugar_error loc cause = (loc, DESUGAR cause)
let ail_typing_error loc cause = (loc, AIL_TYPING cause)
let core_typing_error loc cause = (loc, CORE_TYPING cause)
let linking_error loc cause = (loc, CORE_LINKING cause)
let core_run_error loc cause = (loc, CORE_RUN cause)
let internal_error loc err = (loc, INTERNAL_ERROR err)

let match_internal_error = function
  | (_, INTERNAL_ERROR err) -> Some err
  | _ -> None
