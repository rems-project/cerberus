type resource_inference_type =
  | PredicateRequest of
      Error_common.situation
      * Request.Predicate.t
      * (Cerb_location.t * string) option
      * (Resource.predicate * int list)

type log_entry =
  | ResourceInferenceStep of (Context.t * resource_inference_type * Context.t)

type log = log_entry list

val add_log_entry : log_entry -> unit

val get_proof_log : unit -> log_entry list

val record_resource_inference_step
  :  Context.t ->
  Context.t ->
  resource_inference_type ->
  unit
