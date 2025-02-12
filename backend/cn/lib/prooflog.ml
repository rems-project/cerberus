type resource_inference_type =
  | PredicateRequest of
      Error_common.situation
      * Request.Predicate.t
      * (Locations.t * string) option
      * (Resource.predicate * int list)

(** Info about what happened *)
type log_entry =
  | ResourceInferenceStep of (Context.t * resource_inference_type * Context.t)

type log = log_entry list (* most recent first *)

(* list of log entries *)
let proof_log = ref []

let add_log_entry entry = proof_log := entry :: !proof_log

let get_proof_log () = !proof_log

let record_resource_inference_step
  (c : Context.t)
  (c' : Context.t)
  (ri : resource_inference_type)
  : unit
  =
  add_log_entry (ResourceInferenceStep (c, ri, c'))
