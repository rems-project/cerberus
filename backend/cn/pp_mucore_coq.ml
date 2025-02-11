(* Converts a list of ResourceInferenceStep.t to a Coq formatted string.
   It uses Pp.resource_inference_step_to_coq to convert an individual step. *)
let pp_resource_inference_steps steps =
  let header = "(* Begin Resource Inference Steps *)\n" in
  let footer = "(* End Resource Inference Steps *)\n" in
  let body = String.concat "\n" (List.map Pp.resource_inference_step_to_coq steps) in
  header ^ body ^ "\n" ^ footer

(* Combines the mucore file document with resource inference steps.
   It first calls pp_unit_file to get the Coq document for the mucore file
   and then appends the resource inference steps. *)
let pp_unit_file_with_resource_inference prog5 steps =
  let mucore_doc = pp_unit_file prog5 in
  let rsteps_doc = pp_resource_inference_steps steps in
  mucore_doc ^ "\n" ^ rsteps_doc 