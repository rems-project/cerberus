type eval_mode =
  | Strict
  | Lazy

val eval
  :  ?mode:eval_mode ->
  ?prog5:unit Mucore.mu_file ->
  IndexTerms.t ->
  (IndexTerms.t, string) result

val partial_eval
  :  ?mode:eval_mode ->
  ?prog5:unit Mucore.mu_file ->
  IndexTerms.t ->
  IndexTerms.t
