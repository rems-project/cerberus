type t

type op = Cons | Op of string

type context = 
  | Field
  | App_right
  | App_left
  | Infix_left of t
  | Infix_right of t
  | Delimited

type exp_kind =
  | App
  | Infix of t
  | Let
  | Atomic
        
type pat_context =
  | Plist
  | Pas_left
  | Pcons_left
  | Pcons_right
  | Pdelimited

type pat_kind =
  | Papp
  | Pas
  | Pcons
  | Patomic

val not_infix : t
val is_infix : t -> bool
val get_prec : op -> t
val get_prec_ocaml : op -> t
val get_prec_hol : op -> t
val get_prec_isa : op -> t
val needs_parens : context -> exp_kind -> bool
val pat_needs_parens : pat_context -> pat_kind -> bool
