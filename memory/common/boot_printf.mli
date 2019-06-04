type formatting = {
  basis:     AilSyntax.basis option;
  use_upper: bool;
}

val pseudo_printf: string -> (formatting * Core_ctype.ctype0) list * (string list -> string)
