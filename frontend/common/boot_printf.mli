type formatting = {
  basis:     AilSyntax.basis option;
  use_upper: bool;
}

val pseudo_printf: string -> (formatting * Ctype.ctype) list * (string list -> string)
