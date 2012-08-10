module A = CpAil
module AC = CpAilConstraint
module AT = CpAilTypes

module AIC = CpAilIntegerConstraint

let conv_impl t const =
  let name = match t with
    | A.SIGNED A.ICHAR     -> "signed_char"
    | A.SIGNED A.SHORT     -> "signed_short"
    | A.SIGNED A.INT       -> "signed_int"
    | A.SIGNED A.LONG      -> "signed_long"
    | A.SIGNED A.LONG_LONG -> "signed_long_long"
    | A.BOOL | A.UNSIGNED _ ->
        invalid_arg "Signed integer type was expected." in
  AC.fn ("to_" ^ name) [const]

let min = function
  | A.BOOL                 -> AC.zero
  | A.SIGNED   A.ICHAR     -> AIC.schar_min
  | A.SIGNED   A.SHORT     -> AIC.shrt_min
  | A.SIGNED   A.INT       -> AIC.int_min
  | A.SIGNED   A.LONG      -> AIC.long_min
  | A.SIGNED   A.LONG_LONG -> AIC.llong_min
  | A.UNSIGNED A.ICHAR     -> AC.zero
  | A.UNSIGNED A.SHORT     -> AC.zero
  | A.UNSIGNED A.INT       -> AC.zero
  | A.UNSIGNED A.LONG      -> AC.zero
  | A.UNSIGNED A.LONG_LONG -> AC.zero

let max = function
  | A.BOOL                 -> AC.one
  | A.SIGNED   A.ICHAR     -> AIC.schar_max
  | A.SIGNED   A.SHORT     -> AIC.shrt_max
  | A.SIGNED   A.INT       -> AIC.int_max
  | A.SIGNED   A.LONG      -> AIC.long_max
  | A.SIGNED   A.LONG_LONG -> AIC.llong_max
  | A.UNSIGNED A.ICHAR     -> AIC.uchar_max
  | A.UNSIGNED A.SHORT     -> AIC.ushrt_max
  | A.UNSIGNED A.INT       -> AIC.uint_max
  | A.UNSIGNED A.LONG      -> AIC.ulong_max
  | A.UNSIGNED A.LONG_LONG -> AIC.ullong_max

let in_range_int t const = AC.conj (AC.le (min t) const) (AC.le const (max t))

let in_range t const = match t with
  | A.BASE (_, A.INTEGER i) -> in_range_int i const
  | _ -> invalid_arg "Not an integer type."

let min_range_of it =
  let module M = CpRange in
  match it with
  | A.BOOL -> M.bool
  | A.SIGNED A.ICHAR -> M.schar
  | A.SIGNED A.SHORT -> M.shrt
  | A.SIGNED A.INT -> M.int
  | A.SIGNED A.LONG -> M.long
  | A.SIGNED A.LONG_LONG -> M.llong
  | A.UNSIGNED A.ICHAR -> M.uchar
  | A.UNSIGNED A.SHORT -> M.ushrt
  | A.UNSIGNED A.INT -> M.uint
  | A.UNSIGNED A.LONG -> M.ulong
  | A.UNSIGNED A.LONG_LONG -> M.ullong

let conv_int_type i const =
  let a = AC.fresh_name () in
  let constr = match i with
    | A.BOOL -> AC.case (AC.eq AC.zero const) (AC.eq a AC.zero) (AC.eq a AC.one)
    | A.UNSIGNED _ as i -> AC.eq a (AC.modulo const (max i))
    | A.SIGNED _ as i ->
        AC.case (in_range_int i const)
          (AC.eq a const)
          (AC.eq a (conv_impl i const)) in
  let conv = AC.conv_int (min_range_of i) constr const in
  a, conv

let conv_int t const =
  match t with
  | A.BASE (_, A.INTEGER i) -> conv_int_type i const
  | _ -> invalid_arg "Not an integer type."

let conv t t' const =
  match t, t' with
  | _, A.BASE (_, A.INTEGER i) when AT.is_integer t ->
      conv_int_type i const
  | _ -> const, AC.tt

let size_int i = match i with
  | A.BOOL                 -> AIC.bool_size
  | A.SIGNED   A.ICHAR     -> AIC.schar_size
  | A.SIGNED   A.SHORT     -> AIC.shrt_size
  | A.SIGNED   A.INT       -> AIC.int_size
  | A.SIGNED   A.LONG      -> AIC.long_size
  | A.SIGNED   A.LONG_LONG -> AIC.llong_size
  | A.UNSIGNED A.ICHAR     -> AIC.uchar_size
  | A.UNSIGNED A.SHORT     -> AIC.ushrt_size
  | A.UNSIGNED A.INT       -> AIC.uint_size
  | A.UNSIGNED A.LONG      -> AIC.ulong_size
  | A.UNSIGNED A.LONG_LONG -> AIC.ullong_size


let size t = match t with
  | A.BASE (_, A.INTEGER i) -> size_int i

let align_int = function
  | A.BOOL                 -> AIC.bool_align
  | A.SIGNED   A.ICHAR     -> AIC.schar_align
  | A.SIGNED   A.SHORT     -> AIC.shrt_align
  | A.SIGNED   A.INT       -> AIC.int_align
  | A.SIGNED   A.LONG      -> AIC.long_align
  | A.SIGNED   A.LONG_LONG -> AIC.llong_align
  | A.UNSIGNED A.ICHAR     -> AIC.uchar_align
  | A.UNSIGNED A.SHORT     -> AIC.ushrt_align
  | A.UNSIGNED A.INT       -> AIC.uint_align
  | A.UNSIGNED A.LONG      -> AIC.ulong_align
  | A.UNSIGNED A.LONG_LONG -> AIC.ullong_align

let align t addr =
  let alignment = match t with
    | A.BASE (_, A.INTEGER i) -> (align_int i)
    | _ -> AC.one in
  AC.eq (AC.modulo addr alignment) AC.zero
