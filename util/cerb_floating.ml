let less_than f1 f2 =
  Float.compare f1 f2 < 0

let less_equal f1 f2 =
  Float.compare f1 f2 <= 0

external round_double_to_float32: Float.t -> Float.t = "round_double_to_float32"
