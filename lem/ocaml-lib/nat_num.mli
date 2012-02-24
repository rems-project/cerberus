type num = int
val (<) : num -> num -> bool
val (<=) : num -> num -> bool
val (>) : num -> num -> bool
val (>=) : num -> num -> bool
val (+) : num -> num -> num
val (-) : num -> num -> num
val ( * ) : num -> num -> num
val (/) : num -> num -> num
val (%) : num -> num -> num
val ( ** ) : num -> num -> num
val num_of_int : int -> num
val int_of_num : num -> int
val string_of_num : num -> string
val num_of_string : string -> num
val compare_num : 'a -> 'a -> num
