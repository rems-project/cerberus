exception TODO of string
module Duplicate(S : Set.S) : sig 
  type dups = 
    | No_dups of S.t
    | Has_dups of S.elt
  val duplicates : S.elt list -> dups
end
val compare_list : ('a -> 'b -> int) -> 'a list -> 'b list -> int
val map_changed : ('a -> 'a option) -> 'a list -> 'a list option
val option_map : ('a -> 'b) -> 'a option -> 'b option
val changed2 : ('a -> 'b -> 'c) -> ('a -> 'a option) -> 'a -> ('b -> 'b option) -> 'b -> 'c option
                                              
