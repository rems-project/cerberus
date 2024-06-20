(* Module SymPair -- TODO: BCP: What is it for?? *)

(* TODO: BCP: Some filenames use_underscores, while some areInCamlCase
   -- any compelling reason for that? *)

module SymPair :
  sig
    type t = Sym.t * Sym.t
    val compare :
      Sym.S.sym * Sym.S.sym ->
      Sym.S.sym * Sym.S.sym -> int
  end

(* TODO: BCP: All of the rest comes from `include Pset` in the .ml
   file.  I guess there should be an analogous signature include here,
   but I can't figure out where Pset comes from.  (In fact, I am not
   very clear on the purpose of this whole module.  The SymPair type
   seems to be the only thing it adds.) *)

type 'a set = 'a Pset.set
val is_empty : 'a set -> bool
val from_list : ('a -> 'a -> int) -> 'a list -> 'a set
val mem : 'a -> 'a set -> bool
val add : 'a -> 'a set -> 'a set
val singleton : ('a -> 'a -> int) -> 'a -> 'a set
val remove : 'a -> 'a set -> 'a set
val union : 'a set -> 'a set -> 'a set
val inter : 'a set -> 'a set -> 'a set
val diff : 'a set -> 'a set -> 'a set
val compare : 'a set -> 'a set -> int
val equal : 'a set -> 'a set -> bool
val subset : 'a set -> 'a set -> bool
val subset_proper : 'a set -> 'a set -> bool
val iter : ('a -> unit) -> 'a set -> unit
val fold : ('a -> 'b -> 'b) -> 'a set -> 'b -> 'b
val map : ('b -> 'b -> int) -> ('a -> 'b) -> 'a set -> 'b set
val map_union : ('b -> 'b -> int) -> ('a -> 'b set) -> 'a set -> 'b set
val for_all : ('a -> bool) -> 'a set -> bool
val exists : ('a -> bool) -> 'a set -> bool
val filter : ('a -> bool) -> 'a set -> 'a set
val partition : ('a -> bool) -> 'a set -> 'a set * 'a set
val cardinal : 'a set -> int
val elements : 'a set -> 'a list
val min_elt : 'a set -> 'a
val max_elt : 'a set -> 'a
val min_elt_opt : 'a set -> 'a option
val max_elt_opt : 'a set -> 'a option
val choose : 'a set -> 'a
val set_case : 'a set -> 'b -> ('a -> 'b) -> 'b -> 'b
val choose_and_split : 'a set -> ('a set * 'a * 'a set) option
val split : 'a -> 'a set -> 'a set * bool * 'a set
val comprehension1 :
  ('b -> 'b -> int) -> ('a -> 'b) -> ('a -> bool) -> 'a set -> 'b set
val comprehension2 :
  ('c -> 'c -> int) ->
  ('a -> 'b -> 'c) -> ('a -> 'b -> bool) -> 'a set -> 'b set -> 'c set
val comprehension3 :
  ('d -> 'd -> int) ->
  ('a -> 'b -> 'c -> 'd) ->
  ('a -> 'b -> 'c -> bool) -> 'a set -> 'b set -> 'c set -> 'd set
val comprehension4 :
  ('e -> 'e -> int) ->
  ('a -> 'b -> 'c -> 'd -> 'e) ->
  ('a -> 'b -> 'c -> 'd -> bool) ->
  'a set -> 'b set -> 'c set -> 'd set -> 'e set
val comprehension5 :
  ('f -> 'f -> int) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> bool) ->
  'a set -> 'b set -> 'c set -> 'd set -> 'e set -> 'f set
val comprehension6 :
  ('g -> 'g -> int) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> bool) ->
  'a set -> 'b set -> 'c set -> 'd set -> 'e set -> 'f set -> 'g set
val comprehension7 :
  ('h -> 'h -> int) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) ->
  ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> bool) ->
  'a set ->
  'b set -> 'c set -> 'd set -> 'e set -> 'f set -> 'g set -> 'h set
val bigunion : ('a -> 'a -> int) -> 'a set set -> 'a set
val lfp : 'a set -> ('a set -> 'a set) -> 'a set
val tc : ('a * 'a -> 'a * 'a -> int) -> ('a * 'a) set -> ('a * 'a) set
val sigma :
  ('a * 'b -> 'a * 'b -> int) -> 'a set -> ('a -> 'b set) -> ('a * 'b) set
val cross : ('a * 'b -> 'a * 'b -> int) -> 'a set -> 'b set -> ('a * 'b) set
val get_elem_compare : 'a set -> 'a -> 'a -> int
val compare_by : ('a -> 'a -> int) -> 'a set -> 'a set -> int
