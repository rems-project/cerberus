module Interval : sig
  (** A interval on integers *)
  type t [@@deriving eq, ord]

  (** Empty interval *)
  val empty : t

  (** A singleton interval containing just the given integer. *)
  val const : Z.t -> t

  (** Entire integer range *)
  val int : t

  (** Non-negative numbers *)
  val nat : t

  (** [uint n] is the interval for unsigned integers of [n] bits. [n >= 0] *)
  val uint : int -> t

  (** [sint n] is the interval for signed integers of [n] bits. [n >= 1] *)
  val sint : int -> t

  (** Integers less than the given one *)
  val lt : Z.t -> t

  (** Integers greater than the given one *)
  val gt : Z.t -> t

  (** Integers less-than or equal-to the given one *)
  val leq : Z.t -> t

  (** Integers greater-than or equal-to the given one *)
  val geq : Z.t -> t

  (** [range x y] gives an interval [\[x, y)] *)
  val range : Z.t -> Z.t -> t

  (** [combine i j] is a triple [(below,common,above)] where
      [common] is the values in both intervals, [below] is the smaller values
      that are only in one of intervals, and [above] are the larger values
      that are only in one of the intervals. *)
  val combine : t -> t -> t * t * t

  (** Is this interval empty *)
  val is_empty : t -> bool

  (** Is this a singleton interval. *)
  val is_const : t -> Z.t option

  (** [true] if the first interval is completely below the second
      (i.e., the two do not overlap) *)
  val is_known_below : t -> t -> bool

  (** String rendition of an interval *)
  val to_string : t -> string

  (** Minimum value in interval if it exists *)
  val minimum : t -> Z.t option

  (** Maximum value in interval if it exists *)
  val maximum : t -> Z.t option
end

module Intervals : sig
  (** A subset of the integers *)
  type t [@@deriving eq, ord]

  (** A single interval *)
  val of_interval : Interval.t -> t

  (** The intervals for this type.  Empty list if the interval is empty.
      The intervals are disjoint, separated, sorted. *)
  val to_intervals : t -> Interval.t list

  (** Intersection of two integer subsets *)
  val intersect : t -> t -> t

  (** Union of two integer subsets *)
  val union : t -> t -> t

  (** Complement of two integer subsets *)
  val complement : t -> t

  (** Convert to string *)
  val to_string : t -> string

  (** Is this a singleton subset. *)
  val is_const : t -> Z.t option

  val is_empty : t -> bool

  (** Minimum value in subset if it exists *)
  val minimum : t -> Z.t option

  (** Maximum value in subset if it exists *)
  val maximum : t -> Z.t option
end

module Solver : sig
  module IT = IndexTerms
  module RT = ResourceTypes

  (** Try to simplify a resource type *)
  val simp_rt : (IT.t -> IT.t option) -> RT.t -> RT.t
end
