type ('a,'s) t

val empty : ('a,'s) t
val cons_sep : 's -> ('a,'s) t -> ('a,'s) t
(* cons_sep_alt doesn't add the separator if the list is empty *)
val cons_sep_alt : 's -> ('a,'s) t -> ('a,'s) t
val cons_entry : 'a -> ('a,'s) t -> ('a,'s) t

val is_empty : ('a,'s) t -> bool

(* gets the first entry, if there is one *)
val hd : ('a,'s) t -> 'a
(* gets the first seperator, if there is one *)
val hd_sep : ('a,'s) t -> 's

(* Removes the first entry, fails is there is none, or if a separator is
 * first *)
val tl : ('a,'s) t -> ('a,'s) t

(* Removes the first entry, fails is there is none, removes any separator that
 * precedes the first entry *)
val tl_alt : ('a,'s) t -> ('a,'s) t

(* Removes the first separator, fails is there is none, or if an entry
 * is first *)
val tl_sep : ('a,'s) t -> ('a,'s) t

(* Makes a normal list, ignoring separators *)
val to_list : ('a,'s) t -> 'a list

(* Flattens into a normal list with separators and elements intermixed *)
val to_sep_list : ('a -> 'b) -> ('s -> 'b) -> ('a,'s) t -> 'b list

type ('s,'a) optsep = Optional | Require of 's | Forbid of ('s -> 'a)

(* Flattens into a normal list with separators and elements intermixed, with
 * special control over the first separator.  Optional indicates no special
 * treatment (works as to_sep_list), Require adds the given initial separator if
 * there is none, and Forbid removes the initial separator if there is one.  In
 * the latter case, the initial separator is processed by the function argument
 * to Forbid *)
val to_sep_list_first : ('s,'b) optsep -> ('a -> 'b) -> ('s -> 'b) -> ('a,'s) t
-> 'b list

(* As to_sep_list_first, but for the last separator *)
val to_sep_list_last : ('s,'b) optsep -> ('a -> 'b) -> ('s -> 'b) -> ('a,'s) t
-> 'b list

val to_list_map : ('a -> 'b) -> ('a,'s) t -> 'b list
val iter : ('a -> unit) -> ('a,'s) t -> unit

(* The from list functions ignore the last separator in the input list *)
val from_list : ('a * 's) list -> ('a,'s) t
val from_list_prefix : 's -> bool -> ('a * 's) list -> ('a,'s) t
val from_list_suffix : ('a * 's) list -> 's -> bool -> ('a,'s) t

val length : ('a,'s) t -> int

val map : ('a -> 'b) -> ('a,'s) t -> ('b, 's) t

(* Returns None if the function returns None on all of the elements, otherwise
* returns a list that uses the original element where the function returns None
* *)
val map_changed : ('a -> 'a option) -> ('a,'s) t -> ('a,'s) t option

(* Maps with an accumulating parameter.  The _right version builds the
* accumulator right-to-left, and the _left version builds it left-to-right. *)
val map_acc_right : ('a -> 'c -> 'b * 'c) -> 'c -> ('a, 's) t -> ('b, 's) t * 'c
val map_acc_left : ('a -> 'c -> 'b * 'c) -> 'c -> ('a, 's) t -> ('b, 's) t * 'c

val for_all : ('a -> bool) -> ('a,'s) t -> bool
val exists : ('a -> bool) -> ('a,'s) t -> bool


val pp : (Format.formatter -> 'a -> unit) -> (Format.formatter -> 'b -> unit) -> Format.formatter -> ('a,'b) t -> unit
                                                                           
