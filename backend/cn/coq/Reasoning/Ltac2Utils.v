(* General-purpose Ltac2 utilities *)

From Ltac2 Require Import Ltac2 Notations Std Constr Printf Ident Env.
Import Unsafe.

Ltac2 rec list_subtract
  (eq : 'a -> 'a -> bool)
  (l1 : 'a list)
  (l2 : 'a list) : 'a list :=
  match l1 with
  | [] => []
  | h :: t =>
      if Ltac2.List.exist (fun x => eq h x) l2 then
        list_subtract eq t l2
      else
        h :: list_subtract eq t l2
  end.

(* Specialisation of [list_subtract] for [constr] that uses strict
       syntactic equality: only up to α-conversion and evar
       expansion *)
Ltac2 const_list_subtract (l1 : constr list) (l2 : constr list) : constr list :=
  list_subtract (fun t1 t2 => Constr.equal t1 t2) l1 l2.

  (*
    get_constructor_name : constr -> constr
  
    Given a term c, if c is an application then this function returns its head,
    which is usually the actual constructor name; otherwise it returns c itself.
  *)
Ltac2 get_constructor_name (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => f
  | _ => c
  end.
  
  (** [destruct_list a l] deconstructs the Coq list [l] (of type [list A], where [a] represents the element type) into an Ltac2 list of [constr] elements. It raises a tactic failure if [l] is not a well‐formed list.
  
  @param a A Coq term representing the element type [A].
  @param l A Coq term of type [list A].
  @return An Ltac2 list of [constr] containing the elements of [l].
  
  @example If [l] is equivalent to [e1 :: e2 :: ... :: en :: nil], then [destruct_list a l] returns [e1; e2; ...; en].
  *)
Ltac2 rec destruct_list (a : constr) (l : constr) : constr list :=
  let nil_constr  := constr:(@nil $a) in
  let cons_constr := constr:(@cons $a) in
  match Constr.Unsafe.kind l with
  | Constr.Unsafe.App f args =>
      let f_name     := get_constructor_name f in
      let nil_name   := get_constructor_name nil_constr in
      let cons_name  := get_constructor_name cons_constr in
      if Constr.equal f_name nil_name then
        []
      else if Constr.equal f_name cons_name then
             let head := Array.get args 1 in
             let tail := Array.get args 2 in
             head :: destruct_list a tail
           else
             Control.throw (Tactic_failure (Some (Message.of_string "Not a list")))
  | _ =>
      Control.throw (Tactic_failure (Some (Message.of_string "Not a list")))
  end.

(*
  recons_list : constr list -> constr -> constr

  Description:
    Given an Ltac2 list of Coq terms (i.e. a value of type 'constr list')
    and a Coq term 'A' representing the element type,
    this Ltac2 function reconstructs a Coq list (of type 'list A').
    Internally, it constructs the nil and cons constructors for type 'A' and then
    recursively rebuilds the Coq list.

  Parameters:
    - l : An Ltac2 list of 'constr' representing the elements of the list.
    - A : A Coq term representing the element type.

  Returns:
    - A Coq term (of type 'constr') representing the list of type 'list A'
      that contains exactly the elements in 'l'.

  Behavior:
    - If 'l' is empty, it returns 'constr:(@nil A)'.
    - Otherwise, it takes the head 'h' and recursively builds the tail,
      then returns 'constr:(@cons A h tail)'.
*)

Ltac2 rec recons_list (a : constr) (l : constr list) : constr :=
  match l with
  | [] => constr:(@nil $a)
  | h :: t =>
      let tail_constr := recons_list a t in
      constr:(@cons $a $h $tail_constr)
end.
  
(**
 Destructs a Coq constr representing a pair into its two components.

 This function inspects the internal representation of the term using
 [Constr.Unsafe.kind]. It only works for fully applied pairs, i.e. when the
 pair constructor is applied to exactly two arguments.

 @param t The Coq constr to destruct.
 @return A tuple (a, b) containing the first and second component of the pair.
 @raise An exception if parameter is not a fully applied pair
 *)
 Ltac2 destruct_pair (t : constr) :=
 match Constr.Unsafe.kind t with
 | Constr.Unsafe.App f args =>
     let pair_constr := constr:(@pair) in
     let pair_constr_name := get_constructor_name pair_constr in
     let f_name := get_constructor_name f in
     if Constr.equal f_name pair_constr_name then
       if Int.equal (Array.length args) 4 then
         let a := Array.get args 2 in
         let b := Array.get args 3 in
         (a, b)
       else
         Control.throw (Tactic_failure (Some (Message.of_string "Term is not a fully applied pair")))
     else
       Control.throw (Tactic_failure (Some (Message.of_string "Term is not a pair")))
 | _ =>
     Control.throw (Tactic_failure (Some (Message.of_string "Term is not an application (and thus not a pair)")))
 end.
 
 (* Ident to constant reference *)
 Ltac2 const_to_const_reference  (x:constr) :=  
  match Constr.Unsafe.kind x with
  | Constr.Unsafe.Constant c _ => Std.ConstRef c
  | _ => Control.throw (Tactic_failure (Some (Message.of_string "Term is not a constant")))
  end.

