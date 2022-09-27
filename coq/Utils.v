Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.ZArith.

From Coq.Strings Require Import Ascii.

From ExtLib.Structures Require Import Monad Monads.

Import ListNotations.
Import MonadNotation.

Require Import SimpleError.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Fixpoint list_init {A:Type} (n:nat) (f:nat -> A): list A
  :=
  match n with
  | O => []
  | S n => (f n) :: list_init n f
  end.

(** Inlike OCaml version if lists have different sizes, we just terminate
    after consuming the shortest one, without signaling error *)
Fixpoint fold_left2 {A B C:Type} (f: A -> B -> C -> A) (accu:A) (l1:list B) (l2:list C): A :=
  match l1, l2 with
  | a1::l1, a2::l2 => fold_left2 f (f accu a1 a2) l1 l2
  | _, _ => accu
  end.

Definition mem {A:Type} `{forall (x y:A), Decidable (x = y)} (a:A): (list A) -> bool
  := List.existsb (fun e => decide (e = a)).

Definition mapi {A B: Type} (f: nat -> A -> B) (l:list A) : list B :=
  let fix map_ n (l:list A) :=
    match l with
    | [] => []
    | a :: t => (f n a) :: (map_ (S n) t)
    end
  in map_ O l.

(* c.f.
   List.fold_left
     : forall A B : Type, (A -> B -> A) -> list B -> A -> A
 *)
Fixpoint monadic_fold_left
  {A B : Type}
  {m : Type -> Type}
  {M : Monad m}
  (f : A -> B -> m A) (l : list B) (a : A)
  : m A
  := match l with
     | List.nil => ret a
     | List.cons b l =>
         a' <- f a b ;;
         monadic_fold_left f l a'
     end.

Fixpoint monadic_fold_left2
  {A B C:Type}
  {m : Type -> Type}
  {M : Monad m}
  (f: A -> B -> C -> m A)
  (accu:A)
  (l1:list B)
  (l2:list C)
  : m A
  :=
  match l1, l2 with
  | a1::l1, a2::l2 =>
      accu' <- f accu a1 a2 ;;
      monadic_fold_left2 f accu' l1 l2
  | _, _ => ret accu
  end.

Definition maybeEqualBy
  {A: Type}
  (f: A -> A -> bool)
  (a: option A)
  (b: option A)
  : bool
  :=
  match a,b with
  | None, None => true
  | Some a, Some b => f a b
  | _, _ => false
  end.

(* TODO: Z.extract_num *)
Definition extract_num: Z -> Z -> Z -> Z.
Proof. admit. Admitted.

(* Using two's complement encoding. We do not perform range checks
   here assuming Z is in the proper range.
   (TODO: review)
 *)
Definition byte_of_Z (z:Z): ascii :=
  match z with
  | Z0 => Ascii.zero
  | Zpos x => ascii_of_pos x
  | Zneg _ =>
      let n := Z.abs_nat (Z.opp (Z.add z 1%Z)) in
      match ascii_of_nat n with
      | Ascii a1 a2 a3 a4 a5 a6 a7 a8 => Ascii (negb a1) (negb a2) (negb a3) (negb a4) (negb a5) (negb a6) (negb a7) true
      end
  end.

(* TODO: make sure bit order is correct. *)
Definition bool_bits_of_bytes (bytes : list ascii): list bool
  :=
  let ascii_to_bits (x:ascii) :=
    match x with
    | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a0; a1; a2; a3; a4; a5; a6; a7]
    end
  in
  List.fold_left (fun l a => List.app l (ascii_to_bits a)) bytes [].


(* size is in bytes *)
Definition bytes_of_Z (is_signed: bool) (size: nat) (i: Z): serr (list ascii)
  :=
  let nbits := Z.mul 8 (Z.of_nat size) in
  let '(min, max) :=
    if is_signed then
      ((Z.opp (Z.pow 2 (Z.sub nbits 1))),
        (Z.sub (Z.pow 2 (Z.sub nbits 1)) 1))
    else
      (0,
        (Z.sub (Z.pow 2 nbits)
           (1))) in
  if
    (negb (Z.leb min i && Z.leb i max)) || (Z.gtb nbits 128)
  then
    raise "bytes_of_Z failure"%string
  else
    ret (list_init size
           (fun n => byte_of_Z (extract_num i (Z.mul 8 (Z.of_nat n)) 8))).

Definition Z_of_bytes (is_signed: bool) (bs:list ascii): serr Z
  :=
  match (List.rev bs), Nat.leb (List.length bs) 16 with
  | [], _ => raise "empty list"
  | _, false =>  raise "byte list too long"
  | (first::_) as cs, _ =>
      let init :=
        if is_signed && (Z.eqb 1 (extract_num (Z.of_nat (nat_of_ascii first)) 7 1))
        then -1
        else 0
      in
      let fix aux (acc : Z) (cs : list ascii): serr Z :=
        match cs with
        | [] => ret acc
        | c_value::cs' =>
            aux (Z.lxor (Z.of_nat (nat_of_ascii c_value)) (Z.shiftl acc 8)) cs'
        end in
      aux init cs
  end.

(* TODO: check if these are correct *)
Definition Z_integerRem_t := Z.rem.
Definition Z_integerRem_f := Z.rem.
Definition Z_integerDiv_t := Z.div.


Definition float_of_bits: Z -> float.
Proof. Admitted. (* TODO *)

Definition bits_of_float: float -> Z.
Proof. Admitted. (* TODO *)
