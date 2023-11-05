Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zdigits.
Require Import Coq.Vectors.Vector.
Require Import Coq.Strings.Ascii.

From ExtLib.Structures Require Import Monad Monads.

Require Import StructTact.StructTactics.

Import ListNotations.
Import MonadNotation.

Require Import SimpleError.

From Sail Require Import Values.

Local Open Scope list_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition debugging : bool := true.

(* this definition will be remapped on extraction to OCaml's print_endline *)
Definition print_msg (msg : string) : unit := tt.

Definition sprint_msg (msg : string) : serr unit :=
  if debugging then 
    ret (print_msg msg)
  else 
    ret tt.

Fixpoint list_init {A:Type} (n:nat) (f:nat -> A): list A
  :=
  match n with
  | O => []
  | S n => (f n) :: list_init n f
  end.

Fixpoint monadic_list_init
  {A:Type}
  {m : Type -> Type}
  {M : Monad m}
  (n:nat)
  (f: nat -> m A): m (list A)
  :=
  match n with
  | O => ret []
  | S n =>
      h <- f n ;;
      t <- monadic_list_init n f ;;
      ret (h :: t)
  end.


(** Inlike OCaml version if lists have different sizes, we just terminate
    after consuming the shortest one, without signaling error *)
Fixpoint fold_left2 {A B C:Type} (f: A -> B -> C -> A) (accu:A) (l1:list B) (l2:list C): A :=
  match l1, l2 with
  | a1::l1, a2::l2 => fold_left2 f (f accu a1 a2) l1 l2
  | _, _ => accu
  end.

Definition bool_list_cmp (a b: list bool) : bool :=
  if Nat.eqb (List.length a) (List.length b)
  then fold_left2 (fun a b c => andb (Bool.eqb b c) a) true a b
  else false.

Definition mem {A:Type} `{forall (x y:A), Decidable (x = y)} (a:A): (list A) -> bool
  := List.existsb (fun e => decide (e = a)).

Definition mapi {A B: Type} (f: nat -> A -> B) (l:list A) : list B :=
  let fix map_ n (l:list A) :=
    match l with
    | [] => []
    | a :: t => (f n a) :: (map_ (S n) t)
    end
  in map_ O l.

(* alternative definition of [mapi] *)
Fixpoint mapi' {A B: Type} (f: nat -> A -> B) (l:list A) : list B :=
  match l with
  | [] => []
  | x :: xs => (f O x) :: (mapi' (fun n v => f (S n) v) xs)
  end.

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

Definition vector_drop {A:Type} {t:nat} (h:nat) (v:Vector.t A (h+t)) : Vector.t A t
  :=  snd (Vector.splitat h v).

(** [extract a off len] returns a nonnegative number corresponding to bits
    [off] to [off]+[len]-1 of [a].
    Negative [a] are considered in infinite-length 2's complement
    representation.
    [len] must not be 0.
 *)
Program Definition extract_num (a:Z) (off:nat) (len:nat): serr Z :=
  match len with
  | O => raise "0 length not allowed"
  | S len' =>
      match a with
      | Z0 => ret 0
      | _ =>
          let v := Z_to_two_compl (off + len')%nat a in
          let v := vector_drop (t:=len) off v in
          let v := Vector.take len _ v in
          ret (binary_value len v)
      end
  end.

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

Definition bool_bits_of_bytes (bytes : list ascii): list bool
  :=
  let ascii_to_bits (x:ascii) :=
    match x with
    | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a7; a6; a5; a4; a3; a2; a1; a0]
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
    monadic_list_init size
      (fun n => extract_num i (Nat.mul 8%nat n) 8%nat >>= (fun x => ret (byte_of_Z x))).

Definition Z_of_bytes (is_signed: bool) (bs:list ascii): serr Z
  :=
  match (List.rev bs), Nat.leb (List.length bs) 16 with
  | [], _ => raise "empty list"
  | _, false =>  raise "byte list too long"
  | (first::_) as cs, _ =>
      x <- extract_num (Z.of_nat (nat_of_ascii first)) 7%nat 1%nat ;;
      let init := if is_signed && (Z.eqb 1 x) then -1 else 0
      in
      let fix aux (acc : Z) (cs : list ascii): serr Z :=
        match cs with
        | [] => ret acc
        | c_value::cs' =>
            aux (Z.lxor (Z.of_nat (nat_of_ascii c_value)) (Z.shiftl acc 8)) cs'
        end in
      aux init cs
  end.

(* could be generalized as monadic map, or implemented as composition
   of [map] and [sequence]. *)
Fixpoint try_map {A B:Type} (f : A -> option B) (l:list A) : option (list B)
  :=
  match l with
  | [] => Some []
  | a :: t =>
      match f a with
      | Some b =>
          match try_map f t with
          | Some bs =>  Some (b :: bs)
          | None => None
          end
      | None => None
      end
  end.

Definition Z_integerRem_t := Z.rem.

Definition Z_integerRem_f a b :=
  let r := Z.rem a b in
  if Z.geb (Z.sgn r) 0 then r else Z.add r (Z.abs b).

Definition Z_integerDiv_t := Z.div.

Definition float_of_bits (_:Z): float := PrimFloat.zero. (* TODO: implement *)

Definition bits_of_float (_:float) : Z := Z.zero. (* TODO: implement *)

Fixpoint List_bool_eqb (l1:list bool) (l2:list bool) : bool := 
  match (l1,l2) with
    ([],[]) => true 
  | ([],_) => false 
  | (_,[]) => false 
  | (h1::t1,h2::t2) => (Bool.eqb h1 h2) && List_bool_eqb t1 t2
  end.

Fixpoint word_to_list_bool {n} w :=
  match w with
  | Word.WO => []
  | Word.WS b w => b :: word_to_list_bool w
  end.

(* Stores less-significant bits in lower indices *)
Definition mword_to_list_bool {n} (w : mword n) : list bool := 
  word_to_list_bool (get_word w). 
  
Definition string_of_bool (b:bool) :=
  match b with
  | true => "true"
  | false => "false"
  end.

Lemma ascii_eq_refl: forall x : ascii, Ascii.compare x x = Eq.
Proof.
  intros x.
  unfold compare.
  apply N.compare_eq_iff.
  reflexivity.
Qed.

Lemma string_eq_refl: forall x : string, String.compare x x = Eq.
Proof.
  intros x.
  induction x.
  -
    auto.
  -
    cbn.
    rewrite ascii_eq_refl.
    assumption.
Qed.

Lemma string_eq_trans: forall x y z : string,
    String.compare x y = Eq ->
    String.compare y z = Eq ->
    String.compare x z = Eq.
Proof.
  intros x y z H0 H1.
  apply String.compare_eq_iff in H0, H1.
  rewrite H0, H1.
  apply string_eq_refl.
Qed.

(** Helper function to split a list at given position.
      List.split_at in Lem.
 *)
Definition split_at {A:Type} (n:nat) (l:list A)
  := (List.firstn n l, List.skipn n l).
