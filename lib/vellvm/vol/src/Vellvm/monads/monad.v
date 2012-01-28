Require Import Coq.Logic.FunctionalExtensionality.
Require Import List.
Require Import Arith.
Require Import Recdef.
Require Import Omega.

Implicit Type X Y Z W : Type.

Notation monad := option.

Notation munit := Some.

Notation merror := None.

(*
Inductive monad (X:Type) : Type :=
| munit : forall (x:X), monad X
| merror : monad X
.

Hint Constructors monad.
*)

Definition mbind (X:Type) (Y:Type) (f:X -> monad Y) (mx:monad X) : monad Y :=
match mx with
| munit x => f x
| merror => merror
end.

Definition mif (X:Type) (c:bool) (tclause : monad X) (fclause : monad X) : monad X :=
match c with
| true => tclause
| false => fclause
end.

Fixpoint mswitch (X:Type) (cases : list (bool*monad X)) (default_case : monad X) : monad X :=
match cases with
| nil => default_case
| (true, action)::cases' => action
| (false, action)::cases' => mswitch _ cases' default_case
end.

Fixpoint mfor (X:Type) (li:list X) (f:X->monad Prop) : monad Prop :=
match li with
| nil => munit True
| i::li' => 
  match (f i) with
  | munit True => mfor _ li' f
  | _ => merror
  end
end.

Record Range : Type := mkRange
{
  Range_b : nat;
  Range_e : nat;
  Range_d : nat;
  Range_P : Range_d > 0
}.

Function _range2list (i:Range) 
         {measure 
           (fun x =>
           match x with
           | (mkRange b e d P) =>
             e - b
           end)
         } : list nat :=
match i with
| (mkRange b e d P) =>
  match (le_lt_dec e b) with
  | left _ =>   (* e <= b *)
    nil
  | right _ =>  (* b < e *)
    b::_range2list (mkRange (b+1) e d P) 
  end
end.
Proof.
  intros i b e d P l H1 H2.
  destruct i.
  inversion l; subst.
  omega.
Qed.

Lemma one_gt_zero : 1 > 0. omega. Qed.

Definition range2list_1 (b e:nat) := _range2list (mkRange b e 1 one_gt_zero).

Notation "'ret' x" := (@munit _ x) (at level 41).
Notation "'Assert' x" := (@munit Prop x) (at level 41).
Notation "x >>= f" := (@mbind _ _ f x) (at level 42, left associativity).
Notation "e1 >> e2" := (e1 >>= (fun _ => e2)) (at level 42, left associativity).
Notation "'do' x <- a ; b" := ( a >>= (fun x => b) ) (at level 42, left associativity).
Notation "'do' a ; b" := ( a >> b ) (at level 42, left associativity).
Notation "'do' a 'enddo'" := ( a ) (at level 42, left associativity).
Notation "'If' b 'then' t 'else' f 'endif'" := (mif _ b t f) (at level 43).
Notation "'If' b 'then' t 'endif'" := (mif _ b t (ret True)) (at level 43).
Notation "'If' b1 'then' t1 'elseif' b2 'then' t2 'else' f2 'endif'" := (mif _ b1 t1 (mif _ b2 t2 f2)) (at level 43).
Notation "'If' b1 'then' t1 'elseif' b2 'then' t2 'elseif' b3 'then' t3 'else' f3 'endif'" := (mif _ b1 t1 (mif _ b2 t2 (mif _ b3 t3 f3))) (at level 43).
Notation "'If' b1 'then' t1 'elseif' b2 'then' t2 'elseif' b3 'then' t3 'elseif' b4 'then' t4 'else' f4 'endif'" := (mif _ b1 t1 (mif _ b2 t2 (mif _ b3 t3 (mif _ b4 t4 f4)))) (at level 43).
Notation "'If' b1 'then' t1 'elseif' b2 'then' t2 'endif'" := (mif _ b1 t1 (mif _ b2 t2 (ret True))) (at level 43).
Notation "'If' x <- mx 'then' t 'else' f 'endif'" := 
  (match mx with
   | merror => f
   | munit _ => (do x <- mx ; t)
   end) (at level 43).
Notation "'switch' cases 'default' default 'endswitch'" := ( mswitch _ cases default ) (at level 44). 
Notation "'for' i 'in' li 'do' block 'endfor'" := (mfor _ li (fun i => block)) (at level 44).
Notation "'for' i 'From' b 'to' e 'do' block 'endfor'" := (mfor _ (range2list_1 b e) (fun i => block)) (at level 44).

Definition mifk (X Y:Type) (c:bool) (tclause : monad X) (fclause : monad X) (con : X -> monad Y) : monad Y :=
match c with
| true => tclause >>= con
| false => fclause >>= con
end.

Fixpoint mswitchk (X Y:Type) (cases : list (bool*monad X)) (default_case : monad X) (con : X -> monad Y) : monad Y :=
match cases with
| nil => default_case >>= con
| (true, action)::cases' => action >>= con
| (false, action)::cases' => mswitchk _ _ cases' default_case con
end.

Check
  do c <- ret true;
  do d <- ret c;
  do If c 
     then 
       do d <- ret false ; 
       do ret d 
       enddo 
     else 
       do ret false; 
       do ret true 
       enddo 
     endif;
  do c <- ret d;
  do switch 
       ((true, ret false)::nil) 
       default (ret false) 
     endswitch;
  do ret d 
  enddo.

Lemma mbind_mbind : forall (X Y Z:Set) (f : X -> monad Y) (g : Y -> monad Z) (x : monad X),
  x >>= f >>= g = x >>= (fun u => f u >>= g).
Proof.
  intros. destruct x; trivial.
Qed.

Lemma mbind_munit : forall (X Y:Set) (f : X -> monad Y) (x : X),
  (ret x) >>= f = f x.
Proof.
  intros. trivial.
Qed.

Lemma munit_mbind : forall (X:Set) (x : monad X),
  x >>= (@munit X) = x.
Proof.
  intros. destruct x; trivial.
Qed.

Hint Rewrite mbind_mbind mbind_munit munit_mbind : monad.

Hint Extern 1 (_ = _ : monad _) => autorewrite with monad : monad.

Ltac monad := intros; autorewrite with monad; auto with monad.

Definition mmap X Y (f : X -> Y) (x : monad X) : monad Y :=
  x >>= (fun x => ret (f x)).

Notation "x >>- f" := (@mmap _ _ f x) (at level 42, left associativity).

Definition mjoin X : monad (monad X) -> monad X :=
  mbind (monad X) X (fun x => x).

Definition mlift X Y (f : X -> Y) : monad X -> monad Y :=
  mbind X Y (fun u => ret (f u)).

Definition mlift2 X Y Z (f : X -> Y -> Z) (a : monad X) (b : monad Y) : monad Z :=
  a >>= (fun x => b >>= fun y => ret (f x y)).

Definition mlift3 X Y Z W (f : X -> Y -> Z -> W) (a : monad X) (b : monad Y) (c : monad Z) : monad W :=
  a >>= (fun x => b >>= fun y => c >>= fun z => ret (f x y z)).

Section Monad_Facts.

Lemma mbind_congr : forall X Y (f g : X -> monad Y) (x y : monad X),
  x = y -> (forall a, f a = g a) -> x >>= f = y >>= g.
Proof.
intros. replace g with f. subst y. reflexivity.
apply functional_extensionality; trivial.
Qed.

Lemma munit_mbind_match : forall X
  (f : X -> monad X) (x : monad X),
  (forall a, f a = ret a) -> x >>= f = x.
Proof.
intros. transitivity (x >>= @munit X).
apply mbind_congr; trivial.
unfold mbind. destruct x; auto.
Qed.

Hint Resolve mbind_congr munit_mbind_match : monad.

Lemma mmap_congr : forall X Y (f g : X -> Y) (x y : monad X),
  x = y -> (forall a, f a = g a) -> x >>- f = y >>- g.
Proof.
intros. unfold mmap. apply mbind_congr; auto.
intros a. rewrite H0. reflexivity.
Qed.

Hint Resolve mmap_congr : monad.

Lemma mmap_id : forall X (f : X -> X) (x : monad X),
  (forall a, f a = a) -> x >>- f = x.
Proof.
unfold mmap; monad. 
unfold mbind. destruct x; try solve [rewrite H; reflexivity | reflexivity].
Qed.

Hint Resolve mmap_id : monad.

Lemma mmap_munit : forall X Y (f : X -> Y) (x : X),
  ret x >>- f = ret (f x).
Proof.
unfold mmap; monad.
Qed.

Lemma mmap_mmap : forall X Y Z (f : X -> Y) (g : Y -> Z) (x : monad X),
  (x >>- f) >>- g = x >>- (fun u => g (f u)).
Proof.
unfold mmap. unfold mbind; monad. destruct x; auto.
Qed.

Lemma mmap_mbind : forall X Y Z (f : X -> Y) (g : Y -> monad Z) (x : monad X),
  x >>- f >>= g = x >>= (fun u => g (f u)).
Proof.
unfold mmap. unfold mbind; monad. destruct x; auto.
Qed.

Lemma mbind_mmap : forall X Y Z (f : X -> monad Y) (g : Y -> Z) (x : monad X),
  x >>= f >>- g = x >>= (fun u => f u >>- g).
Proof.
unfold mmap. unfold mbind; monad. destruct x; auto.
Qed.

Hint Rewrite mmap_munit mmap_mmap mmap_mbind mbind_mmap : monad.

Lemma mjoin_mjoin : forall X (x : monad (monad (monad X))),
  mjoin X (mjoin (monad X) x) = mjoin X (x >>- (mjoin X)).
Proof.
unfold mjoin. unfold mbind; monad. destruct x; auto.
Qed.

Lemma mjoin_munit : forall X (x : monad X),
  mjoin X (ret x) = x.
Proof.
unfold mjoin; monad.
Qed.

Lemma munit_mjoin : forall X (x : monad X),
  mjoin X (x >>- @munit X) = x.
Proof.
unfold mjoin. unfold mbind; monad. destruct x; auto.
Qed.

Lemma mjoin_mmap : forall X Y (f : X -> monad Y) (x : monad X),
  mjoin Y (x >>- f) = x >>= f.
Proof.
unfold mjoin; monad.
Qed.

End Monad_Facts.

Hint Resolve munit_mbind_match mbind_congr mmap_congr mmap_id : monad.

Hint Rewrite mmap_munit mmap_mmap mmap_mbind mbind_mmap
             mjoin_mjoin mjoin_munit munit_mjoin mjoin_mmap : monad.

Definition monad2prop (X:Type) (m:monad X) : Prop :=
match m with 
| munit _ => True
| merror => False
end.

Notation "{{{ m }}}" := (@monad2prop _ m) (at level 50).


