Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zcompare.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads Traversable.

From Coq.Lists Require Import List. (* after exltlib *)

From Common Require Import Utils.

Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope monad_scope.

Import ListNotations.
Import MonadNotation.

Require Import Coq.FSets.FMapFacts.

Module ZMap := FMapAVL.Make(Z_as_OT).
Module Import ZP := FMapFacts.WProperties_fun(Z_as_OT)(ZMap).

Fixpoint zmap_range_init {T} (a0:Z) (n:nat) (step:Z) (v:T) (m:ZMap.t T) : ZMap.t T
  :=
  match n with
  | O => m
  | S n =>
      let m := zmap_range_init a0 n step v m in
      ZMap.add (Z.add a0 (Z.mul (Z.of_nat n) step)) v m
  end.

Definition zmap_update_element
  {A:Type}
  (key: Z)
  (v: A)
  (m: ZMap.t A)
  : (ZMap.t A)
  :=
  ZMap.add key v (ZMap.remove key m).

(** [update key f m] returns a map containing the same bindings as
  [m], except for the binding of [key]. Depending on the value of [y]
  where [y] is [f (find_opt key m)], the binding of [key] is added,
  removed or updated. If [y] is [None], the binding is removed if it
  exists; otherwise, if [y] is [Some z] then key is associated to [z]
  in the resulting map. *)
Definition zmap_update
  {A:Type}
  (key: Z)
  (f: option A -> option A)
  (m: ZMap.t A)
  : (ZMap.t A)
  :=
  let y := f (ZMap.find key m) in
  let m' := ZMap.remove key m in (* could be optimized, as removal may be unecessary in some cases *)
  match y with
  | None => m'
  | Some z => ZMap.add key z m'
  end.

Definition zmap_sequence
  {A: Type}
  {m: Type -> Type}
  {M: Monad m}
  (mv: ZMap.t (m A)): m (ZMap.t A)
  :=
  let (kl,vl) := List.split (ZMap.elements mv) in
  vl' <- sequence (F:=m) (T:=list) vl ;;
  ret (of_list (combine kl vl')).

(*
Alternative defintion. More efficient but harder to prove.
TODO: also uses "elements!".

Definition zmap_sequence
  {A: Type}
  {m: Type -> Type}
  {M: Monad m}
  (mv: ZMap.t (m A)): m (ZMap.t A)
  :=
  let fix loop (ls: list (ZMap.key*(m A))) (acc:ZMap.t A) : m (ZMap.t A) :=
    match ls with
    | [] => ret acc
    | (k,mv)::ls => mv >>= (fun v => loop ls (ZMap.add k v acc))
    end
  in
  loop (ZMap.elements mv) (ZMap.empty A).
 *)

(** Adds elements of given [list] to a [map] starting at [index]. *)
Definition zmap_add_list_at
  {T:Type}
  (map: ZMap.t T)
  (list: list T)
  (offset: Z)
  : ZMap.t T
  :=
  let ilist := mapi (fun (i: nat) (v: T) => ((Z.add offset (Z.of_nat i)), v)) list in
  List.fold_left (fun acc '(k, v) =>  ZMap.add k v acc) ilist map.

(* Monadic mapi *)
Definition zmap_mmapi
  {A B : Type}
  {m : Type -> Type}
  {M : Monad m}
  (f : ZMap.key -> A -> m B) (zm: ZMap.t A)
  : m (ZMap.t B)
  :=
  zmap_sequence (ZMap.mapi f zm).

Definition zmap_find_first {A:Type} (f:ZMap.key -> A -> bool) (m:ZMap.t A): option (ZMap.key * A)
  :=
  ZMap.fold (fun k v (acc:option (ZMap.key * A)) =>
               match acc with
               | None => if f k v
                        then Some (k, v)
                        else None
               | Some _ => acc
               end)
    m None.
