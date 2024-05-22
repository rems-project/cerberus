Require Import Coq.ZArith.BinInt.
Require Import Coq.FSets.FMapAVL.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads Traversable.

From Coq.Lists Require Import List. (* after exltlib *)

From CheriCaps.Morello Require Import Capabilities.

From Common Require Import Utils.

Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope monad_scope.

Import MonadNotation.

Require Import Coq.FSets.FMapFacts.

Module AMap := FMapAVL.Make(AddressValue_as_OT).
Module Import AP := FMapFacts.WProperties_fun(AddressValue_as_OT)(AMap).

Fixpoint amap_range_init {T} (a0:AddressValue.t) (n:nat) (step:Z) (v:T) (m:AMap.t T) : AMap.t T
  :=
  match n with
  | O => m
  | S n =>
      let m := amap_range_init a0 n step v m in
      AMap.add (AddressValue.with_offset a0 (Z.mul (Z.of_nat n) step)) v m
  end.

Definition amap_update_element
  {A:Type}
  (key: AddressValue.t)
  (v: A)
  (m: AMap.t A)
  : (AMap.t A)
  :=
  AMap.add key v (AMap.remove key m).

(** [update key f m] returns a map containing the same bindings as
  [m], except for the binding of [key]. Depending on the value of [y]
  where [y] is [f (find_opt key m)], the binding of [key] is added,
  removed or updated. If [y] is [None], the binding is removed if it
  exists; otherwise, if [y] is [Some z] then key is associated to [z]
  in the resulting map. *)
Definition amap_update
  {A:Type}
  (key: AddressValue.t)
  (f: option A -> option A)
  (m: AMap.t A)
  : (AMap.t A)
  :=
  let y := f (AMap.find key m) in
  let m' := AMap.remove key m in (* could be optimized, as removal may be unecessary in some cases *)
  match y with
  | None => m'
  | Some z => AMap.add key z m'
  end.

Definition amap_sequence
  {A: Type}
  {m: Type -> Type}
  {M: Monad m}
  (mv: AMap.t (m A)): m (AMap.t A)
  :=
  let (kl,vl) := List.split (AMap.elements mv) in
  vl' <- sequence (F:=m) (T:=list) vl ;;
  ret (of_list (combine kl vl')).

(** Adds elements of given [list] to a [map] starting at [addr]. *)
Definition amap_add_list_at
  {T:Type}
  (map: AMap.t T)
  (list: list T)
  (addr: AddressValue.t)
  : AMap.t T
  :=
  let ilist := mapi (fun (i: nat) (v: T) => ((AddressValue.with_offset addr (Z.of_nat i)), v)) list in
  List.fold_left (fun acc '(k, v) =>  AMap.add k v acc) ilist map.

(* Monadic mapi *)
Definition amap_mmapi
  {A B : Type}
  {m : Type -> Type}
  {M : Monad m}
  (f : AMap.key -> A -> m B) (zm: AMap.t A)
  : m (AMap.t B)
  :=
  amap_sequence (AMap.mapi f zm).

Definition amap_find_first {A:Type} (f:AMap.key -> A -> bool) (m:AMap.t A): option (AMap.key * A)
  :=
  AMap.fold (fun k v (acc:option (AMap.key * A)) =>
               match acc with
               | None => if f k v
                        then Some (k, v)
                        else None
               | Some _ => acc
               end)
    m None.
