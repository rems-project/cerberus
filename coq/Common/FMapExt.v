Require Import Coq.ZArith.BinInt.
Require Import Coq.FSets.FMapAVL.
From Coq.Structures Require Import OrderedType OrderedTypeEx.

From ExtLib.Data Require Import List.
From ExtLib.Structures Require Import Monad Monads Traversable.

From Coq.Lists Require Import List. (* after exltlib *)

Require Import Utils.

Local Open Scope type_scope.
Local Open Scope list_scope.
Local Open Scope monad_scope.

Import MonadNotation.

Require Import Coq.FSets.FMapFacts.

(* Ordered type with additional operations *)
Module Type OrderedTypeExt.
  Include UsualOrderedType.

  Parameter with_offset: t -> Z -> t.
  Parameter of_nat: nat -> t.
  Parameter of_Z: Z -> t.
End OrderedTypeExt.

(* FMap with additional operatons and properties. *)
Module Type FMapExt
  (OT:OrderedTypeExt).

  Module Import M := FMapAVL.Make(OT).
  Module Import P := FMapFacts.WProperties_fun(OT)(M).
  Module Import F := FMapFacts.WFacts_fun(OT)(M).

  Fixpoint map_range_init {T} (a0:M.key) (n:nat) (step:Z) (v:T) (m:M.t T) : M.t T
    :=
    match n with
    | O => m
    | S n =>
        let m := map_range_init a0 n step v m in
        M.add (OT.with_offset a0 (Z.mul (Z.of_nat n) step)) v m
    end.

  Definition map_update_element
    {A:Type}
    (key: M.key)
    (v: A)
    (m: M.t A)
    : (M.t A)
    :=
    M.add key v (M.remove key m).

  (** [update key f m] returns a map containing the same bindings as
  [m], except for the binding of [key]. Depending on the value of [y]
  where [y] is [f (find_opt key m)], the binding of [key] is added,
  removed or updated. If [y] is [None], the binding is removed if it
  exists; otherwise, if [y] is [Some z] then key is associated to [z]
  in the resulting map. *)
  Definition map_update
    {A:Type}
    (key: M.key)
    (f: option A -> option A)
    (m: M.t A)
    : (M.t A)
    :=
    let y := f (M.find key m) in
    let m' := M.remove key m in (* could be optimized, as removal may be unecessary in some cases *)
    match y with
    | None => m'
    | Some z => M.add key z m'
    end.

  Definition map_sequence
    {A: Type}
    {m: Type -> Type}
    {M: Monad m}
    (mv: M.t (m A)): m (M.t A)
    :=
    let (kl,vl) := List.split (M.elements mv) in
    vl' <- sequence (F:=m) (T:=list) vl ;;
    ret (of_list (combine kl vl')).

  (** Adds elements of given [list] to a [map] starting at [addr]. *)
  Definition map_add_list_at
    {T:Type}
    (map: M.t T)
    (list: list T)
    (addr: M.key)
    : M.t T
    :=
    let ilist :=
      Utils.mapi
        (fun (i: nat) (v: T) =>
           ((OT.with_offset addr (Z.of_nat i)), v)
        )
        list in
    List.fold_left (fun acc '(k, v) =>  M.add k v acc) ilist map.

  (* Monadic mapi *)
  Definition map_mmapi
    {A B : Type}
    {m : Type -> Type}
    {M : Monad m}
    (f : M.key -> A -> m B) (zm: M.t A)
    : m (M.t B)
    :=
    map_sequence (M.mapi f zm).

  Definition map_find_first {A:Type} (f:M.key -> A -> bool) (m:M.t A): option (M.key * A)
    :=
    M.fold (fun k v (acc:option (M.key * A)) =>
              match acc with
              | None => if f k v
                       then Some (k, v)
                       else None
              | Some _ => acc
              end)
      m None.

End FMapExt.

