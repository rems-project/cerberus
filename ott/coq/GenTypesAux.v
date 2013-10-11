Require Import Common.
Require Import AilTypes.
Require Import AilSyntax.
Require Import Range.

Require Implementation.
Require AilTyping.
Require AilTypesAux.

Require Import GenTypes.

Definition array gt : bool :=
  match gt with
  | GenArray _ _ => true
  | _            => false
  end.

Definition function gt : bool :=
  match gt with
  | GenFunction _ _ => true
  | _            => false
  end.

Definition pointer_conversion gt :=
  match gt with
  | GenArray    t _ => GenPointer no_qualifiers t
  | GenFunction t q => GenPointer no_qualifiers (Function t q)
  | _               => gt
  end.

Definition integer gt :=
  match gt with
  | GenBasic (GenInteger _) => true
  | _ => false
  end.

Definition real gt : bool := integer gt.

Definition pointer gt :=
  match gt with
  | GenPointer _ _ => true
  | _ => false
  end.

Definition arithmetic gt : bool := integer gt.

Definition scalar t : bool := pointer t || arithmetic t.

Definition void gt : bool :=
  match gt with
  | GenVoid => true
  | _ => false
  end.

Definition pointer_to_complete_object gt : bool :=
  match gt with
  | GenPointer _ t => AilTypesAux.complete t
  | _              => false
  end.

Definition pointers_to_compatible_complete_objects gt1 gt2 : bool :=
  match gt1, gt2 with
  | GenPointer _ t1, GenPointer _ t2 => AilTypesAux.complete t1 && AilTypesAux.complete t2 && AilTypesAux.compatible t1 t2
  | _              , _               => false
  end.  

Definition pointers_to_compatible_objects gt1 gt2 : bool :=
  match gt1, gt2 with
  | GenPointer _ t1, GenPointer _ t2 => AilTypesAux.object t1 && AilTypesAux.object t2 && AilTypesAux.compatible t1 t2
  | _              , _               => false
  end.  

Definition pointer_to_object gt : bool :=
  match gt with
  | GenPointer _ t => AilTypesAux.object t
  | _              => false
  end.

Definition pointer_to_void gt : bool :=
  match gt with
  | GenPointer _ Void => true
  | _                 => false
  end.

Definition pointers_to_compatible_types t1 t2 : bool :=
  match t1, t2 with
  | GenPointer _ t1, GenPointer _ t2 => AilTypesAux.compatible t1 t2
  | _              , _               => false
  end.

Definition composite_pointer gt1 gt2 : option genType :=
  match gt1, gt2 with
  | GenPointer q1 t1, GenPointer q2 t2 => if AilTypesAux.compatible t1 t2
                                             then option_map (GenPointer (AilTypesAux.combine_qualifiers q1 q2)) (AilTypesAux.composite t1 t2)
                                             else None
  | _               , _                => None
  end.

(* Sound but not principal. *)
Definition integer_promotion git : genIntegerType :=
  Promote git.

Definition promotion gt : option genType :=
  match gt with
  | GenBasic (GenInteger git) => Some (GenBasic (GenInteger (integer_promotion git)))
  | _                         => None
  end.

(* Sound but not principal. *)
Definition usual_arithmetic_promoted_integer git1 git2 : genIntegerType :=
  Usual git1 git2.

Definition usual_arithmetic_integer git1 git2 : genIntegerType :=
  usual_arithmetic_promoted_integer
    (integer_promotion git1)
    (integer_promotion git2).

Definition usual_arithmetic gt1 gt2 :=
  match gt1, gt2 with
  | GenBasic (GenInteger git1), GenBasic (GenInteger git2) => Some (GenBasic (GenInteger (usual_arithmetic_integer git1 git2)))
  | _ , _ => None
  end.

Fixpoint interpret_genIntegerType P git : option integerType :=
  match git with
  | Concrete it => Some it
  | SizeT => Some (Implementation.size_t P)
  | PtrdiffT => Some (Implementation.ptrdiff_t P)
  | Unknown ic => AilTyping.type_of_constant P ic
  | Promote git =>
      interpret_genIntegerType P git >>= fun it =>
      Some (AilTypesAux.integer_promotion P it)
  | Usual git1 git2 =>
      interpret_genIntegerType P git1 >>= fun it1 =>
      interpret_genIntegerType P git2 >>= fun it2 =>
      Some (AilTypesAux.usual_arithmetic_integer P it1 it2)
  end.

Definition interpret_genBasicType P gbt : option basicType :=
  match gbt with
  | GenInteger git  => interpret_genIntegerType P git >>= fun it =>
                       Some (Integer it)
  end.

Definition interpret_genType P gt : option ctype :=
  match gt with
  | GenVoid         => Some Void
  | GenBasic gbt    => interpret_genBasicType P gbt >>= fun bt =>
                       Some (Basic bt)
  | GenArray    t n => Some (Array    t n)
  | GenFunction t p => Some (Function t p)
  | GenPointer  q t => Some (Pointer  q t)
  end.

Definition interpret_genTypeCategory P gt : option typeCategory :=
  match gt with
  | GenRValueType   gt => interpret_genType P gt >>= fun t =>
                          Some (RValueType   t)
  | GenLValueType q t  => Some (LValueType q t)
  end.
