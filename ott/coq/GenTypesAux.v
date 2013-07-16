Require Import Common.
Require Import AilTypes.
Require Import GenTypes.

Require AilTypesAux.

Definition pointer_conversion gt :=
  match gt with
  | GenArray    t _ => GenPointer no_qualifiers t
  | GenFunction t q => GenPointer no_qualifiers (Function t q)
  | _               => gt
  end.

Definition array gt : bool :=
  match gt with
  | GenArray _ _ => true
  | _            => false
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

(* Sound but not principal. *)
Definition promotion gt : option genType :=
  match gt with
  | GenBasic (GenInteger git) => Some (GenBasic (GenInteger (Promote git)))
  | _                         => None
  end.

(* Sound but not principal. *)
Definition usual_arithmetic gt1 gt2 :=
  match gt1, gt2 with
  | GenBasic (GenInteger git1), GenBasic (GenInteger git2) => Some (GenBasic (GenInteger (Usual git1 git2)))
  | _ , _ => None
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

Require Import Implementation.
Require Import Range.
Require Import AilTypesAux.
Require Import AilTyping.

Fixpoint interpret_genIntegerType P git : option integerType :=
  match git with
  | Concrete it => Some it
  | SizeT => Some (size_t P)
  | PtrdiffT => Some (ptrdiff_t P)
  | Unknown ic => type_of_constant P ic
  | Promote git =>
      interpret_genIntegerType P git >>= fun it =>
      Some (integer_promotion P it)
  | Usual git1 git2 =>
      interpret_genIntegerType P git1 >>= fun it1 =>
      interpret_genIntegerType P git2 >>= fun it2 =>
      Some (usual_arithmetic_integer P it1 it2)
  end.

Fixpoint interpret_genBasicType P gbt : option basicType :=
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

Require Import AilSyntax.

Definition signed_integerSuffix (s : integerSuffix) : bool :=
  match s with
      |  L |  LL => true
  | U | UL | ULL => false
  end.

Definition signed_integerConstant (ic : integerConstant) : bool :=
  match snd ic with
  | None   => true
  | Some s => signed_integerSuffix s
  end.

Definition min_interpret_integerSuffix s :=
  match s with
  | L   => Long
  | LL  => LongLong
  | U   => Int
  | UL  => Long
  | ULL => LongLong
  end.

Definition min_interpret_optionIntegerSuffix os :=
  match os with
  | None   => Int
  | Some s => min_interpret_integerSuffix s
  end.

Definition min_interpret_integerConstant (ic:integerConstant) :=
  min_interpret_optionIntegerSuffix (snd ic).

Require Import ZArith.
Open Local Scope Z.

Lemma le_one_min_precision ibt : 1 <= min_precision ibt.
Proof. destruct ibt; simpl; omega. Qed.

Definition min_range_unsigned ibt :=
  let prec := min_precision ibt in
  @make_range 0 (2^prec - 1) (integer_range_unsigned (le_one_min_precision ibt)).

Definition min_range_signed ibt :=
  let prec := min_precision ibt in
  @make_range (-2^(prec - 1) + 1) (2^(prec - 1) - 1) (integer_range_signed2 (le_one_min_precision ibt)). 

Definition min_integer_range git :=
  match git with
  | Promote _
  | Usual _ _
  | Concrete Char           => make_range (integer_range_signed_upper (le_one_min_precision Ichar))
  | Concrete Bool           => make_range Z.le_0_1
  | Concrete (Unsigned ibt) => min_range_unsigned ibt
  | Concrete (Signed   ibt) => min_range_signed   ibt
  | SizeT                   => min_range_unsigned Int
  | PtrdiffT                => min_range_signed   Int
  | Unknown ic              => if signed_integerConstant ic
                                 then min_range_signed   (min_interpret_integerConstant ic)
                                 else min_range_unsigned (min_interpret_integerConstant ic)
  end.

Definition max_integerBaseType ibt1 ibt2 : integerBaseType :=
  match ibt1, ibt2 with
  | LongLong, _
  | _       , LongLong => LongLong
  | Long    , _
  | _       , Long     => Long
  | Int     , _
  | _       , Int      => Int
  | Short   , _
  | _       , Short    => Short
  | _       , _        => Ichar
  end.
