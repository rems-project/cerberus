Require Import Bool.
Require Import ZArith.

Require Import Common.
Require Import AilTypes.
Require Import Implementation.

Local Open Scope Z.

Definition isInteger_fun t :=
  match t with
  | Basic (Integer _) => true
  | _ => false
  end.

Definition isVoid_fun t :=
  match t with
  | Void => true
  | _ => false
  end.

Definition isPointer_fun t :=
  match t with
  | Pointer _ _ => true
  | _ => false
  end.

Definition isBool_fun t :=
  match t with
  | Basic (Integer Bool) => true
  | _ => false
  end.

Definition isSigned_fun P it : bool :=
  match it with
  | Signed _ => true
  | Char => isCharSigned P
  | _ => false
  end.

Definition isUnsigned_fun P it : bool :=
  match it with
  | Unsigned _ => true
  | Bool => true
  | Char => negb (isCharSigned P)
  | _ => false
  end.

Definition integerTypeRange P it :=
  let prec := precision P it in
  if isUnsigned_fun P it then
    @mkRange 0 (2^prec - 1) (integerTypeRange_unsigned (precision_ge_one P _))
  else
    match binMode P with
    | TwosComplement    => @mkRange (-2^(prec - 1))     (2^(prec - 1) - 1) (integerTypeRange_signed1 (precision_ge_one P _))
    | OnesComplement    => @mkRange (-2^(prec - 1) + 1) (2^(prec - 1) - 1) (integerTypeRange_signed2 (precision_ge_one P _))
    | SignPlusMagnitude => @mkRange (-2^(prec - 1) + 1) (2^(prec - 1) - 1) (integerTypeRange_signed2 (precision_ge_one P _))
    end.

Definition isSignedType_fun it : bool :=
  match it with
  | Signed _ => true
  | _ => false
  end.

Definition isUnsignedType_fun it : bool :=
  match it with
  | Unsigned _ => true
  | Bool => true
  | _ => false
  end.

Definition inIntegerTypeRange_fun P n it : bool :=
  memNat_fun n (integerTypeRange P it).

Definition leIntegerTypeRange_fun P it1 it2 : bool :=
  match it1, it2 with
  | Char             , Char              => true
  | Char             , Signed   Ichar    => isCharSigned P
  | Char             , Signed   ibt      => orb (isCharSigned P)
                                                (Z.ltb (precision P Char) (precision P (Signed ibt)))
  | Signed Ichar     , Char              => isCharSigned P
  | Signed ibt       , Char              => andb (isCharSigned P)
                                                 (Z.eqb (precision P (Signed ibt)) (precision P Char))
  | Unsigned Ichar   , Char              => negb (isCharSigned P)
  | Unsigned ibt     , Char              => andb (negb (isCharSigned P))
                                                 (Z.eqb (precision P (Unsigned ibt)) (precision P Char))
  | Char             , Unsigned _        => negb (isCharSigned P)
  | Char             , Bool              => andb (negb (isCharSigned P))
                                                 (Z.eqb (precision P Char) (precision P Bool))
  | Bool             , Char              => orb (negb (isCharSigned P))
                                                (Z.ltb (precision P Bool) (precision P Char))

  | Signed   Ichar   , Signed   _        => true
  | Signed   Short   , Signed   Short    => true
  | Signed   Short   , Signed   Int      => true
  | Signed   Short   , Signed   Long     => true
  | Signed   Short   , Signed   LongLong => true
  | Signed   Int     , Signed   Int      => true
  | Signed   Int     , Signed   Long     => true
  | Signed   Int     , Signed   LongLong => true
  | Signed   Long    , Signed   Long     => true
  | Signed   Long    , Signed   LongLong => true
  | Signed   LongLong, Signed   LongLong => true
  | Signed   ibt1    , Signed   ibt2     => Z.eqb (precision P (Signed ibt1))
                                                  (precision P (Signed ibt2))

  | Bool             , Bool              => true
  | Bool             , Unsigned _        => true
  | Unsigned Ichar   , Unsigned _        => true
  | Unsigned Short   , Unsigned Short    => true
  | Unsigned Short   , Unsigned Int      => true
  | Unsigned Short   , Unsigned Long     => true
  | Unsigned Short   , Unsigned LongLong => true
  | Unsigned Int     , Unsigned Int      => true
  | Unsigned Int     , Unsigned Long     => true
  | Unsigned Int     , Unsigned LongLong => true
  | Unsigned Long    , Unsigned Long     => true
  | Unsigned Long    , Unsigned LongLong  => true
  | Unsigned LongLong, Unsigned LongLong => true
  | Unsigned ibt     , Bool              => Z.eqb (precision P (Unsigned ibt))
                                                  (precision P Bool)
  | Unsigned ibt1    , Unsigned   ibt2   => Z.eqb (precision P (Unsigned ibt1))
                                                  (precision P (Unsigned ibt2))

  | Signed   _       , Bool              => false
  | Signed   _       , Unsigned _        => false

  | Bool             , Signed   ibt2     => Z.ltb (precision P Bool)
                                                  (precision P (Signed   ibt2))
  | Unsigned _       , Signed   Ichar    => false
  | Unsigned Short   , Signed   Short    => false
  | Unsigned Int     , Signed   Int      => false
  | Unsigned Long    , Signed   Long     => false
  | Unsigned LongLong, Signed   LongLong => false
  | Unsigned ibt1    , Signed   ibt2     => Z.ltb (precision P (Unsigned ibt1))
                                                  (precision P (Signed   ibt2))
  end.


Definition eqIntegerRankBase_fun it1 it2 : bool :=
  match it1, it2 with
  | Signed ibt1, Unsigned ibt2   => bool_of_decision (decide ibt1 ibt2 : Decision (ibt1 = ibt2))
  | Char       , Unsigned  Ichar => true
  | Char       , Signed    Ichar => true
  | _          , _               => false
  end.

Definition eqIntegerRank_fun it1 it2 : bool :=
  orb (bool_of_decision (decide it1 it2 : Decision (it1 = it2)))
      (orb (eqIntegerRankBase_fun it1 it2)
           (eqIntegerRankBase_fun it2 it1)).

Definition ltIntegerRankBase_fun P it1 it2 : bool :=
  match it1, it2 with
  | Bool        , it              => negb (bool_of_decision (decide Bool it : Decision (_ = _)))
  | Signed  Long, Signed LongLong => true
  | Signed   Int, Signed     Long => true
  | Signed Short, Signed      Int => true
  | Signed Ichar, Signed    Short => true
  | Signed  ibt1, Signed     ibt2 => Z.ltb (precision P (Signed ibt1)) (precision P (Signed ibt2))
  | _           , _               => false
  end.

Definition ltIntegerRankCongruence_fun P it1 it2 : bool :=
  match it1, it2 with
  | _            , Bool          => false
  | Bool         , _             => true
  | _            , Char          => false
  | Char         , Unsigned ibt2 => ltIntegerRankBase_fun P (Signed Ichar) (Signed ibt2)
  | Char         , Signed   ibt2 => ltIntegerRankBase_fun P (Signed Ichar) (Signed ibt2)
  | Signed ibt1  , Signed   ibt2 => ltIntegerRankBase_fun P (Signed  ibt1) (Signed ibt2)
  | Unsigned ibt1, Unsigned ibt2 => ltIntegerRankBase_fun P (Signed  ibt1) (Signed ibt2)
  | Unsigned ibt1, it2           => ltIntegerRankBase_fun P (Signed  ibt1) it2
  | it1          , Unsigned ibt2 => ltIntegerRankBase_fun P it1            (Signed ibt2)
  end.

Definition ltIntegerRank_fun it1 it2 : bool :=
  match it1, it2 with
  | _             , Bool           => false
  | Bool          , _              => true

  | _             , Char           => false
  | _             , Signed   Ichar => false
  | _             , Unsigned Ichar => false
  | Char          , Signed    ibt2 => true
  | Char          , Unsigned  ibt2 => true
  | Signed   Ichar, Signed    ibt2 => true
  | Signed   Ichar, Unsigned  ibt2 => true
  | Unsigned Ichar, Signed    ibt2 => true
  | Unsigned Ichar, Unsigned  ibt2 => true

  | _             , Signed   Short => false
  | _             , Unsigned Short => false
  | Signed   Short, Signed    ibt2 => true
  | Signed   Short, Unsigned  ibt2 => true
  | Unsigned Short, Signed    ibt2 => true
  | Unsigned Short, Unsigned  ibt2 => true

  | _             , Signed     Int => false
  | _             , Unsigned   Int => false
  | Signed     Int, Signed    ibt2 => true
  | Signed     Int, Unsigned  ibt2 => true
  | Unsigned   Int, Signed    ibt2 => true
  | Unsigned   Int, Unsigned  ibt2 => true

  | _             , Signed    Long => false
  | _             , Unsigned  Long => false
  | Signed    Long, Signed    ibt2 => true
  | Signed    Long, Unsigned  ibt2 => true
  | Unsigned  Long, Signed    ibt2 => true
  | Unsigned  Long, Unsigned  ibt2 => true

  | _             , _              => false
  end.

Definition leIntegerRank_fun it1 it2 : bool :=
  orb (eqIntegerRank_fun it1 it2) (ltIntegerRank_fun it1 it2).

Definition isArithmetic_fun t : bool := isInteger_fun t.

Definition isScalar_fun t : bool := orb (isPointer_fun t) (isArithmetic_fun t).

Definition isArray_fun t : bool :=
  match t with
  | Array _ _ => true
  | _         => false
  end.

Definition isFunction_fun t : bool :=
  match t with
  | Function _ _ => true
  | _            => false
  end.

Definition isCorrespondingUnsigned_fun it1 it2 : bool :=
  match it1, it2 with
  | Signed ibt1, Unsigned ibt2 => bool_of_decision (decide ibt1 ibt2 : Decision (ibt1 = ibt2))
  | _          , _             => false
  end.

Definition isCorrespondingUnsigned_find it : option integerType :=
  match it with
  | Signed ibt => Some (Unsigned ibt)
  | _          => None
  end.

Definition isIntegerPromotion_fun P it1 it2 : bool :=
  match it1, it2 with
  | Signed   Int, Signed   Int => true
  | Unsigned Int, Signed   Int => false
  | Unsigned Int, Unsigned Int => true
  | Signed   Int, Unsigned Int => false
  | _           , Signed   Int => andb (leIntegerRank_fun        it1 (Signed Int))
                                       (leIntegerTypeRange_fun P it1 (Signed Int))
  | _           , Unsigned Int => andb (leIntegerRank_fun        it1 (Signed Int))
                                       (negb (leIntegerTypeRange_fun P it1 (Signed Int)))
  | _           , _            => andb (bool_of_decision (decide it1 it2 : Decision (it1 = it2)))
                                       (negb (leIntegerRank_fun it1 (Signed Int)))
  end.

Definition isIntegerPromotion_find P it : integerType :=
  match it with
  | Signed   Int => Signed   Int
  | Unsigned Int => Unsigned Int
  | _            => if leIntegerRank_fun it (Signed Int)
                      then if leIntegerTypeRange_fun P it (Signed Int)
                             then Signed Int
                             else Unsigned Int
                      else it
  end.

Definition isUsualArithmeticInteger_fun P it1 it2 it3 : bool :=
  if bool_of_decision(decide it1 it2 : Decision (it1 = it2)) then
    bool_of_decision(decide it1 it3 : Decision (it1 = it3))
  else
    if isSignedType_fun it1 then
      if isSignedType_fun it2 then
        if ltIntegerRank_fun it2 it1 then
          bool_of_decision(decide it1 it3 : Decision (it1 = it3))
        else
          bool_of_decision(decide it2 it3 : Decision (it2 = it3))
      else if isUnsignedType_fun it2 then
        if leIntegerRank_fun it1 it2 then
          bool_of_decision(decide it2 it3 : Decision (it2 = it3))
        else
          if leIntegerTypeRange_fun P it2 it1 then
            bool_of_decision(decide it1 it3 : Decision (it1 = it3))
          else
            isCorrespondingUnsigned_fun it1 it3
      else
        false
    else if isUnsignedType_fun it1 then
      if isUnsignedType_fun it2 then
        if ltIntegerRank_fun it2 it1 then
          bool_of_decision(decide it1 it3 : Decision (it1 = it3))
        else
          bool_of_decision(decide it2 it3 : Decision (it2 = it3))
      else if isSignedType_fun it2 then
        if leIntegerRank_fun it2 it1 then
          bool_of_decision(decide it1 it3 : Decision (it1 = it3))
        else if leIntegerTypeRange_fun P it1 it2 then
          bool_of_decision(decide it2 it3 : Decision (it2 = it3))
        else
          isCorrespondingUnsigned_fun it2 it3
      else
        false
    else
      false.

Definition isUsualArithmeticInteger_find P it1 it2 : option integerType :=
  if bool_of_decision(decide it1 it2 : Decision (it1 = it2)) then
    Some it1
  else
    if isSignedType_fun it1 then
      if isSignedType_fun it2 then
        if ltIntegerRank_fun it2 it1 then
          Some it1
        else
          Some it2
      else if isUnsignedType_fun it2 then
        if leIntegerRank_fun it1 it2 then
          Some it2
        else
          if leIntegerTypeRange_fun P it2 it1 then
            Some it1
          else
            isCorrespondingUnsigned_find it1
      else
        None
    else if isUnsignedType_fun it1 then
      if isUnsignedType_fun it2 then
        if ltIntegerRank_fun it2 it1 then
          Some it1
        else
          Some it2
      else if isSignedType_fun it2 then
        if leIntegerRank_fun it2 it1 then
          Some it1
        else if leIntegerTypeRange_fun P it1 it2 then
          Some it2
        else
          isCorrespondingUnsigned_find it2
      else
        None
    else
      None.

Definition isUsualArithmetic_find P t1 t2 : option type :=
  match t1, t2 with
  | Basic (Integer it1), Basic (Integer it2) =>
      match isUsualArithmeticInteger_find P (isIntegerPromotion_find P it1) (isIntegerPromotion_find P it2) with
      | Some it => Some (Basic (Integer it))
      | None    => None
      end
  | _, _ => None
  end.

Definition isUsualArithmetic_fun P t1 t2 t3 : bool :=
  bool_of_decision (decide (isUsualArithmetic_find P t1 t2) (Some t3) : Decision (_ = _)).

Definition isObject_fun t : bool :=
  match t with
  | Basic _ => true
  | Void => true
  | Pointer _ _ => true
  | Array _ _ => true
  | _ => false
  end.

Definition isComplete_fun t : bool :=
  match t with
  | Basic _ => true
  | Pointer _ _ => true
  | Array _ _ => true
  | _ => false
  end.

Definition isIncomplete_fun t : bool :=
  match t with
  | Void => true
  | _ => false
  end.

Definition isModifiable_fun qs t : bool :=
  andb (isObject_fun t)
       (andb (negb (isArray_fun t)) 
             (andb (negb (isIncomplete_fun t))
                   (negb (list_in_fun (fun x y => bool_of_decision (decide x y : Decision (x = y))) Const qs))
             )
       ).

Definition isReal_fun t : bool := isInteger_fun t.

Definition isLvalueConvertible_fun t : bool := andb (negb (isArray_fun t)) (isComplete_fun t).

Fixpoint isCompatible_fun t1 t2 {struct t1} : bool :=
  if bool_of_decision(decide t1 t2 : Decision (t1 = t2)) then
    true
  else
    match t1, t2 with
    | Function t1 p1, Function t2 p2 =>
        andb (isCompatible_fun t1 t2) (isCompatible_params_fun p1 p2)
    | _, _ => false
    end
with isCompatible_params_fun p1 p2 : bool :=
  match p1, p2 with
  | ParamsNil         , ParamsNil          => true
  | ParamsNil         , _                  => false
  | _                 , ParamsNil          => false
  | ParamsCons _ t1 p1, ParamsCons _ t2 p2 => andb (isCompatible_fun        t1 t2)
                                                   (isCompatible_params_fun p1 p2)
  end.

Fixpoint isComposite_fun t1 t2 t3 : bool :=
  if andb (bool_of_decision (decide t1 t2 : Decision (t1 = t2)))
          (bool_of_decision (decide t1 t3 : Decision (t1 = t3))) then
    true
  else
    match t1, t2, t3 with
    | Array t1 n1, Array t2 n2, Array t3 n3 =>
        andb (andb (bool_of_decision (decide n1 n2 : Decision (n1 = n2)))
                   (bool_of_decision (decide n1 n3 : Decision (n1 = n3))))
             (isComposite_fun t1 t2 t3)
    | Function t1 p1, Function t2 p2, Function t3 p3 =>
        andb (isComposite_fun        t1 t2 t3)
             (isComposite_params_fun p1 p2 p3)
    | _, _, _ => false
    end
with isComposite_params_fun p1 p2 p3 : bool :=
  match p1, p2, p3 with
  | ParamsNil         , ParamsNil         , ParamsNil            => true
  | ParamsCons _ t1 p1, ParamsCons _ t2 p2, ParamsCons nil t3 p3 => andb (isComposite_fun        t1 t2 t3)
                                                                         (isComposite_params_fun p1 p2 p3)
  | _                 , _                 , _                    => false
  end.
