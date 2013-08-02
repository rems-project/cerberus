Require Import ZArith.

Require Import Common.
Require Import AilTypes.
Require Import Implementation.

Local Open Scope Z.
Local Open Scope list_scope.
Local Open Scope bool_scope.

Definition unqualified qs :=
  match qs with
  | {| const    := false;
       restrict := false;
       volatile := false |} => true
  | _                       => false
  end.

Definition integer t :=
  match t with
  | Basic (Integer _) => true
  | _ => false
  end.

Definition void t :=
  match t with
  | Void => true
  | _ => false
  end.

Definition pointer t :=
  match t with
  | Pointer _ _ => true
  | _ => false
  end.

Definition boolean t :=
  match t with
  | Basic (Integer Bool) => true
  | _ => false
  end.

Definition unsigned P it : bool :=
  negb (signed P it).

Definition signed_type it : bool :=
  match it with
  | Signed _ => true
  | _ => false
  end.

Definition unsigned_type it : bool :=
  match it with
  | Unsigned _ => true
  | Bool => true
  | _ => false
  end.

Definition in_integer_range P n it : bool :=
  Range.mem_nat n (integer_range P it).

Definition le_integer_range P it1 it2 : bool :=
  match it1, it2 with
  | Char             , Char              => true
  | Char             , Signed   Ichar    => signed P Char
  | Char             , Signed   ibt      => signed P Char ||
                                            lt_Z (precision P Char) (precision P (Signed ibt))
  | Signed Ichar     , Char              => signed P Char
  | Signed ibt       , Char              => signed P Char &&
                                            eq_Z (precision P (Signed ibt)) (precision P Char)
  | Unsigned Ichar   , Char              => negb (signed P Char)
  | Unsigned ibt     , Char              => negb (signed P Char) &&
                                            eq_Z (precision P (Unsigned ibt)) (precision P Char)
  | Char             , Unsigned _        => negb (signed P Char)
  | Char             , Bool              => negb (signed P Char) &&
                                            eq_Z (precision P Char) (precision P Bool)
  | Bool             , Char              => negb (signed P Char) ||
                                            lt_Z (precision P Bool) (precision P Char)

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
  | Signed   ibt1    , Signed   ibt2     => eq_Z (precision P (Signed ibt1))
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
  | Unsigned Long    , Unsigned LongLong => true
  | Unsigned LongLong, Unsigned LongLong => true
  | Unsigned ibt     , Bool              => eq_Z (precision P (Unsigned ibt))
                                                  (precision P Bool)
  | Unsigned ibt1    , Unsigned   ibt2   => eq_Z (precision P (Unsigned ibt1))
                                                  (precision P (Unsigned ibt2))

  | Signed   _       , Bool              => false
  | Signed   _       , Unsigned _        => false

  | Bool             , Signed   ibt2     => lt_Z (precision P Bool)
                                                 (precision P (Signed ibt2))
  | Unsigned _       , Signed   Ichar    => false
  | Unsigned Short   , Signed   Short    => false
  | Unsigned Int     , Signed   Int      => false
  | Unsigned Long    , Signed   Long     => false
  | Unsigned LongLong, Signed   LongLong => false
  | Unsigned ibt1    , Signed   ibt2     => lt_Z (precision P (Unsigned ibt1))
                                                 (precision P (Signed   ibt2))
  end.

Definition eq_integer_rank_base it1 it2 : bool :=
  match it1, it2 with
  | Signed ibt1, Unsigned ibt2   => eq_integerBaseType ibt1 ibt2
  | Char       , Unsigned  Ichar => true
  | Char       , Signed    Ichar => true
  | _          , _               => false
  end.

Definition eq_integer_rank it1 it2 : bool :=
  eq_integerType it1 it2 || eq_integer_rank_base it1 it2 || eq_integer_rank_base it2 it1.

Definition lt_integer_rank_base P it1 it2 : bool :=
  match it1, it2 with
  | Bool        , it              => negb (eq_integerType Bool it)
  | Signed  Long, Signed LongLong => true
  | Signed   Int, Signed     Long => true
  | Signed Short, Signed      Int => true
  | Signed Ichar, Signed    Short => true
  | Signed  ibt1, Signed     ibt2 => lt_Z (precision P (Signed ibt1)) (precision P (Signed ibt2))
  | _           , _               => false
  end.

Definition lt_integer_rank_congruence P it1 it2 : bool :=
  match it1, it2 with
  | _            , Bool          => false
  | Bool         , _             => true
  | _            , Char          => false
  | Char         , Unsigned ibt2 => lt_integer_rank_base P (Signed Ichar) (Signed ibt2)
  | Char         , Signed   ibt2 => lt_integer_rank_base P (Signed Ichar) (Signed ibt2)
  | Signed ibt1  , Signed   ibt2 => lt_integer_rank_base P (Signed  ibt1) (Signed ibt2)
  | Unsigned ibt1, Unsigned ibt2 => lt_integer_rank_base P (Signed  ibt1) (Signed ibt2)
  | Unsigned ibt1, it2           => lt_integer_rank_base P (Signed  ibt1) it2
  | it1          , Unsigned ibt2 => lt_integer_rank_base P it1            (Signed ibt2)
  end.

Definition lt_integer_rank it1 it2 : bool :=
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

Definition le_integer_rank it1 it2 : bool :=
  orb (eq_integer_rank it1 it2) (lt_integer_rank it1 it2).

Definition arithmetic t : bool := integer t.

Definition scalar t : bool := pointer t || arithmetic t.

Definition array t : bool :=
  match t with
  | Array _ _ => true
  | _         => false
  end.

Definition function t : bool :=
  match t with
  | Function _ _ => true
  | _            => false
  end.

Definition is_corresponding_unsigned it1 it2 : bool :=
  match it1, it2 with
  | Signed ibt1, Unsigned ibt2 => eq_integerBaseType ibt1 ibt2
  | _          , _             => false
  end.

Definition corresponding_unsigned it : option integerType :=
  match it with
  | Signed ibt => Some (Unsigned ibt)
  | _          => None
  end.

Definition make_corresponding_unsigned it : integerType :=
  match it with
  | Signed ibt => Unsigned ibt
  | _          => it
  end.

Definition is_integer_promotion P it1 it2 : bool :=
  match it1, it2 with
  | Signed   Int, Signed   Int => true
  | Unsigned Int, Signed   Int => false
  | Unsigned Int, Unsigned Int => true
  | Signed   Int, Unsigned Int => false
  | _           , Signed   Int => le_integer_rank it1 (Signed Int) &&
                                  le_integer_range P it1 (Signed Int)
  | _           , Unsigned Int => le_integer_rank it1 (Signed Int) &&
                                  negb (le_integer_range P it1 (Signed Int))
  | _           , _            => eq_integerType it1 it2 &&
                                  negb (le_integer_rank it1 (Signed Int))
  end.

Definition integer_promotion P it : integerType :=
  match it with
  | Signed   Int => Signed   Int
  | Unsigned Int => Unsigned Int
  | _            => if le_integer_rank it (Signed Int)
                      then if le_integer_range P it (Signed Int)
                             then Signed Int
                             else Unsigned Int
                      else it
  end.

Definition is_promotion P t1 t2 : bool :=
  match t1, t2 with
  | Basic (Integer it1), Basic (Integer it2) => is_integer_promotion P it1 it2
  | _                  , _                   => false
  end.

Definition promotion P t : option ctype :=
  match t with
  | Basic (Integer it) => Some (Basic (Integer (integer_promotion P it)))
  | _                  => None
  end.

Definition is_usual_arithmetic_promoted_integer P it1 it2 it3 : bool :=
  if signed_type it1 then
    if signed_type it2 then
      if lt_integer_rank it2 it1 then
        eq_integerType it1 it3
      else
        eq_integerType it2 it3
    else if unsigned_type it2 then
      if le_integer_rank it1 it2 then
        eq_integerType it2 it3
      else
        if le_integer_range P it2 it1 then
          eq_integerType it1 it3
        else
          is_corresponding_unsigned it1 it3
    else
      false
  else if unsigned_type it1 then
    if unsigned_type it2 then
      if lt_integer_rank it2 it1 then
        eq_integerType it1 it3
      else
        eq_integerType it2 it3
    else if signed_type it2 then
      if le_integer_rank it2 it1 then
        eq_integerType it1 it3
      else if le_integer_range P it1 it2 then
        eq_integerType it2 it3
      else
        is_corresponding_unsigned it2 it3
    else
      false
  else
    false.

Definition usual_arithmetic_promoted_integer P it1 it2 : integerType :=
  if signed_type it1 then
    if signed_type it2 then
      if lt_integer_rank it2 it1 then
        it1
      else
        it2
    else
      if le_integer_rank it1 it2 then
        it2
      else
        if le_integer_range P it2 it1 then
          it1
        else
          make_corresponding_unsigned it1
  else
    if unsigned_type it2 then
      if lt_integer_rank it2 it1 then
        it1
      else
        it2
    else
      if le_integer_rank it2 it1 then
        it1
      else if le_integer_range P it1 it2 then
        it2
      else
        make_corresponding_unsigned it2.

Definition is_usual_arithmetic_integer P it1 it2 it3 : bool :=
  is_usual_arithmetic_promoted_integer P (integer_promotion P it1)
                                         (integer_promotion P it2) it3.

Definition usual_arithmetic_integer P it1 it2 : integerType :=
  usual_arithmetic_promoted_integer P (integer_promotion P it1)
                                      (integer_promotion P it2).

Definition is_usual_arithmetic P t1 t2 t3 : bool :=
  match t1, t2, t3 with
  | Basic (Integer it1), Basic (Integer it2), Basic (Integer it3) => is_usual_arithmetic_integer P it1 it2 it3
  | _                  , _                  , _                   => false
  end.

Definition usual_arithmetic P t1 t2 : option ctype :=
  match t1, t2 with
  | Basic (Integer it1), Basic (Integer it2) => Some (Basic (Integer (usual_arithmetic_integer P it1 it2)))
  | _                  , _                   => None
  end.

Definition object t : bool :=
  match t with
  | Basic _ => true
  | Void => true
  | Pointer _ _ => true
  | Array _ _ => true
  | _ => false
  end.

Definition complete t : bool :=
  match t with
  | Basic _ => true
  | Pointer _ _ => true
  | Array _ _ => true
  | _ => false
  end.

Definition incomplete t : bool :=
  match t with
  | Void => true
  | _ => false
  end.

Definition modifiable q t : bool :=
  object t &&
  negb (array t) &&
  negb (incomplete t) &&
  negb (const q).

Definition real t : bool := integer t.

Definition compatible_params_aux compatible :=
  fix compatible_params (p1 p2 : list (qualifiers * ctype)) : bool :=
    match p1, p2 with
    | nil          , nil           => true
    | (_, t1) :: p1, (_, t2) :: p2 => compatible t1 t2 && compatible_params p1 p2
    | _            , _             => false
    end.

Fixpoint compatible t1 t2 {struct t1} : bool :=
  let compatible_params := compatible_params_aux compatible in
  match t1, t2 with
  | Void          , Void           => true
  | Basic bt1     , Basic bt2      => eq_basicType bt1 bt2
  | Array    t1 n1, Array    t2 n2 => compatible t1 t2 && eq_nat n1 n2
  | Function t1 p1, Function t2 p2 => compatible t1 t2 && compatible_params p1 p2
  | Pointer  q1 t1, Pointer  q2 t2 => compatible t1 t2 && eq_qualifiers q1 q2
  | _             , _              => false
  end.

Definition compatible_params := compatible_params_aux compatible.

Definition is_composite_params_aux is_composite :=
  fix  is_composite_params_aux(p1 p2 p3 : list (qualifiers * ctype)) : bool :=
    match p1, p2, p3 with
    | nil          , nil          , nil            => true
    | (_, t1) :: p1, (_, t2) :: p2, (q3, t3) :: p3 => unqualified q3 &&
                                                      is_composite t1 t2 t3 &&
                                                      is_composite_params_aux p1 p2 p3
    | _            , _            , _              => false
    end.

Fixpoint is_composite (t1 t2 t3 : ctype) : bool :=
  let is_composite_params := is_composite_params_aux is_composite in
  match t1, t2, t3 with
  | Void          , Void          , Void           => true
  | Basic bt1     , Basic bt2     , Basic bt3      => eq_basicType bt1 bt2 && eq_basicType bt1 bt3
  | Array t1 n1   , Array t2 n2   , Array t3 n3    => is_composite t1 t2 t3 && eq_nat n1 n2 && eq_nat n1 n3
  | Function t1 p1, Function t2 p2, Function t3 p3 => is_composite t1 t2 t3 && is_composite_params p1 p2 p3
  | Pointer  q1 t1, Pointer  q2 t2, Pointer  q3 t3 => is_composite t1 t2 t3 && eq_qualifiers q1 q2 && eq_qualifiers q1 q3
  | _             , _             , _              => false
  end.

Definition is_composite_params := is_composite_params_aux is_composite.

Definition composite_params_aux composite :=
  fix composite_params (p1 p2 : list (qualifiers * ctype)) : option (list (qualifiers * ctype)):=
    match p1, p2 with
    | nil          , nil           => Some nil
    | (_, t1) :: p1, (_, t2) :: p2 => match composite t1 t2, composite_params p1 p2 with
                                      | Some t, Some p => Some ((no_qualifiers, t) :: p)
                                      | _     , _      => None
                                      end
    | _            , _             => None
    end.

Fixpoint composite t1 t2 : option ctype :=
  let composite_params := composite_params_aux composite in
  match t1, t2 with
  | Void          , Void           => Some Void
  | Basic bt1     , Basic bt2      => if eq_basicType bt1 bt2
                                        then Some (Basic bt1)
                                        else None
  | Array t1 n1   , Array t2 n2    => if eq_nat n1 n2
                                        then option_map (fun t => Array t n1) (composite t1 t2)
                                        else None
  | Function t1 p1, Function t2 p2 =>
      match composite t1 t2, composite_params p1 p2 with
      | Some t, Some p => Some (Function t p)
      | _     , _      => None
      end
  | Pointer  q1 t1, Pointer  q2 t2 => if eq_qualifiers q1 q2
                                        then option_map (Pointer q1) (composite t1 t2)
                                        else None
  | _             , _              => None
  end.

Definition composite_params := composite_params_aux composite.

Definition combine_qualifiers qs1 qs2 := {|
  const    := const    qs1 || const    qs2;
  restrict := restrict qs1 || restrict qs2;
  volatile := volatile qs1 || volatile qs2
|}.

Definition sub_qualifiers qs1 qs2 :=
     implb (const    qs1) (const    qs2)
  && implb (restrict qs1) (restrict qs2)
  && implb (volatile qs1) (volatile qs2).

Definition pointer_conversion (t:ctype) : ctype :=
  match t with
  | Array    t n => Pointer no_qualifiers t
  | Function t q => Pointer no_qualifiers (Function t q)
  | _            => t
end.

Definition lvalue_convertible t : bool := negb (array t) && complete t.

Definition lvalue_conversion t : option ctype :=
  if lvalue_convertible t then
    Some (pointer_conversion t)
  else
    None.

Definition pointer_to_complete_object t : bool :=
  match t with
  | Pointer _ t => complete t
  | _           => false
  end.

Definition pointers_to_compatible_complete_objects t1 t2 : bool :=
  match t1, t2 with
  | Pointer _ t1, Pointer _ t2 => complete t1 && complete t2 && compatible t1 t2
  | _           , _            => false
  end.  

Definition pointers_to_compatible_objects t1 t2 : bool :=
  match t1, t2 with
  | Pointer _ t1, Pointer _ t2 => object t1 && object t2 && compatible t1 t2
  | _           , _            => false
  end.  

Definition pointer_to_object t : bool :=
  match t with
  | Pointer _ t => object t
  | _           => false
  end.

Definition pointer_to_void t : bool :=
  match t with
  | Pointer _ Void => true
  | _              => false
  end.

Definition pointers_to_compatible_types t1 t2 : bool :=
  match t1, t2 with
  | Pointer _ t1, Pointer _ t2 => compatible t1 t2
  | _           , _            => false
  end.  
