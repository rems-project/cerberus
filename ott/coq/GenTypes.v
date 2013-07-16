Require Import Common.

Require Import AilTypes.
Require Import AilSyntax.

Inductive genIntegerType : Set :=
 | Concrete (it:integerType)
 | SizeT
 | PtrdiffT
 | Unknown (ic : integerConstant)
 | Promote (git : genIntegerType)
 | Usual (git1 : genIntegerType) (git2 : genIntegerType).

Fixpoint eq_genIntegerType x y : bool :=
  match x, y with
  | Concrete it1, Concrete it2 => eq_integerType it1 it2
  | SizeT, SizeT => true
  | PtrdiffT, PtrdiffT => true
  | Unknown ic1, Unknown ic2 => eq_integerConstant ic1 ic2
  | Promote x, Promote y => eq_genIntegerType x y
  | Usual x1 x2, Usual y1 y2 => eq_genIntegerType x1 y1 && eq_genIntegerType x2 y2
  | _, _ => false
  end.

(* equiv_genIntegerType? Looks like composite might need it. *)

Inductive genBasicType : Set :=
 | GenInteger (git:genIntegerType).

Definition eq_genBasicType x y : bool :=
  match x, y with
  | GenInteger git1, GenInteger git2 => eq_genIntegerType git1 git2
  end.

Inductive genType : Set :=
 | GenVoid
 | GenBasic (bt:genBasicType)
 | GenArray (t:ctype) (n:nat)
 | GenFunction (t:ctype) (p:list (qualifiers * ctype))
 | GenPointer (q:qualifiers) (t:ctype).

Fixpoint eq_genType x y :=
  match x, y with
  | GenVoid          , GenVoid           => true
  | GenBasic    gbt1 , GenBasic    gbt2  => eq_genBasicType gbt1 gbt2
  | GenArray    t1 n1, GenArray    t2 n2 => eq_ctype t1 t2 && eq_nat n1 n2
  | GenFunction t1 p1, GenFunction t2 p2 => eq_ctype t1 t2 && eq_params p1 p2
  | GenPointer  q1 t1, GenPointer  q2 t2 => eq_qualifiers q1 q2 && eq_ctype t1 t2
  | _                , _                 => false
  end.

Inductive genTypeCategory : Set := 
 | GenLValueType (q:qualifiers) (t:ctype)
 | GenRValueType (gt:genType).

Definition eq_genTypeCategory x y : bool :=
  match x, y with
  | GenLValueType q1 t1 , GenLValueType q2 t2  => eq_ctype t1 t2 && eq_qualifiers q1 q2
  | GenRValueType    gt1, GenRValueType    gt2 => eq_genType gt1 gt2
  | _                   , _                    => false
  end.

Definition inject_integerType it : genIntegerType := Concrete it.

Definition inject_basicType bt : genBasicType :=
  match bt with
  | Integer it => GenInteger (inject_integerType it)
  end.

Definition inject_parameters_aux (inject_type : ctype -> genType) :=
  fix inject_parameters (p : list (qualifiers * ctype)) :=
    match p with
    | nil         => nil
    | (q, t) :: p => (q, inject_type t) :: (inject_parameters p)
    end.

Fixpoint inject_type t : genType :=
  let inject_parameters := inject_parameters_aux inject_type in
  match t with
  | Void         => GenVoid
  | Basic bt     => GenBasic (inject_basicType bt)
  | Pointer q t => GenPointer q t
  | Array    t n => GenArray t n
  | Function t p => GenFunction t p
  end.

Definition inject_parameters := inject_parameters_aux inject_type.

Definition inject_typeCategory tc : genTypeCategory :=
  match tc with
  | LValueType q t => GenLValueType q t
  | RValueType   t => GenRValueType   (inject_type t)
  end.
