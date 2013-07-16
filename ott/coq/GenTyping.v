Require Import Common.
Require Import Implementation.
Require Import AilSyntax.
Require Import AilTypes.
Require Import AilSyntaxAux.
Require Import AilWf.

Require AilTypesAux.
Require AilTyping.

Require Import GenTypes.
Require Import GenTypesAux.
Require Import Annotation.

Notation "'do' x <- m ; c" := (m >>= (fun x => c))
    (at level 60, right associativity, x ident).
Notation "'do' ( x , y ) <- m ; c" := (m >>= (fun p => let '(x, y) := p in c))
    (at level 60, right associativity, x ident, y ident).

Definition type_of {A1 A2 : Set} (A : annotation A1 A2) (e : expression A2) :=
  let '(AnnotatedExpression a _) := e in
  get_type A a.

Definition annotate_rvalue_aux {A1 A2 : Set}
                               (A : annotation A1 A2)
                               (annotate_expression : expression A1 -> option (expression A2)) e :=
  do e <- annotate_expression e;
  match type_of A e with
  | GenRValueType   gt => Some (e, pointer_conversion gt)
  | GenLValueType _ t  => do t <- AilTypesAux.lvalue_conversion t;
                          Some (e, inject_type t)
  end.

(* Sound but not principal. *)
Definition type_of_constant ic : genIntegerType := Unknown ic.

Definition well_typed_assignment t1 t2 null2 :=
  match t1, t2 with
  | Pointer q1 t1, GenPointer q2 t2 => null2 ||
                                       AilTypesAux.sub_qualifiers q2 q1 && (AilTypesAux.compatible t1 t2 || AilTypesAux.void t1 && AilTypesAux.object t2 || AilTypesAux.void t2 && AilTypesAux.object t1)
  | Pointer q1 t1, _                => null2
  | _            , GenPointer _  _  => AilTypesAux.boolean t1
  | _            , _                => AilTypesAux.arithmetic t1 && arithmetic t2
  end.

Definition well_typed_equality t1 t2 is_null1 is_null2 : bool :=
     pointer t1 && is_null2
  || pointer t2 && is_null1
  || pointer_to_void t1 && pointer_to_object t2
  || pointer_to_void t2 && pointer_to_object t1
  || pointers_to_compatible_types t1 t2
  || arithmetic t1 && arithmetic t2.

Definition well_typed_binary_arithmetic t1 aop t2 : bool :=
  match aop with
  | Mul  => arithmetic t1 && arithmetic t2
  | Div  => arithmetic t1 && arithmetic t2
  | Mod  => integer    t1 && integer    t2
  | Add  => arithmetic t1 && arithmetic t2
  | Sub  => arithmetic t1 && arithmetic t2
  | Shl  => integer    t1 && integer    t2
  | Shr  => integer    t1 && integer    t2
  | Band => integer    t1 && integer    t2
  | Xor  => integer    t1 && integer    t2
  | Bor  => integer    t1 && integer    t2
  end.

Definition combine_qualifiers_left gt1 gt2 : genType :=
  match gt1, gt2 with
  | GenPointer q1 t1, GenPointer q2 _ => GenPointer (AilTypesAux.combine_qualifiers q1 q2) t1
  | GenPointer _  _ , _               => gt1
  | _               , _               => gt1
  end.

Definition combine_qualifiers_right gt1 gt2 : genType :=
  match gt1, gt2 with
  | GenPointer q1 _, GenPointer q2 t2 => GenPointer (AilTypesAux.combine_qualifiers q1 q2) t2
  | _              , GenPointer _   _ => gt2
  | _              , _                => gt2
  end.

Definition well_typed_conditional gt1 gt2 gt3 null2 null3 : option genTypeCategory :=
  if scalar gt1 then
    if arithmetic gt2 && arithmetic gt3 then
      do gt <- usual_arithmetic gt2 gt3;
      Some (GenRValueType gt)
    else
      match composite_pointer gt2 gt3 with
      | Some gt => Some (GenRValueType gt)
      | None    => if void gt2 && void gt3 then
                     Some (GenRValueType GenVoid)
                   else if pointer gt2 && null3 then
                     Some (GenRValueType (combine_qualifiers_left gt2 gt3))
                   else if pointer gt3 && null2 then
                     Some (GenRValueType (combine_qualifiers_right gt2 gt3))
                   else if pointer_to_object gt2 && pointer_to_void gt3 then
                     Some (GenRValueType (combine_qualifiers_right gt2 gt3))
                   else if pointer_to_object gt3 && pointer_to_void gt2 then
                     Some (GenRValueType (combine_qualifiers_left gt2 gt3))
                   else None
      end
  else
    None.

Definition annotate_assignee_aux {A1 A2 : Set}
                                 (A : annotation A1 A2)
                                 (annotate_rvalue : expression A1 -> option (expression A2 * genType)) :=
  fun t1 e2 =>
    do (e2, gt2) <- annotate_rvalue e2;
    if well_typed_assignment t1 gt2 (null_pointer_constant e2)
      then Some e2
      else None.

Definition annotate_arguments_aux {A1 A2 : Set}
                                  (A : annotation A1 A2)
                                  (annotate_assignee : ctype -> expression A1 -> option (expression A2)) :=
  fix annotate_arguments es (p : list (qualifiers * _)) : option (list (expression A2)) :=
    match es, p with
    | nil    , nil          => Some nil
    | e :: es, (_, t1) :: p => do e  <- annotate_assignee (AilTypesAux.pointer_conversion t1) e;
                               do es <-annotate_arguments es p;
                               Some (e :: es)
    | _      , _            => None
    end.

Fixpoint annotate_expression' {A1 A2 B1 B2 : Set}
                              (A : annotation A1 A2)
                              (S : sigma B1 B2) (G : gamma)
                              (e : expression' A1) : option (expression' A2 * genTypeCategory) :=
  let annotate_rvalue := annotate_rvalue_aux A (annotate_expression A S G) in
  let annotate_assignee := annotate_assignee_aux A annotate_rvalue in
  let annotate_arguments := annotate_arguments_aux A annotate_assignee in
  match e with
  | Var v =>
      match lookup G v, lookup S v with
      | Some (q, t), None   => Some (Var v, GenLValueType q t)
      | None       , Some p => Some (Var v, GenRValueType (inject_type (type_from_sigma p)))
      | _          , _      => None
      end
  | Binary e1 Comma e2 => 
      do (e1, _  ) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      Some (Binary e1 Comma e2, GenRValueType gt2)
  | Unary Address e =>
      do e <- annotate_expression A S G e;
      match type_of A e with
      | GenLValueType q t               => Some (Unary Address e, GenRValueType (GenPointer q t))
      | GenRValueType (GenFunction t p) => Some (Unary Address e, GenRValueType (GenPointer no_qualifiers (Function t p)))
      | _                               => None
      end
  | Unary (Plus  as uop)  e
  | Unary (Minus as uop) e =>
      do (e, gt) <- annotate_rvalue e;
      if arithmetic gt then
        do gt <- promotion gt;
        Some (Unary uop e, GenRValueType gt)
      else
        None
  | Unary Bnot e =>
      do (e, gt) <- annotate_rvalue e;
      if integer gt then
        do gt <- promotion gt;
        Some (Unary Bnot e, GenRValueType gt)
      else
        None
  | Unary Indirection e =>
      do (e, gt) <- annotate_rvalue e;
      match gt with
      | GenPointer q (Function t p) => if AilTypesAux.unqualified q
                                            then Some (Unary Indirection e, GenRValueType (GenPointer q (Function t p)))
                                            else None
      | GenPointer q t                 => if AilTypesAux.complete t && AilTypesAux.object t
                                            then Some (Unary Indirection e, GenLValueType q t)
                                            else None
      | _                              => None
      end
  | Unary (PostfixIncr as uop) e
  | Unary (PostfixDecr as uop) e =>
      do e <- annotate_expression A S G e;
      match type_of A e with
      | GenLValueType q' t' =>
          do t <- AilTypesAux.lvalue_conversion t';
          if AilTypesAux.modifiable q' t' && (AilTypesAux.real t' || AilTypesAux.pointer t')
            then Some (Unary uop e, GenRValueType (inject_type t))
            else None
      | _ => None
      end
  | Call e es =>
      do (e, gt) <- annotate_rvalue e;
      match gt with
      | GenPointer q (Function t p) => if AilTypesAux.unqualified q then
                                         do es <- annotate_arguments es p;
                                         Some (Call e es, GenRValueType (inject_type t))
                                       else None
      | _                           => None
      end
  | Assign e1 e2 =>
      do e1 <- annotate_expression A S G e1;
      match type_of A e1 with
      | GenLValueType q1 t1 =>
          do e2 <- annotate_assignee t1 e2;
          let t := AilTypesAux.pointer_conversion t1 in
          if AilTypesAux.modifiable q1 t1
            then Some (Assign e1 e2, GenRValueType (inject_type t))
            else None
      | _ => None
      end
  | Binary e1 (Arithmetic (Mul  as aop)) e2
  | Binary e1 (Arithmetic (Div  as aop)) e2
  | Binary e1 (Arithmetic (Mod  as aop)) e2
  | Binary e1 (Arithmetic (Band as aop)) e2
  | Binary e1 (Arithmetic (Xor  as aop)) e2
  | Binary e1 (Arithmetic (Bor  as aop)) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if well_typed_binary_arithmetic gt1 aop gt2
        then do gt <- usual_arithmetic gt1 gt2;
             Some (Binary e1 (Arithmetic aop) e2, GenRValueType gt)
        else None
  | Binary e1 (Arithmetic (Shl  as aop)) e2
  | Binary e1 (Arithmetic (Shr  as aop)) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if well_typed_binary_arithmetic gt1 aop gt2 then
        do gt <- promotion gt1;
        Some (Binary e1 (Arithmetic aop) e2, GenRValueType gt)
      else None
  | Binary e1 (Arithmetic Add) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if pointer_to_complete_object gt1 && integer gt2 then
        Some (Binary e1 (Arithmetic Add) e2, GenRValueType gt1)
      else if pointer_to_complete_object gt2 && integer gt1 then
        Some (Binary e1 (Arithmetic Add) e2, GenRValueType gt2)
      else if well_typed_binary_arithmetic gt1 Add gt2 then
        do gt <- usual_arithmetic gt1 gt2;
        Some (Binary e1 (Arithmetic Add) e2, GenRValueType gt)
      else None
  | Binary e1 (Arithmetic Sub) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if pointers_to_compatible_complete_objects gt1 gt2 then
        Some (Binary e1 (Arithmetic Sub) e2, GenRValueType (GenBasic (GenInteger PtrdiffT)))
      else if pointer_to_complete_object gt1 && integer gt2 then
        Some (Binary e1 (Arithmetic Sub) e2, GenRValueType gt1)
      else if well_typed_binary_arithmetic gt1 Sub gt2 then
        do gt <- usual_arithmetic gt1 gt2;
        Some (Binary e1 (Arithmetic Sub) e2, GenRValueType gt)
      else None
  | Binary e1 (And as bop) e2
  | Binary e1 (Or  as bop) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if scalar gt1 && scalar gt2
        then Some (Binary e1 bop e2, GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
        else None
  | Binary e1 (Lt as bop) e2
  | Binary e1 (Gt as bop) e2
  | Binary e1 (Le as bop) e2
  | Binary e1 (Ge as bop) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if pointers_to_compatible_objects gt1 gt2 then
        Some (Binary e1 bop e2, GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
      else if real gt1 && real gt2 then
        Some (Binary e1 bop e2, GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
      else None
  | Binary e1 (Eq as bop) e2
  | Binary e1 (Ne as bop) e2 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      if well_typed_equality gt1 gt2 (null_pointer_constant e1) (null_pointer_constant e2)
        then Some (Binary e1 bop e2, GenRValueType (GenBasic (GenInteger (Concrete (Signed Int)))))
        else None
  | SizeOf  q t =>
      if wf_lvalue q t && negb (AilTypesAux.function t) && negb (AilTypesAux.incomplete t)
        then Some (SizeOf q t, GenRValueType (GenBasic (GenInteger (SizeT))))
        else None
  | AlignOf q t =>
      if wf_lvalue q t && negb (AilTypesAux.function t) && negb (AilTypesAux.incomplete t)
        then Some (AlignOf q t, GenRValueType (GenBasic (GenInteger (SizeT))))
        else None
  | Cast q Void e =>
      if wf_lvalue q Void then
        do (e, _) <- annotate_rvalue e;
        Some (Cast q Void e, GenRValueType GenVoid)
      else
        None
  | Cast q t e =>
      if wf_lvalue q t then
        do (e, gt) <- annotate_rvalue e;
        if scalar gt && AilTypesAux.scalar t
          then Some (Cast q t e, GenRValueType (inject_type t))
          else None
      else
        None
  | Conditional e1 e2 e3 =>
      do (e1, gt1) <- annotate_rvalue e1;
      do (e2, gt2) <- annotate_rvalue e2;
      do (e3, gt3) <- annotate_rvalue e3;
      do gtc <- well_typed_conditional gt1 gt2 gt3 (null_pointer_constant e2) (null_pointer_constant e3);
      Some (Conditional e1 e2 e3, gtc)
  | CompoundAssign e1 (Add as aop) e2
  | CompoundAssign e1 (Sub as aop) e2 =>
      do e1        <- annotate_expression A S G e1;
      do (e2, gt2) <- annotate_rvalue e2;
      match type_of A e1 with
      | GenLValueType q t => 
          do t1 <- AilTypesAux.lvalue_conversion t;
          if AilTypesAux.modifiable q t && (AilTypesAux.arithmetic t1 && arithmetic gt2 || AilTypesAux.pointer_to_complete_object t && integer gt2)
            then Some (CompoundAssign e1 aop e2, GenRValueType (inject_type t1))
            else None
      | _  => None
      end
  | CompoundAssign e1 aop e2 =>
      do e1        <- annotate_expression A S G e1;
      do (e2, gt2) <- annotate_rvalue e2;
      match type_of A e1 with
      | GenLValueType q t =>
          do t1 <- AilTypesAux.lvalue_conversion t;
          let t1 := inject_type t1 in
          if AilTypesAux.modifiable q t && well_typed_binary_arithmetic t1 aop gt2
            then Some (CompoundAssign e1 aop e2, GenRValueType t1)
            else None
      | _  => None
      end
  | Constant (ConstantInteger ic) =>
      Some (Constant (ConstantInteger ic), GenRValueType (GenBasic (GenInteger (type_of_constant ic))))
  end
with annotate_expression {A1 A2 B1 B2: Set}
                         (A : annotation A1 A2)
                         (S : sigma B1 B2) (G : gamma)
                         (e : expression A1) : option (expression A2) :=
  let '(AnnotatedExpression a e) := e in
  do (e, gt) <- annotate_expression' A S G e;
  Some (AnnotatedExpression (Annotation.add_type A gt a) e).

Definition annotate_rvalue {A1 A2 B1 B2 : Set}
                           (A : annotation A1 A2)
                           (S : sigma B1 B2) (G : gamma) : expression A1 -> option (expression A2 * genType) :=
  annotate_rvalue_aux A (annotate_expression A S G).

Definition annotate_assignee {A1 A2 B1 B2 : Set}
                             (A : annotation A1 A2)
                             (S : sigma B1 B2) (G : gamma) : ctype -> expression A1 -> option (expression A2) :=
  annotate_assignee_aux A (annotate_rvalue A S G).

Definition annotate_arguments {A1 A2 B1 B2 : Set}
                              (A : annotation A1 A2)
                              (S : sigma B1 B2) (G : gamma) : list (expression A1) -> list (qualifiers * ctype) -> option (list (expression A2)) :=
  annotate_arguments_aux A (annotate_assignee A S G).

Definition annotate_block_aux {A1 A2 B : Set}
                              (A : annotation A1 A2)
                              (annotate_statement : statement B A1 -> option (statement B A2)) :=
  fix annotate_block (ss : list (statement B A1)) : option (list (statement B A2)) :=
    match ss with
    | nil     => Some nil
    | s :: ss => do s  <- annotate_statement s;
                 do ss <- annotate_block ss;
                 Some (s :: ss)
    end.

Definition annotate_definition {A1 A2 B1 B2 : Set}
                               (A : annotation A1 A2)
                               (S : sigma B1 B2) G (d : identifier * expression A1) :=
  let '(v, e) := d in
  match lookup G v with
  | Some (_, t) => do e <- annotate_assignee A S G t e;
                   Some (v, e)
  | _           => None
  end.

Fixpoint annotate_definitions {A1 A2 B1 B2 : Set}
                              (A : annotation A1 A2)
                              (S : sigma B1 B2) G ds :=
  match ds with
  | nil     => Some nil
  | d :: ds => do d  <- annotate_definition  A S G d;
               do ds <- annotate_definitions A S G ds;
               Some (d :: ds)
  end.

Fixpoint annotate_statement' {A1 A2 B B1 B2 : Set}
                             (A : annotation A1 A2)
                             (S : sigma B1 B2) G t_return (s : statement' B A1) : option (statement' B A2) :=
  let annotate_block bs := annotate_block_aux A (annotate_statement A S (Context.add_bindings bs G) t_return) in
  match s with
  | Label l s => do s <- annotate_statement A S G t_return s; Some (Label l s)
  | Case ic s => do s <- annotate_statement A S G t_return s; Some (Case ic s)
  | Default s => do s <- annotate_statement A S G t_return s; Some (Default s)
  | Block bs ss => if AilTyping.well_formed_bindings bs && fresh_bindings bs S then
                     do ss <- annotate_block bs ss;
                     Some (Block bs ss)
                   else
                     None
  | Skip      => Some Skip
  | Expression e => do e <- annotate_expression A S G e; Some (Expression e)
  | If e s1 s2 => do (e, t) <- annotate_rvalue A S G e;
                  if scalar t then
                    do s1 <- annotate_statement A S G t_return s1;
                    do s2 <- annotate_statement A S G t_return s2;
                    Some (If e s1 s2)
                  else
                    None
  | Switch e s => do (e, t) <- annotate_rvalue A S G e;
                  if integer t then
                    do s <- annotate_statement A S G t_return s;
                    Some (Switch e s)
                  else
                    None
  | While e s => do (e, t) <- annotate_rvalue A S G e;
                 if scalar t then
                   do s <- annotate_statement A S G t_return s;
                   Some (While e s)
                 else
                   None
  | Do s e => do (e, t) <- annotate_rvalue A S G e;
              if scalar t then
                do s <- annotate_statement A S G t_return s;
                Some (Do s e)
              else
                None
  | Goto v    => Some (Goto v)
  | Continue  => Some Continue
  | Break     => Some Break
  | ReturnVoid => if eq_ctype t_return Void
                    then Some ReturnVoid
                    else None
  | Return e   => do e <- annotate_assignee A S G t_return e;
                  Some (Return e)
  | Declaration ds => do ds <- annotate_definitions A S G ds; Some (Declaration ds)
  end
with annotate_statement {A1 A2 B B1 B2 : Set}
                        (A : annotation A1 A2)
                        (S : sigma B1 B2) G t_return (s : statement B A1) : option (statement B A2) :=
  let '(AnnotatedStatement b s) := s in
  do s <- annotate_statement' A S G t_return s;
  Some (AnnotatedStatement b s).

Definition annotate_block {A1 A2 B B1 B2 : Set}
                          (A : annotation A1 A2)
                          (S : sigma B1 B2) G t_return (bs : list (statement B A1)) :=
  annotate_block_aux A (annotate_statement A S G t_return) bs.

Definition annotate_function {A1 A2 B B1 B2 : Set}
                             (A : annotation A1 A2)
                             (S : sigma B1 B2) (p : _ * _ * statement B A1) :=
  let '(t_return, bs, s) := p in
  if fresh_bindings bs S &&
     AilTyping.well_formed_bindings bs &&
     wf_type (Function t_return (parameters_of_bindings bs))
  then
    do s <- annotate_statement A S (Context.add_bindings bs Context.empty) t_return s;
    Some (t_return, bs, s)
  else
    None.

Definition annotate_sigma {A1 A2 B : Set} (A : annotation A1 A2) (S : sigma B A1) : option (sigma B A2) :=
  Context.mapP eq_identifier (annotate_function A S) S.

Definition annotate_program {A1 A2 B : Set} (A : annotation A1 A2) (p:program B A1) : option (program B A2) :=
  let (main, S) := p in
  match lookup S main with
  | Some (Basic (Integer (Signed Int)), nil, _) => do S <- annotate_sigma A S; Some (main, S)
  | Some _                                      => None
  | None                                        => None
  end.
