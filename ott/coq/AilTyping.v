Require Import Common.
Require Import Context.
Require Import AilTypes.
Require Import AilSyntax.
Require Import AilTypesAux.
Require Import AilSyntaxAux.
Require Import AilWf.
Require Import Implementation.

Definition type_of_constant P ic : option integerType :=
  match ic with
  | (n, None) =>
      if in_integer_range P n (Signed Int) then
        Some (Signed Int)
      else if in_integer_range P n (Signed Long) then
        Some (Signed Long)
      else if in_integer_range P n (Signed LongLong) then
        Some (Signed LongLong)
      else
        None
  | (n, Some U) =>
      if in_integer_range P n (Unsigned Int) then
        Some (Unsigned Int)
      else if in_integer_range P n (Unsigned Long) then
        Some (Unsigned Long)
      else if in_integer_range P n (Unsigned LongLong) then
        Some (Unsigned LongLong)
      else
        None
  | (n, Some L) =>
      if in_integer_range P n (Signed Long) then
        Some (Signed Long)
      else if in_integer_range P n (Signed LongLong) then
        Some (Signed LongLong)
      else
        None
  | (n, Some UL) =>
      if in_integer_range P n (Unsigned Long) then
        Some (Unsigned Long)
      else if in_integer_range P n (Unsigned LongLong) then
        Some (Unsigned LongLong)
      else
        None
  | (n, Some LL) =>
      if in_integer_range P n (Signed LongLong) then
        Some (Signed LongLong)
      else
        None
  | (n, Some ULL) =>
      if in_integer_range P n (Unsigned LongLong) then
        Some (Unsigned LongLong)
      else
        None
  end.

Definition type_of_rvalue_aux {B} (type_of_expression : expression B -> option typeCategory) e :=
  match type_of_expression e with
  | Some (RValueType   t) => Some (pointer_conversion t)
  | Some (LValueType _ t) => lvalue_conversion t
  | None                  => None
  end.

Definition well_typed_assignment t1 t2 null2 :=
  match t1, t2 with
  | Pointer q1 t1, Pointer q2 t2 => null2 ||
                                    sub_qualifiers q2 q1 && (compatible t1 t2 || void t1 && object t2 || void t2 && object t1) 
  | Pointer q1 t1, _             => null2
  | _            , Pointer _  _  => boolean t1
  | _            , _             => arithmetic t1 && arithmetic t2
  end.

Definition assignable_aux {B} (type_of_rvalue : expression B -> option ctype) :=
  fun t1 e2 =>
    match type_of_rvalue e2 with
    | Some t2 => well_typed_assignment t1 t2 (null_pointer_constant e2)
    | None    => false
    end.

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

Definition well_typed_equality t1 t2 is_null1 is_null2 : bool :=
     pointer t1 && is_null2
  || pointer t2 && is_null1
  || pointer_to_void t1 && pointer_to_object t2
  || pointer_to_void t2 && pointer_to_object t1
  || pointers_to_compatible_types t1 t2
  || arithmetic t1 && arithmetic t2.

Definition combine_qualifiers_left t1 t2 : ctype :=
  match t1, t2 with
  | Pointer q1 t1, Pointer q2 _ => Pointer (combine_qualifiers q1 q2) t1
  | Pointer _  _ , _           => t1
  | _            , _           => t1
  end.

Definition combine_qualifiers_right t1 t2 : ctype :=
  match t1, t2 with
  | Pointer q1 _, Pointer q2 t2 => Pointer (combine_qualifiers q1 q2) t2
  | _           , Pointer _   _  => t2
  | _           , _              => t2
  end.

Definition composite_pointer t1 t2 : option ctype :=
  match t1, t2 with
  | Pointer q1 t1, Pointer q2 t2 => if compatible t1 t2
                                          then option_map (Pointer (combine_qualifiers q1 q2)) (composite t1 t2)
                                          else None
  | _            , _             => None
  end.

Definition well_typed_conditional P t1 t2 t3 null2 null3 : option typeCategory :=
  if scalar t1 then
    if arithmetic t2 && arithmetic t3 then
      option_map RValueType (usual_arithmetic P t2 t3)
    else
      match composite_pointer t2 t3 with
      | Some t => Some (RValueType t)
      | None   => if void t2 && void t3 then
                    Some (RValueType Void)
                  else if pointer t2 && null3 then
                    Some (RValueType (combine_qualifiers_left t2 t3))
                  else if pointer t3 && null2 then
                    Some (RValueType (combine_qualifiers_right t2 t3))
                  else if pointer_to_object t2 && pointer_to_void t3 then
                    Some (RValueType (combine_qualifiers_right t2 t3))
                  else if pointer_to_object t3 && pointer_to_void t2 then
                    Some (RValueType (combine_qualifiers_left t2 t3))
                  else None
      end
  else
    None.

Definition well_typed_arguments_aux {B : Set} (assignable : ctype -> expression B -> bool) :=
  fix well_typed_arguments (es : list (expression B)) (ps : list (qualifiers * ctype)) : bool :=
    match es, ps with
    | nil    , nil           => true
    | e :: es, (_, t1) :: ps => assignable (pointer_conversion t1) e && well_typed_arguments es ps 
    | _      , _             => false
    end.

Fixpoint type_of_expression' {A B} P G (S : sigma A B) (e : expression' B) : option typeCategory :=
  let type_of_rvalue       := type_of_rvalue_aux (type_of_expression P G S) in
  let assignable           := assignable_aux type_of_rvalue                 in
  let well_typed_arguments := well_typed_arguments_aux assignable           in
  match e with
  | Var v =>
      match lookup G v, lookup S v with
      | Some (q, t), None   => Some (LValueType     q t)
      | None       , Some p => Some (RValueType (type_from_sigma p))
      | _          , _      => None
      end
  | Binary e1 Comma e2 => 
     type_of_rvalue e1 >>= fun _  =>
     type_of_rvalue e2 >>= fun t2 =>
     Some (RValueType t2)
  | Unary Address e =>
      match type_of_expression P G S e with
      | Some (LValueType q t)             => Some (RValueType (Pointer q t))
      | Some (RValueType (Function t ps)) => Some (RValueType (Pointer no_qualifiers (Function t ps)))
      | _                                 => None
      end
  | Unary Plus e
  | Unary Minus e =>
      type_of_rvalue e >>= fun t =>
      if arithmetic t then
        option_map RValueType (promotion P t)
      else
        None
  | Unary Bnot e =>
      type_of_rvalue e >>= fun t =>
      if integer t then
        option_map RValueType (promotion P t)
      else
        None
  | Unary Indirection e =>
      type_of_rvalue e >>= fun t =>
      match t with
      | Pointer q (Function t p) => if unqualified q
                                      then Some (RValueType (Pointer q (Function t p)))
                                      else None
      | Pointer q t              => if complete t && object t
                                      then Some (LValueType q t)
                                      else None
      | _                        => None
      end
  | Unary PostfixIncr e
  | Unary PostfixDecr e =>
      match type_of_expression P G S e with
      | Some (LValueType q' t') =>
          lvalue_conversion t' >>= fun t =>
          if modifiable q' t' && (real t' || pointer t')
            then Some (RValueType t)
            else None
      | _ => None
      end
  | Call e es =>
      match type_of_rvalue e with
      | Some (Pointer q (Function t ps)) => if unqualified q && well_typed_arguments es ps
                                                then Some (RValueType t)
                                                else None
      | _                                  => None
      end
  | Assign e1 e2 =>
      match type_of_expression P G S e1, type_of_rvalue e2 with
      | Some (LValueType q1 t1), Some t2 =>
          let t := pointer_conversion t1 in
          if modifiable q1 t1 && assignable t e2
            then Some (RValueType t)
            else None
      | _, _ => None
      end
  | Binary e1 (Arithmetic (Mul  as aop)) e2
  | Binary e1 (Arithmetic (Div  as aop)) e2
  | Binary e1 (Arithmetic (Mod  as aop)) e2
  | Binary e1 (Arithmetic (Band as aop)) e2
  | Binary e1 (Arithmetic (Xor  as aop)) e2
  | Binary e1 (Arithmetic (Bor  as aop)) e2 =>
      type_of_rvalue e1 >>= fun t1 => 
      type_of_rvalue e2 >>= fun t2 =>
      if well_typed_binary_arithmetic t1 aop t2
        then option_map RValueType (usual_arithmetic P t1 t2)
        else None
  | Binary e1 (Arithmetic (Shl  as aop)) e2
  | Binary e1 (Arithmetic (Shr  as aop)) e2 =>
      type_of_rvalue e1 >>= fun t1 => 
      type_of_rvalue e2 >>= fun t2 =>
      if well_typed_binary_arithmetic t1 aop t2
        then option_map RValueType (promotion P t1)
        else None
  | Binary e1 (Arithmetic (Add  as aop)) e2 =>
      type_of_rvalue e1 >>= fun t1 => 
      type_of_rvalue e2 >>= fun t2 =>
      if pointer_to_complete_object t1 && integer t2 then
        Some (RValueType t1)
      else if pointer_to_complete_object t2 && integer t1 then
        Some (RValueType t2)
      else if well_typed_binary_arithmetic t1 aop t2 then
        option_map RValueType (usual_arithmetic P t1 t2)
      else None
  | Binary e1 (Arithmetic (Sub  as aop)) e2 =>
      type_of_rvalue e1 >>= fun t1 =>
      type_of_rvalue e2 >>= fun t2 =>
      if pointers_to_compatible_complete_objects t1 t2 then
        Some (RValueType (Basic (Integer (ptrdiff_t P))))
      else if pointer_to_complete_object t1 && integer t2 then
        Some (RValueType t1)
      else if well_typed_binary_arithmetic t1 Sub t2 then
        option_map RValueType (usual_arithmetic P t1 t2)
      else None
  | Binary e1 And e2
  | Binary e1 Or  e2 =>
      type_of_rvalue e1 >>= fun t1 =>
      type_of_rvalue e2 >>= fun t2 =>
      if scalar t1 && scalar t2
        then Some (RValueType (Basic (Integer (Signed Int))))
        else None
  | Binary e1 Lt e2
  | Binary e1 Gt e2
  | Binary e1 Le e2
  | Binary e1 Ge e2 =>
      type_of_rvalue e1 >>= fun t1 =>
      type_of_rvalue e2 >>= fun t2 =>
      if pointers_to_compatible_objects t1 t2 then
        Some (RValueType (Basic (Integer (Signed Int))))
      else if real t1 && real t2 then
        Some (RValueType (Basic (Integer (Signed Int))))
      else None
  | Binary e1 Eq e2
  | Binary e1 Ne e2 =>
      type_of_rvalue e1 >>= fun t1 =>
      type_of_rvalue e2 >>= fun t2 =>
      if well_typed_equality t1 t2 (null_pointer_constant e1) (null_pointer_constant e2)
        then Some (RValueType (Basic (Integer (Signed Int))))
        else None
  | SizeOf  q t
  | AlignOf q t =>
      if wf_lvalue q t && negb (function t) && negb (incomplete t)
        then Some (RValueType (Basic (Integer (size_t P))))
        else None
  | Cast q Void e =>
      if wf_lvalue q Void then
        match type_of_rvalue e with
        | Some _ => Some (RValueType Void)
        | None   => None
        end
      else
        None
  | Cast q t e =>
      if wf_lvalue q t then
        match type_of_rvalue e with
        | Some t' => if scalar t' && scalar t
                        then Some (RValueType t)
                        else None
        | None     => None
        end
      else
        None
  | Constant (ConstantInteger ic) =>
      type_of_constant P ic >>= fun it =>
      Some (RValueType (Basic (Integer it)))
  | Conditional e1 e2 e3 =>
      type_of_rvalue e1 >>= fun t1 =>
      type_of_rvalue e2 >>= fun t2 =>
      type_of_rvalue e3 >>= fun t3 =>
      well_typed_conditional P t1 t2 t3 (null_pointer_constant e2) (null_pointer_constant e3)
  | CompoundAssign e1 Add e2
  | CompoundAssign e1 Sub e2 =>
      match type_of_expression P G S e1, type_of_rvalue e2 with
      | Some (LValueType q t), Some t2 => 
          lvalue_conversion t >>= fun t1 =>
          if modifiable q t && (arithmetic t1 && arithmetic t2 || pointer_to_complete_object t && integer t2)
            then Some (RValueType t1)
            else None
      | _ , _  => None
      end
  | CompoundAssign e1 aop e2 =>
      match type_of_expression P G S e1, type_of_rvalue e2 with
      | Some (LValueType q t), Some t2 => 
          lvalue_conversion t >>= fun t1 =>
          if modifiable q t && well_typed_binary_arithmetic t1 aop t2
            then Some (RValueType t1)
            else None
      | _, _  => None
      end
  end
with type_of_expression {A B} P G (S : sigma A B) (e : expression B) : option typeCategory :=
  match e with
  | AnnotatedExpression _ e => type_of_expression' P G S e
  end.

Definition type_of_rvalue {A B} P G (S : sigma A B) : expression B -> option ctype := 
  type_of_rvalue_aux (type_of_expression P G S).

Definition assignable {A B} P G (S : sigma A B) : ctype -> expression B -> bool :=
  assignable_aux (type_of_rvalue P G S).

Definition well_typed_arguments {A B} P G (S : sigma A B) : list (expression B) -> list (qualifiers * ctype) -> bool :=
  well_typed_arguments_aux (assignable P G S).

Definition typeable {A B} P G (S : sigma A B)  e : bool :=
  match type_of_expression P G S e with
  | Some _ => true
  | None   => false
  end.

Definition well_formed_binding (b : identifier * (qualifiers * ctype)) :=
  let '(_, (q, t)) := b in
  wf_lvalue q t.

Definition well_formed_bindings bs :=
  all_list well_formed_binding bs && disjoint_bindings eq_identifier bs.

Definition well_typed_block_aux {A B : Set} (well_typed_statement : statement A B -> bool) :=
  all_list well_typed_statement.

Definition well_typed_definition {A B : Set} P G (S : sigma A B) (d : identifier * expression B) :=
  let '(v, e) := d in
  match lookup G v with
  | Some (_, t) => assignable P G S t e
  | _           => false
  end.

Definition well_typed_definitions {A B : Set} P G (S : sigma A B) :=
  all_list (well_typed_definition P G S).

Fixpoint well_typed_statement' {A B} P G (S : sigma A B) t_return (s : statement' A B) : bool :=
  let well_typed_block bs := well_typed_block_aux (well_typed_statement P (add_bindings bs G) S t_return) in
  match s with
  | Label _ s => well_typed_statement P G S t_return s
  | Case ic s => match type_of_constant P ic with
                 | Some _ => well_typed_statement P G S t_return s 
                 | None   => false
                 end
  | Default s => well_typed_statement P G S t_return s
  | Block bs ss => well_formed_bindings bs && fresh_bindings bs S && well_typed_block bs ss
  | Skip      => true
  | Expression e => typeable P G S e
  | If e s1 s2 => match type_of_rvalue P G S e with
                  | Some t => scalar t && well_typed_statement P G S t_return s1
                                       && well_typed_statement P G S t_return s2
                  | None   => false
                  end
  | Switch e s => match type_of_rvalue P G S e with
                  | Some t => integer t && well_typed_statement P G S t_return s
                  | None   => false
                  end
  | While e s => match type_of_rvalue P G S e with
                 | Some t => scalar t && well_typed_statement P G S t_return s
                 | None   => false
                 end
  | Do s e => match type_of_rvalue P G S e with
              | Some t => scalar t && well_typed_statement P G S t_return s
              | None   => false
              end
  | Goto _    => true
  | Continue  => true
  | Break     => true
  | ReturnVoid => eq_ctype t_return Void
  | Return e   => assignable P G S t_return e
  | Declaration ds => well_typed_definitions P G S ds
  end
with well_typed_statement {A B} P G (S : sigma A B) t_return (s : statement A B) : bool :=
  match s with
  | AnnotatedStatement _ s => well_typed_statement' P G S t_return s
  end.

Definition well_typed_block {A B} P G (S : sigma A B) t_return :=
  well_typed_block_aux (well_typed_statement P G S t_return).

Definition well_typed_function {A B} P (S : sigma A B) p :=
  let '(t_return, bs, s) := p in
  fresh_bindings bs S &&
  well_formed_bindings bs &&
  wf_type (Function t_return (parameters_of_bindings bs)) &&
  well_typed_statement P (add_bindings bs empty) S t_return s.

Definition well_typed_sigma {A B} P (S : sigma A B) : bool :=
  Context.all eq_identifier (fun _ => well_typed_function P S) S.

Definition well_typed_program {A B} P (p:program A B) : bool :=
  let (main, S) := p in
  match lookup S main with
  | Some (Basic (Integer (Signed Int)), nil, _) => well_typed_sigma P S
  | Some _                                      => false
  | None                                        => false
  end.
