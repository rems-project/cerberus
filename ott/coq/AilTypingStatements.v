Require Import Common.
Require Import Context.
Require Import AilTypes.
Require Import AilTypesAux.
Require Import AilSyntax.
Require Import AilSyntaxAux.
Require Import Implementation.
Require Import AilTyping.
Require Import AilWf.

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
