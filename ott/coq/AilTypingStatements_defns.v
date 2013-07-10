Require Import Common.
Require Import Implementation.
Require Import AilTypes.
Require Import AilSyntax.

Require Import AilTypesAux_defns.
Require Import AilWf_defns.
Require Import AilTyping_defns.
Require Import Context_defns.

Inductive wellFormedBinding : identifier * (qualifiers * ctype) -> Prop :=
 | WellFormedBinding v q t :
     wfLvalue q t ->
     wellFormedBinding (v, (q, t)).

Inductive wellFormedBindings : bindings -> Prop :=
 | WellFormedBindings bs :
     disjointBindings bs ->
     allList wellFormedBinding bs ->
     wellFormedBindings bs.

Inductive wellTypedDefinition {A B} P G (S : sigma  A B) : identifier * expression B -> Prop :=
  | WellTypedDefinition :
      forall v e q t,
        lookup G v (q, t) ->
        assignable P G S t e ->
        wellTypedDefinition P G S (v, e).

Inductive wellTypedStatement' {A B} P G (S : sigma A B) : ctype -> statement' A B -> Prop :=    (* defn wellTypedStatement *)
 | WellTypedStatement'_Label : forall t_return l s,
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Label l s)
 | WellTypedStatement'_Case : forall t_return ic it s,
     typeOfConstant P ic it ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Case ic s)
 | WellTypedStatement'_Default : forall t_return s,
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Default s)
 | WellTypedStatement'_Block : forall t_return bs ss,
     wellFormedBindings bs ->
     freshBindings bs S ->
     allList (wellTypedStatement P (Context.add_bindings bs G) S t_return) ss ->
     wellTypedStatement' P G S t_return (Block bs ss)
 | WellTypedStatement'_Skip : forall t_return,
     wellTypedStatement' P G S t_return Skip
 | WellTypedStatement'_Expression : forall t_return e,
     typeable P G S e ->
     wellTypedStatement' P G S t_return (Expression e)
 | WellTypedStatement'_If : forall t_return e s1 s2 t,
     typeOfRValue P G S e t ->
     scalar t ->
     wellTypedStatement  P G S t_return s1 ->
     wellTypedStatement  P G S t_return s2 ->
     wellTypedStatement' P G S t_return (If e s1 s2)
 | WellTypedStatement'_Switch : forall t_return e s t,
     typeOfRValue P G S e t ->
     integer t ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Switch e s)
 | WellTypedStatement'_While : forall t_return e s t,
     typeOfRValue P G S e t ->
     scalar t ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (While e s)
 | WellTypedStatement'_Do : forall t_return s e t,
     typeOfRValue P G S e t ->
     scalar t ->
     wellTypedStatement  P G S t_return s ->
     wellTypedStatement' P G S t_return (Do s e)
 | WellTypedStatement'_Goto : forall t_return l,
     wellTypedStatement' P G S t_return (Goto l)
 | WellTypedStatement'_Continue : forall t_return,
     wellTypedStatement' P G S t_return Continue
 | WellTypedStatement'_Break : forall t_return,
     wellTypedStatement' P G S t_return Break
 | WellTypedStatement'_ReturnVoid :
     wellTypedStatement' P G S Void ReturnVoid
 | WellTypedStatement'_Return : forall t_return e,
     assignable P G S t_return e ->
     wellTypedStatement' P G S t_return (Return e)
 | WellTypedStatement'_Declaration : forall t_return ds,
     allList (wellTypedDefinition P G S) ds ->
     wellTypedStatement' P G S t_return (Declaration ds)
with wellTypedStatement {A B} P G (S : sigma A B) : ctype -> statement A B -> Prop :=
 | WellTypedStatement_AnnotatedStatement : forall t_return a s,
     wellTypedStatement' P G S t_return s ->
     wellTypedStatement  P G S t_return (AnnotatedStatement a s).

Inductive wellTypedFunction {A B} P (S : sigma A B) : (ctype * bindings) * statement A B -> Prop :=
  | WellTypedFunction t_return bs s :
      wellFormedBindings bs ->
      freshBindings bs S ->
      wfType (Function t_return (parameters_of_bindings bs)) ->
      wellTypedStatement P (Context.add_bindings bs nil) S t_return s ->
      wellTypedFunction P S (t_return, bs, s).      

Inductive wellTypedSigma {A B} P (S : sigma A B) : Prop :=
 | WellTypedSigma :
     (forall v p, lookup S v p -> wellTypedFunction P S p) ->
     wellTypedSigma P S.

Inductive wellTypedProgram {A B} P : program A B -> Prop :=    (* defn wellTypedProgram *)
 | WellTypedProgram main S s:
       lookup S main (Basic (Integer (Signed Int)), nil, s) ->
       wellTypedSigma P S ->
       wellTypedProgram P (main, S).
