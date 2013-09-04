Require Import Common.
Require Import AilTypes.
Require Import AilTypesAux_defns.

Inductive adjusted : ctype -> Prop :=
 | Adjusted t :
     ~ array    t ->
     ~ function t ->
     adjusted t.


(* defns JwfLvalue *)
Inductive wfLvalue : qualifiers -> ctype -> Prop :=    (* defn wfLvalue *)
 | WfLvalue_Default : forall q t,
     ~ pointer t ->
     ~ (restrict q = true) ->
     ~ function t ->
     wfType t ->
     wfLvalue q t
 | WfLvalue_Function : forall q t,
     ~ pointer t ->
     function t ->
     unqualified q ->
     wfType t ->
     wfLvalue q t
 | WfLvalue_PointerToObject : forall (q' q:qualifiers) (t:ctype),
     object t ->
     wfType (Pointer q t) ->
     wfLvalue q' (Pointer q t)
 | WfLvalue_PointerToOther : forall (q' q:qualifiers) (t:ctype),
     ~ object t ->
     ~ (restrict q' = true) ->
     wfType (Pointer q t) ->
     wfLvalue q' (Pointer q t) 
with wfType : ctype -> Prop :=    (* defn wfType *)
 | WfType_Void : 
     wfType Void
 | WfType_BasicType : forall (bt:basicType),
     wfType (Basic bt)
 | WfType_Array : forall (t:ctype) (n:nat),
     complete t ->
     wfType t ->
     wfType (Array t n) 
 | WfType_Function : forall t p,
     ~ array t ->
     ~ function t ->
     wfType t ->
     wfParameters p ->
     wfType (Function t p) 
 | WfType_Pointer : forall (q:qualifiers) (t:ctype),
     wfLvalue q t ->
     wfType (Pointer q t) 
with wfParameters : list (qualifiers * ctype) -> Prop :=
 | WfParameters_nil :
     wfParameters nil
 | WfParameters_cons q t p :
     adjusted t ->
     ~ incomplete t ->
     wfLvalue q t ->
     wfParameters p ->
     wfParameters ((q, t) :: p).
