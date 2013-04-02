Require Import Common.
Require Import AilTypes.
Require Import AilSyntax. 

Fixpoint isNullPointerConstant_fun e : bool :=
  match e with
  | Constant (ConstantInteger (0 , None)) => true
  | Cast nil (Pointer nil Void) e         => isNullPointerConstant_fun e
  | _                                     => false
  end.


Fixpoint fv_fun id e : bool :=
  match e with
  | Unary _ e => fv_fun id e
  | Binary e1 _ e2 => orb (fv_fun id e1) (fv_fun id e2)
  | Assign e1 e2 => orb (fv_fun id e1) (fv_fun id e2)
  | CompoundAssign e1 _ e2 => orb (fv_fun id e1) (fv_fun id e2)
  | Conditional e1 e2 e3 => orb (fv_fun id e1) (orb (fv_fun id e2) (fv_fun id e3))
  | Cast _ _ e => fv_fun id e
  | Call e ls => orb (fv_fun id e) (fv_arguments_fun id ls)
  | Var v => bool_of_decision (decide v id : Decision (_ = _))
  | _ => false
  end
with fv_arguments_fun id l : bool :=
  match l with
  | ArgumentsNil => false
  | ArgumentsCons e l => orb (fv_fun id e) (fv_arguments_fun id l)
  end.
