open Pp
module Loc=Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend

type type_error = 
  | Name_bound_twice of Sym.t
  | Constructor_wrong_argument_number of {
      constructor: CF.Mucore.mu_ctor;
      expected: int;
      has: int;
    }
  | Resource_used of Resources.t * Loc.t list
  | Unbound_name of Sym.t
  | Unbound_impl_const of CF.Implementation.implementation_constant
  | Unreachable of PPrint.document
  | Unsupported of PPrint.document
  | Var_kind_error of {
      sym: Sym.t;
      expected : VarTypes.kind;
      has : VarTypes.kind;
    }
  | Illtyped_it of IndexTerms.t
  | Variadic_function of Sym.t
  | Surplus_A of BaseTypes.t
  | Missing_A of BaseTypes.t
  | Missing_R of Resources.t
  | Mismatch of { has: LS.t; expected: LS.t; }
  | Unsat_constraint of LogicalConstraints.t
  | Unconstrained_l of Sym.t
  | Integer_value_error
  | Generic_error of PPrint.document
  | Undefined of CF.Undefined.undefined_behaviour
  | Unspecified
  | StaticError of string * Sym.t
  | Z3_fail of string
  | Z3_LS_not_implemented_yet of LogicalSorts.t
  | Z3_IT_not_implemented_yet of IndexTerms.t

type t = type_error

let pp (loc : Loc.t) (err : t) = 
  Loc.withloc loc
    begin match err with
    | Var_kind_error err ->
       flow (break 1)
         (List.concat 
            [[ !^"Symbol" ]; [Sym.pp err.sym];
              words "Expected kind"; [VarTypes.pp_kind err.expected];
             (words "but found kind"); [VarTypes.pp_kind err.has]])
    | Name_bound_twice name ->
       !^"Name bound twice" ^^ colon ^^^ squotes (Sym.pp name)
    | Constructor_wrong_argument_number {constructor;expected;has} ->
       let ctor_pp = 
         let open CF.Mucore in
         match constructor with
         | M_Cnil _ -> "list Nil"
         | M_Ccons -> "list Cons"
         | M_Ctuple -> "tuple"
         | M_Carray -> "array"
         | M_CivCOMPL -> "COMPL"
         | M_CivAND -> "AND"
         | M_CivOR -> "OR"
         | M_CivXOR -> "XOR"
         | M_Cspecified -> "specified"
         | M_Cfvfromint -> "fvfromint"
         | M_Civfromfloat -> "fromfloat"
       in
       !^ctor_pp ^^^ !^"constructor applied to" ^^^ !^(string_of_int expected) ^^^ 
         !^"arguments, expected" ^^^ !^(string_of_int has)
    | Generic_error err ->
       err
    | Unreachable unreachable ->
       !^"Internal error, should be unreachable" ^^ colon ^^^ unreachable
    | Illtyped_it it ->
       !^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp false it)
    | Unsupported unsupported ->
       !^"Unsupported feature" ^^ colon ^^^ unsupported
    | Resource_used (resource,where) ->
       !^"Resource" ^^^ Resources.pp false resource ^^^ 
         !^"has already been used:" ^^^ braces (pp_list Loc.pp where)
    | Unbound_name unbound ->
       !^"Unbound symbol" ^^ colon ^^^ Sym.pp unbound
    (* | Inconsistent_fundef {loc; decl; defn} ->
     *    sprintf "%s. Function definition inconsistent. Should be %s, is %s"
     *      (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn) *)
    | Unbound_impl_const i ->
       !^("Unbound implementation defined constant" ^
           CF.Implementation.string_of_implementation_constant i)
    | Variadic_function fn ->
       !^"Variadic functions unsupported" ^^^ parens (Sym.pp fn)
    | Surplus_A t ->
       !^"Unexpected value of type" ^^^ BaseTypes.pp false t
    | Missing_A t ->
       !^"Missing value of type" ^^^ BaseTypes.pp false t
    | Missing_R t ->
       !^"Missing resource of type" ^^^ Resources.pp false t
    | Mismatch {has; expected} ->
       !^"Expected value of type" ^^^ LS.pp false expected ^^^
         !^"but found" ^^^ !^"value of type" ^^^ LS.pp false has
    | Unsat_constraint c ->
       !^"Unsatisfied constraint" ^^^
         LogicalConstraints.pp false c
    | Unconstrained_l name ->
       !^"Unconstrained logical variable" ^^^ Sym.pp name
    | Integer_value_error ->
       !^"integer_value_to_num returned None"
    | Undefined undef ->
       !^"Undefined behaviour" ^^ colon ^^^ 
         !^(CF.Undefined.pretty_string_of_undefined_behaviour undef)
    | Unspecified ->
       !^"Unspecified value"
    | StaticError (err, _pe) ->
       !^("Static error: " ^ err)
    | Z3_fail err ->
       !^("Z3 failure: ^ err")
    | Z3_LS_not_implemented_yet bt ->
       !^"Z3: base type" ^^^ LogicalSorts.pp false bt ^^^ !^"not implemented yet"
    | Z3_IT_not_implemented_yet it ->
       !^"Z3: index term" ^^^ IndexTerms.pp false it ^^^ !^"not implemented yet"
    end




(* let report_type_error loc err : unit = 
 *   unsafe_error (pp loc err) *)

