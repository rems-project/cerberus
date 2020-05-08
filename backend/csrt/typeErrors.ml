open Cerb_frontend
module Loc = Locations
open PPrint
open Pp_tools


(* todo: make error messages use Binders.t *)

type call_return_switch_error = 
 | Surplus_A of Sym.t * BaseTypes.t
 | Missing_A of Sym.t * BaseTypes.t
 | Missing_R of Sym.t * Resources.t
 | Mismatch of { mname: Sym.t option; has: VarTypes.t; expected: VarTypes.t; }
 | Unsat_constraint of Sym.t * LogicalConstraints.t
 | Unconstrained_l of Sym.t * LogicalSorts.t

type type_error = 
 | Name_bound_twice of Sym.t
 | Unbound_name of Sym.t
 | Unbound_impl_const of Implementation.implementation_constant
 | Unreachable of PPrint.document
 | Unsupported of PPrint.document
 | Var_kind_error of {
     sym: Sym.t;
     expected : VarTypes.kind;
     has : VarTypes.kind;
   }
 | Illtyped_it of IndexTerms.t
 | Variadic_function of Sym.t
 | Return_error of call_return_switch_error
 | Call_error of call_return_switch_error
 | Integer_value_error
 | Generic_error of PPrint.document
 | Undefined of Undefined.undefined_behaviour
 | Unspecified
 | StaticError of string * Sym.t
 | Z3_fail of string
 | Z3_BT_not_implemented_yet of BaseTypes.t
 | Z3_IT_not_implemented_yet of IndexTerms.t

type t = type_error

let pp_return_error = function
  | Surplus_A (_name,t) ->
     !^"Returning unexpected value of type" ^^^ BaseTypes.pp t
  | Missing_A (_name,t) ->
     !^"Missing return value of type" ^^^ BaseTypes.pp t
  | Missing_R (_name,t) ->
     !^"Missing return resource of type" ^^^ Resources.pp t
  | Mismatch {mname; has; expected} ->
     let has_pp = match has with
       | A t -> !^ "return value of type" ^^^ BaseTypes.pp t
       | L t -> !^ "logical return value of type" ^^^ LogicalSorts.pp t
       | R t -> !^ "return resource of type" ^^^ Resources.pp t
       | C t -> !^ "return constraint" ^^^ LogicalConstraints.pp t
     in
     begin match expected with
     | A t -> !^"Expected return value of type" ^^^ 
                BaseTypes.pp t ^^^ !^ "but found" ^^^ has_pp
     | L t -> !^ "Expected logical return value of type" ^^^ 
                LogicalSorts.pp t ^^^ !^ "but found" ^^^ has_pp
     | R t -> !^"Expected return resource of type" ^^^ 
                Resources.pp t ^^^ !^ "but found" ^^^ has_pp
     | C t -> !^"Expected return constraint" ^^^ 
                LogicalConstraints.pp t ^^^ !^"but found" ^^^ has_pp
        (* dead, I think *)
     end
  | Unsat_constraint (name,c) ->
     !^"Unsatisfied return constraint" ^^^
       typ (Sym.pp name) (LogicalConstraints.pp c)
  | Unconstrained_l (name, ls) ->
     !^"Unconstrained logical variable" ^^^
       typ (Sym.pp name) (LogicalSorts.pp ls)

let pp_call_error = function
  | Surplus_A (_name,t) ->
     !^"Supplying unexpected argument of type" ^^^ BaseTypes.pp t
  | Missing_A (_name,t) ->
     !^"Missing argument of type" ^^^ BaseTypes.pp t
  | Missing_R (_name,t) ->
     !^"Missing resource argument of type" ^^^ Resources.pp t
  | Mismatch {mname; has; expected} ->
     let has_pp = match has with
       | A t -> !^ "(computational) argument of type" ^^^ BaseTypes.pp t
       | L t -> !^ "logical argument of type" ^^^ LogicalSorts.pp t
       | R t -> !^ "resource argument of type" ^^^ Resources.pp t
       | C t -> !^ "constraint argument" ^^^ LogicalConstraints.pp t
     in
     begin match expected with
     | A t -> !^"Expected (computational) argument of type" ^^^ 
                BaseTypes.pp t ^^^ !^ "but found" ^^^ has_pp
     | L t -> !^ "Expected logical argument of type" ^^^ 
                LogicalSorts.pp t ^^^ !^ "but found" ^^^ has_pp
     | R t -> !^"Expected resource argument of type" ^^^ 
                Resources.pp t ^^^ !^ "but found" ^^^ has_pp
     | C t -> !^"Expected constraint argument" ^^^ 
                LogicalConstraints.pp t ^^^ !^"but found" ^^^ has_pp
        (* dead, I think *)
     end
  | Unsat_constraint (name,c) ->
     !^"Unsatisfied argument constraint" ^^^
       typ (Sym.pp name) (LogicalConstraints.pp c)
  | Unconstrained_l (name, ls) ->
     !^"Unconstrained logical variable" ^^^
       typ (Sym.pp name) (LogicalSorts.pp ls)


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
    | Generic_error err ->
       err
    | Unreachable unreachable ->
       !^"Internal error, should be unreachable" ^^ colon ^^^ unreachable
    | Illtyped_it it ->
       !^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp it)
    | Unsupported unsupported ->
       !^"Unsupported feature" ^^ colon ^^^ unsupported
    | Unbound_name unbound ->
       !^"Unbound symbol" ^^ colon ^^^ Sym.pp unbound
    (* | Inconsistent_fundef {loc; decl; defn} ->
     *    sprintf "%s. Function definition inconsistent. Should be %s, is %s"
     *      (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn) *)
    | Unbound_impl_const i ->
       !^("Unbound implementation defined constant" ^
           Implementation.string_of_implementation_constant i)
    | Variadic_function fn ->
       !^"Variadic functions unsupported" ^^^ parens (Sym.pp fn)
    | Return_error err -> 
       pp_return_error err
    | Call_error err -> 
       pp_call_error err
    | Integer_value_error ->
       !^"integer_value_to_num returned None"
    | Undefined undef ->
       !^"Undefined behaviour" ^^ colon ^^^ 
         !^(Undefined.pretty_string_of_undefined_behaviour undef)
    | Unspecified ->
       !^"Unspecified value"
    | StaticError (err, _pe) ->
       !^("Static error: " ^ err)
    | Z3_fail err ->
       !^("Z3 failure: ^ err")
    | Z3_BT_not_implemented_yet bt ->
       !^"Z3: base type" ^^^ BaseTypes.pp bt ^^^ !^"not implemented yet"
    | Z3_IT_not_implemented_yet it ->
       !^"Z3: index term" ^^^ IndexTerms.pp it ^^^ !^"not implemented yet"
    end




let report_type_error loc err : unit = 
  unsafe_error (pp loc err)

