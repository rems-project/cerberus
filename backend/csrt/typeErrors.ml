open Cerb_frontend
module Loc = Location
open Loc
open PPrint
open Pp_tools

 type call_return_switch_error = 
  | Surplus_A of Sym.t * BaseTypes.t
  | Surplus_L of Sym.t * LogicalSorts.t
  | Surplus_R of Sym.t * Resources.t
  | Missing_A of Sym.t * BaseTypes.t
  | Missing_L of Sym.t * LogicalSorts.t
  | Missing_R of Sym.t * Resources.t
  | Mismatch of { mname: Sym.t option; has: VarTypes.t; expected: VarTypes.t; }
  | Unsat_constraint of Sym.t * LogicalConstraints.t
  | Unconstrained_l of Sym.t * LogicalSorts.t

 type type_error = 
  | Name_bound_twice of Sym.t
  | Unbound_name of Sym.t
  | Unreachable of string
  | Unsupported of string
  | Var_kind_error of {
      sym: Sym.t;
      expected : VarTypes.kind;
      has : VarTypes.kind;
    }
  | Illtyped_it of IndexTerms.t
  | Variadic_function of Sym.t
  | Return_error of call_return_switch_error
  | Call_error of call_return_switch_error
  | Switch_error of call_return_switch_error
  | Integer_value_error
  | Undefined_behaviour of Undefined.undefined_behaviour
  | Unspecified_value
  | Generic_error of string

 let pp_return_error loc err = 
   withloc loc
     begin match err with
     | Surplus_A (_name,t) ->
        !^"Returning unexpected value of type" ^^^ BaseTypes.pp t
     | Surplus_L (_name,t) ->
        !^"Returning unexpected logical value of type" ^^^ LogicalSorts.pp t
     | Surplus_R (_name,t) ->
        !^"Returning unexpected resource of type" ^^^ Resources.pp t
     | Missing_A (_name,t) ->
        !^"Missing return value of type" ^^^ BaseTypes.pp t
     | Missing_L (_name,t) ->
        !^"Missing logical return value of type" ^^^ LogicalSorts.pp t
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
     end

 let pp_call_error loc err = 
   withloc loc
     begin match err with
     | Surplus_A (_name,t) ->
        !^"Supplying unexpected argument of type" ^^^ BaseTypes.pp t
     | Surplus_L (_name,t) ->
        !^"Supplying unexpected logical argument of type" ^^^ LogicalSorts.pp t
     | Surplus_R (_name,t) ->
        !^"Supplying unexpected resource of type" ^^^ Resources.pp t
     | Missing_A (_name,t) ->
        !^"Missing argument of type" ^^^ BaseTypes.pp t
     | Missing_L (_name,t) ->
        !^"Missing logical argument of type" ^^^ LogicalSorts.pp t
     | Missing_R (_name,t) ->
        !^"Missing resource argument of type" ^^^ Resources.pp t
     | Mismatch {mname; has; expected} ->
        let has_pp = match has with
          | A t -> !^ "argument of type" ^^^ BaseTypes.pp t
          | L t -> !^ "logical argument of type" ^^^ LogicalSorts.pp t
          | R t -> !^ "resource argument of type" ^^^ Resources.pp t
          | C t -> !^ "constraint argument" ^^^ LogicalConstraints.pp t
        in
        begin match expected with
        | A t -> !^"Expected argument of type" ^^^ 
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
        !^"Unsatisfied return constraint" ^^^
          typ (Sym.pp name) (LogicalConstraints.pp c)
     | Unconstrained_l (name, ls) ->
        !^"Unconstrained logical variable" ^^^
          typ (Sym.pp name) (LogicalSorts.pp ls)
     end


 let pp loc = function 
  | Var_kind_error err ->
     withloc loc (!^"Expected kind" ^^^ VarTypes.pp_kind err.expected ^^^
                        !^"but found kind" ^^^ VarTypes.pp_kind err.has)
  | Name_bound_twice name ->
     withloc loc (!^"Name bound twice" ^^ colon ^^^ 
                    squotes (Sym.pp name))
  | Generic_error err ->
     withloc loc (!^err)
  | Unreachable unreachable ->
     withloc loc (!^"Internal error, should be unreachable" ^^ 
                    colon ^^^ !^unreachable)
  | Illtyped_it it ->
     withloc loc (!^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp it))
  | Unsupported unsupported ->
     withloc loc (!^"Unsupported feature" ^^ colon ^^^ !^unsupported)
  | Unbound_name unbound ->
     withloc loc (!^"Unbound symbol" ^^ colon ^^^ Sym.pp unbound)
  (* | Inconsistent_fundef {loc; decl; defn} ->
   *    sprintf "%s. Function definition inconsistent. Should be %s, is %s"
   *      (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn) *)
  | Variadic_function fn ->
     withloc loc (!^"Variadic functions unsupported" ^^^ parens (Sym.pp fn))
  | Return_error err -> 
     pp_return_error loc err
  | Call_error err -> 
     pp_call_error loc err
  | Switch_error err -> 
     pp_call_error loc err
  | Integer_value_error ->
     withloc loc (!^"integer_value_to_num returned None")
  | Undefined_behaviour undef ->
     withloc loc (!^"Undefined behaviour" ^^ colon ^^^ 
                    !^(Undefined.pretty_string_of_undefined_behaviour undef))
  | Unspecified_value ->
     withloc loc (!^"Unspecified value")




let report_type_error loc err = 
  print 
    [ h1 "Error!"
    ; pp loc err
    ]
