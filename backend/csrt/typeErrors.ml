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
  | Var_kind_error of {
      loc : Loc.t;
      sym: Sym.t;
      expected : VarTypes.kind;
      has : VarTypes.kind;
    }
  | Name_bound_twice of {
      loc : Loc.t;
      name: Sym.t
    }
  | Unreachable of {
      loc: Loc.t;
      unreachable : string;
    }
  | Illtyped_it of {
      loc: Loc.t;
      it: IndexTerms.t;
    }
  | Unsupported of { 
      loc: Loc.t;
      unsupported: string; 
    }
  | Unbound_name of {
      loc: Loc.t; 
      is_function: bool;
      unbound: Sym.t;
    }
  (* | Inconsistent_fundef of {
   *     loc: Loc.t;
   *     decl: FunctionTypes.t;
   *     defn: FunctionTypes.t;
   *   } *)
  | Variadic_function of {
      loc: Loc.t;
      fn: Sym.t;
    }
  | Return_error of 
      Loc.t * call_return_switch_error
  | Call_error of 
      Loc.t * call_return_switch_error
  | Switch_error of 
      Loc.t * call_return_switch_error
  | Integer_value_error of 
      Loc.t
  | Undefined_behaviour of
      Loc.t * Undefined.undefined_behaviour
  | Unspecified_value of
      Loc.t
  | Generic_error of Loc.t * string

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


 let pp = function 
  | Var_kind_error err ->
     withloc err.loc (!^"Expected kind" ^^^ VarTypes.pp_kind err.expected ^^^
                        !^"but found kind" ^^^ VarTypes.pp_kind err.has)
  | Name_bound_twice err ->
     withloc err.loc (!^"Name bound twice" ^^ colon ^^^ 
                        squotes (Sym.pp err.name))
  | Generic_error (loc, err) ->
     withloc loc (!^err)
  | Unreachable {loc; unreachable} ->
     withloc loc (!^"Internal error, should be unreachable" ^^ 
                    colon ^^^ !^unreachable)
  | Illtyped_it {loc; it} ->
     withloc loc (!^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp it))
  | Unsupported {loc; unsupported} ->
     withloc loc (!^"Unsupported feature" ^^ colon ^^^ !^unsupported)
  | Unbound_name {loc; is_function; unbound} ->
     withloc loc
       (if is_function 
        then !^"Unbound function" ^^ colon ^^^ Sym.pp unbound
        else !^"Unbound symbol" ^^ colon ^^^ Sym.pp unbound)
  (* | Inconsistent_fundef {loc; decl; defn} ->
   *    sprintf "%s. Function definition inconsistent. Should be %s, is %s"
   *      (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn) *)
  | Variadic_function {loc; fn} ->
     withloc loc (!^"Variadic functions unsupported" ^^^ parens (Sym.pp fn))
  | Return_error (loc, err) -> 
     pp_return_error loc err
  | Call_error (loc, err) -> 
     pp_call_error loc err
  | Switch_error (loc, err) -> 
     pp_call_error loc err
  | Integer_value_error loc ->
     withloc loc (!^"integer_value_to_num returned None")
  | Undefined_behaviour (loc, undef) ->
     withloc loc (!^"Undefined behaviour" ^^ colon ^^^ 
                    !^(Undefined.pretty_string_of_undefined_behaviour undef))
  | Unspecified_value loc ->
     withloc loc (!^"Unspecified value")







let report_error err = 
  Cerb_backend.Pipeline.run_pp None (h1 "Error!");
  Cerb_backend.Pipeline.run_pp None (pp err);
