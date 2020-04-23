open Cerb_frontend
module Loc = Location
open Printf

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

 let pp_return_error loc = function
  | Surplus_A (_name,t) ->
     sprintf "Line %s. Returning unexpected value of type %s" 
       (Loc.pp loc) (BaseTypes.pp t)
  | Surplus_L (_name,t) ->
     sprintf "%s. Returning unexpected logical value of type %s" 
       (Loc.pp loc) (LogicalSorts.pp t)
  | Surplus_R (_name,t) ->
     sprintf "%s. Returning unexpected resource of type %s" 
       (Loc.pp loc) (Resources.pp t)
  | Missing_A (_name,t) ->
     sprintf "%s. Missing return value of type %s" 
       (Loc.pp loc) (BaseTypes.pp t)
  | Missing_L (_name,t) ->
     sprintf "%s. MIssing logical return value of type %s" 
       (Loc.pp loc) (LogicalSorts.pp t)
  | Missing_R (_name,t) ->
     sprintf "%s. Missing return resource of type %s" 
       (Loc.pp loc) (Resources.pp t)
  | Mismatch {mname; has; expected} ->
     let has_pp = match has with
       | A t -> sprintf "return value of type %s" (BaseTypes.pp t)
       | L t -> sprintf "logical return value of type %s" (LogicalSorts.pp t)
       | R t -> sprintf "return resource of type %s" (Resources.pp t)
       | C t -> sprintf "return constraint %s" (LogicalConstraints.pp t)
     in
     begin match expected with
     | A t ->
        sprintf "%s. Expected return value of type %s but found %s" 
          (Loc.pp loc) (BaseTypes.pp t) has_pp
     | L t ->
        sprintf "%s. Expected logical return value of type %s but found %s" 
          (Loc.pp loc) (LogicalSorts.pp t) has_pp
     | R t ->
        sprintf "%s. Expected return resource of type %s but found %s" 
          (Loc.pp loc) (Resources.pp t) has_pp
     | C t ->
        (* dead, I think *)
        sprintf "%s. Expected return constraint %s but found %s" 
          (Loc.pp loc) (LogicalConstraints.pp t) has_pp
     end
  | Unsat_constraint (name,c) ->
     sprintf "%s. Unsatisfied return constraint %s: %s" 
       (Loc.pp loc) (Sym.pp name) (LogicalConstraints.pp c)
  | Unconstrained_l (name, ls) ->
     sprintf "%s. Unconstrained logical variable %s: %s" 
       (Loc.pp loc) (Sym.pp name) (LogicalSorts.pp ls)


 let pp_call_error loc = function
  | Surplus_A (_name,t) ->
     sprintf "Line %s. Supplying unexpected argument of type %s" 
       (Loc.pp loc) (BaseTypes.pp t)
  | Surplus_L (_name,t) ->
     sprintf "%s. Supplying unexpected logical argument of type %s" 
       (Loc.pp loc) (LogicalSorts.pp t)
  | Surplus_R (_name,t) ->
     sprintf "%s. Supplying unexpected resource of type %s" 
       (Loc.pp loc) (Resources.pp t)
  | Missing_A (_name,t) ->
     sprintf "%s. Missing argument of type %s" 
       (Loc.pp loc) (BaseTypes.pp t)
  | Missing_L (_name,t) ->
     sprintf "%s. Missing logical argument of type %s" 
       (Loc.pp loc) (LogicalSorts.pp t)
  | Missing_R (_name,t) ->
     sprintf "%s. Missing resource argument of type %s" 
       (Loc.pp loc) (Resources.pp t)
  | Mismatch {mname; has; expected} ->
     let has_pp = match has with
       | A t -> sprintf "argument of type %s" (BaseTypes.pp t)
       | L t -> sprintf "logical argument of type %s" (LogicalSorts.pp t)
       | R t -> sprintf "resource argument of type %s" (Resources.pp t)
       | C t -> sprintf "constraint argument %s" (LogicalConstraints.pp t)
     in
     begin match expected with
     | A t ->
        sprintf "%s. Expected argument of type %s but found %s" 
          (Loc.pp loc) (BaseTypes.pp t) has_pp
     | L t ->
        sprintf "%s. Expected logical argument of type %s but found %s" 
          (Loc.pp loc) (LogicalSorts.pp t) has_pp
     | R t ->
        sprintf "%s. Expected resource argument of type %s but found %s" 
          (Loc.pp loc) (Resources.pp t) has_pp
     | C t ->
        (* dead, I think *)
        sprintf "%s. Expected constraint argument %s but found %s" 
          (Loc.pp loc) (LogicalConstraints.pp t) has_pp
     end
  | Unsat_constraint (name,lc) ->
     sprintf "%s. Unsatisfied return constraint %s: %s" 
       (Loc.pp loc) (Sym.pp name) (LogicalConstraints.pp lc)
  | Unconstrained_l (name,ls) ->
     sprintf "%s. Unconstrained logical variable %s: %s" 
       (Loc.pp loc) (Sym.pp name) (LogicalSorts.pp ls)

 let pp = function 
  | Var_kind_error err ->
     sprintf "%s. Expected kind %s but found kind %s"
       (Loc.pp err.loc) (VarTypes.pp_kind err.expected) (VarTypes.pp_kind err.has)
  | Name_bound_twice err ->
     sprintf "%s. Name bound twice: %s" 
       (Loc.pp err.loc) (Sym.pp err.name)
  | Generic_error (loc, err) ->
     sprintf "%s. %s" 
       (Loc.pp loc) err
  | Unreachable {loc; unreachable} ->
     sprintf "%s. Should be unreachable: %s" 
       (Loc.pp loc) unreachable
  | Illtyped_it {loc; it} ->
     sprintf "%s. Illtyped index term: %s" 
       (Loc.pp loc) (IndexTerms.pp it)
  | Unsupported {loc; unsupported} ->
     sprintf "%s. Unsupported feature: %s" 
       (Loc.pp loc) unsupported
  | Unbound_name {loc; is_function; unbound} ->
     sprintf "%s. Unbound %s %s"
       (Loc.pp loc) (if is_function then "function" else "symbol") (Sym.pp unbound)
  (* | Inconsistent_fundef {loc; decl; defn} ->
   *    sprintf "%s. Function definition inconsistent. Should be %s, is %s"
   *      (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn) *)
  | Variadic_function {loc; fn } ->
     sprintf "Line %s. Variadic functions unsupported (%s)" 
       (Loc.pp loc) (Sym.pp fn)
  | Return_error (loc, err) -> 
     pp_return_error loc err
  | Call_error (loc, err) -> 
     pp_call_error loc err
  | Switch_error (loc, err) -> 
     pp_call_error loc err
  | Integer_value_error loc ->
     sprintf "%s. integer_value_to_num return None"
       (Loc.pp loc)
  | Undefined_behaviour (loc, undef) ->
     sprintf "%s. Undefined behaviour: %s"
       (Loc.pp loc)
       (Undefined.pretty_string_of_undefined_behaviour undef)
  | Unspecified_value loc ->
     sprintf "%s. Unspecified value"
       (Loc.pp loc)




