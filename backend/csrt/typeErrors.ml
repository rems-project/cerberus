open Pp
module Loc=Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module RE=Resources



type type_error = 
  | Name_bound_twice of Sym.t
  | Unbound_name of Sym.t
  | Unbound_impl_const of CF.Implementation.implementation_constant
  | Struct_not_defined of BT.tag

  | Unreachable of PPrint.document
  | Z3_fail of string

  | Unsupported of PPrint.document
  | Variadic_function of Sym.t

  | Mismatch of { has: LS.t; expect: LS.t; }
  | Number_arguments of {has: int; expect: int}
  | Illtyped_it of IndexTerms.t
  | Unsat_constraint of LogicalConstraints.t
  | Unconstrained_logical_variable of Sym.t
  | Missing_resource of Resources.t
  | Resource_already_used of Resources.t * Loc.t list
  | Unused_resource of {resource: Resources.t; is_merge: bool}

  | Undefined_behaviour of CF.Undefined.undefined_behaviour
  | Unspecified of CF.Ctype.ctype
  | StaticError of string * Sym.t

  | Generic of PPrint.document

type t = type_error


let unreachable err = 
  if !debug_level > 0 then 
    let backtrace = Printexc.get_callstack (!debug_level * 10) in
    Unreachable (err ^^ !^"." ^/^ !^(Printexc.raw_backtrace_to_string backtrace))
  else 
    Unreachable err


let withloc loc p : PPrint.document = 
  flow (break 1) [Loc.pp loc;p]

let pp (loc : Loc.t) (err : t) = 
  withloc loc
    begin match err with
    | Name_bound_twice name ->
       !^"Name bound twice" ^^ colon ^^^ squotes (Sym.pp name)
    | Unbound_name unbound ->
       !^"Unbound symbol" ^^ colon ^^^ Sym.pp unbound
    | Unbound_impl_const i ->
       !^("Unbound implementation defined constant" ^
           CF.Implementation.string_of_implementation_constant i)
    | Struct_not_defined (BT.Tag tag) ->
       !^"struct" ^^^ Sym.pp tag ^^^ !^"not defined"

    | Unreachable unreachable ->
       !^"Internal error, should be unreachable" ^^ colon ^^^ unreachable
    | Z3_fail err ->
       !^("Z3 failure: ^ err")
    | Unsupported unsupported ->
       !^"Unsupported feature" ^^ colon ^^^ unsupported
    | Variadic_function fn ->
       !^"Variadic functions unsupported" ^^^ parens (Sym.pp fn)

    | Mismatch {has; expect} ->
       !^"Expected value of type" ^^^ LS.pp false expect ^^^
         !^"but found" ^^^ !^"value of type" ^^^ LS.pp false has
    | Number_arguments {has;expect} ->
       !^"Wrong number of arguments:" ^^^
         !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
           !^"has" ^^^ !^(string_of_int has)
    | Illtyped_it it ->
       !^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp false it)
    | Unsat_constraint c ->
       !^"Unsatisfied constraint" ^^^
         LogicalConstraints.pp false c
    | Unconstrained_logical_variable name ->
       !^"Unconstrained logical variable" ^^^ Sym.pp name

    | Missing_resource t ->
       !^"Missing resource of type" ^^^ Resources.pp false t
    | Resource_already_used (resource,where) ->
       !^"Resource" ^^^ Resources.pp false resource ^^^ 
         !^"has already been used:" ^^^ braces (pp_list Loc.pp where)
    | Unused_resource {resource;_} ->
       !^"Left-over unused resource" ^^^ Resources.pp false resource

    | Undefined_behaviour undef ->
       !^"Undefined behaviour" ^^ colon ^^^ 
         !^(CF.Undefined.pretty_string_of_undefined_behaviour undef)
    | Unspecified _ctype ->
       !^"Unspecified value"
    | StaticError (err, _pe) ->
       !^("Static error: " ^ err)

    | Generic err ->
       err
    end




(* let report_type_error loc err : unit = 
 *   unsafe_error (pp loc err) *)

