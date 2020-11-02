open Pp
module Loc=Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module RE=Resources
module VB=VariableBinding

type stacktrace = string



let do_stack_trace () = 
  let open Pp in
  if !Debug_ocaml.debug_level > 0 then 
    let backtrace = Printexc.get_callstack (!print_level * 10) in
    Some (Printexc.raw_backtrace_to_string backtrace)
  else 
    None

type access = 
  | Load 
  | Store
  | Kill


type sym_or_string = 
  | Sym of Sym.t
  | String of string


type type_error = 
  | Unbound_name of sym_or_string
  | Name_bound_twice of sym_or_string

  | Uninitialised of BT.member option
  | Missing_resource of Resources.t
  | Missing_ownership of access * BT.member option
  | ResourceMismatch of { has: RE.t; expect: RE.t; }
  | Unused_resource of { resource: Resources.t }

  | Number_arguments of {has: int; expect: int}
  | Mismatch of { has: LS.t; expect: LS.t; }
  | Illtyped_it of IndexTerms.t
  | Unsat_constraint of LogicalConstraints.t
  | Unconstrained_logical_variable of Sym.t
  | Kind_mismatch of {has: VariableBinding.kind; expect: VariableBinding.kind}

  | Undefined_behaviour of CF.Undefined.undefined_behaviour * document option
  | Unspecified of CF.Ctype.ctype
  | StaticError of string

  | Internal of Pp.document
  | Z3_fail of Pp.document
  | Unsupported of Pp.document
  | Generic of Pp.document

type t = type_error








let pp_type_error = function
  | Missing_ownership (access,omember) ->
     let msg = match access, omember with
     | Kill, None ->  
        !^"Missing ownership for de-allocating"
     | Kill, Some m ->  
        !^"Missing ownership for de-allocating struct member" ^^^ BT.pp_member m
     | Load, None   ->  
        !^"Missing ownership for reading"
     | Load, Some m -> 
        !^"Missing ownership for reading struct member" ^^^ BT.pp_member m
     | Store, None   -> 
        !^"Missing ownership for writing"
     | Store, Some m -> 
        !^"Missing ownership for writing struct member" ^^^ BT.pp_member m
     in
     (msg, [])
  | Uninitialised omember ->
     begin match omember with
     | None -> 
        (!^"Trying to read uninitialised data", [])
     | Some m -> 
        (!^"Trying to read uninitialised struct member" ^^^ BT.pp_member m, [])
     end
  | Name_bound_twice name ->
     let name_pp = match name with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Name bound twice" ^^ colon ^^^ squotes name_pp, [])
  | Unbound_name unbound ->
     let name_pp = match unbound with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Unbound symbol" ^^ colon ^^^ name_pp, [])
  | Internal err ->
     (!^"Internal error" ^^ colon ^^^ err, [])
  | Z3_fail err ->
     (!^"Z3 failure:" ^^^ err, [])
  | Unsupported unsupported ->
     (!^"Unsupported feature" ^^ colon ^^^ unsupported, [])
  | Mismatch {has; expect} ->
     (!^"Expected value of type" ^^^ LS.pp false expect ^^^
        !^"but found value of type" ^^^ LS.pp false has, [])
  | ResourceMismatch {has; expect} ->
     (!^"Need a resource" ^^^ RE.pp expect ^^^
        !^"but have resource" ^^^ RE.pp has, [])
  | Number_arguments {has;expect} ->
     (!^"Wrong number of arguments:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Kind_mismatch {has; expect} ->
     (!^"Expected" ^^^ VariableBinding.kind_pp expect ^^^ 
        !^"but found" ^^^ VariableBinding.kind_pp has, [])
  | Illtyped_it it ->
     (!^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp it), [])
  | Unsat_constraint c ->
     (!^"Unsatisfied constraint" ^^^ LogicalConstraints.pp c, [])
  | Unconstrained_logical_variable name ->
     (!^"Unconstrained logical variable" ^^^ Sym.pp name, [])
  | Missing_resource t ->
     (!^"Missing resource of type" ^^^ Resources.pp t, [])
  | Unused_resource {resource;_} ->
     (!^"Left-over unused resource" ^^^ Resources.pp resource, [])
  | Undefined_behaviour (undef, omodel) -> 
     let ub = CF.Undefined.pretty_string_of_undefined_behaviour undef in
     let extras = match omodel with
       | Some model -> [("UB",!^ub); ("model", model)]
       | None -> [("UB",!^ub)]
     in
     (!^"Undefined behaviour", extras)
  | Unspecified _ctype ->
     (!^"Unspecified value", [])
  | StaticError err ->
     (!^("Static error: " ^ err), [])
  | Generic err ->
     (err, [])


(* stealing some logic from pp_errors *)
let type_error (loc : Loc.t) (ostacktrace : string option) (err : t) = 
  let open Pp in
  let (head, pos) = Locations.head_pos_of_location loc in
  let (msg, extras) = pp_type_error err in
  let extras = match ostacktrace with
    | Some stacktrace -> extras @ [("stacktrace", !^stacktrace)]
    | None -> extras
  in
  debug 1 (lazy hardline);
  print stderr (format [FG (Red, Bright)] "error:" ^^^ 
                format [FG (Default, Bright)] head ^^^ msg);
  print stderr !^pos;
  List.iter (fun (descr, pp) -> print stderr (item descr pp)) extras

