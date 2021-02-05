open Pp
open Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module RE=Resources
module Loc = Locations

type label_kind = 
  | Return
  | Loop
  | Other


type access =
  | Load of BT.member option
  | Store of BT.member option
  | Kill
  | Free

type situation = 
  | Access of access
  | FunctionCall
  | LabelCall of label_kind
  | Subtyping
  | Unpacking

let for_access = function
  | Kill -> !^"for de-allocating"
  | Load None ->  !^"for reading"
  | Load (Some m) -> !^"for reading struct member" ^^^ Id.pp m
  | Store None ->  !^"for writing"
  | Store (Some m) -> !^"struct member" ^^^ Id.pp m
  | Free -> !^"for free-ing"

let for_situation = function
  | Access access -> for_access access
  | FunctionCall -> !^"for calling function"
  | LabelCall Return -> !^"for returning"
  | LabelCall Loop -> !^"for loop"
  | LabelCall Other -> !^"for calling label"
  | Subtyping -> !^"for subtyping"
  | Unpacking -> !^"for unpacking"





type sym_or_string = 
  | Sym of Sym.t
  | String of string


type state_pp = doc


type type_error = 
  | Unbound_name of sym_or_string
  | Name_bound_twice of sym_or_string
  | Missing_function of Sym.t
  | Missing_struct of BT.tag
  | Missing_predicate of string
  | Missing_member of BT.tag * BT.member

  | Missing_ownership of {addr : doc; state : state_pp; used : (loc list) option; situation : situation}   
  | Unknown_resource_size of {resource: doc; state : state_pp; situation : situation}
  | Missing_resource of {resource : doc; state : state_pp; used: (loc list) option; situation : situation}
  | Resource_mismatch of {has: doc; state : state_pp; expect: doc; situation : situation}
  | Cannot_unpack of {resource : doc; state : state_pp; situation : situation}
  | Uninitialised_read of {is_member : BT.member option; state : state_pp}
  | Unused_resource of {resource: doc; state : state_pp}
  | Misaligned of access

  | Number_members of {has: int; expect: int}
  | Number_arguments of {has: int; expect: int}
  | Mismatch of { has: LS.t; expect: LS.t; }
  | Illtyped_it : 'bt IndexTerms.term -> type_error
  | Polymorphic_it : 'bt IndexTerms.term -> type_error
  | Unsat_constraint of {constr : doc; hint : doc option; state : state_pp}
  | Unconstrained_logical_variable of Sym.t

  | Kind_mismatch of {has: Kind.t; expect: Kind.t}

  | Undefined_behaviour of CF.Undefined.undefined_behaviour * state_pp (*  *)
  | Unspecified of CF.Ctype.ctype
  | StaticError of string

  | Unsupported of Pp.document
  | Generic of Pp.document













let pp_type_error te = 

  let pp_o_used locs = 
    !^"Maybe last used in the following places:" ^^^
      Pp.list Loc.pp locs
  in
  let pp_used = Option.map pp_o_used in
  let in_state, consider_state = 
    let in_state s = !^"In state:" ^/^ s in
    let consider_state s = !^"Consider the state:" ^/^ s in
    (in_state, consider_state)
  in


  match te with
  | Unbound_name unbound ->
     let name_pp = match unbound with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Unbound name" ^^ colon ^^^ name_pp, [])
  | Name_bound_twice name ->
     let name_pp = match name with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Name bound twice" ^^ colon ^^^ squotes name_pp, [])
  | Missing_function sym ->
     (!^"function" ^^^ Sym.pp sym ^^^ !^"not defined", [])
  | Missing_struct tag ->
     (!^"struct" ^^^ Sym.pp tag ^^^ !^"not defined", [])
  | Missing_predicate id ->
     (!^"predicate" ^^^ !^id ^^^ !^"not defined", [])
  | Missing_member (tag, member) ->
     (!^"struct" ^^^ Sym.pp tag ^^^ !^"does not have member" ^^^ 
        Id.pp member, [])

  | Missing_ownership {addr; state; used; situation} ->
     let msg = 
       !^"Missing ownership of location" ^^^ 
         addr ^^^ for_situation situation 
     in
     (msg, in_state state :: Option.list [pp_used used])
  | Unknown_resource_size {resource; state; situation} ->
     let msg = 
       !^"Cannot tell size of resource" ^^^ 
         resource ^^^ for_situation situation 
     in
     (msg, [in_state state])
  | Missing_resource {resource; state; used; situation} ->
     let msg = !^"Missing resource" ^^^ resource ^^^ for_situation situation in
     (msg, in_state state :: Option.list [pp_used used] )
  | Resource_mismatch {has; state; expect; situation} ->
     let msg = !^"Need a resource" ^^^ has ^^^ !^"but have resource" ^^^ expect in
     (msg, [in_state state])
  | Cannot_unpack {resource; state; situation} ->
     let msg = !^"Cannot unpack resource" ^^^ resource ^^^ for_situation situation in
     (msg, [in_state state])

  | Uninitialised_read {is_member; state} ->
     let msg = match is_member with
       | None -> !^"Trying to read uninitialised data"
       | Some m -> !^"Trying to read uninitialised struct member" ^^^ Id.pp m
     in
     (msg, [in_state state])
  | Unused_resource {resource;state} ->
     let msg = !^"Left-over unused resource" ^^^ resource in
     (msg, [in_state state])
  | Misaligned access ->
     let msg = match access with
     | Kill -> !^"Misaligned de-allocation operation"
     | Load _ -> !^"Misaligned read"
     | Store _ ->  !^"Misaligned write"
     | Free ->  !^"Misaligned free"
     in
     (msg, [])

  | Number_members {has;expect} ->
     (!^"Wrong number of struct members:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Number_arguments {has;expect} ->
     (!^"Wrong number of arguments:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Mismatch {has; expect} ->
     (!^"Expected value of type" ^^^ LS.pp false expect ^^^
        !^"but found value of type" ^^^ LS.pp false has, [])
  | Illtyped_it it ->
     (!^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp it), [])
  | Polymorphic_it it ->
     (!^"Polymorphic index term" ^^ colon ^^^ (IndexTerms.pp it), [])
  | Unsat_constraint {constr;hint; state} ->
     let msg = match hint with
       | Some hint -> !^"Unsatisfied constraint" ^^^ parens hint ^^^ constr 
       | None -> !^"Unsatisfied constraint" ^^^ constr 
     in
     (msg, [consider_state state])
  | Unconstrained_logical_variable name ->
     (!^"Unconstrained logical variable" ^^^ Sym.pp name, [])
  | Kind_mismatch {has; expect} ->
     (!^"Expected" ^^^ Kind.pp expect ^^^ 
        !^"but found" ^^^ Kind.pp has, [])

  | Undefined_behaviour (undef, state) -> 
     let ub = CF.Undefined.pretty_string_of_undefined_behaviour undef in
     (!^"Undefined behaviour", [!^ub; consider_state state])
  | Unspecified _ctype ->
     (!^"Unspecified value", [])
  | StaticError err ->
     (!^("Static error: " ^ err), [])

  | Unsupported unsupported ->
     (!^"Unsupported feature" ^^ colon ^^^ unsupported, [])
  | Generic err ->
     (err, [])


(* stealing some logic from pp_errors *)
let report (loc : Loc.t) (ostacktrace : string option) (err : type_error) = 
  let (msg, extras) = pp_type_error err in
  let extras = match ostacktrace with
    | Some stacktrace -> extras @ [item "stacktrace" !^stacktrace]
    | None -> extras
  in
  Pp.error loc msg extras
