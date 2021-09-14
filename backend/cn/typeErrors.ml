open Pp
open Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module Loc = Locations

type label_kind = 
  | Return
  | Loop
  | Other


type access =
  | Load of BT.member option
  | Store of BT.member option
  | Deref
  | Kill
  | Free

type situation = 
  | Access of access
  | FunctionCall
  | LabelCall of label_kind
  | Subtyping
  | ArrayShift
  | MemberShift
  | Pack of Id.t
  | Unpack of Id.t

let checking_situation = function
  | Access access -> !^"checking access"
  | FunctionCall -> !^"checking function call"
  | LabelCall Return -> !^"checking return"
  | LabelCall Loop -> !^"checking loop entry"
  | LabelCall Other -> !^"checking label call"
  | Subtyping -> !^"checking subtyping"
  | ArrayShift -> !^"array shifting"
  | MemberShift -> !^"member shifting"
  | Pack name -> !^"packing predicate" ^^^ Id.pp name
  | Unpack name -> !^"unpacking predicate" ^^^ Id.pp name

let for_access = function
  | Kill -> !^"for de-allocating"
  | Deref -> !^"for dereferencing"
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
  | ArrayShift -> !^"for array shifting"
  | MemberShift -> !^"for member shifting"
  | Pack name -> !^"for packing predicate" ^^^ Id.pp name
  | Unpack name -> !^"for unpacking predicate" ^^^ Id.pp name





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
  | Missing_ctype_predicate of Sctypes.t
  | Missing_member of BT.tag * BT.member

  | Missing_resource of {resource : doc; state : state_pp; situation : situation; oinfo : info option}
  | Resource_mismatch of {has: doc; state : state_pp; expect: doc; situation : situation}
  | Uninitialised_read of {is_member : BT.member option; state : state_pp}
  | Unused_resource of {resource: doc; state : state_pp}

  | Number_members of {has: int; expect: int}
  | Number_arguments of {has: int; expect: int}
  | Number_input_arguments of {has: int; expect: int}
  | Number_output_arguments of {has: int; expect: int}
  | Mismatch of { has: LS.t; expect: LS.t; }
  | Mismatch_lvar of { has: LS.t; expect: LS.t; spec_info: info}
  | Illtyped_it of {context: Pp.document; it: Pp.document; has: LS.t; expected: string} (* 'expected' as in Kayvan's Core type checker *)
  | Polymorphic_it : 'bt IndexTerms.term -> type_error
  | Write_value_unrepresentable of {state : state_pp}
  | Unsat_constraint of {constr : doc; state : state_pp; info : info}
  | Unconstrained_logical_variable of Sym.t * string option
  | Array_as_value of Sym.t * string option
  | Logical_variable_not_good_for_unification of Sym.t * string option

  | Kind_mismatch of {has: Kind.t; expect: Kind.t}

  | Undefined_behaviour of CF.Undefined.undefined_behaviour * state_pp
  | Implementation_defined_behaviour of document * state_pp
  | Unspecified of CF.Ctype.ctype
  | StaticError of string * state_pp

  | Generic of Pp.document













let pp_type_error te = 

  let consider_state s = !^"Consider the state:" ^/^ s in


  match te with
  | Unbound_name unbound ->
     let name_pp = match unbound with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Unbound name" ^^ colon ^^^ squotes (name_pp), [])
  | Name_bound_twice name ->
     let name_pp = match name with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Name bound twice" ^^ colon ^^^ squotes name_pp, [])
  | Missing_function sym ->
     (!^"function" ^^^ squotes (Sym.pp sym) ^^^ !^"not defined", [])
  | Missing_struct tag ->
     (!^"struct" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined", [])
  | Missing_predicate id ->
     (!^"predicate" ^^^ squotes (!^id) ^^^ !^"not defined", [])
  | Missing_ctype_predicate ct ->
     (!^"predicate for ctype" ^^^ squotes (Sctypes.pp ct) ^^^ !^"not defined", [])
  | Missing_member (tag, member) ->
     (!^"struct" ^^^ squotes (Sym.pp tag) ^^^ !^"does not have member" ^^^ 
        Id.pp member, [])

  | Missing_resource {resource; state; situation; oinfo} ->
     let msg = match oinfo with
       | Some (spec_loc, odescr) ->
          let (head, _) = Locations.head_pos_of_location spec_loc in
          !^"Missing resource from" ^^^ !^head ^^^
            (match odescr with
             | Some descr -> parens !^descr ^^ space
             | None -> Pp.empty
            ) ^^^ for_situation situation 
       | None ->
          !^"Missing resource" ^^^ squotes (resource) ^^^ for_situation situation 
     in
     (msg, [consider_state state] )
  | Resource_mismatch {has; state; expect; situation} ->
     let msg = !^"Need a resource" ^^^ squotes expect ^^^ 
                 !^"but have resource" ^^^ squotes has in
     (msg, [consider_state state])

  | Uninitialised_read {is_member; state} ->
     let msg = match is_member with
       | None -> !^"Trying to read uninitialised data"
       | Some m -> !^"Trying to read uninitialised struct member" ^^^ squotes (Id.pp m)
     in
     (msg, [consider_state state])
  | Unused_resource {resource;state} ->
     let msg = !^"Left-over unused resource" ^^^ squotes resource in
     (msg, [consider_state state])
  | Number_members {has;expect} ->
     (!^"Wrong number of struct members:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Number_arguments {has;expect} ->
     (!^"Wrong number of arguments:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Number_input_arguments {has;expect} ->
     (!^"Wrong number of input arguments:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Number_output_arguments {has;expect} ->
     (!^"Wrong number of output arguments:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Mismatch {has; expect} ->
     (!^"Expected value of type" ^^^ squotes (LS.pp expect) ^^^
        !^"but found value of type" ^^^ squotes (LS.pp has), [])
  | Mismatch_lvar { has; expect; spec_info} ->
     let (spec_loc, ospec_descr) = spec_info in
     let (head, _) = Locations.head_pos_of_location spec_loc in
     (!^"Expected value of type" ^^^ squotes (LS.pp expect) ^^^
        !^"for logical variable from" ^^^ !^head ^^^
          (match ospec_descr with
           | Some descr -> parens !^descr ^^ space
           | None -> Pp.empty
          ) ^^
        !^"but found value of type" ^^^ squotes (LS.pp has), [])

  | Illtyped_it {context;it;has;expected} ->
     (!^"Illtyped expression" ^^ squotes context ^^ dot ^^^ 
        !^"Expected" ^^^ it ^^^ !^"to have" ^^^ squotes !^expected ^^^ !^"type" ^^^
          !^"but has" ^^^ squotes (LS.pp has) ^^^ !^"type",  [])
  | Polymorphic_it it ->
     (!^"Polymorphic index term" ^^^ squotes (IndexTerms.pp it), [])
  | Write_value_unrepresentable {state : state_pp} ->
     let msg = !^"Write value unrepresentable" in
     (msg, [consider_state state])
  | Unsat_constraint {constr; state; info} ->
     let (spec_loc, odescr) = info in
     let (head, _) = Locations.head_pos_of_location spec_loc in
     let msg = match odescr with
       | None -> !^"Unsatisfied constraint" ^^^ parens (!^head)
       | Some descr -> !^"Unsatisfied constraint" ^^^ !^descr ^^^ parens (!^head)
     in
     (msg, [consider_state state])
  | Unconstrained_logical_variable (name, odescr) ->
     begin match odescr with
     | Some descr ->
        (!^"Unconstrained logical variable" ^^^ squotes (Sym.pp name) ^^^ parens !^descr, [])
     | None ->
        (!^"Unconstrained logical variable" ^^^ squotes (Sym.pp name), [])
     end
  | Array_as_value (name, odescr) ->
     begin match odescr with
     | Some descr ->
        (!^"Cannot use array" ^^^ squotes (Sym.pp name) ^^^ !^"as value" ^^^ parens !^descr, [])
     | None ->
        (!^"Cannot use array" ^^^ squotes (Sym.pp name) ^^^ !^"as value", [])
     end
  | Logical_variable_not_good_for_unification (name, odescr) ->
     begin match odescr with
     | Some descr ->
        (!^"Logical variable not soluble by unification" ^^^ squotes (Sym.pp name) ^^^ 
           parens (!^descr), [])
     | None ->
        (!^"Logical variable not soluble by unification" ^^^ squotes (Sym.pp name), [])
     end
  | Kind_mismatch {has; expect} ->
     (!^"Expected" ^^^ squotes (Kind.pp expect) ^^^ 
        !^"but found" ^^^ squotes (Kind.pp has), [])

  | Undefined_behaviour (undef, state) -> 
     let ub = CF.Undefined.pretty_string_of_undefined_behaviour undef in
     (!^"Undefined behaviour", [!^ub; consider_state state])
  | Implementation_defined_behaviour (impl, state) -> 
     (!^"Implementation defined behaviour:" ^^^ impl, [consider_state state])
  | Unspecified _ctype ->
     (!^"Unspecified value", [])
  | StaticError (err, state) ->
     (!^("Static error: " ^ err), [consider_state state])

  | Generic err ->
     (err, [])


type t = type_error



(* stealing some logic from pp_errors *)
let report (loc : Loc.t) (ostacktrace : string option) (err : type_error) = 
  let (msg, extras) = pp_type_error err in
  let extras = match ostacktrace with
    | Some stacktrace -> extras @ [Pp.item "stacktrace" (Pp.string stacktrace)]
    | None -> extras
  in
  Pp.error loc msg extras
