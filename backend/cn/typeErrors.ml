open Pp
open Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module Loc = Locations
open Report

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





type type_error = 
  | Unknown_variable of Sym.t
  | Unknown_function of Sym.t
  | Unknown_struct of BT.tag
  | Unknown_predicate of string
  | Unknown_member of BT.tag * BT.member

  | Missing_resource of {resource : doc; state : state_report; situation : situation; oinfo : info option}
  | Resource_mismatch of {has: doc; state : state_report; expect: doc; situation : situation}
  | Uninitialised_read of {is_member : BT.member option; state : state_report}
  | Unused_resource of {resource: doc; state : state_report}

  | Number_members of {has: int; expect: int}
  | Number_arguments of {has: int; expect: int}
  | Number_input_arguments of {has: int; expect: int}
  | Number_output_arguments of {has: int; expect: int}
  | Mismatch of { has: LS.t; expect: LS.t; }
  | Mismatch_lvar of { has: LS.t; expect: LS.t; spec_info: info}
  | Illtyped_it of {context: Pp.document; it: Pp.document; has: LS.t; expected: string} (* 'expected' as in Kayvan's Core type checker *)
  | Polymorphic_it : 'bt IndexTerms.term -> type_error
  | Write_value_unrepresentable of {state : state_report}
  | IntFromPtr_unrepresentable of {ict : Sctypes.t; state : state_report}
  | Unsat_constraint of {constr : doc; state : state_report; info : info}
  | Unconstrained_logical_variable of Sym.t * string option
  | Array_as_value of Sym.t * string option
  | Logical_variable_not_good_for_unification of Sym.t * string option

  | Undefined_behaviour of CF.Undefined.undefined_behaviour * state_report
  | Implementation_defined_behaviour of document * state_report
  | Unspecified of CF.Ctype.ctype
  | StaticError of string * state_report

  | Generic of Pp.document








type report = { 
    short : Pp.doc; 
    descr : Pp.doc option;
    state : state_report option;
  }

let pp_type_error te = 
  match te with
  | Unknown_variable s -> 
     let short = !^"Unknown variable" ^^^ squotes (Sym.pp s) in
     { short; descr = None; state = None }
  | Unknown_function sym -> 
     let short = !^"Unknown function" ^^^ squotes (Sym.pp sym) in
     { short; descr = None; state = None }
  | Unknown_struct tag -> 
     let short = !^"Struct" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined" in
     { short; descr = None; state = None }
  | Unknown_predicate id -> 
     let short = !^"Unknown predicate" ^^^ squotes (!^id) in
     { short; descr = None; state = None }
  | Unknown_member (tag, member) -> 
     let short = !^"Unknown member" ^^^ Id.pp member in
     let descr = 
       !^"struct" ^^^ squotes (Sym.pp tag) ^^^ 
         !^"does not have member" ^^^ 
           Id.pp member
     in
     { short; descr = Some descr; state = None }
  | Missing_resource {resource; state; situation; oinfo} ->
     let short = !^"Missing resource" ^^^ for_situation situation in
     let descr = match oinfo with
       | Some (spec_loc, Some descr) ->
          let (head, _) = Locations.head_pos_of_location spec_loc in
          !^"Missing resource from" ^^^ !^head ^^^ parens !^descr
       | Some (spec_loc, None) ->
          let (head, _) = Locations.head_pos_of_location spec_loc in
          !^"Missing resource from" ^^^ !^head
       | None ->
          !^"Missing resource" ^^^ squotes (resource)
     in
     { short; descr = Some descr; state = Some state }
  | Resource_mismatch {has; state; expect; situation} ->
     let short = !^"Resource mismatch" ^^^ for_situation situation in
     let descr = 
       !^"Need a resource" ^^^ squotes expect ^^^ 
         !^"but have resource" ^^^ squotes has 
     in
     { short; descr = Some descr; state = Some state }
  | Uninitialised_read {is_member; state} ->
     let short = match is_member with
       | None -> !^"Trying to read uninitialised data"
       | Some m -> !^"Trying to read uninitialised struct member" ^^^ squotes (Id.pp m)
     in
     { short; descr = None; state = Some state }
  | Unused_resource {resource; state} ->
     let short = !^"Left-over unused resource" ^^^ squotes resource in
     { short; descr = None; state = Some state}
  | Number_members {has;expect} ->
     let short = !^"Wrong number of struct members" in
     let descr = 
       !^"Expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None}
  | Number_arguments {has;expect} ->
     let short = !^"Wrong number of arguments" in
     let descr = 
       !^"Expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None }
  | Number_input_arguments {has;expect} ->
     let short = !^"Wrong number of input arguments" in
     let descr = 
       !^"Expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None }
  | Number_output_arguments {has;expect} ->
     let short = !^"Wrong number of output arguments" in
     let descr = 
       !^"Expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None }
  | Mismatch {has; expect} ->
     let short = !^"Type error" in
     let descr =
       !^"Expected value of type" ^^^ squotes (LS.pp expect) ^^^
         !^"but found value of type" ^^^ squotes (LS.pp has)
     in
     { short; descr = Some descr; state = None }
  | Mismatch_lvar { has; expect; spec_info} ->
     let short = !^"Type error" in
     let descr = 
       let (spec_loc, ospec_descr) = spec_info in
       let (head, _) = Locations.head_pos_of_location spec_loc in
       !^"Expected value of type" ^^^ squotes (LS.pp expect) ^^^
         !^"for logical variable from" ^^^ !^head ^^^
           (match ospec_descr with
            | Some descr -> parens !^descr ^^ space
            | None -> Pp.empty
           ) ^^
             !^"but found value of type" ^^^ squotes (LS.pp has)
     in
     { short; descr = Some descr; state = None }
  | Illtyped_it {context;it;has;expected} ->
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes context ^^ dot ^^^ 
         !^"Expected" ^^^ it ^^^ !^"to have" ^^^ squotes !^expected ^^^ !^"type" ^^^
           !^"but has" ^^^ squotes (LS.pp has) ^^^ !^"type"
     in
     { short; descr = Some descr; state = None }
  | Polymorphic_it it ->
     let short = !^"Type inference failed" in
     let descr = !^"Polymorphic index term" ^^^ squotes (IndexTerms.pp it) in
     { short; descr = Some descr; state = None }
  | Write_value_unrepresentable {state : state_report} ->
     let short = !^"Write value unrepresentable" in
     { short; descr = None; state = Some state }
  | IntFromPtr_unrepresentable {ict; state : state_report} ->
     let short = 
       !^"pointer value not representable at type" ^^^
         Sctypes.pp ict
     in
     { short; descr = None; state = Some state }
  | Unsat_constraint {constr; state; info} ->
     let short = !^"Unsatisfied constraint" in
     let descr = 
       let (spec_loc, odescr) = info in
       let (head, _) = Locations.head_pos_of_location spec_loc in
       match odescr with
       | None -> !^"Constraint from " ^^^ parens (!^head)
       | Some descr -> !^"Constraint from" ^^^ !^descr ^^^ parens (!^head)
     in
     { short; descr = Some descr; state = Some state }                                  
  | Unconstrained_logical_variable (name, odescr) ->
     let short = !^"Problematic specification" in
     let descr = match odescr with
       | Some descr ->
          !^"Unconstrained logical variable" ^^^ 
            squotes (Sym.pp name) ^^^ parens !^descr
       | None ->
          !^"Unconstrained logical variable" ^^^ 
            squotes (Sym.pp name)
     in
     { short; descr = Some descr; state = None }
  | Array_as_value (name, odescr) ->
     let short = !^"Problematic specification" in
     let descr = match odescr with
       | Some descr ->
          !^"Cannot use array" ^^^ squotes (Sym.pp name) ^^^ 
            !^"as value" ^^^ parens !^descr
       | None ->
          !^"Cannot use array" ^^^ squotes (Sym.pp name) ^^^ 
            !^"as value"
     in
     { short; descr = Some descr; state = None }
  | Logical_variable_not_good_for_unification (name, odescr) ->
     let short = !^"Problematic specification" in
     let descr = match odescr with
       | Some descr ->
          !^"Logical variable not soluble by unification" ^^^ 
            squotes (Sym.pp name) ^^^ parens (!^descr)
       | None ->
          !^"Logical variable not soluble by unification" ^^^ 
            squotes (Sym.pp name)
     in
     { short; descr = Some descr; state = None }
  | Undefined_behaviour (undef, state) -> 
     let short = !^"Undefined behaviour" in
     let descr = !^(CF.Undefined.pretty_string_of_undefined_behaviour undef) in
     { short; descr = Some descr; state = Some state }
  | Implementation_defined_behaviour (impl, state) -> 
     let short = !^"Implementation defined behaviour" in
     let descr = impl in
     { short; descr = Some descr; state = Some state }
  | Unspecified ctype ->
     let short = !^"Unspecified value of C-type" ^^^ CF.Pp_core_ctype.pp_ctype ctype in
     { short; descr = None; state = None }
  | StaticError (err, state) ->
     let short = !^"Static error" in
     let descr = !^err in
     { short; descr = Some descr; state = Some state }
  | Generic err ->
     let short = err in
     { short; descr = None; state = None }


type t = type_error


let state_error_file = "state.html"


(* stealing some logic from pp_errors *)
let report (loc : Loc.t) (ostacktrace : string option) (err : type_error) = 
  let report = pp_type_error err in
  let consider = match report.state with
    | Some state -> 
       let channel = open_out state_error_file in
       let () = Printf.fprintf channel "%s" (Report.print_report state) in
       let () = close_out channel in
       Some (!^"Consider state in" ^^^ !^state_error_file)
    | None -> 
       None
  in
  Pp.error loc report.short 
    ((Option.to_list report.descr) @
       (Option.to_list consider))
