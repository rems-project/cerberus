open Pp
open Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module Loc = Locations
open Report
module RE = Resources
module LC = LogicalConstraints
module RET = ResourceTypes

type label_kind =
  | Return
  | Loop
  | Other


type access =
  | Load
  | Store
  | Deref
  | Kill
  | Free

type automatic = Auto | Manual

type call_situation =
  | FunctionCall of Sym.t
  | LemmaApplication of Sym.t
  | LabelCall of label_kind
  | Subtyping

let call_prefix = function
  | FunctionCall fsym -> "call_" ^ Sym.pp_string fsym
  | LemmaApplication l -> "apply_" ^ Sym.pp_string l
  | LabelCall Return -> "return"
  | LabelCall Loop -> "loop"
  | LabelCall Other -> "goto"
  | Subtyping -> "return"

type situation =
  | Access of access
  | Call of call_situation


let call_situation = function
  | FunctionCall fsym -> !^"checking call of function" ^^^ Sym.pp fsym
  | LemmaApplication l -> !^"applying lemma" ^^^ Sym.pp l
  | LabelCall Return -> !^"checking return"
  | LabelCall Loop -> !^"checking loop entry"
  | LabelCall Other -> !^"checking label call"
  | Subtyping -> !^"checking subtyping"

let checking_situation = function
  | Access access -> !^"checking access"
  | Call s -> call_situation s


let for_access = function
  | Kill -> !^"for de-allocating"
  | Deref -> !^"for dereferencing"
  | Load ->  !^"for reading"
  | Store ->  !^"for writing"
  | Free -> !^"for free-ing"

let for_situation = function
  | Access access -> for_access access
  | Call FunctionCall fsym -> !^"for calling function" ^^^ Sym.pp fsym
  | Call LemmaApplication l -> !^"for applying lemma" ^^^ Sym.pp l
  | Call LabelCall Return -> !^"for returning"
  | Call LabelCall Loop -> !^"for loop"
  | Call LabelCall Other -> !^"for calling label"
  | Call Subtyping -> !^"for subtyping"






type sym_or_string =
  | Sym of Sym.t
  | String of string


type message =
  | Unknown_variable of Sym.t
  | Unknown_function of Sym.t
  | Unknown_struct of Sym.t
  | Unknown_datatype of Sym.t
  | Unknown_datatype_constr of Sym.t
  | Unknown_resource_predicate of {id: Sym.t; logical: bool}
  | Unknown_logical_function of {id: Sym.t; resource: bool}
  | Unexpected_member of Id.t list * Id.t
  | Unknown_lemma of Sym.t

  (* some from Kayvan's compilePredicates module *)
  | First_iarg_missing
  | First_iarg_not_pointer of { pname : ResourceTypes.predicate_name; found_bty: BaseTypes.t }

  | Missing_member of Id.t
  | Duplicate_member of Id.t


  | Missing_resource of {orequest : RET.t option; situation : situation; oinfo : info option; ctxt : Context.t; model: Solver.model_with_q; trace: Trace.t }
  | Merging_multiple_arrays of {orequest : RET.t option; situation : situation; oinfo : info option; ctxt : Context.t; model: Solver.model_with_q }
  | Unused_resource of {resource: RE.t; ctxt : Context.t; model : Solver.model_with_q; trace : Trace.t}
  | Number_members of {has: int; expect: int}
  | Number_arguments of {has: int; expect: int}
  | Number_input_arguments of {has: int; expect: int}
  | Number_output_arguments of {has: int; expect: int}
  | Mismatch of { has: doc; expect: doc; }
  | Illtyped_it : {it: Pp.doc; has: Pp.doc; expected: string; o_ctxt : Context.t option} -> message (* 'expected' and 'has' as in Kayvan's Core type checker *)
  | NIA : {it: IT.t; hint : string; ctxt : Context.t} -> message
  | TooBigExponent : {it: IT.t; ctxt : Context.t} -> message
  | NegativeExponent : {it: IT.t; ctxt : Context.t} -> message
  | Write_value_unrepresentable of {ct: Sctypes.t; location: IT.t; value: IT.t; ctxt : Context.t; model : Solver.model_with_q }
  | Int_unrepresentable of {value : IT.t; ict : Sctypes.t; ctxt : Context.t; model : Solver.model_with_q}
  | Unproven_constraint of {constr : LC.t; info : info; ctxt : Context.t; model : Solver.model_with_q; trace : Trace.t}

  | Undefined_behaviour of {ub : CF.Undefined.undefined_behaviour; ctxt : Context.t; model : Solver.model_with_q}
  | Implementation_defined_behaviour of document * state_report
  | Unspecified of CF.Ctype.ctype
  | StaticError of {err : string; ctxt : Context.t; model : Solver.model_with_q}
  | Generic of Pp.document
  | Generic_with_model of {err : Pp.document; model : Solver.model_with_q; ctxt : Context.t}

  | Parser of Cerb_frontend.Errors.cparser_cause

  | Empty_pattern
  | Missing_pattern of Pp.document
  | Duplicate_pattern
  | Empty_provenance


type type_error = {
    loc : Locations.t;
    msg : message;
  }





type report = {
    short : Pp.doc;
    descr : Pp.doc option;
    state : state_report option;
    trace : Pp.doc option;
  }


let missing_or_bad_request_description oinfo orequest = 
  match oinfo, orequest with
  | Some (spec_loc, Some descr), _ ->
     let (head, _) = Locations.head_pos_of_location spec_loc in
     Some (!^"Resource from" ^^^ !^head ^^^ parens !^descr)
  | Some (spec_loc, None), _ ->
     let (head, _) = Locations.head_pos_of_location spec_loc in
     Some (!^"Resource from" ^^^ !^head)
  | None, Some request ->
     let re_pp = RET.pp request in
     Some (!^"Resource" ^^^ squotes re_pp)
  | None, None ->
     None  



let pp_message te =
  match te with
  | Unknown_variable s ->
     let short = !^"Unknown variable" ^^^ squotes (Sym.pp s) in
     { short; descr = None; state = None; trace = None }
  | Unknown_function sym ->
     let short = !^"Unknown function" ^^^ squotes (Sym.pp sym) in
     { short; descr = None; state = None; trace = None }
  | Unknown_struct tag ->
     let short = !^"Struct" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined" in
     { short; descr = None; state = None; trace = None }
  | Unknown_datatype tag ->
     let short = !^"Datatype" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined" in
     { short; descr = None; state = None; trace = None }
  | Unknown_datatype_constr tag ->
     let short = !^"Datatype constructor" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined" in
     { short; descr = None; state = None; trace = None }
  | Unknown_resource_predicate {id; logical} ->
     let short = !^"Unknown resource predicate" ^^^ squotes (Sym.pp id) in
     let descr = if logical then Some (!^"Note " ^^^ squotes (Sym.pp id) ^^^
             !^" is a known logical predicate.")
         else None in
     { short; descr; state = None; trace = None }
  | Unknown_logical_function {id; resource} ->
     let short = !^"Unknown logical function" ^^^ squotes (Sym.pp id) in
     let descr = if resource then Some (!^"Note " ^^^ squotes (Sym.pp id) ^^^
             !^" is a known resource predicate.")
         else None in
     { short; descr; state = None; trace = None }
  | Unexpected_member (expected, member) ->
     let short = !^"Unexpected member" ^^^ Id.pp member in
     let descr = !^"the struct only has members" ^^^ Pp.list Id.pp expected in
     { short; descr = Some descr; state = None; trace = None }
  | Unknown_lemma sym ->
     let short = !^"Unknown lemma" ^^^ squotes (Sym.pp sym) in
     { short; descr = None; state = None; trace = None }
  | First_iarg_missing ->
     let short = !^"Missing pointer input argument" in
     let descr = !^ "a predicate definition must have at least one input argument" in
     { short; descr = Some descr; state = None; trace = None }
  | First_iarg_not_pointer { pname; found_bty } ->
     let short = !^"Non-pointer first input argument" in
     let descr = 
        !^ "the first input argument of predicate" ^^^ Pp.squotes (ResourceTypes.pp_predicate_name pname) ^^^
        !^ "must have type" ^^^ Pp.squotes (BaseTypes.(pp Loc)) ^^^ !^ "but was found with type" ^^^
        Pp.squotes (BaseTypes.(pp found_bty))
     in
     { short; descr = Some descr; state = None; trace = None }
  | Missing_member m ->
     let short = !^"Missing member" ^^^ Id.pp m in
     { short; descr = None; state = None; trace = None }
  | Duplicate_member m ->
     let short = !^"Duplicate member" ^^^ Id.pp m in
     { short; descr = None; state = None; trace = None }
  | Missing_resource {orequest; situation; oinfo; ctxt; model; trace} ->
     let short = !^"Missing resource" ^^^ for_situation situation in
     let descr = missing_or_bad_request_description oinfo orequest in
     let state = Explain.state ctxt model Explain.{no_ex with request = orequest} in
     let trace_doc = Trace.format_trace (fst model) trace in
     { short; descr = descr; state = Some state; trace = Some trace_doc }
  | Merging_multiple_arrays {orequest; situation; oinfo; ctxt; model} ->
     let short = 
       !^"Cannot satisfy request for resource" ^^^ for_situation situation ^^ dot ^^^
         !^"It requires merging multiple arrays."
     in
     let descr = missing_or_bad_request_description oinfo orequest in
     let state = Explain.state ctxt model Explain.{no_ex with request = orequest} in
     { short; descr = descr; state = Some state; trace = None }
  | Unused_resource {resource; ctxt; model; trace} ->
     let resource = RE.pp resource in
     let short = !^"Left-over unused resource" ^^^ squotes resource in
     let state = Explain.state ctxt model Explain.no_ex in
     let trace_doc = Trace.format_trace (fst model) trace in
     { short; descr = None; state = Some state; trace = Some trace_doc }
  | Number_members {has;expect} ->
     let short = !^"Wrong number of struct members" in
     let descr =
       !^"Expected" ^^^ !^(string_of_int expect) ^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None; trace = None}
  | Number_arguments {has;expect} ->
     let short = !^"Wrong number of arguments" in
     let descr =
       !^"Expected" ^^^ !^(string_of_int expect) ^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None; trace = None }
  | Number_input_arguments {has;expect} ->
     let short = !^"Wrong number of input arguments" in
     let descr =
       !^"Expected" ^^^ !^(string_of_int expect) ^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None; trace = None }
  | Number_output_arguments {has;expect} ->
     let short = !^"Wrong number of output arguments" in
     let descr =
       !^"Expected" ^^^ !^(string_of_int expect) ^^ comma ^^^
         !^"has" ^^^ !^(string_of_int has)
     in
     { short; descr = Some descr; state = None; trace = None }
  | Mismatch {has; expect} ->
     let short = !^"Type error" in
     let descr =
       !^"Expected value of type" ^^^ squotes expect ^^^
         !^"but found value of type" ^^^ squotes has
     in
     { short; descr = Some descr; state = None; trace = None }
  | Illtyped_it {it; has; expected; o_ctxt} ->
     let short = !^"Type error" in
     let descr =
       !^"Illtyped expression" ^^ squotes it ^^ dot ^^^
         !^"Expected" ^^^ it ^^^ !^"to be" ^^^ squotes !^expected ^^^
           !^"but is" ^^^ squotes has
     in
     { short; descr = Some descr; state = None; trace = None }
  | NIA {it; hint; ctxt} ->
     let it = IT.pp it in
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes it ^^ dot ^^^
         !^"Non-linear integer arithmetic in the specification term" ^^^ it ^^ dot ^^^
           !^hint
     in
     { short; descr = Some descr; state = None; trace = None }
  | TooBigExponent {it; ctxt} ->
     let it = IT.pp it in
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes it ^^ dot ^^^
         !^"Too big exponent in the specification term" ^^^ it ^^ dot ^^^
           !^("Exponent must fit int32 type")
     in
     { short; descr = Some descr; state = None; trace = None }
  | NegativeExponent {it; ctxt} ->
     let it = IT.pp it in
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes it ^^ dot ^^^
         !^"Negative exponent in the specification term" ^^^ it ^^ dot ^^^
           !^("Exponent must be non-negative")
     in
     { short; descr = Some descr; state = None; trace = None }
  | Write_value_unrepresentable {ct; location; value; ctxt; model} ->
     let short =
       !^"Write value not representable at type" ^^^
         Sctypes.pp ct
     in
     let location = IT.pp (location) in
     let value = IT.pp (value) in
     let state = Explain.state ctxt model Explain.no_ex in
     let descr =
       !^"Location" ^^ colon ^^^ location ^^ comma ^^^
       !^"value" ^^ colon ^^^ value ^^ dot
     in
     { short; descr = Some descr; state = Some state; trace = None }
  | Int_unrepresentable {value; ict; ctxt; model} ->
     let short =
       !^"integer value not representable at type" ^^^
         Sctypes.pp ict
     in
     let value = IT.pp (value) in
     let descr = !^"Value" ^^ colon ^^^ value in
     let state = Explain.state ctxt model Explain.no_ex in
     { short; descr = Some descr; state = Some state; trace = None }
  | Unproven_constraint {constr; info; ctxt; model; trace} ->
     let short = !^"Unprovable constraint" in
     let state = Explain.state ctxt model
         Explain.{no_ex with unproven_constraint = Some constr} in
     let descr =
       let (spec_loc, odescr) = info in
       let (head, _) = Locations.head_pos_of_location spec_loc in
       match odescr with
       | None -> !^"Constraint from " ^^^ parens (!^head)
       | Some descr -> !^"Constraint from" ^^^ !^descr ^^^ parens (!^head)
     in
     let trace_doc = Trace.format_trace (fst model) trace in
     { short; descr = Some descr; state = Some state; trace = Some trace_doc }
  | Undefined_behaviour {ub; ctxt; model} ->
     let short = !^"Undefined behaviour" in
     let state = Explain.state ctxt model Explain.no_ex in
     let descr = match CF.Undefined.std_of_undefined_behaviour ub with
      | Some stdref -> !^(CF.Undefined.ub_short_string ub) ^^^ parens !^stdref
      | None -> !^(CF.Undefined.ub_short_string ub) 
     in
     { short; descr = Some descr; state = Some state; trace = None }
  | Implementation_defined_behaviour (impl, state) ->
     let short = !^"Implementation defined behaviour" in
     let descr = impl in
     { short; descr = Some descr; state = Some state; trace = None }
  | Unspecified ctype ->
     let short = !^"Unspecified value of C-type" ^^^ CF.Pp_core_ctype.pp_ctype ctype in
     { short; descr = None; state = None; trace = None }
  | StaticError {err; ctxt; model} ->
     let short = !^"Static error" in
     let state = Explain.state ctxt model Explain.no_ex in
     let descr = !^err in
     { short; descr = Some descr; state = Some state; trace = None }
  | Generic err ->
     let short = err in
     { short; descr = None; state = None; trace = None }
  | Generic_with_model {err; model; ctxt} ->
     let short = err in
     let state = Explain.state ctxt model Explain.no_ex in
     { short; descr = None; state = Some state; trace = None }
  | Parser err ->
     let short = !^(Cerb_frontend.Pp_errors.string_of_cparser_cause err) in
     { short; descr = None; state = None; trace = None }
  | Empty_pattern ->
     let short = !^"Empty match expression." in
     { short; descr = None; state = None; trace = None }
  | Missing_pattern p' ->
     let short = !^"Missing pattern" ^^^ squotes p' ^^ dot in
     { short; descr = None; state = None; trace = None }
  | Duplicate_pattern ->
     let short = !^"Duplicate pattern" in
     { short; descr = None; state = None; trace = None }
  | Empty_provenance ->
     let short = !^"Empty provenance" in
     { short; descr = None; state = None; trace = None }


type t = type_error


let output_state state_error_file state =
  let channel = open_out state_error_file in
  let () = Printf.fprintf channel "%s" (Report.print_report state) in
  close_out channel

let output_trace trace =
  let fname = Filename.temp_file "trace_" ".txt" in
  let channel = open_out fname in
  print channel trace;
  close_out channel;
  !^ "trace in" ^^^ !^ fname

(* stealing some logic from pp_errors *)
let report ?state_file:to_ {loc; msg} =
  let report = pp_message msg in
  let consider = match report.state with
    | Some state ->
       let state_error_file = match to_ with
         | Some file -> file
         | None -> Filename.temp_file "state_" ".html"
       in
       output_state state_error_file state;
       let msg = !^"Consider the state in" ^^^ !^state_error_file in
       let msg2 = match report.trace with
         | None -> msg
         | Some tr -> msg ^^^ ampersand ^^^ (output_trace tr)
       in
       Some msg2
    | None ->
       None
  in
  Pp.error loc report.short
    ((Option.to_list report.descr) @
       (Option.to_list consider))


(* stealing some logic from pp_errors *)
let report_json ?state_file:to_ {loc; msg} =
  let report = pp_message msg in
  let state_error_file = match report.state with
    | Some state -> 
       let file = match to_ with
         | Some file -> file
         | None -> Filename.temp_file "" ".cn-state"
       in
       output_state file state;
       `String file
    | None -> `Null in
  let descr = match report.descr with
    | None -> `Null
    | Some descr -> `String (Pp.plain descr)
  in
  let json =
    `Assoc [("loc", Loc.json_loc loc);
            ("short", `String (Pp.plain report.short));
            ("descr", descr);
            ("state", state_error_file)]
  in
  Yojson.Safe.to_channel ~std:true stderr json


