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
  | PackPredicate of Sym.t
  | PackStruct of Sym.t
  | UnpackPredicate of Sym.t
  | UnpackStruct of Sym.t
  | ArgumentInference of Sym.t

let checking_situation = function
  | Access access -> !^"checking access"
  | FunctionCall -> !^"checking function call"
  | LabelCall Return -> !^"checking return"
  | LabelCall Loop -> !^"checking loop entry"
  | LabelCall Other -> !^"checking label call"
  | Subtyping -> !^"checking subtyping"
  | PackPredicate name -> !^"packing predicate" ^^^ Sym.pp name
  | PackStruct tag -> !^"packing struct" ^^^ Sym.pp tag
  | UnpackPredicate name -> !^"unpacking predicate" ^^^ Sym.pp name
  | UnpackStruct tag -> !^"unpacking struct" ^^^ Sym.pp tag
  | ArgumentInference id -> !^"argument inference for" ^^^ Sym.pp id

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
  | PackPredicate name -> !^"for packing predicate" ^^^ Sym.pp name
  | PackStruct tag -> !^"for packing struct" ^^^ Sym.pp tag
  | UnpackPredicate name -> !^"for unpacking predicate" ^^^ Sym.pp name
  | UnpackStruct tag -> !^"for unpacking struct" ^^^ Sym.pp tag
  | ArgumentInference id -> !^"for argument inference for" ^^^ Sym.pp id





type sym_or_string =
  | Sym of Sym.t
  | String of string





type message =
  | Unknown_variable of Sym.t
  | Unknown_function of Sym.t
  | Unknown_struct of BT.tag
  | Unknown_resource_predicate of {id: Sym.t; logical: bool}
  | Unknown_logical_predicate of {id: Sym.t; resource: bool}
  | Unknown_member of BT.tag * BT.member
  | Unknown_record_member of BT.member_types * Id.t

  (* some from Kayvan's compilePredicates module *)
  | First_iarg_missing of { pname: ResourceTypes.predicate_name }
  | First_iarg_not_pointer of { pname : ResourceTypes.predicate_name; found_bty: BaseTypes.t }


  | Missing_resource_request of {orequest : RET.t option; situation : situation; oinfo : info option; ctxt : Context.t; model: Solver.model_with_q; trace: Trace.t }
  | Merging_multiple_arrays of {orequest : RET.t option; situation : situation; oinfo : info option; ctxt : Context.t; model: Solver.model_with_q }
  | Resource_mismatch of {has: RE.t; expect: RE.t; situation : situation; ctxt : Context.t; model : Solver.model_with_q }
  | Uninitialised_read of {ctxt : Context.t; model : Solver.model_with_q}
  | Unused_resource of {resource: RE.t; ctxt : Context.t; model : Solver.model_with_q}

  | Number_members of {has: int; expect: int}
  | Number_arguments of {has: int; expect: int}
  | Number_input_arguments of {has: int; expect: int}
  | Number_output_arguments of {has: int; expect: int}
  | Mismatch of { has: LS.t; expect: LS.t; }
  | Mismatch_lvar of { has: LS.t; expect: LS.t; spec_info: info}
  | Illtyped_it : {context: IT.t; it: IT.t; has: LS.t; expected: string; ctxt : Context.t} -> message (* 'expected' as in Kayvan's Core type checker *)
  | Illtyped_it' : {it: IT.t; has: LS.t; expected: string} -> message (* 'expected' as in Kayvan's Core type checker *)
  | NIA : {context: IT.t; it: IT.t; hint : string; ctxt : Context.t} -> message
  | TooBigExponent : {context: IT.t; it: IT.t; ctxt : Context.t} -> message
  | NegativeExponent : {context: IT.t; it: IT.t; ctxt : Context.t} -> message
  | Polymorphic_it : 'bt IndexTerms.term -> message
  | Write_value_unrepresentable of {ct: Sctypes.t; location: IT.t; value: IT.t; ctxt : Context.t; model : Solver.model_with_q }
  | Write_value_bad of {ct: Sctypes.t; location: IT.t; value: IT.t; ctxt : Context.t; model : Solver.model_with_q }
  | Int_unrepresentable of {value : IT.t; ict : Sctypes.t; ctxt : Context.t; model : Solver.model_with_q}
  | Unsat_constraint of {constr : LC.t; info : info; ctxt : Context.t; model : Solver.model_with_q}
  | Unconstrained_logical_variable of Sym.t * string option
  | Array_as_value of Sym.t * string option
  | Logical_variable_not_good_for_unification of Sym.t * string option

  | Undefined_behaviour of {ub : CF.Undefined.undefined_behaviour; ctxt : Context.t; model : Solver.model_with_q}
  | Implementation_defined_behaviour of document * state_report
  | Unspecified of CF.Ctype.ctype
  | StaticError of {err : string; ctxt : Context.t; model : Solver.model_with_q}
  | No_quantified_constraints of {to_check: IT.t; ctxt: Context.t; model : Solver.model_with_q}
  | Generic of Pp.document
  | Generic_with_model of {err : Pp.document; model : Solver.model_with_q; ctxt : Context.t}


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


let missing_or_bad_request_description oinfo orequest explanation = 
  match oinfo, orequest with
  | Some (spec_loc, Some descr), _ ->
     let (head, _) = Locations.head_pos_of_location spec_loc in
     Some (!^"Resource from" ^^^ !^head ^^^ parens !^descr)
  | Some (spec_loc, None), _ ->
     let (head, _) = Locations.head_pos_of_location spec_loc in
     Some (!^"Resource from" ^^^ !^head)
  | None, Some request ->
     let re_pp = RET.pp (RET.subst explanation.Explain.substitution request) in
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
  | Unknown_resource_predicate {id; logical} ->
     let short = !^"Unknown resource predicate" ^^^ squotes (Sym.pp id) in
     let descr = if logical then Some (!^"Note " ^^^ squotes (Sym.pp id) ^^^
             !^" is a known logical predicate.")
         else None in
     { short; descr; state = None; trace = None }
  | Unknown_logical_predicate {id; resource} ->
     let short = !^"Unknown logical predicate" ^^^ squotes (Sym.pp id) in
     let descr = if resource then Some (!^"Note " ^^^ squotes (Sym.pp id) ^^^
             !^" is a known resource predicate.")
         else None in
     { short; descr; state = None; trace = None }
  | Unknown_member (tag, member) ->
     let short = !^"Unknown member" ^^^ Id.pp member in
     let descr =
       !^"struct" ^^^ squotes (Sym.pp tag) ^^^
         !^"does not have member" ^^^
           Id.pp member
     in
     { short; descr = Some descr; state = None; trace = None }
  | Unknown_record_member (members, member) ->
     let short = !^"Unknown member" ^^^ Id.pp member in
     let descr =
       !^"struct type" ^^^ BT.pp (Record members) ^^^
         !^"does not have member" ^^^
           Id.pp member
     in
     { short; descr = Some descr; state = None; trace = None }
  | First_iarg_missing { pname } ->
     let short = !^"Missing pointer input argument" in
     let descr = 
       !^ "a predicate definition must have at least one iarg (missing from: " ^^ ResourceTypes.pp_predicate_name pname ^^ !^ ")"
     in
     { short; descr = Some descr; state = None; trace = None }
  | First_iarg_not_pointer { pname; found_bty } ->
     let short = !^"Non-pointer first input argument" in
     let descr = 
        !^ "the first iarg of predicate" ^^^ Pp.squotes (ResourceTypes.pp_predicate_name pname) ^^^
        !^ "must have type" ^^^ Pp.squotes (BaseTypes.(pp Loc)) ^^^ !^ "but was found with type" ^^^
        Pp.squotes (BaseTypes.(pp found_bty))
     in
     { short; descr = Some descr; state = None; trace = None }
  | Missing_resource_request {orequest; situation; oinfo; ctxt; model; trace} ->
     let short = !^"Missing resource" ^^^ for_situation situation in
     let relevant = match orequest with
       | None -> IT.SymSet.empty
       | Some request -> (RET.free_vars request)
     in
     let explanation = Explain.explanation ctxt relevant in
     let descr = missing_or_bad_request_description oinfo orequest explanation in
     let state = Explain.state ctxt explanation model orequest in
     { short; descr = descr; state = Some state; trace = None }
  | Merging_multiple_arrays {orequest; situation; oinfo; ctxt; model} ->
     let short = 
       !^"Cannot satisfy request for resource" ^^^ for_situation situation ^^ dot ^^^
         !^"It requires merging multiple arrays."
     in
     let relevant = match orequest with
       | None -> IT.SymSet.empty
       | Some request -> (RET.free_vars request)
     in
     let explanation = Explain.explanation ctxt relevant in
     let descr = missing_or_bad_request_description oinfo orequest explanation in
     let state = Explain.state ctxt explanation model orequest in
     { short; descr = descr; state = Some state; trace = None }
  | Resource_mismatch {has; expect; situation; ctxt; model} ->
     let short = !^"Resource mismatch" ^^^ for_situation situation in
     let relevant = IT.SymSet.union (RE.free_vars has) (RE.free_vars expect) in
     let explanation = Explain.explanation ctxt relevant in
     let has = RE.pp (RE.subst explanation.substitution has) in
     let expect = RE.pp (RE.subst explanation.substitution expect) in
     let state = Explain.state ctxt explanation model None in
     let descr =
       !^"Need a resource" ^^^ squotes expect ^^^
         !^"but have resource" ^^^ squotes has
     in
     { short; descr = Some descr; state = Some state; trace = None }
  | Uninitialised_read {ctxt; model} ->
     let short = !^"Trying to read uninitialised data" in
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model None in
     { short; descr = None; state = Some state; trace = None }
  | Unused_resource {resource; ctxt; model} ->
     let explanation = Explain.explanation ctxt (RE.free_vars resource) in
     let resource = RE.pp (RE.subst explanation.substitution resource) in
     let short = !^"Left-over unused resource" ^^^ squotes resource in
     let state = Explain.state ctxt explanation model None in
     { short; descr = None; state = Some state; trace = None }
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
       !^"Expected value of type" ^^^ squotes (LS.pp expect) ^^^
         !^"but found value of type" ^^^ squotes (LS.pp has)
     in
     { short; descr = Some descr; state = None; trace = None }
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
     { short; descr = Some descr; state = None; trace = None }
  | Illtyped_it {context; it; has; expected; ctxt} ->
     let relevant = IT.free_vars_list [it; context] in
     let explanation = Explain.explanation ctxt relevant in
     let it = IT.pp (IT.subst explanation.substitution it) in
     let context = IT.pp (IT.subst explanation.substitution context) in
     let short = !^"Type error" in
     let descr =
       !^"Illtyped expression" ^^ squotes context ^^ dot ^^^
         !^"Expected" ^^^ it ^^^ !^"to be" ^^^ squotes !^expected ^^^
           !^"but is" ^^^ squotes (LS.pp has)
     in
     { short; descr = Some descr; state = None; trace = None }
  | Illtyped_it' {it; has; expected} ->
     let it = IT.pp it in
     let short = !^"Type error" in
     let descr =
       !^"Illtyped expression" ^^ squotes it ^^ dot ^^^
         !^"Expected" ^^^ it ^^^ !^"to be" ^^^ squotes !^expected ^^^
           !^"but is" ^^^ squotes (LS.pp has)
     in
     { short; descr = Some descr; state = None; trace = None }
  | NIA {context; it; hint; ctxt} ->
     let relevant = IT.free_vars_list [it; context] in
     let explanation = Explain.explanation ctxt relevant in
     let it = IT.pp (IT.subst explanation.substitution it) in
     let context = IT.pp (IT.subst explanation.substitution context) in
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes context ^^ dot ^^^
         !^"Non-linear integer arithmetic in the specification term" ^^^ it ^^ dot ^^^
           !^hint
     in
     { short; descr = Some descr; state = None; trace = None }
  | TooBigExponent {context; it; ctxt} ->
     let relevant = IT.free_vars_list [it; context] in
     let explanation = Explain.explanation ctxt relevant in
     let it = IT.pp (IT.subst explanation.substitution it) in
     let context = IT.pp (IT.subst explanation.substitution context) in
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes context ^^ dot ^^^
         !^"Too big exponent in the specification term" ^^^ it ^^ dot ^^^
           !^("Exponent must fit int32 type")
     in
     { short; descr = Some descr; state = None; trace = None }
  | NegativeExponent {context; it; ctxt} ->
     let relevant = IT.free_vars_list [it; context] in
     let explanation = Explain.explanation ctxt relevant in
     let it = IT.pp (IT.subst explanation.substitution it) in
     let context = IT.pp (IT.subst explanation.substitution context) in
     let short = !^"Type error" in
     let descr = 
       !^"Illtyped expression" ^^ squotes context ^^ dot ^^^
         !^"Negative exponent in the specification term" ^^^ it ^^ dot ^^^
           !^("Exponent must be non-negative")
     in
     { short; descr = Some descr; state = None; trace = None }
  | Polymorphic_it it ->
     let short = !^"Type inference failed" in
     let descr = !^"Polymorphic index term" ^^^ squotes (IndexTerms.pp it) in
     { short; descr = Some descr; state = None; trace = None }
  | Write_value_unrepresentable {ct; location; value; ctxt; model} ->
     let short =
       !^"Write value not representable at type" ^^^
         Sctypes.pp ct
     in
     let explanation =
       Explain.explanation ctxt
         (IT.free_vars_list [value; location])
     in
     let location = IT.pp (IT.subst explanation.substitution location) in
     let value = IT.pp (IT.subst explanation.substitution value) in
     let state = Explain.state ctxt explanation model None in
     let descr =
       !^"Location" ^^ colon ^^^ location ^^ comma ^^^
       !^"value" ^^ colon ^^^ value ^^ dot
     in
     { short; descr = Some descr; state = Some state; trace = None }
  | Write_value_bad {ct; location; value; ctxt; model} ->
     let short =
       !^"Bad write value: the value is not representable at type" ^^^
         Sctypes.pp ct ^^^ !^"or is a misaligned pointer value"
     in
     let explanation =
       Explain.explanation ctxt
         (IT.free_vars_list [value; location])
     in
     let location = IT.pp (IT.subst explanation.substitution location) in
     let value = IT.pp (IT.subst explanation.substitution value) in
     let state = Explain.state ctxt explanation model None in
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
     let explanation = Explain.explanation ctxt (IT.free_vars value) in
     let value = IT.pp (IT.subst explanation.substitution value) in
     let descr = !^"Value" ^^ colon ^^^ value in
     let state = Explain.state ctxt explanation model None in
     { short; descr = Some descr; state = Some state; trace = None }
  | Unsat_constraint {constr; info; ctxt; model} ->
     let short = !^"Unsatisfied constraint" in
     let explanation = Explain.explanation ctxt (LC.free_vars constr) in
     let _constr = LC.pp (LC.subst explanation.substitution constr) in
     let state = Explain.state ctxt explanation model None in
     let descr =
       let (spec_loc, odescr) = info in
       let (head, _) = Locations.head_pos_of_location spec_loc in
       match odescr with
       | None -> !^"Constraint from " ^^^ parens (!^head)
       | Some descr -> !^"Constraint from" ^^^ !^descr ^^^ parens (!^head)
     in
     { short; descr = Some descr; state = Some state; trace = None }
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
     { short; descr = Some descr; state = None; trace = None }
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
     { short; descr = Some descr; state = None; trace = None }
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
     { short; descr = Some descr; state = None; trace = None }
  | Undefined_behaviour {ub; ctxt; model} ->
     let short = !^"Undefined behaviour" in
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model None in
     let descr = !^(CF.Undefined.pretty_string_of_undefined_behaviour ub) in
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
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model None in
     let descr = !^err in
     { short; descr = Some descr; state = Some state; trace = None }
  | No_quantified_constraints {to_check; ctxt; model} ->
     let short = !^"Found no quantified constraints containing this fact" in
     let explanation = Explain.explanation ctxt (IT.free_vars to_check) in
     let state = Explain.state ctxt explanation model None in
     let descr = None in
       (* parens (!^"to check:" ^^^ IT.pp (IT.subst explanation.substitution to_check)) *)
     { short; descr = descr; state = Some state; trace = None }
  | Generic err ->
     let short = err in
     { short; descr = None; state = None; trace = None }
  | Generic_with_model {err; model; ctxt} ->
     let short = err in
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model None in
     { short; descr = None; state = Some state; trace = None }


type t = type_error


let output_state state_error_file state =
  let channel = open_out state_error_file in
  let () = Printf.fprintf channel "%s" (Report.print_report state) in
  close_out channel

(* stealing some logic from pp_errors *)
let report ?state_file:to_ {loc; msg} =
  let report = pp_message msg in
  let consider = match report.state with
    | Some state ->
       let state_error_file = match to_ with
         | Some file -> file
         | None -> Filename.temp_file "" ".html"
       in
       output_state state_error_file state;
       Some (!^"Consider the state in" ^^^ !^state_error_file)
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


