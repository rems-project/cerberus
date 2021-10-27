open Pp
open Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module Loc = Locations
open Report
module RE = Resources.RE
module LC = LogicalConstraints
module RER = Resources.Requests

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
  | Pack of CF.Annot.to_pack_unpack
  | Unpack of CF.Annot.to_pack_unpack
  | ArgumentInference of Id.t

let checking_situation = function
  | Access access -> !^"checking access"
  | FunctionCall -> !^"checking function call"
  | LabelCall Return -> !^"checking return"
  | LabelCall Loop -> !^"checking loop entry"
  | LabelCall Other -> !^"checking label call"
  | Subtyping -> !^"checking subtyping"
  | ArrayShift -> !^"array shifting"
  | MemberShift -> !^"member shifting"
  | Pack (TPU_Predicate name) -> !^"packing predicate" ^^^ Id.pp name
  | Pack (TPU_Struct tag) -> !^"packing struct" ^^^ Sym.pp tag
  | Unpack (TPU_Predicate name) -> !^"unpacking predicate" ^^^ Id.pp name
  | Unpack (TPU_Struct tag) -> !^"unpacking struct" ^^^ Sym.pp tag
  | ArgumentInference id -> !^"argument inference for" ^^^ Id.pp id

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
  | Pack (TPU_Predicate name) -> !^"for packing predicate" ^^^ Id.pp name
  | Pack (TPU_Struct tag) -> !^"for packing struct" ^^^ Sym.pp tag
  | Unpack (TPU_Predicate name) -> !^"for unpacking predicate" ^^^ Id.pp name
  | Unpack (TPU_Struct tag) -> !^"for unpacking struct" ^^^ Sym.pp tag
  | ArgumentInference id -> !^"for argument inference for" ^^^ Id.pp id





type sym_or_string =
  | Sym of Sym.t
  | String of string





type message =
  | Unknown_variable of Sym.t
  | Unknown_function of Sym.t
  | Unknown_struct of BT.tag
  | Unknown_resource_predicate of string
  | Unknown_logical_predicate of string
  | Unknown_member of BT.tag * BT.member

  | Missing_resource_request of {orequest : RER.t option; situation : situation; oinfo : info option; ctxt : Context.t; model: Solver.model_with_q }
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
  | Polymorphic_it : 'bt IndexTerms.term -> message
  | Write_value_unrepresentable of {ct: Sctypes.t; location: IT.t; value: IT.t; ctxt : Context.t; model : Solver.model_with_q }
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


type type_error = {
    loc : Locations.t;
    msg : message;
  }





type report = {
    short : Pp.doc;
    descr : Pp.doc option;
    state : state_report option;
  }

let pp_message te =
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
  | Unknown_resource_predicate id ->
     let short = !^"Unknown resource predicate" ^^^ squotes (!^id) in
     { short; descr = None; state = None }
  | Unknown_logical_predicate id ->
     let short = !^"Unknown logical predicate" ^^^ squotes (!^id) in
     { short; descr = None; state = None }
  | Unknown_member (tag, member) ->
     let short = !^"Unknown member" ^^^ Id.pp member in
     let descr =
       !^"struct" ^^^ squotes (Sym.pp tag) ^^^
         !^"does not have member" ^^^
           Id.pp member
     in
     { short; descr = Some descr; state = None }
  | Missing_resource_request {orequest; situation; oinfo; ctxt; model} ->
     let short = !^"Missing resource" ^^^ for_situation situation in
     let relevant = match orequest with
       | None -> IT.SymSet.empty
       | Some request -> (RER.free_vars request)
     in
     let explanation = Explain.explanation ctxt relevant in
     let descr = match oinfo, orequest with
       | Some (spec_loc, Some descr), _ ->
          let (head, _) = Locations.head_pos_of_location spec_loc in
          Some (!^"Missing resource from" ^^^ !^head ^^^ parens !^descr)
       | Some (spec_loc, None), _ ->
          let (head, _) = Locations.head_pos_of_location spec_loc in
          Some (!^"Missing resource from" ^^^ !^head)
       | None, Some request ->
          let re_pp = RER.pp (RER.subst explanation.substitution request) in
          Some (!^"Missing resource" ^^^ squotes re_pp)
       | None, None ->
          None
     in
     let state = Explain.state ctxt explanation model in
     { short; descr; state = Some state }
  | Resource_mismatch {has; expect; situation; ctxt; model} ->
     let short = !^"Resource mismatch" ^^^ for_situation situation in
     let relevant = IT.SymSet.union (RE.free_vars has) (RE.free_vars expect) in
     let explanation = Explain.explanation ctxt relevant in
     let has = RE.pp (RE.subst explanation.substitution has) in
     let expect = RE.pp (RE.subst explanation.substitution expect) in
     let state = Explain.state ctxt explanation model in
     let descr =
       !^"Need a resource" ^^^ squotes expect ^^^
         !^"but have resource" ^^^ squotes has
     in
     { short; descr = Some descr; state = Some state }
  | Uninitialised_read {ctxt; model} ->
     let short = !^"Trying to read uninitialised data" in
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model in
     { short; descr = None; state = Some state }
  | Unused_resource {resource; ctxt; model} ->
     let explanation = Explain.explanation ctxt (RE.free_vars resource) in
     let resource = RE.pp (RE.subst explanation.substitution resource) in
     let short = !^"Left-over unused resource" ^^^ squotes resource in
     let state = Explain.state ctxt explanation model in
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
     { short; descr = Some descr; state = None }
  | Polymorphic_it it ->
     let short = !^"Type inference failed" in
     let descr = !^"Polymorphic index term" ^^^ squotes (IndexTerms.pp it) in
     { short; descr = Some descr; state = None }
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
     let state = Explain.state ctxt explanation model in
     let descr =
       !^"Location" ^^ colon ^^^ location ^^ comma ^^^
       !^"value" ^^ colon ^^^ value ^^ dot
     in
     { short; descr = Some descr; state = Some state }
  | Int_unrepresentable {value; ict; ctxt; model} ->
     let short =
       !^"integer value not representable at type" ^^^
         Sctypes.pp ict
     in
     let explanation = Explain.explanation ctxt (IT.free_vars value) in
     let value = IT.pp (IT.subst explanation.substitution value) in
     let descr = !^"Value" ^^ colon ^^^ value in
     let state = Explain.state ctxt explanation model in
     { short; descr = Some descr; state = Some state }
  | Unsat_constraint {constr; info; ctxt; model} ->
     let short = !^"Unsatisfied constraint" in
     let explanation = Explain.explanation ctxt (LC.free_vars constr) in
     let _constr = LC.pp (LC.subst explanation.substitution constr) in
     let state = Explain.state ctxt explanation model in
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
  | Undefined_behaviour {ub; ctxt; model} ->
     let short = !^"Undefined behaviour" in
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model in
     let descr = !^(CF.Undefined.pretty_string_of_undefined_behaviour ub) in
     { short; descr = Some descr; state = Some state }
  | Implementation_defined_behaviour (impl, state) ->
     let short = !^"Implementation defined behaviour" in
     let descr = impl in
     { short; descr = Some descr; state = Some state }
  | Unspecified ctype ->
     let short = !^"Unspecified value of C-type" ^^^ CF.Pp_core_ctype.pp_ctype ctype in
     { short; descr = None; state = None }
  | StaticError {err; ctxt; model} ->
     let short = !^"Static error" in
     let explanation = Explain.explanation ctxt IT.SymSet.empty in
     let state = Explain.state ctxt explanation model in
     let descr = !^err in
     { short; descr = Some descr; state = Some state }
  | No_quantified_constraints {to_check; ctxt; model} ->
     let short = !^"Found no quantified constraints containing this fact" in
     let explanation = Explain.explanation ctxt (IT.free_vars to_check) in
     let state = Explain.state ctxt explanation model in
     let descr = None in
       (* parens (!^"to check:" ^^^ IT.pp (IT.subst explanation.substitution to_check)) *)
     { short; descr = descr; state = Some state }
  | Generic err ->
     let short = err in
     { short; descr = None; state = None }


type t = type_error


let state_error_file () =
   Filename.temp_file "" ".cn-state"

let output_state ?to_:file state =
  let state_error_file =
    match file with
    | Some file -> file
    | None -> state_error_file () in
   let channel = open_out state_error_file in
   let () = Printf.fprintf channel "%s" (Report.print_report state) in
   let () = close_out channel in
   state_error_file

(* stealing some logic from pp_errors *)
let report ?state_file:to_ {loc; msg} =
  let report = pp_message msg in
  let consider = match report.state with
    | Some state ->
      let state_error_file = output_state ?to_ state in
       Some (!^"Consider state in" ^^^ !^state_error_file)
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
    | Some state -> `String (output_state ?to_ state)
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


