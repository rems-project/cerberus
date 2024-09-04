open Explain
open Pp
open Locations
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module CF = Cerb_frontend
module Loc = Locations
module RE = Resources
module LC = LogicalConstraints
module RET = ResourceTypes

type label_kind = Where.label

type access =
  | Load
  | Store
  | Deref
  | Kill
  | Free

type automatic =
  | Auto
  | Manual

type call_situation =
  | FunctionCall of Sym.t
  | LemmaApplication of Sym.t
  | LabelCall of label_kind
  | Subtyping

let call_prefix = function
  | FunctionCall fsym -> "call_" ^ Sym.pp_string fsym
  | LemmaApplication l -> "apply_" ^ Sym.pp_string l
  | LabelCall la -> Where.label_prefix la
  | Subtyping -> "return"


type situation =
  | Ptr_diff
  | Access of access
  | Call of call_situation

let call_situation = function
  | FunctionCall fsym -> !^"checking call of function" ^^^ Sym.pp fsym
  | LemmaApplication l -> !^"applying lemma" ^^^ Sym.pp l
  | LabelCall la ->
    (match la with
     | LAreturn -> !^"checking return"
     | LAloop_break _ -> !^"checking loop break"
     | LAloop_continue _ -> !^"checking loop continue"
     | LAloop _ -> !^"checking loop entry"
     | LAswitch -> !^"todo: checking LAswitch"
     | LAcase -> !^"todo: checking LAcase"
     | LAdefault -> !^"todo: checking LAdefault"
     | LAactual_label -> !^"checking jump to label")
  | Subtyping -> !^"checking return"


let checking_situation = function
  | Access _ -> !^"checking access"
  | Ptr_diff -> !^"checking pointer difference"
  | Call s -> call_situation s


let for_access = function
  | Kill -> !^"for de-allocating"
  | Deref -> !^"for dereferencing"
  | Load -> !^"for reading"
  | Store -> !^"for writing"
  | Free -> !^"for free-ing"


let for_situation = function
  | Access access -> for_access access
  | Ptr_diff -> !^"for subtracting pointers"
  | Call s ->
    (match s with
     | FunctionCall fsym -> !^"for calling function" ^^^ Sym.pp fsym
     | LemmaApplication l -> !^"for applying lemma" ^^^ Sym.pp l
     | LabelCall la ->
       (match la with
        | LAreturn -> !^"for returning"
        | LAloop_break _ -> !^"for breaking from loop"
        | LAloop_continue _ -> !^"for loop continue"
        | LAloop _ -> !^"for loop"
        | LAswitch -> !^"for switch statement"
        | LAcase -> !^"for case switch"
        | LAdefault -> !^"for default case"
        | LAactual_label -> !^"for jumping to label")
     | Subtyping -> !^"for returning")


type request_chain_elem =
  { resource : RET.t;
    loc : Locations.t option;
    reason : string option
  }

type request_chain = request_chain_elem list

type message =
  | Unknown_variable of Sym.t
  | Unknown_function of Sym.t
  | Unknown_struct of Sym.t
  | Unknown_datatype of Sym.t
  | Unknown_datatype_constr of Sym.t
  | Unknown_resource_predicate of
      { id : Sym.t;
        logical : bool
      }
  | Unknown_logical_function of
      { id : Sym.t;
        resource : bool
      }
  | Unexpected_member of Id.t list * Id.t
  | Unknown_lemma of Sym.t
  (* some from Kayvan's compilePredicates module *)
  | First_iarg_missing
  | First_iarg_not_pointer of
      { pname : ResourceTypes.predicate_name;
        found_bty : BaseTypes.t
      }
  | Missing_member of Id.t
  | Missing_resource of
      { requests : request_chain;
        situation : situation;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Merging_multiple_arrays of
      { requests : request_chain;
        situation : situation;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Unused_resource of
      { resource : RE.t;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Number_members of
      { has : int;
        expect : int
      }
  | Number_arguments of
      { has : int;
        expect : int
      }
  | Number_input_arguments of
      { has : int;
        expect : int
      }
  | Number_output_arguments of
      { has : int;
        expect : int
      }
  | Mismatch of
      { has : document;
        expect : document
      }
  | Illtyped_it of
      { it : Pp.document;
        has : Pp.document; (* 'expected' and 'has' as in Kayvan's Core type checker *)
        expected : string;
        reason : string
      }
  | Illtyped_binary_it of
      { left : IT.Surface.t;
        right : IT.Surface.t;
        binop : CF.Cn.cn_binop
      }
  | NIA of
      { it : IT.t;
        hint : string
      }
  | TooBigExponent : { it : IT.t } -> message
  | NegativeExponent : { it : IT.t } -> message
  | Write_value_unrepresentable of
      { ct : Sctypes.t;
        location : IT.t;
        value : IT.t;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Int_unrepresentable of
      { value : IT.t;
        ict : Sctypes.t;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Unproven_constraint of
      { constr : LC.t;
        requests : request_chain;
        info : info;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Undefined_behaviour of
      { ub : CF.Undefined.undefined_behaviour;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  (* | Implementation_defined_behaviour of document * state_report *)
  | Unspecified of CF.Ctype.ctype
  | StaticError of
      { err : string;
        ctxt : Context.t * log;
        model : Solver.model_with_q
      }
  | Generic of Pp.document
  | Generic_with_model of
      { err : Pp.document;
        model : Solver.model_with_q;
        ctxt : Context.t * log
      }
  | Unsupported of Pp.document
  | Parser of Cerb_frontend.Errors.cparser_cause
  | Empty_pattern
  | Missing_pattern of Pp.document
  | Redundant_pattern of Pp.document
  | Duplicate_pattern
  | Empty_provenance
  | Inconsistent_assumptions of string * (Context.t * log)

type type_error =
  { loc : Locations.t;
    msg : message
  }

type report =
  { short : Pp.document;
    descr : Pp.document option;
    state : Report.report option
  }

let request_chain_description requests =
  let pp_req req =
    let doc = RET.pp req.resource in
    let doc =
      match req.loc with
      | None -> doc
      | Some loc ->
        doc ^^ hardline ^^ !^"      " ^^ !^(fst (Locations.head_pos_of_location loc))
    in
    match req.reason with None -> doc | Some str -> doc ^^^ parens !^str
  in
  let rec loop req = function
    | [] -> !^"Resource needed:" ^^^ pp_req req
    | req2 :: reqs -> loop req2 reqs ^^ hardline ^^ !^"  which requires:" ^^^ pp_req req
  in
  match requests with [] -> None | req :: reqs -> Some (loop req reqs)


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
  | Unknown_datatype tag ->
    let short = !^"Datatype" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined" in
    { short; descr = None; state = None }
  | Unknown_datatype_constr tag ->
    let short = !^"Datatype constructor" ^^^ squotes (Sym.pp tag) ^^^ !^"not defined" in
    { short; descr = None; state = None }
  | Unknown_resource_predicate { id; logical } ->
    let short = !^"Unknown resource predicate" ^^^ squotes (Sym.pp id) in
    let descr =
      if logical then
        Some (!^"Note " ^^^ squotes (Sym.pp id) ^^^ !^" is a known logical predicate.")
      else
        None
    in
    { short; descr; state = None }
  | Unknown_logical_function { id; resource } ->
    let short = !^"Unknown logical function" ^^^ squotes (Sym.pp id) in
    let descr =
      if resource then
        Some (!^"Note " ^^^ squotes (Sym.pp id) ^^^ !^" is a known resource predicate.")
      else
        None
    in
    { short; descr; state = None }
  | Unexpected_member (expected, member) ->
    let short = !^"Unexpected member" ^^^ Id.pp member in
    let descr = !^"the struct only has members" ^^^ Pp.list Id.pp expected in
    { short; descr = Some descr; state = None }
  | Unknown_lemma sym ->
    let short = !^"Unknown lemma" ^^^ squotes (Sym.pp sym) in
    { short; descr = None; state = None }
  | First_iarg_missing ->
    let short = !^"Missing pointer input argument" in
    let descr = !^"a predicate definition must have at least one input argument" in
    { short; descr = Some descr; state = None }
  | First_iarg_not_pointer { pname; found_bty } ->
    let short = !^"Non-pointer first input argument" in
    let descr =
      !^"the first input argument of predicate"
      ^^^ Pp.squotes (ResourceTypes.pp_predicate_name pname)
      ^^^ !^"must have type"
      ^^^ Pp.squotes BaseTypes.(pp (Loc ()))
      ^^^ !^"but was found with type"
      ^^^ Pp.squotes BaseTypes.(pp found_bty)
    in
    { short; descr = Some descr; state = None }
  | Missing_member m ->
    let short = !^"Missing member" ^^^ Id.pp m in
    { short; descr = None; state = None }
  | Missing_resource { requests; situation; ctxt; model } ->
    let short = !^"Missing resource" ^^^ for_situation situation in
    let descr = request_chain_description requests in
    let orequest =
      Option.map (fun r -> r.resource) (List.nth_opt (List.rev requests) 0)
    in
    let state = trace ctxt model Explain.{ no_ex with request = orequest } in
    { short; descr; state = Some state }
  | Merging_multiple_arrays { requests; situation; ctxt; model } ->
    let short =
      !^"Cannot satisfy request for resource"
      ^^^ for_situation situation
      ^^ dot
      ^^^ !^"It requires merging multiple arrays."
    in
    let descr = request_chain_description requests in
    let orequest =
      Option.map (fun r -> r.resource) (List.nth_opt (List.rev requests) 0)
    in
    let state = trace ctxt model Explain.{ no_ex with request = orequest } in
    { short; descr; state = Some state }
  | Unused_resource { resource; ctxt; model } ->
    let resource = RE.pp resource in
    let short = !^"Left-over unused resource" ^^^ squotes resource in
    let state = trace ctxt model Explain.no_ex in
    { short; descr = None; state = Some state }
  | Number_members { has; expect } ->
    let short = !^"Wrong number of struct members" in
    let descr =
      !^"Expected"
      ^^^ !^(string_of_int expect)
      ^^ comma
      ^^^ !^"has"
      ^^^ !^(string_of_int has)
    in
    { short; descr = Some descr; state = None }
  | Number_arguments { has; expect } ->
    let short = !^"Wrong number of arguments" in
    let descr =
      !^"Expected"
      ^^^ !^(string_of_int expect)
      ^^ comma
      ^^^ !^"has"
      ^^^ !^(string_of_int has)
    in
    { short; descr = Some descr; state = None }
  | Number_input_arguments { has; expect } ->
    let short = !^"Wrong number of input arguments" in
    let descr =
      !^"Expected"
      ^^^ !^(string_of_int expect)
      ^^ comma
      ^^^ !^"has"
      ^^^ !^(string_of_int has)
    in
    { short; descr = Some descr; state = None }
  | Number_output_arguments { has; expect } ->
    let short = !^"Wrong number of output arguments" in
    let descr =
      !^"Expected"
      ^^^ !^(string_of_int expect)
      ^^ comma
      ^^^ !^"has"
      ^^^ !^(string_of_int has)
    in
    { short; descr = Some descr; state = None }
  | Mismatch { has; expect } ->
    let short = !^"Mismatched types." in
    let descr =
      !^"Expected value of type"
      ^^^ squotes expect
      ^^^ !^"but found value of type"
      ^^^ squotes has
    in
    { short; descr = Some descr; state = None }
  | Illtyped_it { it; has; expected; reason } ->
    let short = !^"Type error" in
    let descr =
      !^"Expression"
      ^^^ squotes it
      ^^^ !^"has type"
      ^^^ squotes has
      ^^ dot
      ^/^ !^"I expected it to have type"
      ^^^ squotes !^expected
      ^^^ !^"because of"
      ^^^ !^reason
    in
    { short; descr = Some descr; state = None }
  | NIA { it; hint } ->
    let it = IT.pp it in
    let short = !^"Non-linear integer arithmetic." in
    let descr =
      !^"Illtyped expression"
      ^^^ squotes it
      ^^ dot
      ^^^ !^"Non-linear integer arithmetic in the specification term"
      ^^^ it
      ^^ dot
      ^^^ !^hint
    in
    { short; descr = Some descr; state = None }
  | TooBigExponent { it } ->
    let it = IT.pp it in
    let short = !^"Exponent too big" in
    let descr =
      !^"Illtyped expression"
      ^^^ squotes it
      ^^ dot
      ^^^ !^"Too big exponent in the specification term"
      ^^^ it
      ^^ dot
      ^^^ !^"Exponent must fit int32 type"
    in
    { short; descr = Some descr; state = None }
  | NegativeExponent { it } ->
    let it = IT.pp it in
    let short = !^"Negative exponent" in
    let descr =
      !^"Illtyped expression"
      ^^ squotes it
      ^^ dot
      ^^^ !^"Negative exponent in the specification term"
      ^^^ it
      ^^ dot
      ^^^ !^"Exponent must be non-negative"
    in
    { short; descr = Some descr; state = None }
  | Write_value_unrepresentable { ct; location; value; ctxt; model } ->
    let short = !^"Write value not representable at type" ^^^ Sctypes.pp ct in
    let location = IT.pp location in
    let value = IT.pp value in
    let state = trace ctxt model Explain.no_ex in
    let descr =
      !^"Location" ^^ colon ^^^ location ^^ comma ^^^ !^"value" ^^ colon ^^^ value ^^ dot
    in
    { short; descr = Some descr; state = Some state }
  | Int_unrepresentable { value; ict; ctxt; model } ->
    let short = !^"integer value not representable at type" ^^^ Sctypes.pp ict in
    let value = IT.pp value in
    let descr = !^"Value" ^^ colon ^^^ value in
    let state = trace ctxt model Explain.no_ex in
    { short; descr = Some descr; state = Some state }
  | Unproven_constraint { constr; requests; info; ctxt; model } ->
    let short = !^"Unprovable constraint" in
    let state =
      trace ctxt model Explain.{ no_ex with unproven_constraint = Some constr }
    in
    let descr =
      let spec_loc, odescr = info in
      let head, pos = Locations.head_pos_of_location spec_loc in
      let doc =
        match odescr with
        | None -> !^"Constraint from" ^^^ !^head ^/^ !^pos
        | Some descr -> !^"Constraint from" ^^^ !^descr ^^^ !^head ^/^ !^pos
      in
      match request_chain_description requests with
      | Some doc2 -> doc ^^ hardline ^^ doc2
      | None -> doc
    in
    { short; descr = Some descr; state = Some state }
  | Undefined_behaviour { ub; ctxt; model } ->
    let short = !^"Undefined behaviour" in
    let state = trace ctxt model Explain.no_ex in
    let descr =
      match CF.Undefined.std_of_undefined_behaviour ub with
      | Some stdref -> !^(CF.Undefined.ub_short_string ub) ^^^ parens !^stdref
      | None -> !^(CF.Undefined.ub_short_string ub)
    in
    { short; descr = Some descr; state = Some state }
  (* | Implementation_defined_behaviour (impl, state) -> *)
  (*    let short = !^"Implementation defined behaviour" in *)
  (*    let descr = impl in *)
  (*    { short; descr = Some descr; state = Some state;  } *)
  | Unspecified ctype ->
    let short = !^"Unspecified value of C-type" ^^^ CF.Pp_core_ctype.pp_ctype ctype in
    { short; descr = None; state = None }
  | StaticError { err; ctxt; model } ->
    let short = !^"Static error" in
    let state = trace ctxt model Explain.no_ex in
    let descr = !^err in
    { short; descr = Some descr; state = Some state }
  | Generic err ->
    let short = err in
    { short; descr = None; state = None }
  | Generic_with_model { err; model; ctxt } ->
    let short = err in
    let state = trace ctxt model Explain.no_ex in
    { short; descr = None; state = Some state }
  | Unsupported err ->
    let short = err in
    { short; descr = None; state = None }
  | Parser err ->
    let short = !^(Cerb_frontend.Pp_errors.string_of_cparser_cause err) in
    { short; descr = None; state = None }
  | Empty_pattern ->
    let short = !^"Empty match expression." in
    { short; descr = None; state = None }
  | Missing_pattern p' ->
    let short = !^"Missing pattern" ^^^ squotes p' ^^ dot in
    { short; descr = None; state = None }
  | Redundant_pattern p' ->
    let short = !^"Redundant pattern" in
    { short; descr = Some p'; state = None }
  | Duplicate_pattern ->
    let short = !^"Duplicate pattern" in
    { short; descr = None; state = None }
  | Empty_provenance ->
    let short = !^"Empty provenance" in
    { short; descr = None; state = None }
  | Illtyped_binary_it { left; right; binop } ->
    let short =
      !^"Ill-typed application of binary operation"
      ^^^ squotes (CF.Cn_ocaml.PpAil.pp_cn_binop binop)
      ^^^ dot
    in
    let descr =
      Some
        (squotes (IT.pp left)
         ^^^ !^"has type"
         ^^^ squotes (BaseTypes.Surface.pp (IT.bt left))
         ^^ comma
         ^^^ squotes (IT.pp right)
         ^^^ !^"has type"
         ^^^ squotes (BaseTypes.Surface.pp (IT.bt right))
         ^^ dot)
    in
    { short; descr; state = None }
  | Inconsistent_assumptions (kind, ctxt_log) ->
    let short = !^kind ^^ !^" makes inconsistent assumptions" in
    let state = Some (trace ctxt_log (Solver.empty_model, []) Explain.no_ex) in
    { short; descr = None; state }


type t = type_error

(** Convert a possibly-relative filepath into an absolute one. *)
let canonicalize (path : string) : string =
  if Filename.is_relative path then (
    let current_dir = Sys.getcwd () in
    Filename.concat current_dir path)
  else
    path


(** Create a filename derived from the given error location, and create a file
    with that name in [output_dir], which will be created if it doesn't exist.
    If no directory is provided, or if the provided directory name is
    unusable, the file is created in the system temporary directory instead. *)
let mk_state_file_name
  ?(output_dir : string option)
  ?(fn_name : string option)
  (loc : Cerb_location.t)
  : string
  =
  let dir =
    match output_dir with
    | None -> Filename.get_temp_dir_name ()
    | Some d ->
      let dir = canonicalize d in
      if not (Sys.file_exists dir) then (
        (* 0o700 == r+w+x permissions for current user *)
        Sys.mkdir dir 0o700;
        dir)
      else if Sys.is_directory dir then
        dir
      else
        Filename.get_temp_dir_name ()
  in
  let file_tag =
    match Cerb_location.get_filename loc with
    | None -> ""
    | Some filename -> "__" ^ Filename.basename filename
  in
  let function_tag = match fn_name with None -> "" | Some fn -> "__" ^ fn in
  let filename = "state" ^ file_tag ^ function_tag ^ ".html" in
  Filename.concat dir filename


(** Format the error for human readability and print it to [stderr]. if the
    error contains enough information to create an HTML state report, generate
    one in [output_dir] (or, failing that, the system temporary directory) and
    print a link to it. *)
let report_pretty ?output_dir:dir_ ?(fn_name : string option) { loc; msg } =
  (* stealing some logic from pp_errors *)
  let report = pp_message msg in
  let consider =
    match report.state with
    | Some state ->
      let file = mk_state_file_name ?output_dir:dir_ ?fn_name loc in
      let link = Report.make file (Cerb_location.get_filename loc) state in
      let msg = !^"State file:" ^^^ !^("file://" ^ link) in
      Some msg
    | None -> None
  in
  Pp.error loc report.short (Option.to_list report.descr @ Option.to_list consider)


(* stealing some logic from pp_errors *)
let report_json ?output_dir:dir_ ?(fn_name : string option) { loc; msg } =
  let report = pp_message msg in
  let state_error_file =
    match report.state with
    | Some state ->
      let file = mk_state_file_name ?output_dir:dir_ ?fn_name loc in
      let link = Report.make file (Cerb_location.get_filename loc) state in
      `String link
    | None -> `Null
  in
  let descr =
    match report.descr with None -> `Null | Some descr -> `String (Pp.plain descr)
  in
  let json =
    `Assoc
      [ ("loc", Loc.json_loc loc);
        ("short", `String (Pp.plain report.short));
        ("descr", descr);
        ("state", state_error_file)
      ]
  in
  Yojson.Safe.to_channel ~std:true stderr json
