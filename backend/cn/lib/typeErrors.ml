module IT = IndexTerms
module CF = Cerb_frontend
module Loc = Locations
module Res = Resource
module LC = LogicalConstraints
module Req = Request
open Pp

type label_kind = Where.label

type access =
  | Load
  | Store
  | Deref
  | Kill
  | Free
  | To_bytes
  | From_bytes

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
  | Call s -> call_situation s


let for_access = function
  | Kill -> !^"for de-allocating"
  | Deref -> !^"for dereferencing"
  | Load -> !^"for reading"
  | Store -> !^"for writing"
  | Free -> !^"for free-ing"
  | To_bytes -> !^"for converting to bytes"
  | From_bytes -> !^"for convering from bytes"


let for_situation = function
  | Access access -> for_access access
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


module RequestChain = struct
  type elem =
    { resource : Req.t;
      loc : Locations.t option;
      reason : string option
    }

  type t = elem list

  let pp requests =
    let pp_req req =
      let doc = Req.pp req.resource in
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
end

type message =
  | Global of Global.error
  | WellTyped of WellTyped.message
  (* some from Kayvan's compilePredicates module *)
  | First_iarg_missing
  | First_iarg_not_pointer of
      { pname : Request.name;
        found_bty : BaseTypes.t
      }
  | Missing_resource of
      { requests : RequestChain.t;
        situation : situation;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Merging_multiple_arrays of
      { requests : RequestChain.t;
        situation : situation;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Unused_resource of
      { resource : Res.t;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Illtyped_binary_it of
      { left : IT.Surface.t;
        right : IT.Surface.t;
        binop : CF.Cn.cn_binop
      }
  | TooBigExponent : { it : IT.t } -> message
  | NegativeExponent : { it : IT.t } -> message
  | Write_value_unrepresentable of
      { ct : Sctypes.t;
        location : IT.t;
        value : IT.t;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Int_unrepresentable of
      { value : IT.t;
        ict : Sctypes.t;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Unproven_constraint of
      { constr : LC.t;
        requests : RequestChain.t;
        info : Locations.info;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Undefined_behaviour of
      { ub : CF.Undefined.undefined_behaviour;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Needs_alloc_id of
      { ptr : IT.t;
        ub : CF.Undefined.undefined_behaviour;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Alloc_out_of_bounds of
      { term : IT.t;
        constr : IT.t;
        ub : CF.Undefined.undefined_behaviour;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Allocation_not_live of
      { reason :
          [ `Copy_alloc_id | `Ptr_cmp | `Ptr_diff | `ISO_array_shift | `ISO_member_shift ];
        ptr : IT.t;
        ctxt : Context.t * Explain.log;
        model_constr : (Solver.model_with_q * IT.t) option
      }
  (* | Implementation_defined_behaviour of document * state_report *)
  | Unspecified of CF.Ctype.ctype
  | StaticError of
      { err : string;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Generic of Pp.document (** TODO delete this *)
  | Generic_with_model of
      { err : document;
        model : Solver.model_with_q;
        ctxt : Context.t * Explain.log
      }
  | Unsupported of document
  | Parser of Cerb_frontend.Errors.cparser_cause
  | Empty_provenance
  | Inconsistent_assumptions of string * (Context.t * Explain.log)
  | Byte_conv_needs_owned

type t =
  { loc : Locations.t;
    msg : message
  }

type report =
  { short : document;
    descr : document option;
    state : Report.report option
  }

let pp_global = function
  | Global.Unknown_function sym ->
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
  | Unknown_lemma sym ->
    let short = !^"Unknown lemma" ^^^ squotes (Sym.pp sym) in
    { short; descr = None; state = None }
  | Unexpected_member (expected, member) ->
    let short = !^"Unexpected member" ^^^ Id.pp member in
    let descr = !^"the struct only has members" ^^^ list Id.pp expected in
    { short; descr = Some descr; state = None }


let pp_welltyped = function
  | WellTyped.Global msg -> pp_global msg
  | Unknown_variable s ->
    let short = !^"Unknown variable" ^^^ squotes (Sym.pp s) in
    { short; descr = None; state = None }
  | Number_arguments { type_; has; expect } ->
    let type_ =
      match type_ with `Other -> "" | `Input -> "input" | `Output -> "output"
    in
    let short = !^"Wrong number" ^^^ !^type_ ^^^ !^"of arguments" in
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
  | Empty_pattern ->
    let short = !^"Empty match expression." in
    { short; descr = None; state = None }
  | Generic err ->
    let short = err in
    { short; descr = None; state = None }
  | Redundant_pattern p' ->
    let short = !^"Redundant pattern" in
    { short; descr = Some p'; state = None }
  | Missing_member m ->
    let short = !^"Missing member" ^^^ Id.pp m in
    { short; descr = None; state = None }


let pp_message = function
  | Global msg -> pp_global msg
  | WellTyped msg -> pp_welltyped msg
  | First_iarg_missing ->
    let short = !^"Missing pointer input argument" in
    let descr = !^"a predicate definition must have at least one input argument" in
    { short; descr = Some descr; state = None }
  | First_iarg_not_pointer { pname; found_bty } ->
    let short = !^"Non-pointer first input argument" in
    let descr =
      !^"the first input argument of predicate"
      ^^^ squotes (Request.pp_name pname)
      ^^^ !^"must have type"
      ^^^ squotes BaseTypes.(pp (Loc ()))
      ^^^ !^"but was found with type"
      ^^^ squotes BaseTypes.(pp found_bty)
    in
    { short; descr = Some descr; state = None }
  | Missing_resource { requests; situation; ctxt; model } ->
    let short = !^"Missing resource" ^^^ for_situation situation in
    let descr = RequestChain.pp requests in
    let orequest =
      Option.map
        (fun (r : RequestChain.elem) -> r.RequestChain.resource)
        (List.nth_opt (List.rev requests) 0)
    in
    let state = Explain.trace ctxt model Explain.{ no_ex with request = orequest } in
    { short; descr; state = Some state }
  | Merging_multiple_arrays { requests; situation; ctxt; model } ->
    let short =
      !^"Cannot satisfy request for resource"
      ^^^ for_situation situation
      ^^ dot
      ^^^ !^"It requires merging multiple arrays."
    in
    let descr = RequestChain.pp requests in
    let orequest =
      Option.map (fun r -> r.RequestChain.resource) (List.nth_opt (List.rev requests) 0)
    in
    let state = Explain.trace ctxt model Explain.{ no_ex with request = orequest } in
    { short; descr; state = Some state }
  | Unused_resource { resource; ctxt; model } ->
    let resource = Res.pp resource in
    let short = !^"Left-over unused resource" ^^^ squotes resource in
    let state = Explain.trace ctxt model Explain.no_ex in
    { short; descr = None; state = Some state }
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
    let state = Explain.trace ctxt model Explain.no_ex in
    let descr =
      !^"Location" ^^ colon ^^^ location ^^ comma ^^^ !^"value" ^^ colon ^^^ value ^^ dot
    in
    { short; descr = Some descr; state = Some state }
  | Int_unrepresentable { value; ict; ctxt; model } ->
    let short = !^"integer value not representable at type" ^^^ Sctypes.pp ict in
    let value = IT.pp value in
    let descr = !^"Value" ^^ colon ^^^ value in
    let state = Explain.trace ctxt model Explain.no_ex in
    { short; descr = Some descr; state = Some state }
  | Unproven_constraint { constr; requests; info; ctxt; model } ->
    let short = !^"Unprovable constraint" in
    let state =
      Explain.trace ctxt model Explain.{ no_ex with unproven_constraint = Some constr }
    in
    let descr =
      let spec_loc, odescr = info in
      let head, pos = Locations.head_pos_of_location spec_loc in
      let doc =
        match odescr with
        | None -> !^"Constraint from" ^^^ !^head ^/^ !^pos
        | Some descr -> !^"Constraint from" ^^^ !^descr ^^^ !^head ^/^ !^pos
      in
      match RequestChain.pp requests with
      | Some doc2 -> doc ^^ hardline ^^ doc2
      | None -> doc
    in
    { short; descr = Some descr; state = Some state }
  | Undefined_behaviour { ub; ctxt; model } ->
    let short = !^"Undefined behaviour" in
    let state = Explain.trace ctxt model Explain.no_ex in
    let descr =
      match CF.Undefined.std_of_undefined_behaviour ub with
      | Some stdref -> !^(CF.Undefined.ub_short_string ub) ^^^ parens !^stdref
      | None -> !^(CF.Undefined.ub_short_string ub)
    in
    { short; descr = Some descr; state = Some state }
  | Needs_alloc_id { ptr; ub; ctxt; model } ->
    let short = !^"Pointer " ^^ bquotes (IT.pp ptr) ^^ !^" needs allocation ID" in
    let state = Explain.trace ctxt model Explain.no_ex in
    let descr =
      match CF.Undefined.std_of_undefined_behaviour ub with
      | Some stdref -> !^(CF.Undefined.ub_short_string ub) ^^^ parens !^stdref
      | None -> !^(CF.Undefined.ub_short_string ub)
    in
    { short; descr = Some descr; state = Some state }
  | Alloc_out_of_bounds { constr; term; ub; ctxt; model } ->
    let short = bquotes (IT.pp term) ^^ !^" out of bounds" in
    let state =
      Explain.trace
        ctxt
        model
        Explain.{ no_ex with unproven_constraint = Some (LC.T constr) }
    in
    let descr =
      match CF.Undefined.std_of_undefined_behaviour ub with
      | Some stdref -> !^(CF.Undefined.ub_short_string ub) ^^^ parens !^stdref
      | None -> !^(CF.Undefined.ub_short_string ub)
    in
    { short; descr = Some descr; state = Some state }
  | Allocation_not_live { reason; ptr; ctxt; model_constr } ->
    let adjust = function
      | IT.IT (CopyAllocId { loc; _ }, _, _) -> loc
      | IT.IT (ArrayShift { base; _ }, _, _) -> base
      | IT.IT (MemberShift (ptr, _, _), _, _) -> ptr
      | _ -> assert false
    in
    let reason, ptr =
      match reason with
      | `Copy_alloc_id -> ("copy_alloc_id", adjust ptr)
      | `Ptr_diff -> ("pointer difference", ptr)
      | `Ptr_cmp -> ("pointer comparison", ptr)
      | `ISO_array_shift -> ("array shift", adjust ptr)
      | `ISO_member_shift -> ("member shift", adjust ptr)
    in
    let short =
      !^"Pointer " ^^ bquotes (IT.pp ptr) ^^^ !^"needs to be live for" ^^^ !^reason
    in
    let state =
      Option.map
        (fun (model, constr) ->
          Explain.trace
            ctxt
            model
            Explain.{ no_ex with unproven_constraint = Some (LC.T constr) })
        model_constr
    in
    let descr = !^"Need an Alloc or Owned in context with same allocation id" in
    { short; descr = Some descr; state }
  (* | Implementation_defined_behaviour (impl, state) -> *)
  (*    let short = !^"Implementation defined behaviour" in *)
  (*    let descr = impl in *)
  (*    { short; descr = Some descr; state = Some state;  } *)
  | Unspecified ctype ->
    let short = !^"Unspecified value of C-type" ^^^ CF.Pp_core_ctype.pp_ctype ctype in
    { short; descr = None; state = None }
  | StaticError { err; ctxt; model } ->
    let short = !^"Static error" in
    let state = Explain.trace ctxt model Explain.no_ex in
    let descr = !^err in
    { short; descr = Some descr; state = Some state }
  | Generic err ->
    let short = err in
    { short; descr = None; state = None }
  | Generic_with_model { err; model; ctxt } ->
    let short = err in
    let state = Explain.trace ctxt model Explain.no_ex in
    { short; descr = None; state = Some state }
  | Unsupported err ->
    let short = err in
    { short; descr = None; state = None }
  | Parser err ->
    let short = !^(Cerb_frontend.Pp_errors.string_of_cparser_cause err) in
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
         ^^^ squotes (BaseTypes.Surface.pp (IT.get_bt left))
         ^^ comma
         ^^^ squotes (IT.pp right)
         ^^^ !^"has type"
         ^^^ squotes (BaseTypes.Surface.pp (IT.get_bt right))
         ^^ dot)
    in
    { short; descr; state = None }
  | Inconsistent_assumptions (kind, ctxt_log) ->
    let short = !^kind ^^ !^" makes inconsistent assumptions" in
    let state = Some (Explain.trace ctxt_log (Solver.empty_model, []) Explain.no_ex) in
    { short; descr = None; state }
  | Byte_conv_needs_owned ->
    let short = !^"byte conversion only supports Owned/Block" in
    { short; descr = None; state = None }


(** Convert a possibly-relative filepath into an absolute one. *)
let canonicalize (path : string) : string =
  if Filename.is_relative path then (
    let current_dir = Sys.getcwd () in
    Filename.concat current_dir path)
  else
    path


(** Construct a canonical path to a directory and create the directory if it
    doesn't already exist. If [output_dir] is provided, the path will point to
    it. If not, the path will point to a temporary directory instead. *)
let mk_output_dir (output_dir : string option) : string =
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


(** A naming convention for files that pertain to specific error locations. The
    generated name will always include the user-provided [~name], which should
    be a valid filename. *)
let located_file_name
  ?(fn_name : string option)
  ~(dir : string)
  ~(name : string)
  ~(ext : string)
  (error_loc : Cerb_location.t)
  : string
  =
  let source_file_tag =
    match Cerb_location.get_filename error_loc with
    | None -> ""
    | Some filename -> "__" ^ Filename.basename filename
  in
  let function_tag = match fn_name with None -> "" | Some fn -> "__" ^ fn in
  let filename = name ^ source_file_tag ^ function_tag ^ ext in
  Filename.concat dir filename


(** Construct a canonical filename for state output derived from the given error
    location, located in [output_dir]. *)
let mk_state_file_name
  ?(fn_name : string option)
  (output_dir : string)
  (loc : Cerb_location.t)
  : string
  =
  located_file_name ?fn_name ~dir:output_dir ~name:"state" ~ext:".html" loc


(** Construct a canonical filename for report output derived from the given
    error location, located in [output_dir]. *)
let mk_report_file_name
  ?(fn_name : string option)
  (output_dir : string)
  (loc : Cerb_location.t)
  : string
  =
  located_file_name ?fn_name ~dir:output_dir ~name:"report" ~ext:".json" loc


(** Format the error for human readability and print it to [stderr]. if the
    error contains enough information to create an HTML state report, generate
    one in [output_dir] (or, failing that, the system temporary directory) and
    print a link to it. *)
let report_pretty
  ?(output_dir : string option)
  ?(fn_name : string option)
  ?(serialize_json : bool = false)
  { loc; msg }
  =
  (* stealing some logic from pp_errors *)
  let report = pp_message msg in
  let consider =
    match report.state with
    | Some state ->
      let dir = mk_output_dir output_dir in
      let file = mk_state_file_name ?fn_name dir loc in
      let link = Report.make file (Cerb_location.get_filename loc) state in
      let state_msg = !^"State file:" ^^^ !^("file://" ^ link) in
      if serialize_json then (
        let report_file = mk_report_file_name ?fn_name dir loc in
        let report_js = Report.report_to_yojson state in
        let () = Yojson.Safe.to_file report_file report_js in
        let report_msg = !^"Report file:" ^^^ !^("file://" ^ report_file) in
        [ state_msg; report_msg ])
      else
        [ state_msg ]
    | None -> []
  in
  error loc report.short (Option.to_list report.descr @ consider)


(* stealing some logic from pp_errors *)
let report_json
  ?(output_dir : string option)
  ?(fn_name : string option)
  ?(serialize_json : bool = false)
  { loc; msg }
  =
  let report = pp_message msg in
  let state_error_file, report_file =
    match report.state with
    | Some state ->
      let dir = mk_output_dir output_dir in
      let file = mk_state_file_name ?fn_name dir loc in
      let link = Report.make file (Cerb_location.get_filename loc) state in
      if serialize_json then (
        let report_file = mk_report_file_name ?fn_name dir loc in
        let report_js = Report.report_to_yojson state in
        let () = Yojson.Safe.to_file report_file report_js in
        (`String link, `String report_file))
      else
        (`String link, `Null)
    | None -> (`Null, `Null)
  in
  let descr =
    match report.descr with None -> `Null | Some descr -> `String (plain descr)
  in
  let json =
    `Assoc
      [ ("loc", Loc.json_loc loc);
        ("short", `String (plain report.short));
        ("descr", descr);
        ("state", state_error_file);
        ("report", report_file)
      ]
  in
  Yojson.Safe.to_channel ~std:true stderr json
