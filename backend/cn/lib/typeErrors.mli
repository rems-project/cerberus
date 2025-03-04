(** TODO Switch to this structure: https://rustc-dev-guide.rust-lang.org/diagnostics.html#diagnostic-structure *)

(** TODO Cleanly factor out all pretty printing from all error gathering.
    Pp.document, string to actual types (including polymorphic variants if need be) *)

val call_prefix : Error_common.call_situation -> string

(** TODO move *)
val call_situation : Error_common.call_situation -> Pp.document

(** TODO move *)
val checking_situation : Error_common.situation -> Pp.document

(** TODO move *)
val for_access : Error_common.access -> Pp.document

(** TODO move *)
val for_situation : Error_common.situation -> Pp.document

module RequestChain : sig
  type elem =
    { resource : Request.t;
      loc : Cerb_location.t option;
      reason : string option (** TODO replace with an actual type *)
    }

  type t = elem list

  (** TODO move *)
  val pp : t -> Pp.document option
end

type message =
  | Global of Global.error
  | WellTyped of WellTyped.message
  | First_iarg_missing
  | First_iarg_not_pointer of
      { pname : Request.name;
        found_bty : BaseTypes.t
      }
  | Missing_resource of
      { requests : RequestChain.t;
        situation : Error_common.situation;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Merging_multiple_arrays of
      { requests : RequestChain.t;
        situation : Error_common.situation;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Unused_resource of
      { resource : Resource.t;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Illtyped_binary_it of
      { left : IndexTerms.Surface.t;
        right : IndexTerms.Surface.t;
        binop : Cerb_frontend.Cn.cn_binop
      }
  | TooBigExponent : { it : IndexTerms.t } -> message
  | NegativeExponent : { it : IndexTerms.t } -> message
  | Write_value_unrepresentable of
      { ct : Sctypes.t;
        location : IndexTerms.t;
        value : IndexTerms.t;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Int_unrepresentable of
      { value : IndexTerms.t;
        ict : Sctypes.t;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Unproven_constraint of
      { constr : LogicalConstraints.t;
        requests : RequestChain.t;
        info : Locations.info;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Undefined_behaviour of
      { ub : Cerb_frontend.Undefined.undefined_behaviour;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Needs_alloc_id of
      { ptr : IndexTerms.t;
        ub : Cerb_frontend.Undefined.undefined_behaviour;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Alloc_out_of_bounds of
      { term : IndexTerms.t;
        constr : IndexTerms.t;
        ub : Cerb_frontend.Undefined.undefined_behaviour;
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Allocation_not_live of
      { reason :
          [ `Copy_alloc_id | `ISO_array_shift | `ISO_member_shift | `Ptr_cmp | `Ptr_diff ];
        ptr : IndexTerms.t;
        ctxt : Context.t * Explain.log;
        model_constr : (Solver.model_with_q * IndexTerms.t) option
      }
  | Unspecified of Cerb_frontend.Ctype.ctype
  | StaticError of
      { err : string; (** TODO replace with an actual type *)
        ctxt : Context.t * Explain.log;
        model : Solver.model_with_q
      }
  | Generic of Pp.document [@deprecated "Please add a specific constructor"]
  (** TODO delete this *)
  | Generic_with_model of
      { err : Pp.document;
        model : Solver.model_with_q;
        ctxt : Context.t * Explain.log
      } [@deprecated "Please add a specific constructor"] (** TODO delete this too *)
  | Unsupported of Pp.document (** TODO add source location *)
  | Parser of Cerb_frontend.Errors.cparser_cause
  | Empty_provenance
  | Inconsistent_assumptions of string * (Context.t * Explain.log)
  (** TODO replace string with an actual type *)
  | Byte_conv_needs_owned
  | Double_spec of
      { fname : Sym.t;
        orig_loc : Locations.t
      }
  | Requires_after_ensures of { ens_loc : Locations.t }

type t =
  { loc : Locations.t;
    msg : message
  }

(** TODO move *)
type report =
  { short : Pp.document;
    descr : Pp.document option;
    state : Report.report option (** Why is this here? *)
  }

(** TODO move *)
val pp_message : message -> report

(** TODO move *)
val canonicalize : string -> string

(** TODO move *)
val mk_output_dir : string option -> string

(** TODO move *)
val located_file_name
  :  ?fn_name:string ->
  dir:string ->
  name:string ->
  ext:string ->
  Cerb_location.t ->
  string

(** TODO move *)
val mk_state_file_name : ?fn_name:string -> string -> Cerb_location.t -> string

(** TODO move *)
val mk_report_file_name : ?fn_name:string -> string -> Cerb_location.t -> string

(** TODO move *)
val report_pretty
  :  ?output_dir:string ->
  ?fn_name:string ->
  ?serialize_json:bool ->
  t ->
  unit

(** TODO move *)
val report_json
  :  ?output_dir:string ->
  ?fn_name:string ->
  ?serialize_json:bool ->
  t ->
  unit
