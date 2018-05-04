open Core

module type CONFIG =
sig
  (* Show ISO STD marks *)
  val show_std: bool
  (* Show function from #include -- actually from .h files *)
  val show_include: bool
  (* handle_location c_loc core_range *)
  val handle_location: Location_ocaml.t -> PPrint.range -> unit
end

module type PP_CORE =
sig
  val pp_core_object_type: core_object_type -> PPrint.document
  val pp_core_base_type: core_base_type -> PPrint.document
  val pp_object_value: object_value -> PPrint.document
  val pp_value: value -> PPrint.document
  val pp_params: (Symbol.sym * core_base_type) list -> PPrint.document
  val pp_pexpr: ('ty, Symbol.sym) generic_pexpr -> PPrint.document
  val pp_expr: ('a, 'b, Symbol.sym) generic_expr -> PPrint.document
  val pp_expr: ('a, 'b, Symbol.sym) generic_expr -> PPrint.document
  val pp_file: ('a, 'b) generic_file -> PPrint.document

  val pp_action: ('a, Symbol.sym) generic_action_ -> PPrint.document
  val pp_stack: 'a stack -> PPrint.document
end

module Make (C : CONFIG) : PP_CORE

module Basic : PP_CORE
module All : PP_CORE


