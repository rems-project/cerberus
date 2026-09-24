open Cerb_symbol
open Core
open Ctype

val valueFromMemValue : Impl_mem.mem_value -> core_object_type * value
val memValueFromValue : ctype -> value -> Impl_mem.mem_value option

val loadedValueFromMemValue :
  Impl_mem.mem_value -> core_object_type * loaded_value

val core_object_type_of_ctype : ctype -> core_object_type option
val valueFromPexpr : pexpr -> value option
val valueFromPexprs : pexpr list -> value list option
val to_pure : 'a expr -> pexpr option

(* Core pattern builders  ************************************************** *)
val mk_empty_pat : core_base_type -> pattern
val mk_sym_pat : Sym.t -> core_base_type -> pattern
val mk_tuple_pat : pattern list -> pattern
val mk_specified_pat : pattern -> pattern
val mk_unspecified_pat : pattern -> pattern

(* Core pexpr builders  ***************************************************** *)
val mk_sym_pe : Sym.t -> pexpr
val mk_integer_pe : Z.t -> pexpr
val mk_floating_pe : float -> pexpr
val mk_nullptr_pe : ctype -> pexpr
val mk_specified_pe : pexpr -> pexpr
val mk_unspecified_pe : ctype -> pexpr
val mk_array_pe : pexpr list -> pexpr
val mk_unit_pe : pexpr
val mk_boolean_pe : bool -> pexpr
val mk_ail_ctype_pe : ctype -> pexpr
val mk_ctype_pe : ctype -> pexpr
val mk_list_pe : core_base_type -> pexpr list -> pexpr
val mk_tuple_pe : pexpr list -> pexpr
val mk_ivmax_pe : pexpr -> pexpr

(* val mk_ivmin_pe: pexpr -> pexpr *)
val mk_sizeof_pe : pexpr -> pexpr
val mk_alignof_pe : pexpr -> pexpr
val mk_nullcap_pe : bool -> pexpr
val mk_undef_pe : Cerb_location.t -> Undefined.undefined_behaviour -> pexpr
val mk_error_pe : string -> pexpr -> pexpr
val mk_not_pe : pexpr -> pexpr
val mk_op_pe : binop -> pexpr -> pexpr -> pexpr
val mk_conv_int_pe : integerType -> pexpr -> pexpr
val mk_wrapI_pe : integerType -> iop -> pexpr -> pexpr -> pexpr

val mk_catch_exceptional_condition_pe :
  integerType -> iop -> pexpr -> pexpr -> pexpr

val mk_let_pe : pattern -> pexpr -> pexpr -> pexpr
val mk_if_pe : pexpr -> pexpr -> pexpr -> pexpr
val mk_array_shift : pexpr -> ctype -> pexpr -> pexpr
val mk_member_shift_pe : pexpr -> Sym.t -> Identifier.t -> pexpr
val mk_memop_pe : Mem_common.pure_memop -> pexpr list -> pexpr
val mk_case_pe : pexpr -> (pattern * pexpr) list -> pexpr
val mk_neg_pe : integerType -> pexpr -> pexpr
val mk_struct_pe : Sym.t -> (Identifier.t * pexpr) list -> pexpr
val mk_union_pe : Sym.t -> Identifier.t -> pexpr -> pexpr
val mk_memberof_pe : Sym.t -> Identifier.t -> pexpr -> pexpr
val mk_value_pe : value -> pexpr
val mk_cfunction_pe : pexpr -> pexpr
val mk_std_pe : string -> pexpr -> pexpr

val mk_std_undef_pe :
  Cerb_location.t -> string -> Undefined.undefined_behaviour -> pexpr

val mk_std_pair_pe : string -> pexpr * pexpr -> pexpr * pexpr
val mk_call_pe : name -> pexpr list -> pexpr
val mk_are_compatible : pexpr -> pexpr -> pexpr
val mk_undef_exceptional_condition : Cerb_location.t -> pexpr
val bitwise_complement_pe : pexpr -> pexpr -> pexpr
val bitwise_AND_pe : pexpr -> pexpr -> pexpr -> pexpr
val bitwise_OR_pe : pexpr -> pexpr -> pexpr -> pexpr
val bitwise_XOR_pe : pexpr -> pexpr -> pexpr -> pexpr
val mk_ivfromfloat_pe : pexpr -> pexpr -> pexpr
val mk_fvfromint_pe : pexpr -> pexpr


(* Core expr builders ****************************************************** *)
val mk_pure_e : pexpr -> 'a expr
val mk_value_e : value -> 'a expr
val mk_skip_e : unit expr
val mk_unseq_e : 'a expr list -> 'a expr
val mk_case_e : pexpr -> (pattern * unit expr) list -> unit expr
val mk_wseq_e : pattern -> 'a expr -> 'a expr -> 'a expr
val mk_sseq_e : pattern -> 'a expr -> 'a expr -> 'a expr

val mk_save_e_ :
  Annot.annot list ->
  Sym.t * core_base_type ->
  (Sym.t
  * ((core_base_type * (Ctype.ctype * pass_by_value_or_pointer) option) * pexpr))
  list ->
  unit expr ->
  unit expr

val mk_run_e : Sym.t -> pexpr list -> unit expr
val mk_nd_e : unit expr list -> unit expr
val mk_if_e_ : Annot.annot list -> pexpr -> unit expr -> unit expr -> unit expr
val mk_if_e : pexpr -> unit expr -> unit expr -> unit expr
val mk_let_e : pattern -> pexpr -> unit expr -> unit expr
val mk_ccall_e_ : Annot.annot list -> pexpr -> pexpr -> pexpr list -> unit expr
val mk_memop_e : Mem_common.memop -> pexpr list -> unit expr
val mk_wait_e : Mem_common.thread_id -> 'a expr

(* Core expr "smart" builders ************************************************)
val mk_unseq : 'a expr list -> 'a expr
val mk_unit_sseq : unit expr list -> unit expr -> unit expr
val mk_sseqs : (pattern * unit expr) list -> unit expr -> unit expr
val concat_sseq : 'a expr -> 'a expr -> 'a expr

(* Core (positive) memory action builders **************************************)
val pcreate : Cerb_location.t -> pexpr -> pexpr -> Cerb_symbol.prefix -> unit expr

val pcreate_readonly :
  Cerb_location.t -> pexpr -> pexpr -> pexpr -> Cerb_symbol.prefix -> unit expr

val pkill : Cerb_location.t -> kill_kind -> pexpr -> unit expr

val pstore :
  Cerb_location.t ->
  pexpr ->
  pexpr ->
  pexpr ->
  Atomics.memory_order ->
  unit expr

val pstore_lock :
  Cerb_location.t ->
  pexpr ->
  pexpr ->
  pexpr ->
  Atomics.memory_order ->
  unit expr

val pload :
  Cerb_location.t -> pexpr -> pexpr -> Atomics.memory_order -> unit expr

val pcompare_exchange_strong :
  Cerb_location.t ->
  pexpr ->
  pexpr ->
  pexpr ->
  pexpr ->
  Atomics.memory_order ->
  Atomics.memory_order ->
  unit expr

val pcompare_exchange_weak :
  Cerb_location.t ->
  pexpr ->
  pexpr ->
  pexpr ->
  pexpr ->
  Atomics.memory_order ->
  Atomics.memory_order ->
  unit expr

val plinux_load :
  Cerb_location.t -> pexpr -> pexpr -> Linux.linux_memory_order -> unit expr

val plinux_store :
  Cerb_location.t ->
  pexpr ->
  pexpr ->
  pexpr ->
  Linux.linux_memory_order ->
  unit expr

val plinux_rmw :
  Cerb_location.t ->
  pexpr ->
  pexpr ->
  pexpr ->
  Linux.linux_memory_order ->
  unit expr

val seq_rmw :
  Cerb_location.t ->
  bool ->
  pexpr ->
  Core.core_object_type ->
  pexpr ->
  Sym.t ->
  pexpr ->
  unit expr

(* Substitutions and pattern matching *)
val subst_sym_pexpr : Sym.t -> value -> pexpr -> pexpr
val subst_sym_expr : Sym.t -> value -> 'a expr -> 'a expr
val subst_wait : Mem_common.thread_id -> value -> 'a expr -> 'a expr
val subst_pattern : pattern -> pexpr -> 'a expr -> 'a expr option
val unsafe_subst_pattern : pattern -> pexpr -> 'a expr -> 'a expr
val unsafe_subst_sym_pexpr : Sym.t -> pexpr -> pexpr -> pexpr
val unsafe_subst_sym_expr : Sym.t -> pexpr -> 'a expr -> 'a expr

val select_case :
  (Sym.t -> value -> 'a -> 'a) -> value -> (pattern * 'a) list -> 'a option

(* Annotations and attributes *)
val add_loc : Cerb_location.t -> unit expr -> unit expr
val add_stmt : unit expr -> unit expr
val add_expr : unit expr -> unit expr
val add_std : string -> unit expr -> unit expr
val add_stds : string list -> unit expr -> unit expr
val add_attrs : Annot.attributes -> unit expr -> unit expr
val add_annot : Annot.annot -> unit expr -> unit expr
val add_annots : Annot.annot list -> unit expr -> unit expr
val annotate_integer_type_pexpr : integerType -> pexpr -> pexpr
val maybe_annotate_integer_type_pexpr : ctype -> pexpr -> pexpr
val maybe_annotate_integer_type : ctype -> unit expr -> unit expr
val lookup_env : Sym.t -> (Sym.t, value) Pmap.map list -> value option

val update_env :
  pattern ->
  value ->
  (Sym.t, value) Pmap.map list ->
  (Sym.t, value) Pmap.map list

val find_labeled_continuation :
  Sym.t -> 'a expr -> (Sym.t list * 'a expr) option

val collect_labeled_continuations_NEW :
  'a file ->
  ( Sym.t,
    (Sym.t, (Sym.t * core_base_type) list * 'a expr) Pmap.map )
  Pmap.map

(* ONLY USED by millicore.ml *)
type 'a m_labeled_continuation =
  core_base_type
  * (Sym.t
    * ((core_base_type * (Ctype.ctype * pass_by_value_or_pointer) option)
      * pexpr))
    list
  * 'a expr
  * Annot.annot list

type 'a m_labeled_continuations =
  (Sym.t, 'a m_labeled_continuation) Pmap.map

val m_collect_saves : 'a expr -> 'a m_labeled_continuations

(* ONLY USED by  ocaml core_peval.ml *)
val in_pattern : Sym.t -> pattern -> bool
val match_pattern : pattern -> value -> (Sym.t * value) list option
