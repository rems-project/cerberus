type act =
  { loc : Locations.t;
    annot : Cerb_frontend.Annot.annot list;
    ct : Sctypes.t
  }

type 'TY object_value_ =
  | OVinteger of Cerb_frontend.Impl_mem.integer_value
  | OVfloating of Cerb_frontend.Impl_mem.floating_value
  | OVpointer of Cerb_frontend.Impl_mem.pointer_value
  | OVarray of 'TY object_value list
  | OVstruct of Sym.t * (Id.t * Sctypes.t * Cerb_frontend.Impl_mem.mem_value) list
  | OVunion of Sym.t * Id.t * Cerb_frontend.Impl_mem.mem_value

and 'TY object_value = OV of 'TY * 'TY object_value_

and 'TY value_ =
  | Vobject of 'TY object_value
  | Vctype of Cerb_frontend.Ctype.ctype
  | Vfunction_addr of Sym.t
  | Vunit
  | Vtrue
  | Vfalse
  | Vlist of Cerb_frontend.Core.core_base_type * 'TY value list
  | Vtuple of 'TY value list

and 'TY value = V of 'TY * 'TY value_

let bt_of_value (V (bty, _)) = bty

let bt_of_object_value (OV (bty, _)) = bty

type ctor =
  | Cnil of Cerb_frontend.Core.core_base_type
  | Ccons
  | Ctuple
  | Carray

type 'TY pattern_ =
  | CaseBase of (Sym.t option * Cerb_frontend.Core.core_base_type)
  | CaseCtor of ctor * 'TY pattern list

and 'TY pattern =
  | Pattern of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY pattern_

let bt_of_pattern (Pattern (_, _, bty, _)) = bty

let loc_of_pattern (Pattern (loc, _, _, _)) = loc

type mu_function =
  | F_params_length
  | F_params_nth
  | F_are_compatible
  | F_size_of
  | F_align_of
  | F_max_int
  | F_min_int
  | F_ctype_width

let pp_function =
  let open Pp.Infix in
  function
  | F_params_length -> !^"params_length"
  | F_params_nth -> !^"params_nth"
  | F_are_compatible -> !^"are_compatible"
  | F_align_of -> !^"align_of"
  | F_size_of -> !^"size_of"
  | F_max_int -> !^"max_int"
  | F_min_int -> !^"min_int"
  | F_ctype_width -> !^"ctype_width"


let fun_param_types mu_fun =
  let open BaseTypes in
  let short_int = Bits (Signed, 32) in
  match mu_fun with
  | F_params_length -> [ List CType ]
  | F_params_nth -> [ List CType; short_int ]
  | F_are_compatible -> [ CType; CType ]
  | F_align_of -> [ CType ]
  | F_size_of -> [ CType ]
  | F_max_int -> [ CType ]
  | F_min_int -> [ CType ]
  | F_ctype_width -> [ CType ]


let evaluate_fun mu_fun args =
  let module IT = IndexTerms in
  let here = Locations.other __FUNCTION__ in
  match mu_fun with
  | F_params_length ->
    (match args with
     | [ arg ] ->
       Option.bind (IT.dest_list arg) (fun xs ->
         Some (`Result_Integer (Z.of_int (List.length xs))))
     | _ -> None)
  | F_params_nth ->
    (match args with
     | [ arg1; arg2 ] ->
       Option.bind (IT.dest_list arg1) (fun xs ->
         Option.bind (IT.is_bits_const arg2) (fun (bits_info, i) ->
           assert (BaseTypes.fits_range bits_info i);
           if Z.lt i (Z.of_int (List.length xs)) && Z.leq Z.zero i then
             Option.bind (List.nth_opt xs (Z.to_int i)) (fun it -> Some (`Result_IT it))
           else
             None))
     | _ -> None)
  | F_are_compatible ->
    (match List.map IT.is_const args with
     | [ Some (IT.CType_const ct1, _); Some (IT.CType_const ct2, _) ] ->
       if Sctypes.equal ct1 ct2 then
         Some (`Result_IT (IT.bool_ true here))
       else
         None
     | _ -> None)
  | F_size_of ->
    (match List.map IT.is_const args with
     | [ Some (IT.CType_const ct, _) ] ->
       Some (`Result_Integer (Z.of_int (Memory.size_of_ctype ct)))
     | _ -> None)
  | F_align_of ->
    (match List.map IT.is_const args with
     | [ Some (IT.CType_const ct, _) ] ->
       Some (`Result_Integer (Z.of_int (Memory.align_of_ctype ct)))
     | _ -> None)
  | F_max_int ->
    (match List.map IT.is_const args with
     | [ Some (IT.CType_const (Sctypes.Integer ity), _) ] ->
       let bt = Memory.bt_of_sct (Sctypes.Integer ity) in
       Some (`Result_IT (IT.num_lit_ (Memory.max_integer_type ity) bt here))
     | _ -> None)
  | F_min_int ->
    (match List.map IT.is_const args with
     | [ Some (IT.CType_const (Sctypes.Integer ity), _) ] ->
       let bt = Memory.bt_of_sct (Sctypes.Integer ity) in
       Some (`Result_IT (IT.num_lit_ (Memory.min_integer_type ity) bt here))
     | _ -> None)
  | F_ctype_width ->
    (match List.map IT.is_const args with
     | [ Some (IT.CType_const ct, _) ] ->
       Some (`Result_Integer (Z.of_int (Memory.size_of_ctype ct * 8)))
     | _ -> None)


type bw_binop =
  | BW_OR
  | BW_AND
  | BW_XOR

type bw_unop =
  | BW_COMPL
  | BW_CTZ
  | BW_FFS

(** What to do on out of bounds.
    The annotated C type is the result type of the operation. *)
type bound_kind =
  | Bound_Wrap of act (** Wrap around (used for unsigned types) *)
  | Bound_Except of act (** Report an exception, for signed types *)

let bound_kind_act = function Bound_Wrap act -> act | Bound_Except act -> act

type 'TY pexpr_ =
  | PEsym of Sym.t
  | PEval of 'TY value
  | PEconstrained of (Cerb_frontend.Mem.mem_iv_constraint * 'TY pexpr) list
  | PEctor of ctor * 'TY pexpr list
  | PEbitwise_unop of bw_unop * 'TY pexpr
  | PEbitwise_binop of bw_binop * 'TY pexpr * 'TY pexpr
  | Cfvfromint of 'TY pexpr
  | Civfromfloat of act * 'TY pexpr
  | PEarray_shift of 'TY pexpr * Sctypes.t * 'TY pexpr
  | PEmember_shift of 'TY pexpr * Sym.t * Id.t
  | PEnot of 'TY pexpr
  | PEop of Cerb_frontend.Core.binop * 'TY pexpr * 'TY pexpr
  | PEapply_fun of mu_function * 'TY pexpr list
  | PEstruct of Sym.t * (Id.t * 'TY pexpr) list
  | PEunion of Sym.t * Id.t * 'TY pexpr
  | PEcfunction of 'TY pexpr
  | PEmemberof of Sym.t * Id.t * 'TY pexpr
  | PEbool_to_integer of 'TY pexpr
  | PEconv_int of 'TY pexpr * 'TY pexpr
  | PEconv_loaded_int of 'TY pexpr * 'TY pexpr
  | PEwrapI of act * 'TY pexpr
  | PEcatch_exceptional_condition of act * 'TY pexpr
  | PEbounded_binop of bound_kind * Cerb_frontend.Core.iop * 'TY pexpr * 'TY pexpr
  | PEis_representable_integer of 'TY pexpr * act
  | PEundef of Locations.t * Cerb_frontend.Undefined.undefined_behaviour
  | PEerror of string * 'TY pexpr
  | PElet of 'TY pattern * 'TY pexpr * 'TY pexpr
  | PEif of 'TY pexpr * 'TY pexpr * 'TY pexpr

and 'TY pexpr = Pexpr of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY pexpr_

let loc_of_pexpr (Pexpr (loc, _, _, _)) = loc

let bt_of_pexpr : 'TY. 'TY pexpr -> 'TY = fun (Pexpr (_loc, _annots, bty, _e)) -> bty

let is_undef_or_error_pexpr (Pexpr (_, _, _, pe)) =
  match pe with PEundef _ | PEerror _ -> true | _ -> false


let is_ctype_const (Pexpr (_loc, _, _, pe)) =
  match pe with PEval (V (_, Vctype ct)) -> Some ct | _ -> None


let fun_return_type mu_fun args =
  let open BaseTypes in
  match (mu_fun, args) with
  | F_params_length, _ -> Some (`Returns_BT (Memory.bt_of_sct (Integer (Unsigned Short))))
  | F_params_nth, _ -> Some (`Returns_BT CType)
  | F_are_compatible, _ -> Some (`Returns_BT Bool)
  | F_align_of, _ -> Some `Returns_Integer
  | F_size_of, _ -> Some (`Returns_BT Memory.size_bt) (* TODO: Is that good? *)
  | F_max_int, [ ct ] ->
    Option.bind (is_ctype_const ct) Sctypes.of_ctype
    |> Option.map (fun sct -> `Returns_BT (Memory.bt_of_sct sct))
  | F_max_int, _ -> None
  | F_min_int, [ ct ] ->
    Option.bind (is_ctype_const ct) Sctypes.of_ctype
    |> Option.map (fun sct -> `Returns_BT (Memory.bt_of_sct sct))
  | F_min_int, _ -> None
  | F_ctype_width, _ -> Some `Returns_Integer


type m_kill_kind =
  | Dynamic
  | Static of Sctypes.t

type 'TY action_ =
  | Create of 'TY pexpr * act * Cerb_frontend.Symbol.prefix
  | CreateReadOnly of 'TY pexpr * act * 'TY pexpr * Cerb_frontend.Symbol.prefix
  | Alloc of 'TY pexpr * 'TY pexpr * Cerb_frontend.Symbol.prefix
  | Kill of m_kill_kind * 'TY pexpr
  | Store of bool * act * 'TY pexpr * 'TY pexpr * Cerb_frontend.Cmm_csem.memory_order
  | Load of act * 'TY pexpr * Cerb_frontend.Cmm_csem.memory_order
  | RMW of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | Fence of Cerb_frontend.Cmm_csem.memory_order
  | CompareExchangeStrong of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | CompareExchangeWeak of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cerb_frontend.Cmm_csem.memory_order
      * Cerb_frontend.Cmm_csem.memory_order
  | LinuxFence of Cerb_frontend.Linux.linux_memory_order
  | LinuxLoad of act * 'TY pexpr * Cerb_frontend.Linux.linux_memory_order
  | LinuxStore of act * 'TY pexpr * 'TY pexpr * Cerb_frontend.Linux.linux_memory_order
  | LinuxRMW of act * 'TY pexpr * 'TY pexpr * Cerb_frontend.Linux.linux_memory_order

type 'TY action = Action of Locations.t * 'TY action_

type 'TY paction = Paction of Cerb_frontend.Core.polarity * 'TY action

type 'TY memop =
  | PtrEq of ('TY pexpr * 'TY pexpr)
  | PtrNe of ('TY pexpr * 'TY pexpr)
  | PtrLt of ('TY pexpr * 'TY pexpr)
  | PtrGt of ('TY pexpr * 'TY pexpr)
  | PtrLe of ('TY pexpr * 'TY pexpr)
  | PtrGe of ('TY pexpr * 'TY pexpr)
  | Ptrdiff of (act * 'TY pexpr * 'TY pexpr)
  | IntFromPtr of (act * act * 'TY pexpr)
  | PtrFromInt of (act * act * 'TY pexpr)
  | PtrValidForDeref of (act * 'TY pexpr)
  | PtrWellAligned of (act * 'TY pexpr)
  | PtrArrayShift of ('TY pexpr * act * 'TY pexpr)
  | PtrMemberShift of (Sym.t * Id.t * 'TY pexpr)
  | Memcpy of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Memcmp of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Realloc of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Va_start of ('TY pexpr * 'TY pexpr)
  | Va_copy of 'TY pexpr
  | Va_arg of ('TY pexpr * act)
  | Va_end of 'TY pexpr
  | CopyAllocId of ('TY pexpr * 'TY pexpr)

type 'TY expr_ =
  | Epure of 'TY pexpr
  | Ememop of 'TY memop
  | Eaction of 'TY paction
  | Eskip
  | Eccall of act * 'TY pexpr * 'TY pexpr list
  | Elet of 'TY pattern * 'TY pexpr * 'TY expr
  | Eunseq of 'TY expr list
  | Ewseq of 'TY pattern * 'TY expr * 'TY expr
  | Esseq of 'TY pattern * 'TY expr * 'TY expr
  | Eif of 'TY pexpr * 'TY expr * 'TY expr
  | Ebound of 'TY expr
  | End of 'TY expr list
  | Erun of Sym.t * 'TY pexpr list
  | CN_progs of
      (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_statement list
      * Cnprog.t list

and 'TY expr = Expr of Locations.t * Cerb_frontend.Annot.annot list * 'TY * 'TY expr_

let is_undef_or_error_expr (Expr (_, _, _, e)) =
  match e with Epure pe -> is_undef_or_error_pexpr pe | _ -> false


let bt_of_expr : 'TY. 'TY expr -> 'TY = fun (Expr (_loc, _annots, bty, _e)) -> bty

let loc_of_expr (Expr (loc, _, _, _)) = loc

type 'TY globs =
  | GlobalDef of Sctypes.t * 'TY expr
  | GlobalDecl of Sctypes.t

type 'i arguments_l =
  | Define of (Sym.t * IndexTerms.t) * Locations.info * 'i arguments_l
  | Resource of (Sym.t * (Request.t * BaseTypes.t)) * Locations.info * 'i arguments_l
  | Constraint of LogicalConstraints.t * Locations.info * 'i arguments_l
  | I of 'i

let mDefine (bound, info) t = Define (bound, info, t)

let mResource (bound, info) t = Resource (bound, info, t)

let mConstraint (lc, info) t = Constraint (lc, info, t)

let mConstraints lcs t = List.fold_right mConstraint lcs t

let mResources res t = List.fold_right mResource res t

type 'i arguments =
  | Computational of (Sym.t * BaseTypes.t) * Locations.info * 'i arguments
  | L of 'i arguments_l

let mComputational (bound, info) t = Computational (bound, info, t)

let dtree_of_arguments_l dtree_i =
  let module IT = IndexTerms in
  let open Cerb_frontend.Pp_ast in
  let rec aux = function
    | Define ((s, it), _, t) ->
      Dnode (pp_ctor "Define", [ Dleaf (Sym.pp s); IT.dtree it; aux t ])
    | Resource ((s, (rt, bt)), _, t) ->
      Dnode
        ( pp_ctor "Resource",
          [ Dleaf (Sym.pp s); Request.dtree rt; Dleaf (BaseTypes.pp bt); aux t ] )
    | Constraint (lc, _, t) ->
      Dnode (pp_ctor "Constraint", [ LogicalConstraints.dtree lc; aux t ])
    | I i -> Dnode (pp_ctor "I", [ dtree_i i ])
  in
  aux


let dtree_of_arguments dtree_i =
  let open Cerb_frontend.Pp_ast in
  let rec aux = function
    | Computational ((s, _bt), _, lat) ->
      Dnode (pp_ctor "Computational", [ Dleaf (Sym.pp s); aux lat ])
    | L l -> dtree_of_arguments_l dtree_i l
  in
  aux


type parse_ast_label_spec =
  { label_spec : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list }

type 'TY label_def =
  | Return of Locations.t
  | Label of
      Locations.t
      * 'TY expr arguments
      * Cerb_frontend.Annot.annot list
      * parse_ast_label_spec
      * [ `Loop of Locations.t * Locations.t ]
(*first loc is condition, second is whole loop*)
(*loop condition location, for executable checking *)

type trusted =
  | Trusted of Locations.t
  | Checked

type desugared_spec =
  { accesses : (Sym.t * Cerb_frontend.Ctype.ctype) list;
    requires : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list;
    ensures : (Sym.t, Cerb_frontend.Ctype.ctype) Cerb_frontend.Cn.cn_condition list
  }

type 'TY args_and_body =
  ('TY expr * (Sym.t, 'TY label_def) Pmap.map * ReturnTypes.t) arguments

type 'TY fun_map_decl =
  | Proc of
      { loc : Locations.t;
        args_and_body : 'TY args_and_body;
        trusted : trusted;
        desugared_spec : desugared_spec
      }
  | ProcDecl of Locations.t * ArgumentTypes.ft option

type tag_definition =
  | StructDef of Memory.struct_layout
  | UnionDef

type function_to_convert =
  { loc : Locations.t;
    c_fun_sym : Sym.t;
    l_fun_sym : Sym.t
  }

type datatype =
  { loc : Locations.t;
    cases : (Sym.t * (Id.t * BaseTypes.t) list) list
  }

type 'TY file =
  { main : Sym.t option;
    tagDefs : (Sym.t, tag_definition) Pmap.map;
    globs : (Sym.t * 'TY globs) list;
    funs : (Sym.t, 'TY fun_map_decl) Pmap.map;
    extern : Cerb_frontend.Core.extern_map;
    stdlib_syms : Sym.Set.t;
    mk_functions : function_to_convert list;
    resource_predicates : (Sym.t * ResourcePredicates.Definition.t) list;
    logical_predicates : (Sym.t * LogicalFunctions.definition) list;
    datatypes : (Sym.t * datatype) list;
    lemmata : (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list;
    call_funinfo : (Sym.t, Sctypes.c_concrete_sig) Pmap.map
  }

let empty_file : 'TY file =
  { main = None;
    tagDefs = Pmap.empty Sym.compare;
    globs = [];
    funs = Pmap.empty Sym.compare;
    extern = Pmap.empty Id.compare;
    stdlib_syms = Sym.Set.empty;
    mk_functions = [];
    resource_predicates = [];
    logical_predicates = [];
    datatypes = [];
    lemmata = [];
    call_funinfo = Pmap.empty Sym.compare
  }
