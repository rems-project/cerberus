(* Module Mucore - A more specialized version of Cerberus's Core module

   This is what CN actually uses. Core can pass around C types as values, while CN is more
   restrictive, for simplicity. *)

open Pp
module CF = Cerb_frontend
open Cerb_frontend
open Annot
open Pp_ast
module Loc = Cerb_location
module IT = IndexTerms
module SymSet = Set.Make (Sym)

type loc = Loc.t

type trusted =
  | Trusted of Cerb_location.t
  | Checked

type make_logical_function = Make_Logical_Function of Id.t

module T = struct
  type ct = Sctypes.t

  type bt = BaseTypes.t

  type cbt = Core.core_base_type

  type ft = ArgumentTypes.ft

  type lt = ArgumentTypes.lt

  type rt = ReturnTypes.t

  type st = Memory.struct_layout

  type ut = unit

  (* type mapping = Mapping.t *)
  type logical_arguments = Sym.t * (Sym.t * BaseTypes.t) list

  type resource_predicates = (Sym.t * ResourcePredicates.definition) list

  type logical_predicates = (Sym.t * LogicalFunctions.definition) list
end

type symbol = Symbol.sym

type act =
  { loc : loc;
    annot : Annot.annot list;
    (* type_annot : 'TY; *)
    ct : T.ct
  }

type 'TY object_value_ =
  (* C object values *)
  | OVinteger of Impl_mem.integer_value (* integer value *)
  | OVfloating of Impl_mem.floating_value (* floating-point value *)
  | OVpointer of Impl_mem.pointer_value (* pointer value *)
  | OVarray of 'TY object_value list (* C array value *)
  | OVstruct of
      symbol * (Symbol.identifier * T.ct * Impl_mem.mem_value) list (* C struct value *)
  | OVunion of symbol * Symbol.identifier * Impl_mem.mem_value (* C union value *)

and 'TY object_value = OV of 'TY * 'TY object_value_

(* and 'TY loaded_value =  (\* potentially unspecified C object values *\) *)
(*  | LVspecified of 'TY object_value (\* non-unspecified loaded value *\) *)
and 'TY value_ =
  (* Core values *)
  | Vobject of 'TY object_value (* C object value *)
  (* | Vloaded of 'TY loaded_value (\* loaded C object value *\) *)
  | Vctype of Ctype.ctype
  | Vfunction_addr of Symbol.sym
  | Vunit
  | Vtrue
  | Vfalse
  | Vlist of T.cbt * 'TY value list
  | Vtuple of 'TY value list (* tuple *)

and 'TY value = V of 'TY * 'TY value_

type ctor =
  (* data constructors *)
  | Cnil of T.cbt (* empty list *)
  (* annotated with the type of the list items *)
  | Ccons (* list cons *)
  | Ctuple (* tuple *)
  | Carray (* C array *)

(* | Cspecified (\* non-unspecified loaded value *\) *)
(* | CivCOMPL (\* bitwise complement *\)
 * | CivAND (\* bitwise AND *\)
 * | CivOR (\* bitwise OR *\)
 * | CivXOR (\* bitwise XOR *\)
 * | Cfvfromint (\* cast integer to floating value *\)
 * | Civfromfloat (\* cast floating to integer value *\) *)

type 'TY pattern_ =
  | CaseBase of (Symbol.sym option * T.cbt)
  | CaseCtor of ctor * 'TY pattern list

and 'TY pattern = Pattern of loc * annot list * 'TY * 'TY pattern_

type mu_function =
  (* some functions that persist into mucore, not just (infix) binops *)
  | F_params_length
  | F_params_nth
  | F_are_compatible
  | F_size_of
  | F_align_of
  | F_max_int
  | F_min_int
  | F_ctype_width

type bw_binop =
  | BW_OR
  | BW_AND
  | BW_XOR

type bw_unop =
  | BW_COMPL
  | BW_CTZ
  | BW_FFS

type bound_kind =
  | Bound_Wrap of act
  | Bound_Except of act

let bound_kind_act = function Bound_Wrap act -> act | Bound_Except act -> act

type 'TY pexpr_ =
  (* Core pure expressions *)
  | PEsym of symbol
  (* | PEimpl of Implementation.implementation_constant (\* implementation-defined
     constant *\) *)
  | PEval of 'TY value
  | PEconstrained of (Mem.mem_iv_constraint * 'TY pexpr) list (* constrained value *)
  | PEctor of ctor * 'TY pexpr list (* data constructor application *)
  | PEbitwise_unop of bw_unop * 'TY pexpr
  | PEbitwise_binop of bw_binop * 'TY pexpr * 'TY pexpr
  | Cfvfromint of 'TY pexpr (* cast integer to floating value *)
  | Civfromfloat of act * 'TY pexpr (* cast floating to integer value *)
  | PEarray_shift of 'TY pexpr * T.ct * 'TY pexpr (* pointer array shift *)
  | PEmember_shift of
      'TY pexpr * symbol * Symbol.identifier (* pointer struct/union member shift *)
  | PEnot of 'TY pexpr (* boolean not *)
  | PEop of Core.binop * 'TY pexpr * 'TY pexpr
  | PEapply_fun of mu_function * 'TY pexpr list
  | PEstruct of symbol * (Symbol.identifier * 'TY pexpr) list (* C struct expression *)
  | PEunion of symbol * Symbol.identifier * 'TY pexpr (* C union expression *)
  | PEcfunction of 'TY pexpr
  | PEmemberof of
      symbol * Symbol.identifier * 'TY pexpr (* C struct/union member access *)
  (* | PEassert_undef of 'TY pexpr * Cerb_location.t *
     Undefined.undefined_behaviour *)
  | PEbool_to_integer of 'TY pexpr
  | PEconv_int of 'TY pexpr * 'TY pexpr
  | PEconv_loaded_int of 'TY pexpr * 'TY pexpr
  | PEwrapI of act * 'TY pexpr
  | PEcatch_exceptional_condition of act * 'TY pexpr
  | PEbounded_binop of bound_kind * Core.iop * 'TY pexpr * 'TY pexpr
  | PEis_representable_integer of 'TY pexpr * act
  | PEundef of Cerb_location.t * Undefined.undefined_behaviour (* undefined behaviour *)
  | PEerror of string * 'TY pexpr (* impl-defined static error *)
  (* | PEcase of ('TY pexpr) * (pattern * 'TY tpexpr) list (\* pattern matching
     *\) *)
  | PElet of 'TY pattern * 'TY pexpr * 'TY pexpr (* pure let *)
  | PEif of 'TY pexpr * 'TY pexpr * 'TY pexpr
(* pure if *)

and 'TY pexpr = Pexpr of loc * annot list * 'TY * 'TY pexpr_

let loc_of_pexpr (Pexpr (loc, _, _, _)) = loc

type m_kill_kind =
  | Dynamic
  | Static of T.ct

type 'TY action_ =
  (* memory actions *)
  | Create of 'TY pexpr * act * Symbol.prefix
  | CreateReadOnly of 'TY pexpr * act * 'TY pexpr * Symbol.prefix
  | Alloc of 'TY pexpr * 'TY pexpr * Symbol.prefix
  | Kill of m_kill_kind * 'TY pexpr
    (* the boolean indicates whether the action is dynamic (i.e. free()) *)
  | Store of
      bool
      * act
      * 'TY pexpr
      * 'TY pexpr
      * Cmm_csem.memory_order (* the boolean indicates whether the store is locking *)
  | Load of act * 'TY pexpr * Cmm_csem.memory_order
  | RMW of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cmm_csem.memory_order
      * Cmm_csem.memory_order
  | Fence of Cmm_csem.memory_order
  | CompareExchangeStrong of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cmm_csem.memory_order
      * Cmm_csem.memory_order
  | CompareExchangeWeak of
      act
      * 'TY pexpr
      * 'TY pexpr
      * 'TY pexpr
      * Cmm_csem.memory_order
      * Cmm_csem.memory_order
  | LinuxFence of Linux.linux_memory_order
  | LinuxLoad of act * 'TY pexpr * Linux.linux_memory_order
  | LinuxStore of act * 'TY pexpr * 'TY pexpr * Linux.linux_memory_order
  | LinuxRMW of act * 'TY pexpr * 'TY pexpr * Linux.linux_memory_order

type 'TY action = Action of Cerb_location.t * 'TY action_

type 'TY paction =
  (* memory actions with Core.polarity *)
  | Paction of Core.polarity * 'TY action

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
  | PtrMemberShift of (symbol * Symbol.identifier * 'TY pexpr)
  | Memcpy of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Memcmp of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Realloc of ('TY pexpr * 'TY pexpr * 'TY pexpr)
  | Va_start of ('TY pexpr * 'TY pexpr)
  | Va_copy of 'TY pexpr
  | Va_arg of ('TY pexpr * act)
  | Va_end of 'TY pexpr
  | CopyAllocId of ('TY pexpr * 'TY pexpr)

type 'TY expr_ =
  (* (effectful) expression *)
  | Epure of 'TY pexpr
  | Ememop of 'TY memop
  | Eaction of 'TY paction (* memory action *)
  | Eskip
  | Eccall of act * 'TY pexpr * 'TY pexpr list
  (* C function call *)
  (* | Eproc of name * ('TY pexpr) list (\* Core procedure call *\) *)
  | Elet of 'TY pattern * 'TY pexpr * 'TY expr
  | Eunseq of 'TY expr list (* unsequenced expressions *)
  | Ewseq of 'TY pattern * 'TY expr * 'TY expr (* weak sequencing *)
  | Esseq of 'TY pattern * 'TY expr * 'TY expr (* strong sequencing *)
  (* | Ecase of 'TY pexpr * (pattern * ('TY texpr)) list (\* pattern matching
     *\) *)
  | Eif of 'TY pexpr * 'TY expr * 'TY expr
  | Ebound of 'TY expr (* $\ldots$and boundary *)
  | End of 'TY expr list (* nondeterministic choice *)
  (* | Edone of 'TY expr *)
  | Erun of symbol * 'TY pexpr list (* run from label *)
  | CN_progs of (Sym.t, Ctype.ctype) CF.Cn.cn_statement list * Cnprog.cn_prog list

and 'TY expr = Expr of loc * annot list * 'TY * 'TY expr_

let loc_of_expr (Expr (loc, _, _, _)) = loc

type info = Locations.info

type 'i arguments_l =
  | Define of (Sym.t * IndexTerms.t) * info * 'i arguments_l
  | Resource of (Sym.t * (ResourceTypes.t * BaseTypes.t)) * info * 'i arguments_l
  | Constraint of LogicalConstraints.t * info * 'i arguments_l
  | I of 'i

let dtree_of_arguments_l dtree_i =
  let rec aux = function
    | Define ((s, it), _, t) ->
      Dnode (pp_ctor "Define", [ Dleaf (Sym.pp s); IT.dtree it; aux t ])
    | Resource ((s, (rt, bt)), _, t) ->
      Dnode
        ( pp_ctor "Resource",
          [ Dleaf (Sym.pp s); ResourceTypes.dtree rt; Dleaf (BaseTypes.pp bt); aux t ] )
    | Constraint (lc, _, t) ->
      Dnode (pp_ctor "Constraint", [ LogicalConstraints.dtree lc; aux t ])
    | I i -> Dnode (pp_ctor "I", [ dtree_i i ])
  in
  aux


type 'i arguments =
  | Computational of (Sym.t * T.bt) * info * 'i arguments
  | L of 'i arguments_l

let dtree_of_arguments dtree_i =
  let rec aux = function
    | Computational ((s, _bt), _, lat) ->
      Dnode (pp_ctor "Computational", [ Dleaf (Sym.pp s); aux lat ])
    | L l -> dtree_of_arguments_l dtree_i l
  in
  aux


let rec count_computational = function
  | Computational (_, _, args) -> count_computational args + 1
  | L _ -> 0


let mDefine (bound, info) t = Define (bound, info, t)

let mResource (bound, info) t = Resource (bound, info, t)

let mConstraint (lc, info) t = Constraint (lc, info, t)

let mComputational (bound, info) t = Computational (bound, info, t)

let mConstraints lcs t = List.fold_right mConstraint lcs t

let mResources res t = List.fold_right mResource res t

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


let is_ctype_const pe =
  let (Pexpr (_loc, _, _, pe_)) = pe in
  match pe_ with PEval (V (_, Vctype ct)) -> Some ct | _ -> None


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


let pp_function = function
  | F_params_length -> !^"params_length"
  | F_params_nth -> !^"params_nth"
  | F_are_compatible -> !^"are_compatible"
  | F_align_of -> !^"align_of"
  | F_size_of -> !^"size_of"
  | F_max_int -> !^"max_int"
  | F_min_int -> !^"min_int"
  | F_ctype_width -> !^"ctype_width"


let is_undef_or_error_pexpr pexpr =
  let (Pexpr (_, _, _, pe)) = pexpr in
  match pe with PEundef _ | PEerror _ -> true | _ -> false


let is_undef_or_error_expr expr =
  let (Expr (_, _, _, e)) = expr in
  match e with Epure pe -> is_undef_or_error_pexpr pe | _ -> false


let bt_of_value (V (bty, _)) = bty

let bt_of_object_value (OV (bty, _)) = bty

let bt_of_pattern (Pattern (_, _, bty, _)) = bty

let loc_of_pattern (Pattern (loc, _, _, _)) = loc

let bt_of_expr : 'TY. 'TY expr -> 'TY = fun (Expr (_loc, _annots, bty, _e)) -> bty

let bt_of_pexpr : 'TY. 'TY pexpr -> 'TY = fun (Pexpr (_loc, _annots, bty, _e)) -> bty

let evaluate_fun mu_fun args =
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


type parse_ast_label_spec = { label_spec : (Sym.t, Ctype.ctype) CF.Cn.cn_condition list }

type 'TY label_def =
  | Return of loc
  | Label of
      loc
      * 'TY expr arguments
      * annot list
      * (* for generating runtime assertions *)
        parse_ast_label_spec

let dtree_of_label_def = function
  | Return _ -> Dleaf !^"return label"
  | Label (_, args_and_body, _, _) ->
    dtree_of_arguments (fun _body -> Dleaf !^"(body)") args_and_body


type 'TY label_defs = (symbol, 'TY label_def) Pmap.map

type 'TY proc_args_and_body = ('TY expr * 'TY label_defs * T.rt) arguments

(* let dtree_of_args_and_body a =  *)
(*   dtree_of_arguments (fun (_body, labels, rt) -> *)
(*       Dnode ("FunctionBodyLabelsReturn" [ *)
(*                  Dleaf !^"(body)"; *)
(*                  Dnode (pp_ctor "labels" *)
(*         ]) *)
(*     ) a *)

type parse_ast_function_specification =
  { accesses : (Sym.t * Ctype.ctype) list;
    requires : (Sym.t, Ctype.ctype) CF.Cn.cn_condition list;
    ensures : (Sym.t, Ctype.ctype) CF.Cn.cn_condition list
  }

type 'TY fun_map_decl =
  (* | Fun of T.bt * (symbol * T.bt) list * 'TY pexpr *)
  | Proc of
      Cerb_location.t
      * 'TY proc_args_and_body
      * trusted
      * parse_ast_function_specification
    (* recording the desugared parse ast, for generating runtime checks *)
  | ProcDecl of Cerb_location.t * T.ft option
(* | BuiltinDecl of Cerb_location.t * T.bt * T.bt list *)

type 'TY fun_map = (symbol, 'TY fun_map_decl) Pmap.map

type extern_map = Core.extern_map

type 'TY globs =
  | GlobalDef of T.ct * 'TY expr
  | GlobalDecl of T.ct

type 'TY globs_map = (symbol, 'TY globs) Pmap.map

type tag_definition =
  | StructDef of T.st
  | UnionDef of T.ut

type tag_definitions = (Symbol.sym, tag_definition) Pmap.map

type 'TY globs_list = (symbol * 'TY globs) list

type datatype =
  { loc : Loc.t;
    cases : (Sym.t * (Id.t * T.bt) list) list
  }

type function_to_convert =
  { loc : Loc.t;
    c_fun_sym : Sym.t;
    l_fun_sym : Sym.t
  }

type 'TY file =
  { main : symbol option;
    tagDefs : tag_definitions;
    globs : 'TY globs_list;
    funs : 'TY fun_map;
    extern : extern_map;
    stdlib_syms : SymSet.t;
    mk_functions : function_to_convert list;
    resource_predicates : T.resource_predicates;
    logical_predicates : T.logical_predicates;
    datatypes : (Sym.t * datatype) list;
    lemmata : (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list;
    call_funinfo : (symbol, Sctypes.c_concrete_sig) Pmap.map
  }
