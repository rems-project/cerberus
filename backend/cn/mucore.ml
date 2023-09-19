open Pp
module CF=Cerb_frontend
open Cerb_frontend
open Annot
open Pp_ast

module Loc = Cerb_location
module IT = IndexTerms
module SymSet = Set.Make(Sym)
type loc = Loc.t




type trusted = 
  | Trusted of Cerb_location.t
  | Checked

type make_logical_function =
  | Make_Logical_Function of Id.t



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
  type logical_arguments = (Sym.t * (Sym.t * BaseTypes.t) list)
  type resource_predicates = (Sym.t * ResourcePredicates.definition) list
  type logical_predicates = (Sym.t * LogicalFunctions.definition) list
end



type symbol = Symbol.sym

type 'TY act = { 
    loc: loc;
    annot: Annot.annot list;
    (* type_annot : 'TY; *)
    ct: T.ct
  }





type 'TY mu_object_value =  (* C object values *)
 | M_OVinteger of Impl_mem.integer_value (* integer value *)
 | M_OVfloating of Impl_mem.floating_value (* floating-point value *)
 | M_OVpointer of Impl_mem.pointer_value (* pointer value *)
 | M_OVarray of ('TY mu_object_value) list (* C array value *)
 | M_OVstruct of symbol * (Symbol.identifier * T.ct * Impl_mem.mem_value) list (* C struct value *)
 | M_OVunion of symbol * Symbol.identifier * Impl_mem.mem_value (* C union value *)


(* and 'TY mu_loaded_value =  (\* potentially unspecified C object values *\) *)
(*  | M_LVspecified of 'TY mu_object_value (\* non-unspecified loaded value *\) *)

and 'TY mu_value =  (* Core values *)
 | M_Vobject of 'TY mu_object_value (* C object value *)
 (* | M_Vloaded of 'TY mu_loaded_value (\* loaded C object value *\) *)
 | M_Vctype of Ctype.ctype
 | M_Vfunction_addr of Symbol.sym
 | M_Vunit
 | M_Vtrue
 | M_Vfalse
 | M_Vlist of T.cbt * ('TY mu_value) list
 | M_Vtuple of ('TY mu_value) list (* tuple *)



type mu_ctor =  (* data constructors *)
 | M_Cnil of T.cbt (* empty list *)
 (* annotated with the type of the list items *)
 | M_Ccons (* list cons *)
 | M_Ctuple (* tuple *)
 | M_Carray (* C array *)
 (* | M_Cspecified (\* non-unspecified loaded value *\) *)
 (* | M_CivCOMPL (\* bitwise complement *\)
  * | M_CivAND (\* bitwise AND *\)
  * | M_CivOR (\* bitwise OR *\)
  * | M_CivXOR (\* bitwise XOR *\)
  * | M_Cfvfromint (\* cast integer to floating value *\)
  * | M_Civfromfloat (\* cast floating to integer value *\) *)

type mu_pattern_ = 
 | M_CaseBase of (Symbol.sym option * T.cbt)
 | M_CaseCtor of mu_ctor * mu_pattern list

and mu_pattern = 
 | M_Pattern of loc * annot list * mu_pattern_

type mu_function = (* some functions that persist into mucore, not just (infix) binops *)
 | M_F_params_length
 | M_F_params_nth
 | M_F_are_compatible
 | M_F_size_of
 | M_F_align_of
 | M_F_max_int
 | M_F_min_int
 | M_F_ctype_width

type bw_binop =
 | M_BW_OR
 | M_BW_AND
 | M_BW_XOR

type bw_unop =
 | M_BW_COMPL
 | M_BW_CTZ
 | M_BW_FFS

type 'TY bound_kind =
 | M_Bound_Wrap of 'TY act
 | M_Bound_Except of 'TY act

type 'TY mu_pexpr_ =  (* Core pure expressions *)
 | M_PEsym of symbol
 (* | M_PEimpl of Implementation.implementation_constant (\* implementation-defined constant *\) *)
 | M_PEval of 'TY mu_value
 | M_PEconstrained of (Mem.mem_iv_constraint * 'TY mu_pexpr) list (* constrained value *)
 | M_PEctor of mu_ctor * ('TY mu_pexpr) list (* data constructor application *)
 | M_PEbitwise_unop of bw_unop * 'TY mu_pexpr
 | M_PEbitwise_binop of bw_binop * 'TY mu_pexpr * 'TY mu_pexpr
 | M_Cfvfromint of 'TY mu_pexpr (* cast integer to floating value *)
 | M_Civfromfloat of 'TY act * 'TY mu_pexpr (* cast floating to integer value *)
 | M_PEarray_shift of ('TY mu_pexpr) * T.ct * ('TY mu_pexpr) (* pointer array shift *)
 | M_PEmember_shift of ('TY mu_pexpr) * symbol * Symbol.identifier (* pointer struct/union member shift *)
 | M_PEnot of 'TY mu_pexpr (* boolean not *)
 | M_PEop of Core.binop * ('TY mu_pexpr) * ('TY mu_pexpr)
 | M_PEapply_fun of mu_function * ('TY mu_pexpr) list
 | M_PEstruct of symbol * (Symbol.identifier * 'TY mu_pexpr) list (* C struct expression *)
 | M_PEunion of symbol * Symbol.identifier * 'TY mu_pexpr (* C union expression *)
 | M_PEcfunction of 'TY mu_pexpr
 | M_PEmemberof of symbol * Symbol.identifier * 'TY mu_pexpr (* C struct/union member access *)

 (* | M_PEassert_undef of 'TY mu_pexpr * Cerb_location.t * Undefined.undefined_behaviour *)
 | M_PEbool_to_integer of 'TY mu_pexpr
 | M_PEconv_int of 'TY mu_pexpr * 'TY mu_pexpr
 | M_PEconv_loaded_int of 'TY mu_pexpr * 'TY mu_pexpr
 | M_PEwrapI of 'TY act * 'TY mu_pexpr
 | M_PEcatch_exceptional_condition of 'TY act * 'TY mu_pexpr
 | M_PEbounded_binop of 'TY bound_kind * Core.iop * 'TY mu_pexpr * 'TY mu_pexpr
 | M_PEis_representable_integer of 'TY mu_pexpr * 'TY act

 | M_PEundef of Cerb_location.t * Undefined.undefined_behaviour (* undefined behaviour *)
 | M_PEerror of string * 'TY mu_pexpr (* impl-defined static error *)
 (* | M_PEcase of ('TY mu_pexpr) * (mu_pattern * 'TY mu_tpexpr) list (\* pattern matching *\) *)
 | M_PElet of (mu_pattern) * ('TY mu_pexpr) * ('TY mu_pexpr) (* pure let *)
 | M_PEif of 'TY mu_pexpr * ('TY mu_pexpr) * ('TY mu_pexpr) (* pure if *)



and 'TY mu_pexpr = 
 | M_Pexpr of loc * annot list * 'TY * ('TY mu_pexpr_)

let loc_of_pexpr (M_Pexpr (loc, _, _, _)) = loc



type m_kill_kind = 
  | M_Dynamic
  | M_Static of T.ct

type 'TY mu_action_ =  (* memory actions *)
 | M_Create of 'TY mu_pexpr * ('TY act) * Symbol.prefix
 | M_CreateReadOnly of 'TY mu_pexpr * 'TY act * 'TY mu_pexpr * Symbol.prefix
 | M_Alloc of 'TY mu_pexpr * 'TY mu_pexpr * Symbol.prefix
 | M_Kill of m_kill_kind * 'TY mu_pexpr (* the boolean indicates whether the action is dynamic (i.e. free()) *)
 | M_Store of bool * 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order (* the boolean indicates whether the store is locking *)
 | M_Load of 'TY act * 'TY mu_pexpr * Cmm_csem.memory_order
 | M_RMW of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_Fence of Cmm_csem.memory_order
 | M_CompareExchangeStrong of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_CompareExchangeWeak of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr * Cmm_csem.memory_order * Cmm_csem.memory_order
 | M_LinuxFence of Linux.linux_memory_order
 | M_LinuxLoad of 'TY act * 'TY mu_pexpr * Linux.linux_memory_order
 | M_LinuxStore of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * Linux.linux_memory_order
 | M_LinuxRMW of 'TY act * 'TY mu_pexpr * 'TY mu_pexpr * Linux.linux_memory_order


type 'TY mu_action = 
 | M_Action of Cerb_location.t * ('TY mu_action_)


type 'TY mu_paction =  (* memory actions with Core.polarity *)
 | M_Paction of Core.polarity * ('TY mu_action)

type 'TY mu_memop =
  | M_PtrEq of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrNe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrLt of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrGt of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrLe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_PtrGe of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_Ptrdiff of ('TY act * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_IntFromPtr of ('TY act * 'TY act * 'TY mu_pexpr)
  | M_PtrFromInt of ('TY act * 'TY act * 'TY mu_pexpr)
  | M_PtrValidForDeref of ('TY act * 'TY mu_pexpr)
  | M_PtrWellAligned of ('TY act * 'TY mu_pexpr)
  | M_PtrArrayShift of ('TY mu_pexpr * 'TY act * 'TY mu_pexpr)
  | M_PtrMemberShift of (symbol * Symbol.identifier * 'TY mu_pexpr)
  | M_Memcpy of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Memcmp of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Realloc of ('TY mu_pexpr * 'TY mu_pexpr * 'TY mu_pexpr)
  | M_Va_start  of ('TY mu_pexpr * 'TY mu_pexpr)
  | M_Va_copy of ('TY mu_pexpr)
  | M_Va_arg of ('TY mu_pexpr * 'TY act)
  | M_Va_end of ('TY mu_pexpr)
  | M_CopyAllocId of ('TY mu_pexpr * 'TY mu_pexpr)









type 'TY mu_expr_ =  (* (effectful) expression *)
 | M_Epure of ('TY mu_pexpr)
 | M_Ememop of 'TY mu_memop
 | M_Eaction of ('TY mu_paction) (* memory action *)
 | M_Eskip
 | M_Eccall of 'TY act * 'TY mu_pexpr * ('TY mu_pexpr) list (* C function call *)
 (* | M_Eproc of mu_name * ('TY mu_pexpr) list (\* Core procedure call *\) *)

 | M_Elet of (mu_pattern) * ('TY mu_pexpr) * ('TY mu_expr)
 | M_Eunseq of ('TY mu_expr) list (* unsequenced expressions *)
 | M_Ewseq of mu_pattern * ('TY mu_expr) * ('TY mu_expr) (* weak sequencing *)
 | M_Esseq of mu_pattern * ('TY mu_expr) * ('TY mu_expr) (* strong sequencing *)
 (* | M_Ecase of 'TY mu_pexpr * (mu_pattern * ('TY mu_texpr)) list (\* pattern matching *\) *)
 | M_Eif of 'TY mu_pexpr * ('TY mu_expr) * ('TY mu_expr)
 | M_Ebound of ('TY mu_expr) (* $\ldots$and boundary *)
 | M_End of ('TY mu_expr) list (* nondeterministic choice *)
 (* | M_Edone of 'TY mu_expr *)
 | M_Erun of symbol * ('TY mu_pexpr) list (* run from label *)

 | M_CN_progs of ((Sym.t, Ctype.ctype) Cn.cn_statement) list * Cnprog.cn_prog list


and 'TY mu_expr = 
 | M_Expr of loc * annot list * ('TY mu_expr_)

let loc_of_expr (M_Expr (loc, _, _)) = loc



let embed_pexpr_expr pe : 'TY mu_expr= 
  let (M_Pexpr (loc, _, _, _)) = pe in
  M_Expr (loc, [], (M_Epure pe))


type info = Locations.info

type 'i mu_arguments_l = 
  | M_Define of (Sym.t * IndexTerms.t) * info * 'i mu_arguments_l
  | M_Resource of (Sym.t * (ResourceTypes.t * BaseTypes.t)) * info * 'i mu_arguments_l
  | M_Constraint of LogicalConstraints.t * info * 'i mu_arguments_l
  | M_I of 'i

let dtree_of_mu_arguments_l dtree_i = 
  let rec aux = function
  | M_Define ((s, it), _, t) ->
     Dnode (pp_ctor "Define", [Dleaf (Sym.pp s); IT.dtree it; aux t])
  | M_Resource ((s, (rt, bt)), _, t) ->
     Dnode (pp_ctor "Resource", [Dleaf (Sym.pp s); ResourceTypes.dtree rt; Dleaf (BaseTypes.pp bt); aux t])
  | M_Constraint (lc, _, t) ->
     Dnode (pp_ctor "Constraint", [LogicalConstraints.dtree lc; aux t])
  | M_I i ->
     Dnode (pp_ctor "I", [dtree_i i])
  in
  aux


type 'i mu_arguments = 
  | M_Computational of (Sym.t * T.bt) * info * 'i mu_arguments
  | M_L of 'i mu_arguments_l


let dtree_of_mu_arguments dtree_i = 
  let rec aux = function
  | M_Computational ((s, bt), _, lat) ->
     Dnode (pp_ctor "Computational", [Dleaf (Sym.pp s); aux lat])
  | M_L l -> 
     dtree_of_mu_arguments_l dtree_i l
  in
  aux





let rec mu_count_computational = function
  | M_Computational (_, _, args) -> mu_count_computational args + 1
  | M_L _ -> 0

let mDefine (bound, info) t = M_Define (bound, info, t)
let mResource (bound, info) t = M_Resource (bound, info, t)
let mConstraint (lc, info) t = M_Constraint (lc, info, t)
let mComputational (bound, info) t = M_Computational (bound, info, t)

let mConstraints lcs t = List.fold_right mConstraint lcs t
let mResources res t = List.fold_right mResource res t

let mu_fun_param_types mu_fun =
  let open BaseTypes in
  match mu_fun with
  | M_F_params_length -> [List CType]
  | M_F_params_nth -> [List CType; Integer]
  | M_F_are_compatible -> [CType; CType]
  | M_F_align_of -> [CType]
  | M_F_size_of -> [CType]
  | M_F_max_int -> [CType]
  | M_F_min_int -> [CType]
  | M_F_ctype_width -> [CType]

let pp_function = function
  | M_F_params_length -> !^ "params_length"
  | M_F_params_nth -> !^ "params_nth"
  | M_F_are_compatible -> !^ "are_compatible"
  | M_F_align_of -> !^ "align_of"
  | M_F_size_of -> !^ "size_of"
  | M_F_max_int -> !^ "max_int"
  | M_F_min_int -> !^ "min_int"
  | M_F_ctype_width -> !^ "ctype_width"

let evaluate_fun mu_fun args =
  match mu_fun with
  | M_F_params_length ->
     begin match args with
     | [arg] ->
        Option.bind (IT.dest_list arg) (fun xs ->
        Some (IT.int_ (List.length xs)))
     | _ -> None
     end
  | M_F_params_nth ->
     begin match args with
     | [arg1;arg2] ->
        Option.bind (IT.dest_list arg1) (fun xs ->
        Option.bind (IT.is_z arg2) (fun i ->
            if Z.lt i (Z.of_int (List.length xs))
            then List.nth_opt xs (Z.to_int i) else None
        ))
     | _ -> None
     end
  | M_F_are_compatible ->
     begin match List.map IT.is_const args with
     | [Some (IT.CType_const ct1, _); Some (IT.CType_const ct2, _)] ->
        if Sctypes.equal ct1 ct2
        then Some (IT.bool_ true) else None
     | _ -> None
     end
  | M_F_size_of ->
     begin match List.map IT.is_const args with
     | [Some (IT.CType_const ct, _)] ->
        Some (IT.int_ (Memory.size_of_ctype ct))
     | _ -> None
     end
  | M_F_align_of ->
     begin match List.map IT.is_const args with
     | [Some (IT.CType_const ct, _)] ->
        Some (IT.int_ (Memory.align_of_ctype ct))
     | _ -> None
     end
  | M_F_max_int ->
     begin match List.map IT.is_const args with
     | [Some (IT.CType_const (Sctypes.Integer ity), _)] ->
        Some (IT.z_ (Memory.max_integer_type ity))
     | _ -> None
     end
  | M_F_min_int ->
     begin match List.map IT.is_const args with
     | [Some (IT.CType_const (Sctypes.Integer ity), _)] ->
        Some (IT.z_ (Memory.min_integer_type ity))
     | _ -> None
     end
  | M_F_ctype_width ->
     begin match List.map IT.is_const args with
     | [Some (IT.CType_const ct, _)] ->
        Some (IT.int_ (Memory.size_of_ctype ct * 8))
     | _ -> None
     end


type parse_ast_label_spec =
  { label_spec: (Sym.t, Ctype.ctype) Cn.cn_condition list }

type 'TY mu_label_def = 
  | M_Return of loc
  | M_Label of loc * ('TY mu_expr) mu_arguments * annot list * 
                 (* for generating runtime assertions *)
                 parse_ast_label_spec

let dtree_of_label_def = function
  | M_Return _ -> 
     Dleaf !^"return label"
  | M_Label (_loc, args_and_body, _, _) ->
     dtree_of_mu_arguments (fun body ->
         Dleaf !^"(body)"
       ) args_and_body
  

type 'TY mu_label_defs = 
  (symbol, ('TY mu_label_def)) Pmap.map



type 'TY mu_proc_args_and_body =
  ('TY mu_expr * 'TY mu_label_defs * T.rt) mu_arguments

(* let dtree_of_mu_args_and_body a =  *)
(*   dtree_of_mu_arguments (fun (_body, labels, rt) -> *)
(*       Dnode ("FunctionBodyLabelsReturn" [ *)
(*                  Dleaf !^"(body)"; *)
(*                  Dnode (pp_ctor "labels" *)
(*         ]) *)
(*     ) a *)


type parse_ast_function_specification =
  { accesses: (Sym.t * Ctype.ctype) list;
    requires: (Sym.t, Ctype.ctype) Cn.cn_condition list;
    ensures: (Sym.t, Ctype.ctype) Cn.cn_condition list; }

type 'TY mu_fun_map_decl =
  (* | M_Fun of T.bt * (symbol * T.bt) list * 'TY mu_pexpr *)
  | M_Proc of Cerb_location.t * 'TY mu_proc_args_and_body * trusted * 
                parse_ast_function_specification
      (* recording the desugared parse ast, for generating runtime checks *)
                
  | M_ProcDecl of Cerb_location.t * T.ft option
  (* | M_BuiltinDecl of Cerb_location.t * T.bt * T.bt list *)

type 'TY mu_fun_map = 
  (symbol, 'TY mu_fun_map_decl) Pmap.map



type mu_extern_map = Core.extern_map

type 'TY mu_globs =
  | M_GlobalDef of T.ct * 'TY mu_expr
  | M_GlobalDecl of T.ct

type 'TY mu_globs_map = 
  (symbol, 'TY mu_globs) Pmap.map


type mu_tag_definition =
  | M_StructDef of T.st
  | M_UnionDef of T.ut

type mu_tag_definitions = 
  (Symbol.sym, mu_tag_definition) Pmap.map

type 'TY mu_globs_list = 
  (symbol * 'TY mu_globs) list

type mu_datatype = 
  { loc : Loc.t;
    cases : (Sym.t * (Id.t * T.bt) list) list }

type 'TY mu_file = {
  mu_main    : symbol option;
  mu_tagDefs : mu_tag_definitions;
  mu_globs   : 'TY mu_globs_list;
  mu_funs    : 'TY mu_fun_map;
  mu_extern  : mu_extern_map;
  mu_stdlib_syms  : SymSet.t;
  mu_resource_predicates : T.resource_predicates;
  mu_logical_predicates : T.logical_predicates;
  mu_datatypes : (Sym.t * mu_datatype) list;
  mu_lemmata : (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list;
  mu_call_funinfo : (symbol, Sctypes.c_concrete_sig) Pmap.map;
}






