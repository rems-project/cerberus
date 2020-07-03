open Cerb_frontend
open Extra
open Panic
open Coq_ast
open Rc_annot

type typed_ail = GenTypes.genTypeCategory AilSyntax.ail_program
type ail_expr  = GenTypes.genTypeCategory AilSyntax.expression
type c_type    = Ctype.ctype
type i_type    = Ctype.integerType
type type_cat  = GenTypes.typeCategory
type loc       = Location_ocaml.t

let c_type_of_type_cat : type_cat -> c_type = fun tc ->
  match tc with
  | GenTypes.LValueType(_,c_ty,_) -> c_ty
  | GenTypes.RValueType(c_ty)     -> c_ty

let to_type_cat : GenTypes.genTypeCategory -> type_cat = fun tc ->
  let loc = Location_ocaml.unknown in
  let impl = Ocaml_implementation.hafniumIntImpl in
  let m_tc = GenTypesAux.interpret_genTypeCategory loc impl tc in
  match ErrorMonad.runErrorMonad m_tc with
  | Either.Right(tc) -> tc
  | Either.Left(_,_) -> assert false (* FIXME possible here? *)

let tc_of : ail_expr -> type_cat = fun e ->
  let AilSyntax.AnnotatedExpression(ty,_,_,_) = e in to_type_cat ty

let loc_of : ail_expr -> loc = fun e ->
  let AilSyntax.AnnotatedExpression(_,_,loc,_) = e in loc

let not_impl loc fmt = panic loc ("Not implemented: " ^^ fmt)

let forbidden loc fmt = panic loc ("Forbidden: " ^^ fmt)

(* Short names for common functions. *)
let sym_to_str : Symbol.sym -> string =
  Pp_symbol.to_string_pretty

let id_to_str : Symbol.identifier -> string =
  fun Symbol.(Identifier(_,id)) -> id

let loc_of_id : Symbol.identifier -> loc =
  fun Symbol.(Identifier(loc,_)) -> loc

(* Register a location. *)
let register_loc : Location.Pool.t -> loc -> Location.t = fun p loc ->
  match Location_ocaml.(get_filename loc, to_cartesian loc) with
  | (Some(f), Some((l1,c1),(0 ,0 ))) -> Location.make f l1 c1 l1 c1 p
  | (Some(f), Some((l1,c1),(l2,c2))) -> Location.make f l1 c1 l2 c2 p
  | (_      , _                    ) -> Location.none coq_locs

let register_str_loc : Location.Pool.t -> loc -> Location.t = fun p loc ->
  match Location_ocaml.(get_filename loc, to_cartesian loc) with
  | (Some(f), Some((l1,c1),(l2,c2))) -> Location.make f l1 (c1+1) l2 (c2-1) p
  | (_      , _                    ) -> Location.none coq_locs

let mkloc elt loc = Location.{ elt ; loc }

let noloc elt = mkloc elt (Location.none coq_locs)

(* Extract attributes with namespace ["rc"]. *)
let collect_rc_attrs : Annot.attributes -> rc_attr list =
  let fn acc Annot.{attr_ns; attr_id; attr_args} =
    match Option.map id_to_str attr_ns with
    | Some("rc") ->
        let rc_attr_id =
          let Symbol.(Identifier(loc, id)) = attr_id in
          mkloc id (register_loc rc_locs loc)
        in
        let rc_attr_args =
          let fn (loc, s) = mkloc s (register_str_loc rc_locs loc) in
          List.map fn attr_args
        in
        {rc_attr_id; rc_attr_args} :: acc
    | _          -> acc
  in
  fun (Annot.Attrs(attrs)) -> List.fold_left fn [] attrs

let rec translate_int_type : loc -> i_type -> Coq_ast.int_type = fun loc i ->
  let open Ctype in
  let open Ocaml_implementation in
  let size_of_base_type signed i =
    match i with
    (* Things defined in the standard libraries *)
    | IntN_t(_)       -> not_impl loc "size_of_base_type (IntN_t)"
    | Int_leastN_t(_) -> not_impl loc "size_of_base_type (Int_leastN_t)"
    | Int_fastN_t(_)  -> not_impl loc "size_of_base_type (Int_fastN_t)"
    | Intmax_t        -> not_impl loc "size_of_base_type (Intmax_t)"
    | Intptr_t        -> ItSize_t(signed)
    (* Normal integer types *)
    | Ichar | Short | Int_ | Long | LongLong ->
    let ity = if signed then Signed(i) else Unsigned i in
    match HafniumImpl.sizeof_ity ity with
    | Some(1) -> ItI8(signed)
    | Some(2) -> ItI16(signed)
    | Some(4) -> ItI32(signed)
    | Some(8) -> ItI64(signed)
    | Some(p) -> not_impl loc "unknown integer precision: %i" p
    | None    -> assert false
  in
  match i with
  | Char        -> size_of_base_type (hafniumIntImpl.impl_signed Char) Ichar
  | Bool        -> ItBool
  | Signed(i)   -> size_of_base_type true  i
  | Unsigned(i) -> size_of_base_type false i
  | Enum(s)     -> translate_int_type loc (HafniumImpl.typeof_enum s)
  (* Things defined in the standard libraries *)
  | Wchar_t     -> not_impl loc "layout_of (Wchar_t)"
  | Wint_t      -> not_impl loc "layout_of (Win_t)"
  | Size_t      -> ItSize_t(false)
  | Ptrdiff_t   -> not_impl loc "layout_of (Ptrdiff_t)"

(** [layout_of fa c_ty] translates the C type [c_ty] into a layout.  Note that
    argument [fa] must be set to [true] when in function arguments, since this
    requires a different tranlation for arrays (always pointers). *)
let layout_of : bool -> c_type -> Coq_ast.layout = fun fa c_ty ->
  let rec layout_of Ctype.(Ctype(annots, c_ty)) =
    let loc = Annot.get_loc_ annots in
    match c_ty with
    | Void                -> LVoid
    | Basic(Integer(i))   -> LInt (translate_int_type loc i)
    | Basic(Floating(_))  -> not_impl loc "layout_of (Basic float)"
    | Array(_,_) when fa  -> LPtr
    | Array(c_ty,None )   -> LPtr
    | Array(c_ty,Some(n)) -> LArray(layout_of c_ty, Z.to_string n)
    | Function(_,_,_,_)   -> not_impl loc "layout_of (Function)"
    | Pointer(_,_)        -> LPtr
    | Atomic(c_ty)        -> layout_of c_ty
    | Struct(sym)         -> LStruct(sym_to_str sym, false)
    | Union(sym)          -> LStruct(sym_to_str sym, true )
  in
  layout_of c_ty

(* Get a layout under a pointer indirection in the type of [e]. *)
let ptr_layout_of : ail_expr -> Coq_ast.layout = fun e ->
  match c_type_of_type_cat (tc_of e) with
  | Ctype(_, Pointer(_,c_ty)) -> layout_of false c_ty
  | _                         -> assert false

(* Hashtable of local variables to distinguish global ones. *)
let local_vars = Hashtbl.create 17

(* Hashtable of global variables used. *)
let used_globals = Hashtbl.create 5

(* Hashtable of used function. *)
let used_functions = Hashtbl.create 5

let (fresh_ret_id, reset_ret_id) =
  let counter = ref (-1) in
  let fresh () = incr counter; Printf.sprintf "$%i" !counter in
  let reset () = counter := -1 in
  (fresh, reset)

let (fresh_block_id, reset_block_id) =
  let counter = ref (-1) in
  let fresh () = incr counter; Printf.sprintf "#%i" !counter in
  let reset () = counter := -1 in
  (fresh, reset)

let layout_of_tc : type_cat -> Coq_ast.layout = fun tc ->
  layout_of false (c_type_of_type_cat tc)

let is_atomic : c_type -> bool = AilTypesAux.is_atomic

let is_atomic_tc : GenTypes.typeCategory -> bool = fun tc ->
  is_atomic (c_type_of_type_cat tc)

let is_const_0 (AilSyntax.AnnotatedExpression(_, _, _, e)) =
  let open AilSyntax in
  match e with
  | AilEconst(c) ->
      begin
        match c with
        | ConstantInteger(IConstant(i,_,_)) -> Z.equal Z.zero i
        | _                                 -> false
      end
  | _            -> false

let rec op_type_of loc Ctype.(Ctype(_, c_ty)) =
  match c_ty with
  | Void                -> not_impl loc "op_type_of (Void)"
  | Basic(Integer(i))   -> OpInt(translate_int_type loc i)
  | Basic(Floating(_))  -> not_impl loc "op_type_of (Basic float)"
  | Array(_,_)          -> not_impl loc "op_type_of (Array)"
  | Function(_,_,_,_)   -> not_impl loc "op_type_of (Function)"
  | Pointer(_,c_ty)     -> OpPtr(layout_of false c_ty)
  | Atomic(c_ty)        ->
      begin
        match op_type_of loc c_ty with
        | OpInt(_) as op_ty -> op_ty
        | _                 -> not_impl loc "op_type_of (Atomic not an int)"
      end
  | Struct(_)           -> not_impl loc "op_type_of (Struct)"
  | Union(_)            -> not_impl loc "op_type_of (Union)"

(* Get an op_type under a pointer indirection in the type of [e]. *)
let ptr_op_type_of : ail_expr -> Coq_ast.op_type = fun e ->
  match c_type_of_type_cat (tc_of e) with
  | Ctype(_, Pointer(_,c_ty)) -> op_type_of (loc_of e) c_ty
  | _                         -> assert false

let op_type_of_tc : loc -> type_cat -> Coq_ast.op_type = fun loc tc ->
  op_type_of loc (c_type_of_type_cat tc)

(* We need similar function returning options for casts. *)
let rec op_type_opt loc Ctype.(Ctype(_, c_ty)) =
  match c_ty with
  | Void                -> None
  | Basic(Integer(i))   -> Some(OpInt(translate_int_type loc i))
  | Basic(Floating(_))  -> None
  | Array(_,_)          -> None
  | Function(_,_,_,_)   -> None
  | Pointer(_,c_ty)     -> Some(OpPtr(layout_of false c_ty))
  | Atomic(c_ty)        ->
      begin
        match op_type_opt loc c_ty with
        | Some(OpInt(_)) as op_ty -> op_ty
        | _                       -> None
      end
  | Struct(_)           -> None
  | Union(_)            -> None

let op_type_tc_opt : loc -> type_cat -> Coq_ast.op_type option = fun loc tc ->
  op_type_opt loc (c_type_of_type_cat tc)

let struct_data : ail_expr -> string * bool = fun e ->
  let AilSyntax.AnnotatedExpression(gtc,_,_,_) = e in
  let open GenTypes in
  match gtc with
  | GenRValueType(GenPointer(_,Ctype(_,Struct(s))))
  | GenLValueType(_,Ctype(_,Struct(s)),_)           -> (sym_to_str s, false)
  | GenRValueType(GenPointer(_,Ctype(_,Union(s) )))
  | GenLValueType(_,Ctype(_,Union(s) ),_)           ->(sym_to_str s, true )
  | GenRValueType(_                               ) -> assert false
  | GenLValueType(_,_                 ,_)           -> assert false

let strip_expr (AilSyntax.AnnotatedExpression(_,_,_,e)) = e

let rec function_decls decls =
  let open AilSyntax in
  match decls with
  | []                                                           -> []
  | (id, (_, attrs, Decl_function(_,(_,ty),args,_,_,_))) :: decls ->
      (sym_to_str id, (ty, args, attrs)) :: function_decls decls
  | (_ , (_, _    , Decl_object(_,_,_)                )) :: decls ->
      function_decls decls

let global_fun_decls = ref []
let global_tag_defs = ref []

let tag_def_data : loc -> string -> (string * op_type) list = fun loc id ->
  let fs =
    match List.find (fun (s,_) -> sym_to_str s = id) !global_tag_defs with
    | (_, (_, Ctype.StructDef(fs,_)))
    | (_, (_, Ctype.UnionDef(fs)   )) -> fs
  in
  let fn (s, (_, _, c_ty)) = (id_to_str s, op_type_of loc c_ty) in
  List.map fn fs

let rec align_of : c_type -> int = fun c_ty ->
  let Ctype.(Ctype(annots, c_ty)) = c_ty in
  let open Ocaml_implementation.HafniumImpl in
  let unwrap o =
    match o with Some(n) -> n | None ->
    let loc = Annot.get_loc_ annots in
    panic loc "Undefined alignment requirement."
  in
  match c_ty with
  | Void                -> 1
  | Basic(Integer(i))   -> unwrap (alignof_ity i)
  | Basic(Floating(f))  -> unwrap (alignof_fty f)
  | Array(c_ty,_)       -> align_of c_ty
  | Function(_,_,_,_)   -> unwrap alignof_pointer
  | Pointer(_,_)        -> unwrap alignof_pointer
  | Atomic(c_ty)        -> align_of c_ty (* FIXME may not be the same? *)
  | Struct(sym)         -> align_of_struct false sym
  | Union(sym)          -> align_of_struct true  sym

and align_of_struct : bool -> Symbol.sym -> int = fun is_union id ->
  let id = sym_to_str id in
  let fs =
    match List.find (fun (s,_) -> sym_to_str s = id) !global_tag_defs with
    | (_, (_, Ctype.StructDef(fs,_)))
    | (_, (_, Ctype.UnionDef(fs)   )) -> fs
  in
  let fn acc (_, (_, _, c_ty)) = max acc (align_of c_ty) in
  List.fold_left fn 1 fs

let rec size_of : c_type -> int = fun c_ty ->
  let Ctype.(Ctype(annots, c_ty)) = c_ty in
  let open Ocaml_implementation.HafniumImpl in
  let unwrap o =
    match o with Some(n) -> n | None ->
    let loc = Annot.get_loc_ annots in
    panic loc "Undefined size."
  in
  match c_ty with
  | Void                -> 1
  | Basic(Integer(i))   -> unwrap (sizeof_ity i)
  | Basic(Floating(f))  -> unwrap (sizeof_fty f)
  | Array(c_ty,None)    -> unwrap sizeof_pointer
  | Array(c_ty,Some(n)) -> size_of c_ty * Nat_big_num.to_int n
  | Function(_,_,_,_)   -> unwrap sizeof_pointer
  | Pointer(_,_)        -> unwrap sizeof_pointer
  | Atomic(c_ty)        -> size_of c_ty (* FIXME may not be the same? *)
  | Struct(sym)         -> size_of_struct false sym
  | Union(sym)          -> size_of_struct true  sym

and size_of_struct : bool -> Symbol.sym -> int = fun is_union s ->
  let id = sym_to_str s in
  let fs =
    match List.find (fun (s,_) -> sym_to_str s = id) !global_tag_defs with
    | (_, (_, Ctype.StructDef(fs,_)))
    | (_, (_, Ctype.UnionDef(fs)   )) -> fs
  in
  let fn (_,(_,_,c_ty)) = (align_of c_ty, size_of c_ty) in
  let data = List.map fn fs in
  if is_union then
    List.fold_left (fun acc (_, sz) -> max acc sz) 0 data
  else
    let fn acc (align, sz) =
      let pad = if acc mod align = 0 then 0 else align - acc mod align in
      acc + pad + sz
    in
    let size = List.fold_left fn 0 data in
    let struct_align = align_of_struct is_union s in
    if size mod struct_align = 0 then size
    else size + (struct_align - size mod struct_align)

let handle_invalid_annot : type a b. ?loc:loc -> b ->  (a -> b) -> a -> b =
    fun ?loc default f a ->
  try f a with Invalid_annot(err_loc, msg) ->
  begin
    match Location.get err_loc with
    | None    ->
        Panic.wrn loc "Invalid annotation (ignored).\n  → %s" msg
    | Some(d) ->
        Panic.wrn None "[%a] Invalid annotation (ignored).\n  → %s"
          Location.pp_data d msg
  end; default

let memory_order_of_expr : ail_expr -> Cmm_csem.memory_order = fun e ->
  let i =
    match strip_expr e with
    | AilEconst(ConstantInteger(IConstant(i,_,_))) -> i
    | _                                            ->
        Panic.panic (loc_of e) "Memory order is not an integer constant."
  in
  let i =
    try Z.to_int i with Z.Overflow ->
      Panic.panic (loc_of e) "Memory order is invalid (bad constant)."
  in
  match Builtins.decode_memory_order i with
  | Some(mo) -> mo
  | None     ->
      Panic.panic (loc_of e) "Memory order is invalid (bad constant)."

let integer_constant_to_string loc i =
  let open AilSyntax in
  match i with
  | IConstant(i,_,_) ->
      (Z.to_string i, None)
  | IConstantMax(it) ->
      let it : int_type = translate_int_type loc it in
      Format.(fprintf str_formatter) "(it_max %a - 1)" Coq_pp.pp_int_type it;
      (Format.flush_str_formatter (), Some(it))
  | IConstantMin(it) ->
      let it : int_type = translate_int_type loc it in
      Format.(fprintf str_formatter) "(it_min %a)" Coq_pp.pp_int_type it;
      (Format.flush_str_formatter (), Some(it))

(* Calls accumulated while translating expressions. *)
type call = Location.t * string option * expr * expr list
type calls = call list

type _ call_place =
  | In_Expr : expr call_place (* Nested call in expression. *)
  | In_Stmt : stmt call_place (* Call at the top level. *)

type _ call_res =
  | Call_simple       : expr * expr list     -> 'a   call_place call_res
  | Call_atomic_expr  : expr_aux             -> 'a   call_place call_res
  | Call_atomic_store : layout * expr * expr -> stmt call_place call_res

let rec translate_expr : bool -> op_type option -> ail_expr -> expr * calls =
  fun lval goal_ty e ->
  let open AilSyntax in
  let res_ty = op_type_tc_opt (loc_of e) (tc_of e) in
  let AnnotatedExpression(_, _, loc, e) = e in
  let coq_loc = register_loc coq_locs loc in
  let locate e = mkloc e coq_loc in
  let translate = translate_expr lval None in
  let (e, l) as res =
    match e with
    | AilEunary(Address,e)         ->
        let (e, l) = translate_expr true None e in
        (locate (AddrOf(e)), l)
    | AilEunary(Indirection,e)     -> translate e
    | AilEunary(Plus,e)            -> translate e
    | AilEunary(op,e)              ->
        let ty = op_type_of_tc (loc_of e) (tc_of e) in
        let (e, l) = translate e in
        let op =
          match op with
          | Address     -> assert false (* Handled above. *)
          | Indirection -> assert false (* Handled above. *)
          | Plus        -> assert false (* Handled above. *)
          | Minus       -> NegOp
          | Bnot        -> NotIntOp
          | PostfixIncr -> forbidden loc "nested postfix increment"
          | PostfixDecr -> forbidden loc "nested postfix decrement"
        in
        (locate (UnOp(op, ty, e)), l)
    | AilEbinary(e1,op,e2)         ->
        let ty1 = op_type_of_tc (loc_of e1) (tc_of e1) in
        let ty2 = op_type_of_tc (loc_of e2) (tc_of e2) in
        let arith_op = ref false in
        let op =
          match op with
          | Eq             -> EqOp
          | Ne             -> NeOp
          | Lt             -> LtOp
          | Gt             -> GtOp
          | Le             -> LeOp
          | Ge             -> GeOp
          | And            -> not_impl loc "nested && operator"
          | Or             -> not_impl loc "nested || operator"
          | Comma          -> not_impl loc "binary operator (Comma)"
          | Arithmetic(op) ->
          arith_op := true;
          match op with
          | Mul  -> MulOp | Div  -> DivOp | Mod  -> ModOp | Add  -> AddOp
          | Sub  -> SubOp | Shl  -> ShlOp | Shr  -> ShrOp | Band -> AndOp
          | Bxor -> XorOp | Bor  -> OrOp
        in
        let (goal_ty, ty1, ty2) =
          match (ty1, ty2, res_ty) with
          | (OpInt(_), OpInt(_), Some((OpInt(_) as res_ty))) ->
              if !arith_op then (Some(res_ty), res_ty, res_ty) else
              if ty1 = ty2 then (None, ty1, ty2) else
              not_impl loc "Operand types not uniform for comparing operator."
          | (_       , _       , _                         ) ->
              (None        , ty1   , ty2   )
        in
        let (e1, l1) = translate_expr lval  goal_ty e1 in
        let (e2, l2) = translate_expr false goal_ty e2 in
        (locate (BinOp(op, ty1, ty2, e1, e2)), l1 @ l2)
    | AilEassign(e1,e2)            -> forbidden loc "nested assignment"
    | AilEcompoundAssign(e1,op,e2) -> not_impl loc "expr compound assign"
    | AilEcond(e1,e2,e3)           -> not_impl loc "expr cond"
    | AilEcast(q,c_ty,e)           ->
        begin
          match c_ty with
          | Ctype(_,Pointer(_,Ctype(_,Void))) when is_const_0 e ->
              let AnnotatedExpression(_, _, loc, _) = e in
              ({ elt = Val(Null) ; loc = register_loc coq_locs loc }, [])
          | _                                                   ->
          let ty = op_type_of_tc (loc_of e) (tc_of e) in
          let op_ty = op_type_of loc c_ty in
          let (e, l) = translate e in
          (locate (UnOp(CastOp(op_ty), ty, e)), l)
        end
    | AilEcall(e,es)               ->
        let (call, l) = translate_call In_Expr loc lval e es in
        begin
          match call with
          | Call_atomic_expr(e) -> (locate e, l)
          | Call_simple(e, es)  ->
              let ret_id = Some(fresh_ret_id ()) in
              (locate (Var(ret_id, false)), l @ [(coq_loc, ret_id, e, es)])
        end
    | AilEassert(e)                -> not_impl loc "expr assert nested"
    | AilEoffsetof(c_ty,is)        -> not_impl loc "expr offsetof"
    | AilEgeneric(e,gas)           -> not_impl loc "expr generic"
    | AilEarray(b,c_ty,oes)        -> not_impl loc "expr array"
    | AilEstruct(sym,fs) when lval -> not_impl loc "Struct initializer not supported in lvalue context"
    | AilEstruct(sym,fs)           ->
        let st_id = sym_to_str sym in
        (* Map of types for the fields. *)
        let map = try tag_def_data loc st_id with Not_found -> assert false in
        let fs =
          let fn (id, eo) = Option.map (fun e -> (id_to_str id, e)) eo in
          List.filter_map fn fs
        in
        let (fs, l) =
          let fn (id, e) (fs, l) =
            let ty = try List.assoc id map with Not_found -> assert false in
            let (e, l_e) = translate_expr lval (Some(ty)) e in
            ((id, e) :: fs, l_e @ l)
          in
          List.fold_right fn fs ([], [])
        in
        (locate (Struct(st_id, fs)), l)
    | AilEunion(sym,id,eo)         -> not_impl loc "expr union"
    | AilEcompound(q,c_ty,e)       -> translate e (* FIXME? *)
    | AilEmemberof(e,id)           ->
        if not lval then assert false;
        let (struct_name, from_union) = struct_data e in
        let (e, l) = translate e in
        (locate (GetMember(e, struct_name, from_union, id_to_str id)), l)
    | AilEmemberofptr(e,id)        ->
        let (struct_name, from_union) = struct_data e in
        let (e, l) = translate e in
        (locate (GetMember(e, struct_name, from_union, id_to_str id)), l)
    | AilEbuiltin(b)               -> not_impl loc "expr builtin"
    | AilEstr(s)                   -> not_impl loc "expr str"
    | AilEconst(c)                 ->
        let c =
          match c with
          | ConstantIndeterminate(c_ty) -> assert false
          | ConstantNull                -> Null
          | ConstantInteger(i)          ->
              let (i, it) =
                let (i, ito) = integer_constant_to_string loc i in
                let it =
                  match (res_ty, ito) with
                  | (Some(OpInt(it)), Some(it_c)) -> assert (it = it_c); it
                  | (Some(OpInt(it)), None      ) -> it
                  | (_              , _         ) -> assert false
                in
                (i, it)
              in
              Int(i, it)
          | ConstantFloating(_)         -> not_impl loc "constant float"
          | ConstantCharacter(_)        -> not_impl loc "constant char"
          | ConstantArray(_,_)          -> not_impl loc "constant array"
          | ConstantStruct(_,_)         -> not_impl loc "constant struct"
          | ConstantUnion(_,_,_)        -> not_impl loc "constant union"
        in
        (locate (Val(c)), [])
    | AilEident(sym)               ->
        let id = sym_to_str sym in
        let global = not (Hashtbl.mem local_vars id) in
        if global then Hashtbl.add used_globals id ();
        (locate (Var(Some(id), global)), [])
    | AilEsizeof(q,c_ty)           ->
        (locate (Val(SizeOf(layout_of false c_ty))), [])
    | AilEsizeof_expr(e)           -> not_impl loc "expr sizeof_expr"
    | AilEalignof(q,c_ty)          -> not_impl loc "expr alignof"
    | AilEannot(c_ty,e)            -> not_impl loc "expr annot"
    | AilEva_start(e,sym)          -> not_impl loc "expr va_start"
    | AilEva_arg(e,c_ty)           -> not_impl loc "expr va_arg"
    | AilEva_copy(e1,e2)           -> not_impl loc "expr va_copy"
    | AilEva_end(e)                -> not_impl loc "expr va_end"
    | AilEprint_type(e)            -> not_impl loc "expr print_type"
    | AilEbmc_assume(e)            -> not_impl loc "expr bmc_assume"
    | AilEreg_load(r)              -> not_impl loc "expr reg_load"
    | AilErvalue(e)                ->
        let res =
          match e with
          (* Struct initializers are lvalues for Ail, but rvalues for us. *)
          | AnnotatedExpression(_, _, _, AilEcompound(_, _, _)) -> translate e
          | _                                                   ->
          let layout = layout_of_tc (tc_of e) in
          let atomic = is_atomic_tc (tc_of e) in
          let (e, l) = translate_expr true None e in
          let gen =
            if lval then Deref(atomic, layout, e)
            else Use(atomic, layout, e)
          in
          (locate gen, l)
        in res
    | AilEarray_decay(e) when lval -> translate e
    | AilEarray_decay(e)           ->
        let (e, l) = translate_expr true None e in
        (locate (AddrOf(e)), l)
    | AilEfunction_decay(e)        -> not_impl loc "expr function_decay"
  in
  match (goal_ty, res_ty) with
  | (None         , _           )
  | (_            , None        ) -> res
  | (Some(goal_ty), Some(res_ty)) ->
      if goal_ty = res_ty then res
      else (mkloc (UnOp(CastOp(goal_ty), res_ty, e)) e.loc, l)

and translate_call : type a. a call_place -> loc -> bool -> ail_expr
    -> ail_expr list -> a call_place call_res * calls =
  fun place loc lval e es ->
  let loc_e = register_loc coq_locs (loc_of e) in
  match strip_expr e with
  | AilEfunction_decay(e) -> translate_call place loc lval e es
  | AilEident(sym)        ->
      let fun_id = sym_to_str sym in
      Hashtbl.add used_functions fun_id ();
      let e = mkloc (Var(Some(fun_id), true)) loc_e in
      let (_, args, attrs) = List.assoc fun_id !global_fun_decls in
      let attrs = collect_rc_attrs attrs in
      let annot_args =
        handle_invalid_annot ~loc [] function_annot_args attrs
      in
      let nb_args = List.length es in
      let check_useful (i, _, _) =
        if i >= nb_args then
          Panic.wrn (Some(loc))
            "Argument annotation not usable (not enough arguments)."
      in
      List.iter check_useful annot_args;
      let (es, l) =
        let fn i e =
          let (_, ty, _) = List.nth args i in
          match op_type_opt Location_ocaml.unknown ty with
          | Some(OpInt(_)) as goal_ty -> translate_expr false goal_ty e
          | _                         -> translate_expr false None e
        in
        let es_ls = List.mapi fn es in
        (List.map fst es_ls, List.concat (List.map snd es_ls))
      in
      let annotate i e =
        let annot_args = List.filter (fun (n, _, _) -> n = i) annot_args in
        let fn (_, k, coq_e) acc = mkloc (AnnotExpr(k, coq_e, e)) e.loc in
        List.fold_right fn annot_args e
      in
      (Call_simple(e, List.mapi annotate es), l)
  | AilEbuiltin(b)        ->
      begin
        match b with
        | AilBatomic(AilBAthread_fence)            ->
            not_impl loc "call to builtin atomic (thread_fence)"
        | AilBatomic(AilBAstore)                   ->
            let (e1, e2, e3) =
              match es with
              | [e1; e2; e3] -> (e1, e2, e3)
              | _            -> assert false
            in
            let layout = ptr_layout_of e1 in
            let op_type = ptr_op_type_of e1 in
            let (e1, l1) = translate_expr true None e1 in
            let (e2, l2) = translate_expr false (Some(op_type)) e2 in
            let mo = memory_order_of_expr e3 in
            if mo <> Cmm_csem.Seq_cst then
              Panic.panic loc "Only the Seq_cst memory order is supported.";
            begin
              match place with
              | In_Expr ->
                  forbidden loc "nested (atomic) store"
              | In_Stmt ->
                  let e1 =
                    match e1.elt with
                    | AddrOf(e) -> e
                    | _         -> forbidden loc "atomic store whose LHS is \
                                     not of the form [&e]"
                  in
                  (Call_atomic_store(layout, e1, e2), List.concat [l1; l2])
            end
        | AilBatomic(AilBAload)                    ->
            not_impl loc "call to builtin atomic (load)"
        | AilBatomic(AilBAexchange)                ->
            not_impl loc "call to builtin atomic (exchange)"
        | AilBatomic(AilBAcompare_exchange_strong) ->
            let (e1, e2, e3, e4, e5) =
              match es with
              | [e1; e2; e3; e4; e5] -> (e1, e2, e3, e4, e5)
              | _                    -> assert false
            in
            let op_type = ptr_op_type_of e1 in
            let (e1, l1) = translate_expr lval None e1 in
            let (e2, l2) = translate_expr lval None e2 in
            let (e3, l3) = translate_expr lval (Some(op_type)) e3 in
            let mo1 = memory_order_of_expr e4 in
            let mo2 = memory_order_of_expr e4 in
            if mo1 <> Cmm_csem.Seq_cst || mo2 <> Cmm_csem.Seq_cst then
              Panic.panic loc "Only the Seq_cst memory order is supported.";
            let cas = CAS(op_type, e1, e2, e3) in
            (Call_atomic_expr(cas), List.concat [l1; l2; l3])
        | AilBatomic(AilBAcompare_exchange_weak)   ->
            not_impl loc "call to builtin atomic (compare_exchange_weak)"
        | AilBatomic(AilBAfetch_key)               ->
            not_impl loc "call to builtin atomic (fetch_key)"
        | AilBlinux(AilBLfence)                    ->
            not_impl loc "call to linux builtin (fence)"
        | AilBlinux(AilBLread)                     ->
            not_impl loc "call to linux builtin (read)"
        | AilBlinux(AilBLwrite)                    ->
            not_impl loc "call to linux builtin (write)"
        | AilBlinux(AilBLrmw)                      ->
            not_impl loc "call to linux builtin (rmw)"
      end
  | _                     -> not_impl loc "expr complicated call"

type bool_expr =
  | BE_leaf of ail_expr
  | BE_neg  of bool_expr
  | BE_and  of bool_expr * bool_expr
  | BE_or   of bool_expr * bool_expr

let rec bool_expr : ail_expr -> bool_expr = fun e ->
  match strip_expr e with
  | AilEbinary(e1,And,e2) -> BE_and(bool_expr e1, bool_expr e2)
  | AilEbinary(e1,Or ,e2) -> BE_or(bool_expr e1, bool_expr e2)
  | AilEbinary(e1,Eq ,e2) ->
      begin
        let be1 = bool_expr e1 in
        let be2 = bool_expr e2 in
        match (is_const_0 e1, be1, is_const_0 e2, be2) with
        | (false, _         , false, _         )
        | (true , _         , true , _         )
        | (false, BE_leaf(_), true , _         )
        | (true , _         , false, BE_leaf(_)) -> BE_leaf(e)
        | (false, _         , true , _         ) -> BE_neg(be1)
        | (true , _         , false, _         ) -> BE_neg(be2)
      end
  | _                     -> BE_leaf(e)

let add_block ?annots id s blocks =
  if SMap.mem id blocks then assert false;
  let annots =
    match annots with
    | None         -> BA_none
    | Some(annots) -> BA_loop(annots)
  in
  SMap.add id (annots, s) blocks

type op_ty_opt = Coq_ast.op_type option

let trans_expr : ail_expr -> op_ty_opt -> (expr -> stmt) -> stmt =
    fun e goal_ty e_stmt ->
  let (e, calls) = translate_expr false goal_ty e in
  let fn (loc, id, e, es) stmt =
    mkloc (Call(id, e, es, stmt)) loc
  in
  List.fold_right fn calls (e_stmt e)

let trans_bool_expr : ail_expr -> (expr -> stmt) -> stmt = fun e e_stmt ->
  trans_expr e (Some(OpInt(ItBool))) e_stmt

let translate_bool_expr then_goto else_goto blocks e =
  let rec translate then_goto else_goto blocks be =
    match be with
    | BE_leaf(e)      ->
        let fn e = mkloc (If(e, then_goto, else_goto)) e.loc in
        (trans_bool_expr e fn, blocks)
    | BE_neg(be)      ->
        translate else_goto then_goto blocks be
    | BE_and(be1,be2) ->
        let id = fresh_block_id () in
        let id_goto = noloc (Goto(id)) in (* FIXME loc *)
        let (s, blocks) = translate id_goto else_goto blocks be1 in
        let blocks =
          let (s, blocks) = translate then_goto else_goto blocks be2 in
          add_block id s blocks
        in
        (s, blocks)
    | BE_or (be1,be2) ->
        let id = fresh_block_id () in
        let id_goto = noloc (Goto(id)) in (* FIXME loc *)
        let (s, blocks) = translate then_goto id_goto blocks be1 in
        let blocks =
          let (s, blocks) = translate then_goto else_goto blocks be2 in
          add_block id s blocks
        in
        (s, blocks)
  in
  translate then_goto else_goto blocks (bool_expr e)

let trans_lval e : expr =
  let (e, calls) = translate_expr true None e in
  if calls <> [] then assert false; e

(* Insert local variables. *)
let insert_bindings bindings =
  let fn (id, ((loc, _, _), _, c_ty)) =
    let id = sym_to_str id in
    if Hashtbl.mem local_vars id then
      not_impl loc "Variable name collision with [%s]." id;
    Hashtbl.add local_vars id (true, c_ty)
  in
  List.iter fn bindings

let collect_bindings () =
  let fn id (is_var, c_ty) acc =
    if is_var then (id, layout_of false c_ty) :: acc else acc
  in
  Hashtbl.fold fn local_vars []

let warn_ignored_attrs so attrs =
  let pp_rc ff {rc_attr_id = id; rc_attr_args = args} =
    Format.fprintf ff "%s(" id.elt;
    match args with
    | arg :: args ->
        let open Location in
        Format.fprintf ff "%s" arg.elt;
        List.iter (fun arg -> Format.fprintf ff ", %s" arg.elt) args;
        Format.fprintf ff ")"
    | []          ->
        Format.fprintf ff ")"
  in
  let fn attr =
    let desc s =
      let open AilSyntax in
      match s with
      | AilSblock(_,_)     -> "a block"
      | AilSgoto(_)        -> "a goto"
      | AilSreturnVoid
      | AilSreturn(_)      -> "a return"
      | AilSbreak          -> "a break"
      | AilScontinue       -> "a continue"
      | AilSskip           -> "a skip"
      | AilSexpr(_)        -> "an expression"
      | AilSif(_,_,_)      -> "an if statement"
      | AilSwhile(_,_)     -> "a while loop"
      | AilSdo(_,_)        -> "a do-while loop"
      | AilSswitch(_,_)    -> "a switch statement"
      | AilScase(_,_)      -> "a case statement"
      | AilSdefault(_)     -> "a default statement"
      | AilSlabel(_,_)     -> "a label"
      | AilSdeclaration(_) -> "a declaration"
      | AilSpar(_)         -> "a par statement"
      | AilSreg_store(_,_) -> "a register store statement"
    in
    let desc =
      match so with
      | Some(s) -> Printf.sprintf " (on %s)" (desc s)
      | None    -> " (on an outer block)"
    in
    Panic.wrn None "Ignored attribute [%a]%s." pp_rc attr desc
  in
  List.iter fn attrs

type stmto = stmt option

type k_data =
  { k_break    : stmto (* What to do in case of break. *)
  ; k_continue : stmto (* What to do in case of break. *)
  ; k_final    : stmto (* What to do at the end of control flow. *)
  ; k_on_case  : bool (* Was this pushed for a case or default? *) }

let k_push : stmto -> stmto -> stmto -> bool -> k_data list -> k_data list =
  fun k_break k_continue k_final k_on_case l ->
    { k_break ; k_continue ; k_final ; k_on_case } :: l

let k_push_final : stmt -> k_data list -> k_data list = fun s l ->
  k_push None None (Some(s)) false l

let k_push_final_case : stmt -> k_data list -> k_data list = fun s l ->
  k_push None None (Some(s)) true l

let rec k_gen : (k_data -> stmto) -> k_data list -> stmt = fun f l ->
  match l with
  | []     -> assert false
  | k :: l -> match f k with None -> k_gen f l | Some(s) -> s

let k_break    = k_gen (fun k -> k.k_break   )
let k_continue = k_gen (fun k -> k.k_continue)
let k_final    = k_gen (fun k -> k.k_final   )

let rec k_pop_cases : k_data list -> k_data list = fun l ->
  match l with
  | []     -> []
  | k :: l -> if k.k_on_case then k_pop_cases l else k :: l

let debug = false

let k_stack_print : out_channel -> k_data list -> unit = fun oc l ->
  let to_str s =
    match Location.(s.elt) with
    | Goto(l)   -> l
    | Return(_) -> "RET"
    | _         -> "???"
  in
  let opt_to_str to_str o =
    match o with
    | None    -> "-"
    | Some(e) -> to_str e
  in
  let print_data d =
    Printf.fprintf oc " (%s,%s,%s,%s)"
      (opt_to_str to_str d.k_break)
      (opt_to_str to_str d.k_continue)
      (opt_to_str to_str d.k_final)
      (if d.k_on_case then "y" else "n")
  in
  Printf.fprintf oc "K-stack:";
  List.iter print_data l;
  Printf.fprintf oc "\n%!"


let translate_block stmts blocks ret_ty =
  let rec trans extra_attrs swstk ks stmts blocks =
    let open AilSyntax in
    if debug then Printf.eprintf "[trans] %a" k_stack_print ks;
    (* End of the block reached. *)
    match stmts with
    | []                                           ->
        if debug then Printf.eprintf "End of [trans] with empty list\n%!";
        let ks = k_pop_cases ks in
        (k_final ks, blocks)
    | (AnnotatedStatement(loc, attrs, s)) :: stmts ->
    let coq_loc = register_loc coq_locs loc in
    let locate e = mkloc e coq_loc in
    let attrs = List.rev (collect_rc_attrs attrs) in
    let attrs_used = ref false in
    let res =
      match s with
      (* Nested block. *)
      | AilSblock(bs, ss)   ->
          insert_bindings bs;
          attrs_used := true; (* Will be attach to the first loop we find. *)
          trans (extra_attrs @ attrs) swstk ks (ss @ stmts) blocks
      (* End of block stuff, assuming [stmts] is empty. *)
      | AilSgoto(l)         ->
          let (_, blocks) = trans extra_attrs swstk ks stmts blocks in
          (locate (Goto(sym_to_str l)), blocks)
      | AilSreturnVoid      ->
          let (_, blocks) = trans extra_attrs swstk ks stmts blocks in
          (locate (Return(noloc (Val(Void)))), blocks)
      | AilSbreak           ->
          (k_break ks, snd (trans extra_attrs swstk ks stmts blocks))
      | AilScontinue        ->
          (k_continue ks, snd (trans extra_attrs swstk ks stmts blocks))
      | AilSreturn(e)       ->
          let blocks = snd (trans extra_attrs swstk ks stmts blocks) in
          let goal_ty =
            match ret_ty with
            | Some(OpInt(_)) -> ret_ty
            | _              -> None
          in
          (trans_expr e goal_ty (fun e -> locate (Return(e))), blocks)
      (* All the other constructors. *)
      | AilSskip            ->
          trans extra_attrs swstk ks stmts blocks
      | AilSexpr(e)         ->
          let (stmt, blocks) = trans extra_attrs swstk ks stmts blocks in
          let incr_or_decr op = op = PostfixIncr || op = PostfixDecr in
          let use_annots () =
            attrs_used := true;
            let fn () = Some(expr_annot attrs) in
            handle_invalid_annot ~loc None fn ()
          in
          let stmt =
            let loc_full = loc_of e in
            match strip_expr e with
            | AilEassert(e)                        ->
                trans_bool_expr e (fun e -> locate (Assert(e, stmt)))
            | AilEassign(e1,e2)                    ->
                let atomic = is_atomic_tc (tc_of e1) in
                let e1 = trans_lval e1 in
                let layout = layout_of_tc (tc_of e) in
                let goal_ty =
                  let ty_opt = op_type_tc_opt (loc_of e) (tc_of e) in
                  match ty_opt with
                  | Some(OpInt(_)) -> ty_opt
                  | _              -> None
                in
                let fn e2 = locate (Assign(atomic, layout, e1, e2, stmt)) in
                trans_expr e2 goal_ty fn
            | AilEunary(op,e) when incr_or_decr op ->
                let atomic = is_atomic_tc (tc_of e) in
                let layout = layout_of_tc (tc_of e) in
                let int_ty =
                  let ty_opt = op_type_tc_opt (loc_of e) (tc_of e) in
                  match ty_opt with
                  | Some(OpInt(int_ty)) -> int_ty
                  | _                   -> assert false (* Badly typed. *)
                in
                let op = match op with PostfixIncr -> AddOp | _ -> SubOp in
                let e1 = trans_lval e in
                let e2 =
                  let one = locate (Val(Int("1", int_ty))) in
                  let use = locate (Use(atomic, layout, e1)) in
                  locate (BinOp(op, OpInt(int_ty), OpInt(int_ty), use, one))
                in
                locate (Assign(atomic, layout, e1, e2, stmt))
            | AilEcall(e,es)                       ->
                let (call, calls) =
                  translate_call In_Stmt loc_full false e es
                in
                let stmt =
                  match call with
                  | Call_atomic_expr(e)             ->
                      let annots = use_annots () in
                      locate (ExprS(annots, locate e, stmt))
                  | Call_simple(e,es)               ->
                      locate (Call(None, e, es, stmt))
                  | Call_atomic_store(layout,e1,e2) ->
                      locate (Assign(true, layout, e1, e2, stmt))
                in
                let fn (loc, id, e, es) stmt =
                  mkloc (Call(id, e, es, stmt)) loc
                in
                List.fold_right fn calls stmt
            | _                                    ->
                let annots = use_annots () in
                trans_expr e None (fun e -> locate (ExprS(annots, e, stmt)))
          in
          (stmt, blocks)
      | AilSif(e,s1,s2)     ->
          warn_ignored_attrs None extra_attrs;
          (* Translate the continuation. *)
          let (blocks, ks) =
            if stmts = [] then (blocks, ks) else
            let id_cont = fresh_block_id () in
            let (s, blocks) = trans [] swstk ks stmts blocks in
            let blocks = add_block id_cont s blocks in
            (blocks, k_push_final (mkloc (Goto(id_cont)) s.loc) ks)
          in
          (* Translate the two branches. *)
          let (blocks, then_goto) =
            let id_then = fresh_block_id () in
            let (s, blocks) =
              trans [] swstk ks [s1] blocks
            in
            let blocks = add_block id_then s blocks in
            (blocks, mkloc (Goto(id_then)) s.loc)
          in
          let (blocks, else_goto) =
            let id_else = fresh_block_id () in
            let (s, blocks) =
              trans [] swstk ks [s2] blocks
            in
            let blocks = add_block id_else s blocks in
            (blocks, mkloc (Goto(id_else)) s.loc)
          in
          translate_bool_expr then_goto else_goto blocks e
      | AilSwhile(e,s)      ->
          let attrs = extra_attrs @ attrs in
          let id_cond = fresh_block_id () in
          let id_body = fresh_block_id () in
          (* Translate the continuation. *)
          let (blocks, goto_cont) =
            let id_cont = fresh_block_id () in
            let (s, blocks) = trans [] swstk ks stmts blocks in
            let blocks = add_block id_cont s blocks in
            (blocks, mkloc (Goto(id_cont)) s.loc)
          in
          (* Translate the body. *)
          let (blocks, goto_body) =
            let break    = Some(goto_cont) in
            let continue = Some(locate (Goto(id_cond))) in
            let ks = k_push break continue continue false ks in
            let (s, blocks) = trans [] swstk ks [s] blocks in
            let blocks = add_block id_body s blocks in
            (blocks, mkloc (Goto(id_body)) s.loc)
          in
          (* Translate the condition. *)
          let (s, blocks) =
            translate_bool_expr goto_body goto_cont blocks e
          in
          let blocks =
            let annots =
              attrs_used := true;
              let fn () = Some(loop_annot attrs) in
              handle_invalid_annot ~loc None fn ()
            in
            add_block ~annots id_cond s blocks
          in
          (locate (Goto(id_cond)), blocks)
      | AilSdo(s,e)         ->
          let attrs = extra_attrs @ attrs in
          let id_cond = fresh_block_id () in
          let id_body = fresh_block_id () in
          (* Translate the continuation. *)
          let (blocks, goto_cont) =
            let id_cont = fresh_block_id () in
            let (s, blocks) = trans [] swstk ks stmts blocks in
            let blocks = add_block id_cont s blocks in
            (blocks, mkloc (Goto(id_cont)) s.loc)
          in
          (* Translate the body. *)
          let (blocks, goto_body) =
            let break    = Some(goto_cont) in
            let continue = Some(noloc (Goto(id_cond))) in (* FIXME loc *)
            let ks = k_push break continue continue false ks in
            if debug then Printf.eprintf "Entering do-while body\n%!";
            let (s, blocks) = trans [] swstk ks [s] blocks in
            if debug then Printf.eprintf "Done with do-while body\n%!";
            let blocks = add_block id_body s blocks in
            (blocks, locate (Goto(id_body)))
          in
          (* Translate the condition. *)
          let (s, blocks) = translate_bool_expr goto_body goto_cont blocks e in
          let blocks =
            let annots =
              attrs_used := true;
              let fn () = Some(loop_annot attrs) in
              handle_invalid_annot ~loc None fn ()
            in
            add_block ~annots id_cond s blocks
          in
          (locate (Goto(id_body)), blocks)
      | AilSswitch(e,s)     ->
          warn_ignored_attrs None extra_attrs;
          (* Translate the continuation. *)
          let (blocks, goto_cont) =
            let id_cont = fresh_block_id () in
            let (s, blocks) = trans [] swstk ks stmts blocks in
            let blocks = add_block id_cont s blocks in
            (blocks, mkloc (Goto(id_cont)) s.loc)
          in
          (* Figure out the integer type of [e]. *)
          let it =
            match op_type_of_tc (loc_of e) (tc_of e) with
            | OpInt(it) -> it
            | _         -> assert false (* Not reachable since well-typed. *)
          in
          (* Translate the body. *)
          let (map, bs, def, blocks) =
            (* We push a fresh entry on the switch data stack. *)
            let swdata =
              let cur_label = fresh_block_id () in
              let next_label = fresh_block_id () in
              let cases_map = [] in
              let default = None in
              ref (cases_map, cur_label, next_label, default)
            in
            let (_, blocks) =
              let break = Some(goto_cont) in
              let ks = k_push break None break false ks in
              if debug then Printf.eprintf "Entering switch body\n%!";
              trans [] (swdata :: swstk) ks [s] blocks
            in
            if debug then Printf.eprintf "Done with switch body\n%!";
            (* Extract the accumulated data. *)
            let (map, cur_label, _, default) = !swdata in
            let (map, bs) = List.split (List.rev map) in
            let map = List.mapi (fun i k -> (k, i)) map in
            let bs =
              let fn r = match !r with None -> assert false | Some s -> s in
              List.map fn bs
            in
            let def =
              match default with
              | None    -> goto_cont
              | Some(s) -> match !s with Some(s) -> s | None -> assert false
            in
            let blocks = add_block cur_label goto_cont blocks in
            (map, bs, def, blocks)
          in
          (* Put everything together. *)
          let fn e = locate (Switch(it, e, map, bs, def)) in
          (trans_expr e None fn, blocks)
      | AilScase(i,s)       ->
          warn_ignored_attrs None extra_attrs;
          (* Get the value of the current case. *)
          let i = fst (integer_constant_to_string loc i) in
          (* Prepare the ref to eventually store the compiled [s]. *)
          let (case_ref, cur_label, next_label) =
            (* Obtain the state of the current switch. *)
            let r = match swstk with [] -> assert false | r :: _ -> r in
            let (map, cur_label, next_label, default) = !r in
            if default <> None then assert false;
            (* Register the current case. *)
            let case_ref = ref None in
            let map = (i, case_ref) :: map in
            r := (map, next_label, fresh_block_id (), None);
            (case_ref, cur_label, next_label)
          in
          (* Translate case body. *)
          let (case_s, blocks) =
            let ks = k_push_final_case (noloc (Goto(next_label))) ks in
            if debug then Printf.eprintf "Entering case body (%s)\n%!" i;
            trans [] swstk ks (s :: stmts) blocks
          in
          if debug then Printf.eprintf "Done with case body (%s)\n%!" i;
          let (case_s, blocks) =
            (locate (Goto(cur_label)), add_block cur_label case_s blocks)
          in
          (* Update the case ref. *)
          case_ref := Some(case_s);
          (case_s, blocks)
      | AilSdefault(s)      ->
          warn_ignored_attrs None extra_attrs;
          (* Prepare the ref to eventually store the compiled [s]. *)
          let (default_ref, cur_label, next_label) =
            (* Obtain the state of the current switch. *)
            let r = match swstk with [] -> assert false | r :: _ -> r in
            let (map, cur_label, next_label, default) = !r in
            if default <> None then assert false;
            (* Register the default case. *)
            let default_ref = ref None in
            r := (map, next_label, fresh_block_id (), Some(default_ref));
            (default_ref, cur_label, next_label)
          in
          (* Translate the default body. *)
          let (default_s, blocks) =
            let ks = k_push_final_case (noloc (Goto(next_label))) ks in
            trans [] swstk ks (s :: stmts) blocks
          in
          let (default_s, blocks) =
            (locate (Goto(cur_label)), add_block cur_label default_s blocks)
          in
          (* Update the default ref. *)
          default_ref := Some(default_s);
          (default_s, blocks)
      | AilSlabel(l,s)      ->
          let (s, blocks) = trans extra_attrs swstk ks (s :: stmts) blocks in
          let blocks = add_block (sym_to_str l) s blocks in
          (locate (Goto(sym_to_str l)), blocks)
      | AilSdeclaration(ls) ->
          let (stmt, blocks) = trans extra_attrs swstk ks stmts blocks in
          let add_decl (id, e) stmt =
            let id = sym_to_str id in
            let ty =
              try snd (Hashtbl.find local_vars id)
              with Not_found -> assert false
            in
            let layout = layout_of false ty in
            let atomic = is_atomic ty in
            let goal_ty = op_type_opt Location_ocaml.unknown ty in
            let fn e =
              let var = noloc (Var(Some(id), false)) in
              noloc (Assign(atomic, layout, var, e, stmt))
            in
            trans_expr e goal_ty fn
          in
          (List.fold_right add_decl ls stmt, blocks)
      | AilSpar(_)          -> not_impl loc "statement par"
      | AilSreg_store(_,_)  -> not_impl loc "statement store"
    in
    if not !attrs_used then warn_ignored_attrs (Some(s)) attrs;
    res
  in
  let initial_ks = k_push_final (noloc (Return(noloc (Val(Void))))) [] in
  trans [] [] initial_ks stmts blocks

(** [translate fname ail] translates typed Ail AST to Coq AST. *)
let translate : string -> typed_ail -> Coq_ast.t = fun source_file ail ->
  (* Get the entry point. *)
  let (entry_point, sigma) =
    match ail with
    | (None    , sigma) -> (None               , sigma)
    | (Some(id), sigma) -> (Some(sym_to_str id), sigma)
  in

  (* Extract the different parts of the AST. *)
  let decls      = sigma.declarations         in
  (*let obj_defs   = sigma.object_definitions   in*)
  let fun_defs   = sigma.function_definitions in
  (*let assertions = sigma.static_assertions    in*)
  let tag_defs   = sigma.tag_definitions      in
  (*let ext_idmap  = sigma.extern_idmap         in*)

  (* Give global access to declarations. *)
  let fun_decls = function_decls decls in
  global_fun_decls := fun_decls;

  (* Give global access to tag declarations *)
  global_tag_defs := tag_defs;

  (* Get the global variables. *)
  let global_vars =
    let fn (id, (_, attrs, decl)) acc =
      match decl with
      | AilSyntax.Decl_object _ ->
         let annots = collect_rc_attrs attrs in
         let fn () = global_annot annots in
         let global_annot = handle_invalid_annot None fn () in
         (sym_to_str id, global_annot) :: acc
      | _                       -> acc
    in
    List.fold_right fn decls []
  in

  (* Get the definition of structs/unions. *)
  let structs =
    let build (id, (attrs, def)) =
      let (fields, struct_is_union) =
        match def with
        | Ctype.StructDef(fields,_) -> (fields, false)
        | Ctype.UnionDef(fields)    -> (fields, true )
      in
      let id = sym_to_str id in
      let struct_annot =
        let attrs = List.rev (collect_rc_attrs attrs) in
        if struct_is_union && attrs <> [] then
          Panic.wrn None "Attributes on unions like [%s] are ignored." id;
        if struct_is_union then Some(SA_union) else
        handle_invalid_annot None (fun _ -> Some(struct_annot attrs)) ()
      in
      let struct_members =
        let fn (id, (attrs, loc, c_ty)) =
          let annot =
            let loc = loc_of_id id in
            let annots = collect_rc_attrs attrs in
            let fn () = Some(member_annot annots) in
            handle_invalid_annot ~loc None fn ()
          in
          let align = align_of c_ty in
          let size = size_of c_ty in
          (id_to_str id, (annot, (align, size), layout_of false c_ty))
        in
        List.map fn fields
      in
      let struct_deps =
        let fn acc (_, (_, _, layout)) =
          let rec extend acc layout =
            match layout with
            | LVoid         -> acc
            | LPtr          -> acc
            | LStruct(id,_) -> id :: acc
            | LInt(_)       -> acc
            | LArray(l,_)   -> extend acc l
          in
          extend acc layout
        in
        let deps = List.rev (List.fold_left fn [] struct_members) in
        List.filter (fun s -> s <> id) (List.sort_uniq String.compare deps)
      in
      let struct_ =
        { struct_name = id ; struct_annot ; struct_deps
        ; struct_is_union ; struct_members }
      in
      (id, struct_)
    in
    List.map build tag_defs
  in

  (* Get the definition of functions. *)
  let functions =
    let open AilSyntax in
    let build (func_name, (ret_ty, args_decl, attrs)) =
      (* Initialise all state. *)
      Hashtbl.reset local_vars; reset_ret_id (); reset_block_id ();
      Hashtbl.reset used_globals; Hashtbl.reset used_functions;
      (* Fist parse that annotations. *)
      let func_annot =
        let fn () = Some(function_annot (collect_rc_attrs attrs)) in
        handle_invalid_annot None fn ()
      in
      (* Then find out if the function is defined or just declared. *)
      match List.find (fun (id, _) -> sym_to_str id = func_name) fun_defs with
      | exception Not_found                                       ->
          (* Function is only declared. *)
          (func_name, FDec(func_annot))
      | (_, (_, _, args, AnnotatedStatement(loc, s_attrs, stmt))) ->
      (* Attributes on the function body are ignored. *)
      warn_ignored_attrs None (List.rev (collect_rc_attrs s_attrs));
      (* Function is defined. *)
      let func_args =
        let fn i (_, c_ty, _) =
          let id = sym_to_str (List.nth args i) in
          Hashtbl.add local_vars id (false, c_ty);
          (id, layout_of true c_ty)
        in
        List.mapi fn args_decl
      in
      let _ =
        (* Collection top level local variables. *)
        match stmt with
        | AilSblock(bindings, _) -> insert_bindings bindings
        | _                      -> not_impl loc "Body not a block."
      in
      let func_init = fresh_block_id () in
      let func_blocks =
        let stmts =
          match stmt with
          | AilSblock(_, stmts) -> stmts
          | _                   -> not_impl loc "Body not a block."
        in
        let ret_ty = op_type_opt Location_ocaml.unknown ret_ty in
        let (stmt, blocks) = translate_block stmts SMap.empty ret_ty in
        add_block func_init stmt blocks
      in
      let func_vars = collect_bindings () in
      let func_deps =
        let globals_used =
          (* We preserve order of declaration. *)
          List.filter (Hashtbl.mem used_globals) (List.map fst global_vars)
        in
        let func_used =
          (* We preserve order of declaration. *)
          let potential = List.map (fun (id, _) -> sym_to_str id) decls in
          List.filter (Hashtbl.mem used_functions) potential
        in
        (globals_used, func_used)
      in
      let func =
        { func_name ; func_annot ; func_args ; func_vars ; func_init
        ; func_deps ; func_blocks }
      in
      (func_name, FDef(func))
    in
    List.map build fun_decls
  in

  { source_file ; entry_point ; global_vars ; structs ; functions }
