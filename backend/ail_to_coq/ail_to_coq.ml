open Ctype
open AilSyntax
open Extra
open Coq_ast
open Coq_pp

type typed_ail = GenTypes.genTypeCategory AilSyntax.ail_program

let not_implemented : string -> 'a = fun s ->
  Printf.eprintf "Feature not implemented: %s.\n%!" s;
  exit 1

(* Short names for common functions. *)
let sym_to_str = Pp_symbol.to_string_pretty
let id_to_str Symbol.(Identifier(_,id)) = id

let translate_int_type i =
  let size_of_base_type signed i =
    match i with
    | Ichar           -> not_implemented "size_of_base_type (IChar)"
    | Short           -> not_implemented "size_of_base_type (Short)"
    | Int_            -> ItInt({size = 2; signed})
    | Long            -> not_implemented "size_of_base_type (LongLong)"
    | LongLong        -> not_implemented "size_of_base_type (LongLong)"
      (* Things defined in the standard libraries *)
    | IntN_t(_)       -> not_implemented "size_of_base_type (IntN_t)"
    | Int_leastN_t(_) -> not_implemented "size_of_base_type (Int_leastN_t)"
    | Int_fastN_t(_)  -> not_implemented "size_of_base_type (Int_fastN_t)"
    | Intmax_t        -> not_implemented "size_of_base_type (Intmax_t)"
    | Intptr_t        -> ItIntptr_t(signed)
  in
  match i with
  | Char        -> not_implemented "translate_layout (Char)"
  | Bool        -> not_implemented "translate_layout (Bool)"
  | Signed(i)   -> size_of_base_type true  i
  | Unsigned(i) -> size_of_base_type false i
  | Enum(sym)   -> not_implemented "translate_layout (Enum)"
  (* Things defined in the standard libraries *)
  | Wchar_t     -> not_implemented "translate_layout (Wchar_t)"
  | Wint_t      -> not_implemented "translate_layout (Win_t)"
  | Size_t      -> ItSize_t
  | Ptrdiff_t   -> not_implemented "translate_layout (Ptrdiff_t)"

let translate_layout Ctype.(Ctype(_, c_ty)) =
  match c_ty with
  | Void               -> not_implemented "translate_layout (Void)"
  | Basic(Integer(i))  -> LInt (translate_int_type i)
  | Basic(Floating(_)) -> not_implemented "translate_layout (Basic float)"
  | Array(_,_)         -> not_implemented "translate_layout (Basic)"
  | Function(_,_,_,_)  -> not_implemented "translate_layout (Function)"
  | Pointer(_,_)       -> LPtr
  | Atomic(_)          -> not_implemented "translate_layout (Atomic)"
  | Struct(sym)        -> LStruct(sym_to_str sym)
  | Union(_)           -> not_implemented "translate_layout (Union)"

(* Hashtable of local variables to distinguish global ones. *)
let local_vars = Hashtbl.create 17

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

let rec ident_of_expr (AnnotatedExpression(_, _, _, expr)) =
  match expr with
  | AilEident(sym)        -> Some(sym_to_str sym)
  | AilEfunction_decay(e) -> ident_of_expr e
  | _                     -> None

let translate_gen_type ty =
  let open GenTypes in
  match ty with
  | GenLValueType(_,c_ty,_)      -> translate_layout c_ty
  | GenRValueType(ty)            ->
  match ty with
  | GenPointer(_,_)              -> LPtr
  | GenVoid                      -> assert false 
  | GenArray(_,_)                -> assert false
  | GenFunction(_,_,_,_)         -> assert false
  | GenStruct(id)                -> LStruct(sym_to_str id)
  | GenUnion(_)                  -> assert false
  | GenAtomic(c_ty)              -> translate_layout c_ty
  | GenBasic(b)                  ->
  match b with
  | GenInteger(Concrete(i))      -> LInt(translate_int_type i)
  | GenInteger(SizeT)            -> LInt(ItSize_t)
  | GenInteger(PtrdiffT)         -> assert false
  | GenInteger(Unknown(_))       -> assert false
  | GenInteger(Promote(_))       -> assert false
  | GenInteger(Usual(_,_))       -> assert false
  | GenFloating(_)               -> assert false

let gen_type_of_expr (AnnotatedExpression(ty, _, _, _)) = ty

let is_const_0 (AnnotatedExpression(_, _, _, e)) =
  match e with
  | AilEconst(c) ->
      begin
        match c with
        | ConstantInteger(IConstant(i,_,_)) -> Z.equal Z.zero i
        | _                                 -> false
      end
  | _            -> false

let rec op_type_of_genIntegerType i =
  let open GenTypes in
  match i with
  | Concrete(i) -> OpInt(translate_int_type i)
  | SizeT       -> assert false
  | PtrdiffT    -> assert false
  | Unknown(_)  -> assert false
  | Promote(i)  -> op_type_of_genIntegerType i (* FIXME cast? *)
  | Usual(i,_)  -> op_type_of_genIntegerType i (* FIXME second one? *)

let op_type_of_genTypeCategory ty =
  let open GenTypes in
  match ty with
  | GenLValueType(_,_,_) -> not_implemented "op_type_of_expr (L)"
  | GenRValueType(ty)    ->
  match ty with
  | GenPointer(_,_)          -> OpPtr
  | GenVoid                  -> assert false 
  | GenArray(_,_)            -> assert false
  | GenFunction(_,_,_,_)     -> assert false
  | GenStruct(_)             -> assert false
  | GenUnion(_)              -> assert false
  | GenAtomic(_)             -> assert false (* FIXME *)
  | GenBasic(GenInteger(i))  -> op_type_of_genIntegerType i
  | GenBasic(GenFloating(_)) -> assert false

let op_type_of_expr (AnnotatedExpression(ty, _, _, _)) =
  op_type_of_genTypeCategory ty

let op_type_of_ctype c_ty =
  op_type_of_genTypeCategory (GenTypes.(GenRValueType(inject_type c_ty)))

let strip_expr (AnnotatedExpression(_,_,_,e)) = e

let rec translate_expr lval (AnnotatedExpression(ty, _, _, e)) =
  let translate = translate_expr lval in
  match e with
  | AilEunary(Address,e)         ->
      let (e, l) = translate e in
      (AddrOf(e), l)
  | AilEunary(Indirection,e)     ->
      let layout = translate_gen_type (gen_type_of_expr e) in
      let (e, l) = translate e in
      (Deref(layout, e), l)
  | AilEunary(op,e)              ->
      let ty = op_type_of_expr e in
      let (e, l) = translate e in
      let op =
        match op with
        | Address     -> assert false (* Handled above. *)
        | Indirection -> assert false (* Handled above. *)
        | Plus        -> not_implemented "unary operator (Plus)"
        | Minus       -> not_implemented "unary operator (Minus)"
        | Bnot        -> not_implemented "unary operator (Bnot)"
        | PostfixIncr -> not_implemented "unary operator (PostfixIncr)"
        | PostfixDecr -> not_implemented "unary operator (PostfixDecr)"
      in
      (UnOp(op, ty, e), l)
  | AilEbinary(e1,op,e2)         ->
      let ty1 = op_type_of_expr e1 in
      let ty2 = op_type_of_expr e2 in
      let (e1, l1) = translate e1 in
      let (e2, l2) = translate e2 in
      let op =
        match op with
        | Eq             -> EqOp
        | Ne             -> NeOp
        | Lt             -> LtOp
        | Gt             -> GtOp
        | Le             -> LeOp
        | Ge             -> GeOp
        | And            -> not_implemented "binary operator (And)"
        | Or             -> not_implemented "binary operator (Or)"
        | Comma          -> not_implemented "binary operator (Comma)"
        | Arithmetic(op) ->
        match op with
        | Mul  -> MulOp
        | Div  -> DivOp
        | Mod  -> not_implemented "binary operator (Mod)"
        | Add  -> AddOp
        | Sub  -> SubOp
        | Shl  -> not_implemented "binary operator (Shl)"
        | Shr  -> not_implemented "binary operator (Shr)"
        | Band -> not_implemented "binary operator (Band)"
        | Bxor -> not_implemented "binary operator (Bxor)"
        | Bor  -> not_implemented "binary operator (Bor)"
      in
      (BinOp(op, ty1, ty2, e1, e2), l1 @ l2)
  | AilEassign(e1,e2)            -> not_implemented "nested assignment"
  | AilEcompoundAssign(e1,op,e2) -> not_implemented "expr compound assign"
  | AilEcond(e1,e2,e3)           -> not_implemented "expr cond"
  | AilEcast(q,c_ty,e)           ->
      begin
        match c_ty with
        | Ctype(_,Pointer(_,Ctype(_,Void))) when is_const_0 e ->
            (Val(Null), [])
        | _                                                   ->
        let ty = op_type_of_expr e in
        let op_ty = op_type_of_ctype c_ty in
        let (e, l) = translate e in
        (UnOp(CastOp(op_ty), ty, e), l)
      end
  | AilEcall(e,es)               ->
      let fun_id =
        match ident_of_expr e with
        | None     -> not_implemented "expr complicated call"
        | Some(id) -> id
      in
      let (es, l) =
        let es_ls = List.map translate es in
        (List.map fst es_ls, List.concat (List.map snd es_ls))
      in
      let ret_id = Some(fresh_ret_id ()) in
      let call = (ret_id, Var(Some(fun_id), true), es) in
      (Var(ret_id, false), l @ [call])
  | AilEassert(e)                -> not_implemented "expr assert nested"
  | AilEoffsetof(c_ty,is)        -> not_implemented "expr offsetof"
  | AilEgeneric(e,gas)           -> not_implemented "expr generic"
  | AilEarray(b,c_ty,oes)        -> not_implemented "expr array"
  | AilEstruct(sym,fs)           -> not_implemented "expr struct"
  | AilEunion(sym,id,eo)         -> not_implemented "expr union"
  | AilEcompound(q,c_ty,e)       -> not_implemented "expr compound"
  | AilEmemberof(e,id)           (*-> not_implemented "expr memberof"*)
  | AilEmemberofptr(e,id)        ->
      let struct_name =
        let open GenTypes in
        match gen_type_of_expr e with
        | GenRValueType(GenPointer(_, Ctype(_, Struct(sym)))) ->
            sym_to_str sym
        | GenRValueType(_                                   ) ->
            assert false
        | GenLValueType(_, Ctype(_, Struct(sym)), _)          ->
            sym_to_str sym
        | GenLValueType(_, _                    , _)          ->
            assert false
      in
      let (e, l) = translate e in
      (GetMember(e, struct_name, id_to_str id), l)
  | AilEbuiltin(b)               -> not_implemented "expr builtin"
  | AilEstr(s)                   -> not_implemented "expr str"
  | AilEconst(c)                 ->
      let c =
        match c with
        | ConstantIndeterminate(c_ty) -> assert false
        | ConstantNull                -> Null
        | ConstantInteger(i)          ->
            begin
              match i with
              | IConstant(i,_,_) ->
                  let it =
                    match op_type_of_genTypeCategory ty with
                    | OpInt(it) -> it
                    | _         -> assert false
                  in
                  Int(Z.to_string i, it)
              | _                -> not_implemented "weird integer constant"
            end
        | ConstantFloating(_)         -> not_implemented "constant float"
        | ConstantCharacter(_)        -> not_implemented "constant char"
        | ConstantArray(_,_)          -> not_implemented "constant array"
        | ConstantStruct(_,_)         -> not_implemented "constant struct"
        | ConstantUnion(_,_,_)        -> not_implemented "constant union"
      in
      (Val(c), [])
  | AilEident(sym)               ->
      let id = sym_to_str sym in
      (Var(Some(id), not (Hashtbl.mem local_vars id)), [])
  | AilEsizeof(q,c_ty)           -> not_implemented "expr sizeof"
  | AilEsizeof_expr(e)           -> not_implemented "expr sizeof_expr"
  | AilEalignof(q,c_ty)          -> not_implemented "expr alignof"
  | AilEannot(c_ty,e)            -> not_implemented "expr annot"
  | AilEva_start(e,sym)          -> not_implemented "expr va_start"
  | AilEva_arg(e,c_ty)           -> not_implemented "expr va_arg"
  | AilEva_copy(e1,e2)           -> not_implemented "expr va_copy"
  | AilEva_end(e)                -> not_implemented "expr va_end"
  | AilEprint_type(e)            -> not_implemented "expr print_type"
  | AilEbmc_assume(e)            -> not_implemented "expr bmc_assume"
  | AilEreg_load(r)              -> not_implemented "expr reg_load"
  | AilErvalue(e)                ->
      let layout = translate_gen_type (gen_type_of_expr e) in
      let (e, l) = translate_expr true e in
      ((if lval then Deref(layout,e) else Use(layout,e)), l)
  | AilEarray_decay(e)           -> not_implemented "expr array_decay"
  | AilEfunction_decay(e)        -> not_implemented "expr function_decay"
        
let strip_statement (AnnotatedStatement(_, s)) = s

let trans_expr e (e_stmt : expr -> stmt) : stmt =
  let (e, calls) = translate_expr false e in
  let fn (id, e, es) stmt = Call(id, e, es, stmt) in
  List.fold_right fn calls (e_stmt e)

let trans_lval e : expr =
  let (e, calls) = translate_expr true e in
  if calls <> [] then assert false; e

(* Insert local variables. *)
let insert_bindings bindings =
  let fn (id, (_, _, c_ty)) =
    let id = sym_to_str id in
    if Hashtbl.mem local_vars id then
      not_implemented ("variable name collision with " ^ id);
    Hashtbl.add local_vars id c_ty;
    (id, translate_layout c_ty)
  in
  List.map fn bindings

let translate_block : 'a -> stmt SMap.t -> stmt * stmt SMap.t =
  let rec trans break continue final stmts blocks =
    let resume goto = match goto with None -> assert false | Some(s) -> s in
    (* End of the block reached. *)
    match stmts with
    | []         -> (resume final, blocks)
    | s :: stmts ->
    match strip_statement s with
    (* Nested block. *)
    | AilSblock(bs, ss)   -> ignore (insert_bindings bs);
                             trans break continue final (ss @ stmts) blocks
    (* End of block stuff, assuming [stmts] is empty. *)
    | AilSgoto(l)         -> (Goto(sym_to_str l)               , blocks)
    | AilSreturnVoid      -> (Return(Val(Void))                , blocks)
    | AilSreturn(e)       -> (trans_expr e (fun e -> Return(e)), blocks)
    | AilSbreak           -> (resume break                     , blocks)
    | AilScontinue        -> (resume continue                  , blocks)
    (* All the other constructors. *)
    | AilSskip            ->
        let (stmt, blocks) = trans break continue final stmts blocks in
        (SkipS(stmt), blocks)
    | AilSexpr(e)         ->
        let (stmt, blocks) = trans break continue final stmts blocks in
        let ty = gen_type_of_expr e in
        let stmt =
          match strip_expr e with
          | AilEassert(e)     ->
              trans_expr e (fun e -> Assert(e, stmt))
          | AilEassign(e1,e2) ->
              let e1 = trans_lval e1 in 
              let layout = translate_gen_type ty in
              trans_expr e2 (fun e2 -> Assign(layout, e1, e2, stmt))
          | AilEcall(e,es)    ->
              let translate = translate_expr false in
              let fun_id =
                match ident_of_expr e with
                | None     -> not_implemented "expr complicated call"
                | Some(id) -> id
              in
              let (es, l) =
                let es_ls = List.map translate es in
                (List.map fst es_ls, List.concat (List.map snd es_ls))
              in
              let stmt = Call(None, Var(Some(fun_id), true), es, stmt) in
              let fn (id, e, es) stmt = Call(id, e, es, stmt) in
              List.fold_right fn l stmt
          | _                 ->
              trans_expr e (fun e -> ExprS(e, stmt))
        in
        (stmt, blocks)
    | AilSif(e,s1,s2)     ->
        let (final, blocks) =
          (* Last statement, keep the final goto. *)
          if stmts = [] then (final, blocks) else
          (* Statements after the if in their own block. *)
          let (stmt, blocks) = trans break continue final stmts blocks in
          let block_id = fresh_block_id () in
          (Some(Goto(block_id)), SMap.add block_id stmt blocks)
        in
        let (s1, blocks) = trans break continue final [s1] blocks in
        let (s2, blocks) = trans break continue final [s2] blocks in
        (trans_expr e (fun e -> If(e, s1, s2)), blocks)
    | AilSwhile(e,s)      ->
        let id_body = fresh_block_id () in
        let id_cont = fresh_block_id () in
        (* Translate the continuation. *)
        let blocks =
          let (stmt, blocks) = trans break continue final stmts blocks in
          SMap.add id_cont stmt blocks
        in
        (* Translate the body. *)
        let blocks =
          let break    = Some(Goto(id_cont)) in
          let continue = Some(Goto(id_body)) in
          let (stmt, blocks) = trans break continue continue [s] blocks in
          let stmt = trans_expr e (fun e -> If(e, stmt, Goto(id_cont))) in
          SMap.add id_body stmt blocks
        in
        (Goto(id_body), blocks)
    | AilSdo(s,e)         ->
        let id_body = fresh_block_id () in
        let id_cont = fresh_block_id () in
        (* Translate the continuation. *)
        let blocks =
          let (stmt, blocks) = trans break continue final stmts blocks in
          SMap.add id_cont stmt blocks
        in
        (* Translate the body. *)
        let blocks =
          let break    = Some(Goto(id_cont)) in
          let continue = Some(Goto(id_body)) in
          let stmt =
            trans_expr e (fun e -> If(e, Goto(id_body), Goto(id_cont)))
          in
          let (stmt, blocks) = trans break continue (Some stmt) [s] blocks in
          SMap.add id_body stmt blocks
        in
        (Goto(id_body), blocks)
    | AilSswitch(_,_)     -> not_implemented "statement switch"
    | AilScase(_,_)       -> not_implemented "statement case"
    | AilSdefault(_)      -> not_implemented "statement default"
    | AilSlabel(l,s)      ->
        let (stmt, blocks) = trans break continue final (s :: stmts) blocks in
        (Goto(sym_to_str l), SMap.add (sym_to_str l) stmt blocks)
    | AilSdeclaration(ls) ->
        let (stmt, blocks) = trans break continue final stmts blocks in
        let add_decl (id, e) stmt =
          let id = sym_to_str id in
          let layout =
            try translate_layout (Hashtbl.find local_vars id)
            with Not_found -> assert false
          in
          trans_expr e (fun e -> Assign(layout, Var(Some(id),false), e, stmt))
        in
        (List.fold_right add_decl ls stmt, blocks)
    | AilSpar(_)          -> not_implemented "statement par"
    | AilSreg_store(_,_)  -> not_implemented "statement store"
  in
  trans None None (Some(Return(Val(Void))))
 
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

  (* Get the global variables. *)
  let global_vars =
    let fn (id, (_, decl)) acc =
      match decl with
      | Decl_object _ -> sym_to_str id :: acc
      | _             -> acc
    in
    List.fold_right fn decls []
  in

  (* Get the definition of structs. *)
  let structs =
    let build (id, def) =
      let struct_name = sym_to_str id in
      let struct_members =
        match def with
        | UnionDef(_)  -> not_implemented "union"
        | StructDef(l) ->
            let fn (id, (_, c_ty)) =
              (id_to_str id, translate_layout c_ty)
            in
            List.map fn l
      in
      (struct_name, {struct_name ; struct_members})
    in
    List.map build tag_defs
  in

  (* Get the definition of functions. *)
  let functions =
    let build (id, (_, _, args, AnnotatedStatement(_, stmt))) =
      Hashtbl.reset local_vars; reset_ret_id (); reset_block_id ();
      let func_name = sym_to_str id in
      let func_args =
        let args_decl =
          let rec find l =
            match l with
            | []                     -> assert false
            | (id_decl, (_, d)) :: l ->
            if sym_to_str id_decl <> func_name then find l else
            match d with
            | Decl_function(_,_,args,_,_,_) -> args
            | Decl_object(_,_,_)            -> assert false
          in
          find decls
        in
        let fn i (_, c_ty, _) =
          let id = sym_to_str (List.nth args i) in
          Hashtbl.add local_vars id c_ty;
          (id, translate_layout c_ty)
        in
        List.mapi fn args_decl
      in
      let func_vars =
        match stmt with
        | AilSblock(bindings, _) -> insert_bindings bindings
        | _                      -> not_implemented "body not a block"
      in
      let func_init = fresh_block_id () in
      let func_blocks =
        let stmts =
          match stmt with
          | AilSblock(_, stmts) -> stmts
          | _                   -> not_implemented "body not a block"
        in
        let (stmt, blocks) = translate_block stmts SMap.empty in
        SMap.add func_init stmt blocks
      in
      (func_name, {func_name; func_args; func_vars; func_init; func_blocks})
    in
    List.map build fun_defs
  in

  { source_file ; entry_point ; global_vars ; structs ; functions }

(** [run fname ail] translates typed ail AST to Coq AST and then pretty prints
    the result on the standard output. *)
let run : string -> typed_ail -> unit = fun fname ail ->
  let coq = translate fname ail in
  Format.printf "%a@." Coq_pp.pp_ast coq
