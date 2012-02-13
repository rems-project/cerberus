(* In this module we resolves (variable and function) names. At the same time,
   we rewrite those constructs for which the standard explicitly defines an
   equivalent form, e.g. [[ e1 [e2] ]] -> [[ *(e1 + e2) ]]. *)

(* Implementation note: Naming conventions in this module.
   - exp is an expression that still contains syntactic sugar,
   - d_exp has been "desugared".
*)

open CpPervasives

module C = Cabs
module A = CpAil
module AA = CpAilAnnotate

module ST = CpSymbolTable

exception E_Invalid
exception E_Undefined

type id = CpSymbol.t
type id_set = CpSymbol.set

type ('a_e, 'a_s) env = {
  mutable symbol_set : id_set;
  mutable symbol_table : (string, id) CpSymbolTable.t;
  mutable id_map : (id, A.declaration) BatMap.t;
  mutable globals : (id * (id, 'a_e) A.exp) list;
  mutable function_map : (id, (id list * (id, 'a_e, 'a_s) A.stmt)) BatMap.t
}

let zero l = C.CONSTANT (C.CONST_INT (BatBig_int.zero, None)), l
let one  l = C.CONSTANT (C.CONST_INT (BatBig_int.one,  None)), l
let d_zero l = l, A.CONSTANT (C.CONST_INT (BatBig_int.zero, None))
let d_one  l = l, A.CONSTANT (C.CONST_INT (BatBig_int.one,  None))

let subst env l name =
  try
    CpSymbolTable.find name env.symbol_table
  with Not_found ->
    let msg = "Violation of constraint 6.7#3 as described by footnote 91 \
               \"[A]n undeclared identifier is a violation of syntax\" in\n" in
    CpLogger.info (CpPrint.pp_program msg) l;
    raise E_Invalid

(* Straight-forward (boring!) C to A translation. *)
let desugar_unop = function
  | C.MINUS -> A.MINUS
  | C.PLUS -> A.PLUS
  | C.BNOT -> A.BNOT
  | C.POSTFIX_INCR -> A.POSTFIX_INCR
  | C.POSTFIX_DECR -> A.POSTFIX_DECR
  | C.ADDRESS -> A.ADDRESS
  | C.INDIRECTION -> A.INDIRECTION
  | C.PREFIX_INCR | C.PREFIX_DECR | C.NOT ->
      raise_bug "CpCabsToUde.d_unary_op: Invalid argument."

let collect_ids stmt =
  let rec collect ids (_, s) =
    match s with
    | A.DECLARATION defns ->
        List.fold_left (fun ids (id,_) -> BatSet.add id ids) ids defns
    | A.BLOCK _ -> ids
    | _ -> CpAilRewrite.fold_stmt_left collect (fun a _ -> a) ids s
  in
  collect BatSet.empty stmt  


(* [desugar_exp expression] replaces all occurences of array subscripting,
   prefix incrementing and decrementing by a semantically equivalent
   expressions.
   All other cases are simple C to D translations.
*)
let rec desugar_exp env (e, l) =
  let f = desugar_exp env in
  let ft = desugar_type in
  l, match e with
  (* 6.5.2.1#2 Array subscripting, Semantics: "The definition of the
     subscripting operator [...] is that [[ E1[E2] ]] is identical to [[
     ( *((E1)+(E2))) ]]". *)
  | C.INDEX (e1, e2) ->
      A.UNARY(A.INDIRECTION, (l, A.BINARY (C.ARITHMETIC C.ADD, f e1, f e2)))
  (* 6.5.3#2 Unary operators, Semantic says: "The expression [[ ++E ]] is
     equivalent to [[ (E+=1) ]]". *)
  | C.UNARY (C.PREFIX_INCR, e) ->
      A.ASSIGN (Some C.ADD, f e, d_one l)
  (* 6.5.3#2 Unary operators, Semantic: "The prefix [[ -- ]] operator is
     analogous to the prefix [[ ++ ]] operator". *)
  | C.UNARY (C.PREFIX_DECR, e) ->
      A.ASSIGN (Some C.SUB, f e, d_one l)
  (* 6.5.3.3 Unary arithmetic operators, Semantics: "The expression [[ !E ]] is
     equivalent to [[ (E==0) ]]". *)
  | C.UNARY (C.NOT, e) ->
      A.BINARY (C.RELATIONAL C.EQ, d_zero l, f e)
  (* We have covered all interesting cases. All remaining cases are trivial
     transformations. *)
  | C.UNARY (unop, e) ->
      let d_unop = desugar_unop unop in
      A.UNARY(d_unop, f e)
  | C.BINARY (o, e1, e2) -> A.BINARY (o, f e1, f e2)
  | C.ASSIGN (o, e1, e2) -> A.ASSIGN (o, f e1, f e2)
  | C.QUESTION (e1, e2, e3) -> A.QUESTION (f e1, f e2, f e3)
  | C.CAST (t, e) -> A.CAST(ft t, f e)
  | C.CALL (e, es) -> A.CALL (f e, List.map f es)
  | C.CONSTANT c -> A.CONSTANT c
  | C.VARIABLE n -> A.VARIABLE (subst env l n)
  | C.TYPE_SIZEOF t -> A.SIZEOF (ft t)
  | C.TYPE_ALIGNOF t -> A.ALIGNOF (ft t)
(*
  | C.COMPOUND_LITERAL _ ->
      raise_bug "Compound literals are not yet supported."
*)

and desugar_specifier specifiers =
  let module M = BatMap in
  let module MS = CpMultiSet in
  let mset = MS.from_list in
  let map =
    List.fold_left (fun m (x, y) -> BatMap.add x y m) (M.create MS.compare) (
      [mset [C.VOID], A.VOID]
      @ [mset [C.SIGNED; C.CHAR], A.INTEGER (A.SIGNED A.ICHAR)]
      @ [mset [C.UNSIGNED; C.CHAR], A.INTEGER (A.UNSIGNED A.ICHAR)]
      @ List.map (fun s -> mset s, A.INTEGER (A.SIGNED A.SHORT))
        [ [C.SHORT];
          [C.SIGNED; C.SHORT];
          [C.SHORT; C.INT];
          [C.SIGNED; C.SHORT; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.UNSIGNED A.SHORT))
        [ [C.UNSIGNED; C.SHORT];
          [C.UNSIGNED; C.SHORT; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.SIGNED A.INT))
        [  [C.INT];
           [C.SIGNED];
           [C.SIGNED; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.UNSIGNED A.INT))
        [ [C.UNSIGNED];
          [C.UNSIGNED; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.SIGNED A.LONG))
        [ [C.LONG];
          [C.SIGNED; C.LONG];
          [C.LONG; C.INT];
          [C.SIGNED; C.LONG; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.UNSIGNED A.LONG))
        [ [C.UNSIGNED; C.LONG];
          [C.UNSIGNED; C.LONG; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.SIGNED A.LONG_LONG))
        [ [C.LONG; C.LONG];
          [C.SIGNED; C.LONG; C.LONG];
          [C.LONG; C.LONG; C.INT];
          [C.SIGNED; C.LONG; C.LONG; C.INT]
        ]
      @ List.map (fun s -> mset s, A.INTEGER (A.UNSIGNED A.LONG_LONG))
        [ [C.UNSIGNED; C.LONG; C.LONG];
          [C.UNSIGNED; C.LONG; C.LONG; C.INT]
        ]
      @ [mset [C.BOOL], A.INTEGER A.BOOL]) in
  try
    BatMap.find specifiers map
  with Not_found ->
    Printf.printf "Unrecognised specifier!\n";
    raise E_Invalid

and desugar_type t =
  let ft = desugar_type in
  match t with
  | C.BASE (qs, ss) ->
      A.BASE (qs, desugar_specifier ss)
  | C.ARRAY (_, t, Some e) ->
      let size = match e with
        | C.CONSTANT (C.CONST_INT (size, _)), l -> BatBig_int.to_int size
        | _, l ->
            let msg = "We don't support VLAs and moreover the size of an array \
                       must be an integer constant.\n" in
            CpLogger.error (CpPrint.pp_program msg) l;
            raise ERROR in
      A.ARRAY (ft t, size)
(*
      raise_error "Arrays are not yet supported.\n"
*)
  | C.ARRAY (qs, t, None) ->
      raise_error "Arrays are not yet supported.\n"
  | C.FUNCTION (t, decls) ->
      let f ((_, t, sts), l) =
        match desugar_storage l sts with
(* 
        | Some A.REGISTER ->
            raise_error "No support for storage class register."
*)
        | Some _ ->
            let msg = "Violation of constraint 6.7.6.3#2 Function declarators \
                       (including prototypes), Constraints: \"The only \
                       storage-class that shall occur in a parameter \
                       declaration is register.\" in\n" in
            CpLogger.info (CpPrint.pp_program msg) l;
            raise E_Invalid
        | None -> ft t in
      let d_decls = List.map f decls in
      A.FUNCTION (ft t, d_decls)
  | C.POINTER (qs, t) -> A.POINTER (qs, ft t)

and desugar_stmt env (s, l) =
  let fs = desugar_stmt env in
  let fe = desugar_exp env in
  l, match s with
  | C.BLOCK ss ->
      (* Fairly verbose but really quite simple: We open up a new scope,
         transform each statement/declaration in the block and tear down the
         scope again. *)
      let () = env.symbol_table <- ST.create_scope env.symbol_table in
      let d_ss = List.map fs ss in
      let scope = CpSymbolTable.return_scope env.symbol_table in
      let ids = CpSymbolTable.symbols scope in
      let () = env.symbol_table <- ST.destroy_scope env.symbol_table in
      A.BLOCK (ids, d_ss)
  (* We transform all for statements into while statements. *)
  | C.FOR_EXP (e1_opt, e2_opt, e3_opt, s) ->
      let s1 = match e1_opt with
        | Some e1 -> C.EXPRESSION e1, l
        | None    -> C.SKIP, l in
      let e2 = match e2_opt with
        | Some e2 -> e2
        (* According to 6.8.5.3#2 (Iteration statements, Semantics - The for
           statement) an omitted controlling expression is replace by an
           unspecified non-zero integer constant. We believe that the choice, as
           long as representable, does not matter with respect to the
           semantics. Hence, we arbitrarily choose "1" (which can always be
           represented as an object of type int). *)
        | None -> one l in
      let s3 = match e3_opt with
        | Some e3 -> C.EXPRESSION e3, l
        | None -> C.SKIP, l in
      let body = C.BLOCK [s; s3], l in
      let loop = C.WHILE (e2, body), l in    
      let s = C.BLOCK [s1; loop] in
      let _, d_s = fs (s, l) in
      d_s
  | C.FOR_DECL (defns, e2_opt, e3_opt, s) ->
      let require_auto_or_register ((((_, _, storage), l), _), _) =
        if List.exists (fun s -> s <> C.AUTO && s <> C.REGISTER) storage then
          let msg = "Violation of constraint 6.8.5#3 Iteration statements, \
                     Constraints: \"The declaration part of a for statement \
                     shall only declare identifiers for objects having storage \
                     class auto or register\" in\n" in
          CpLogger.info (CpPrint.pp_program msg) l;
          raise E_Invalid in
      let () = List.iter require_auto_or_register defns in
      let s1 = C.DECLARATION defns, l in
      let e2 = match e2_opt with
        | Some e2 -> e2
        (* See comment above. *)
        | None -> one l in
      let s3 = match e3_opt with
        | Some e3 -> C.EXPRESSION e3, l
        | None -> C.SKIP, l in
      let body = C.BLOCK [s; s3], l in
      let loop = C.WHILE (e2, body), l in    
      let s = C.BLOCK [s1; loop] in
      let _, d_s = fs (s, l) in
      d_s
    | C.DECLARATION defns ->
        let d_defns = List.map (desugar_defn env) defns in
        (* We remove all declarations that don't contain an initialiser. *)
        let f = function
          | id, Some d_e, _ -> Some (id, d_e)
          | _,  None,     _ -> None in
        let d_defns = BatList.filter_map f d_defns in
        A.DECLARATION d_defns
  | C.EXPRESSION e -> A.EXPRESSION (fe e)
  | C.IF (e, s1, s2_opt) ->
      let d_s2 = desugar_stmt_opt env l s2_opt in
      A.IF (fe e, fs s1, d_s2)
  | C.WHILE (e, s) -> A.WHILE (fe e, fs s)
  | C.DO (e, s) -> A.DO (fe e, fs s)
  | C.SWITCH (e, s) -> A.SWITCH (fe e, fs s)
  | C.CASE ((e, l), s) ->
      let integer_constant = match e with
        | C.CONSTANT (C.CONST_INT i) -> i
        | _ -> raise_bug "We don't support anything but integer constants as \
                          [[ case ]] labels." in
      A.CASE (integer_constant, fs s)
  | C.DEFAULT s -> A.DEFAULT (fs s)
  | C.LABEL (n, s) -> (* A.LABEL (n, fs s) *)
      raise_error "No support for labeled statements yet.\n"
  | C.RETURN (Some e) -> A.RETURN_EXPRESSION (fe e)
  | C.RETURN None -> A.RETURN_VOID
  | C.GOTO n -> (* A.GOTO n *)
      raise_error "No support for goto yet.\n"
  | C.SKIP -> A.SKIP
  | C.BREAK -> A.BREAK
  | C.CONTINUE -> A.CONTINUE

and desugar_stmt_opt env l = function
  | Some stmt -> desugar_stmt env stmt
  (* Adding or removing a (finite number of) null operation is semantically
     sound since "a null statement [...] performs no operations" (6.8.3#3,
     Expression and null statements, Semantics). *)
  | None -> l, A.SKIP

and register_name env l name =
  let scope = ST.return_scope env.symbol_table in
  if ST.mem name scope then
    let msg = "Violation of constraint 6.7#3 Declarations, Constraints: \"If \
               an identifier has no linkage, there shall be no more than one \
               declaration of the identifier [...]\" in\n" in
    CpLogger.info (CpPrint.pp_program msg) l;
    raise E_Invalid
  else
    let symbol = CpSymbol.fresh_name env.symbol_set name in
    let () =
      env.symbol_table <- ST.add name symbol env.symbol_table in
    symbol

and desugar_storage l = function
  | [] -> None
  | [C.AUTO]   -> Some A.AUTO
  | [C.STATIC] -> Some A.STATIC
  | [C.REGISTER] -> raise_error "No support for storage class register."
  | [C.EXTERN]   -> raise_error "No support for storage class extern."
  | _ ->
      let msg =
        "Violation of constraint 6.7.1#1 Storage-class specifiers, Contraints: \
         \"At most, one storage-class specifier may be given [...]\" in\n" in
      CpLogger.info (CpPrint.pp_program msg) l;
      raise E_Invalid

and desugar_decl env ((name, t, sts), l) =
  let id = register_name env l name in
  let d_st = desugar_storage l sts in
  let d_t = desugar_type t in
  let () = env.id_map <- BatMap.add id (d_t, d_st) env.id_map in
  id

and desugar_function_decl env ((name, t, sts), l) =
  let desugar_function_type env t =
    match t with
    | C.FUNCTION (t, decls) ->
        let f ((name, t, sts), l) (ids, ds) =
          let id = register_name env l name in
          let d_t = desugar_type t in
          let d_st = match desugar_storage l sts with
          (*
            | Some A.REGISTER ->
            raise_error "No support for storage class register."
          *)
            | Some _ ->
                let msg = "Violation of constraint 6.7.6.3#2 Function \
                         declarators (including prototypes), Constraints: \
                         \"The only storage-class that shall occur in a \
                         parameter declaration is register.\" in\n" in
                CpLogger.info (CpPrint.pp_program msg) l;
                raise E_Invalid
            | None -> None in
          let () = env.id_map <- BatMap.add id (d_t, d_st) env.id_map in
          id :: ids, d_t :: ds in
        let formals, d_decls = List.fold_right f decls ([], []) in
        A.FUNCTION (desugar_type t, d_decls), formals
    | _ -> raise_bug "Not a function type." in
  let id = register_name env l name in
  let d_st = desugar_storage l sts in
  let () = env.symbol_table <- ST.create_scope env.symbol_table in
  let d_t, formals = desugar_function_type env t in
  let fn_scope = ST.return_scope env.symbol_table in
  let () = env.symbol_table <- ST.destroy_scope env.symbol_table in
  let () = env.id_map <- BatMap.add id (d_t, d_st) env.id_map in
  let () = env.symbol_table <- ST.push_table fn_scope env.symbol_table in
  id, formals

and desugar_defn env ((d, e_opt), l) =
  let fe = desugar_exp env in
  let id = desugar_decl env d in
  id, BatOption.map fe e_opt, l

let desugar_global_defn env (defn, l) =
  match defn with
  | C.FUNCTION_DEFINITION (decl, s) ->
      let id, formals = desugar_function_decl env decl in
      let d_s = desugar_stmt env s in
      let () = env.symbol_table <- ST.destroy_scope env.symbol_table in
      env.function_map <- BatMap.add id (formals, d_s) env.function_map
  | C.EXTERNAL_DECLARATION defns ->
      let d_defns = List.map (desugar_defn env) defns in
      let f = function
        | id, Some e, l -> id, e
        | id, None,   l -> id, d_zero l in
      let d_defns = List.map f d_defns in
      env.globals <- env.globals @ d_defns

let desugar_program startup global_defns =
  let env = {
    symbol_set = CpSymbol.make ();
    symbol_table = CpSymbolTable.create_scope CpSymbolTable.empty;
    id_map = BatMap.empty;
    globals = [];
    function_map = BatMap.empty
  } in
  let () = List.iter (desugar_global_defn env) global_defns in
  let main =
    try 
      CpSymbolTable.find "main" env.symbol_table
    with Not_found ->
      let msg = "Could not find startup function \"" ^ startup ^ "\".\n" in
      CpLogger.info (fun x -> x) msg;
      raise E_Invalid in
  { A.main;
    A.id_map = env.id_map;
    A.globals = env.globals;
    A.function_map = env.function_map
  }

let desugar startup (name, global_defns) =
  try
    A.Program (desugar_program startup global_defns)
  with
  | E_Undefined -> A.Undefined
  | E_Invalid -> A.Invalid
