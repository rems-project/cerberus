open Ctype
open AilSyntax

type typed_ail = GenTypes.genTypeCategory AilSyntax.ail_program

let not_implemented : string -> 'a = fun s ->
  Printf.eprintf "Feature not implemented: %s.\n%!" s;
  exit 1

(** [section_name fname] builds a reasonable Coq section name from a file. The
    slash, dash and dot characters are replaced by underscores. Note that this
    function will miserably fail on weird file names (e.g., ["A file.c"]). *)
let section_name : string -> string = fun fname ->
  let cleanup name c = String.concat "_" (String.split_on_char c name) in
  List.fold_left cleanup fname ['/'; '-'; '.']

let run : string -> typed_ail -> unit = fun fname (entry_point, sigma) ->
  (* Extract the different parts of the AST. *)
  let decls      = sigma.declarations         in
  (*let obj_defs   = sigma.object_definitions   in*)
  let fun_defs   = sigma.function_definitions in
  (*let assertions = sigma.static_assertions    in*)
  let tag_defs   = sigma.tag_definitions      in
  (*let ext_idmap  = sigma.extern_idmap         in*)

  (* Formatting utilities. *)
  let indent = ref 0 in
  let line fmt =
    let s = String.make (2 * !indent) ' ' in
    Printf.printf ("%s" ^^ fmt ^^ "\n%!") s
  in
  let comment fmt = line ("(* " ^^ fmt ^^ " *)") in
  let skip_line () = Printf.printf "\n%!" in

  (* Short names for common functions. *)
  let sym_to_str = Pp_symbol.to_string_pretty in
  let id_to_str Symbol.(Identifier(_,id)) = id in

  (* Layout from ctype. *)
  let layout_to_str Ctype.(Ctype(_, c_ty)) =
    match c_ty with
    | Pointer(_,_) -> "LPtr"
    | Struct(sym)  -> "layout_of struct_" ^ sym_to_str sym
    | _            -> not_implemented "some c_type" (* TODO *)
  in

  (* Printing some header. *)
  line "From refinedc.lang Require Export notation.";
  line "Set Default Proof Using \"Type\".";
  skip_line ();

  (* Printing generation data and entry point in a comment. *)
  let entry_point =
    match entry_point with
    | None     -> ""
    | Some(id) -> Printf.sprintf ", entry point [%s]" (sym_to_str id)
  in
  comment "Generated from [%s]%s." fname entry_point;

  (* Opening the section. *)
  let sect = section_name fname in
  line "Section %s." sect;
  incr indent;

  (* Declaration of objects (global variable) in the context. *)
  let decl_obj (id, (_, decl)) =
    match decl with
    | Decl_object _ -> line "Context (%s : loc)." (sym_to_str id);
    | _             -> ()
  in
  comment "Global variables.";
  List.iter decl_obj decls;

  (* Declaration of functions in the context. *)
  skip_line ();
  let decl_obj (id, (_, decl)) =
    match decl with
    | Decl_function _ -> line "Context (%s : loc)." (sym_to_str id);
    | _               -> ()
  in
  comment "Functions.";
  List.iter decl_obj decls;

  (* Definition of structs. *)
  let tag_def (id, def) =
    let id = sym_to_str id in
    skip_line ();
    comment "Definition of struct [%s]." id;
    line "Program Definition struct_%s := {|" id;
    incr indent;
    line "sl_members := [";
    incr indent;
    begin
      match def with
      | UnionDef(_)  -> not_implemented "union" (* TODO *)
      | StructDef(l) ->
          let n = List.length l in
          let fn i (id, (_, c_ty)) =
            let sc = if i = n - 1 then "" else ";" in
            line "(%S, %s)%s" (id_to_str id) (layout_to_str c_ty) sc
          in
          List.iteri fn l
    end;
    decr indent;
    line "];";
    decr indent;
    line "|}.";
    line "Next Obligation. do ! constructor; set_solver. Qed."
  in
  List.iter tag_def tag_defs;

  (* Definition of functions. *)
  let fun_def (id, (_, _, args, AnnotatedStatement(_, stmt))) =
    (* local variables and arguments with their types. *)
    let local_vars = Hashtbl.create 17 in
    let id = sym_to_str id in
    let args_decl =
      let rec find l =
        match l with
        | []                     -> assert false
        | (id_decl, (_, d)) :: l ->
        if sym_to_str id_decl <> id then find l else
        match d with
        | Decl_function(_,_,args,_,_,_) -> args
        | Decl_object(_,_,_)            -> assert false
      in
      find decls
    in
    skip_line ();
    comment "Definition of function [%s]." id;
    line "Definition impl_%s : function := {|" id;
    incr indent;
    line "f_args := [";
    incr indent;
    begin
      let n = List.length args_decl in
      let fn i (_, c_ty, _) =
        let id = sym_to_str (List.nth args i) in
        Hashtbl.add local_vars id c_ty;
        let sc = if i = n - 1 then "" else ";" in
        line "(%S, %s)%s" id (layout_to_str c_ty) sc
      in
      List.iteri fn args_decl
    end;
    decr indent;
    line "];";
    line "f_local_vars := [";
    incr indent;
    begin
      let bindings =
        match stmt with
        | AilSblock(bindings, _) -> bindings
        | _                      -> not_implemented "body not a block"
      in
      let n = List.length bindings in
      let fn i (id, (_, _, c_ty)) =
        Hashtbl.add local_vars (sym_to_str id) c_ty;
        let sc = if i = n - 1 then "" else ";" in
        line "(%S, %s)%s" (sym_to_str id) (layout_to_str c_ty) sc
      in
      List.iteri fn bindings
    end;
    decr indent;
    line "];";
    line "f_init := \"init\";";
    line "f_code := {[ \"init\" :=";
    incr indent;
    begin
      let stmts =
        match stmt with
        | AilSblock(_, stmts) -> stmts
        | _                   -> not_implemented "body not a block"
      in
      let rec ident_of_expr (AnnotatedExpression(_, _, _, expr)) =
        match expr with
        | AilEident(sym)        -> Some(sym_to_str sym)
        | AilEfunction_decay(e) -> ident_of_expr e
        | _                     -> None
      in
      let gen_type_to_str ty =
        let open GenTypes in
        match ty with
        | GenLValueType(_,c_ty,_)        -> layout_to_str c_ty
        | GenRValueType(GenPointer(_,_)) -> "LPtr"
        | GenRValueType(_)               -> "..."
      in
      let gen_type_of_expr (AnnotatedExpression(ty, _, _, _)) = ty in
      let fresh_ret_id =
        let c = ref (-1) in
        fun () -> incr c; "$r" ^ string_of_int !c
      in
      let rec expr_to_str top lval (AnnotatedExpression(ty, _, _, expr)) =
        let spr = Printf.sprintf in
        let e2s = expr_to_str false lval in
        let e2s_lval = expr_to_str false true in
        match expr with
        | AilEunary(Address,e)         ->
            spr "&(%s)" (e2s e)
        | AilEunary(op,e)              ->
            spr "unary (...) (%s)" (e2s e)
        | AilEbinary(e1,Eq,e2)         ->
            spr "(%s) = (%s)" (e2s e1) (e2s e2)
        | AilEbinary(e1,Ne,e2)         ->
            spr "(%s) != (%s)" (e2s e1) (e2s e2)
        | AilEbinary(e1,op,e2)         ->
            spr "binary (%s) (...) (%s)" (e2s e1) (e2s e2)
        | AilEassign(e1,e2)            ->
            let ty = gen_type_of_expr e2 in (* FIXME *)
            spr "%s <-{%s} %s" (e2s_lval e1) (gen_type_to_str ty) (e2s e2)
        | AilEcompoundAssign(e1,op,e2) -> not_implemented "expr compound assign"
        | AilEcond(e1,e2,e3)           -> not_implemented "expr cond"
        | AilEcast(q,c_ty,e)           ->
            begin
              match c_ty with
              | Ctype(_,Pointer(_,Ctype(_,Void))) when e2s e = "0" -> "NULL"
              | _                                                  ->
                  not_implemented "expr some cast"
            end
        | AilEcall(e,es)               ->
            let fun_id =
              match ident_of_expr e with
              | None     -> not_implemented "expr complicated call"
              | Some(id) -> id
            in
            let es = List.map e2s es in
            let call ret_id =
              spr "%S <- %s with [%s]" ret_id fun_id (String.concat "; " es)
            in
            if top then call "_" else
            let ret_id = fresh_ret_id () in
            line "%s;" (call ret_id); spr "%S" ret_id
        | AilEassert(e)                -> not_implemented "expr assert nested"
        | AilEoffsetof(c_ty,is)        -> not_implemented "expr offsetof"
        | AilEgeneric(e,gas)           -> not_implemented "expr generic"
        | AilEarray(b,c_ty,oes)        -> not_implemented "expr array"
        | AilEstruct(sym,fs)           -> not_implemented "expr struct"
        | AilEunion(sym,id,eo)         -> not_implemented "expr union"
        | AilEcompound(q,c_ty,e)       -> not_implemented "expr compound"
        | AilEmemberof(e,id)           -> not_implemented "expr memberof"
        | AilEmemberofptr(e,id)        ->
            let struct_name =
              let open GenTypes in
              match gen_type_of_expr e with
              | GenRValueType(GenPointer(_, Ctype(_, Struct(sym)))) ->
                  "struct_" ^ sym_to_str sym
              | _                                                   ->
                  assert false
            in
            spr "(%s) at{%s} %S" (e2s e) struct_name (id_to_str id)
        | AilEbuiltin(b)               -> not_implemented "expr builtin"
        | AilEstr(s)                   -> not_implemented "expr str"
        | AilEconst(c)                 ->
            begin
              match c with
              | ConstantNull                      -> "NULL"
              | ConstantInteger(IConstant(i,_,_)) -> Z.to_string i
              | _                                 ->
                  not_implemented "expr constant of some form"
            end
        | AilEident(sym)               ->
            let id = sym_to_str sym in
            if Hashtbl.mem local_vars id then spr "%S" id else id
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
            let ty = gen_type_of_expr e in
            let op = if lval then "!" else "use" in
            spr "%s{%s} (%s)" op (gen_type_to_str ty) (e2s_lval e)
        | AilEarray_decay(e)           -> not_implemented "expr array_decay"
        | AilEfunction_decay(e)        -> not_implemented "expr function_decay"
      in
      (* Insert a return void when necessary. *)
      let rec needs_ret stmts =
        match stmts with
        | []                                     -> true
        | AnnotatedStatement(loc, stmt) :: stmts ->
        let last = stmts = [] in
        match stmt with
        | AilSblock(_,s)  when last -> needs_ret stmts
        | AilSif(e,s1,s2) when last -> needs_ret [s1] || needs_ret [s2]
        | AilSreturnVoid            -> false (* What if not last? *)
        | AilSreturn(_)             -> false (* What if not last? *)
        | AilSgoto(_)               -> false (* What if not last? *)
        | _                         -> needs_ret stmts
      in
      let stmts =
        if not (needs_ret stmts) then stmts else
        stmts @ [AnnotatedStatement(Location_ocaml.unknown, AilSreturnVoid)]
      in
      let rec fn (AnnotatedStatement(_, stmt)) =
        match stmt with
        | AilSblock([],stmts) -> List.iter fn stmts
        | AilSblock(_,_)      -> not_implemented "statement block"
        | AilSskip            -> () (* line "skip;" *)
        | AilSexpr(e)         ->
            begin
              match e with
              | AnnotatedExpression(_,_,_,AilEassert(e)) ->
                  begin
                    match e with
                    | AnnotatedExpression(_,_,_,AilEbinary(e1,Ne,e2)) ->
                        line "if: %s = %s then Goto \"abort\" else"
                          (expr_to_str false false e1)
                          (expr_to_str false false e2)
                    | _                                               ->
                        line "if: UnOp NegOp (%s) then Goto \"abort\" else"
                          (expr_to_str false false e)
                  end
              | _                                        ->
                  line "%s;" (expr_to_str true false e)
            end
        | AilSif(e,s1,s2)     ->
            line "if: %s then" (expr_to_str false false e);
            incr indent; fn s1; decr indent;
            line "else";
            incr indent; fn s2; decr indent
        | AilSwhile(e,s)      -> not_implemented "statement while"
        | AilSdo(e,s)         -> not_implemented "statement do"
        | AilSbreak           -> not_implemented "statement break"
        | AilScontinue        -> not_implemented "statement continue"
        | AilSreturnVoid      -> line "Return VOID"
        | AilSreturn(e)       -> line "Return (%s)" (expr_to_str false false e)
        | AilSswitch(e,s)     -> not_implemented "statement switch"
        | AilScase(i,s)       -> not_implemented "statement case"
        | AilSdefault(s)      -> not_implemented "statement default"
        | AilSlabel(l,s)      -> not_implemented "statement label"
        | AilSgoto(l)         -> not_implemented "statement goto"
        | AilSdeclaration(ls) ->
            let decl (id, e) =
              let id = sym_to_str id in
              let c_ty =
                try Hashtbl.find local_vars id with Not_found -> assert false
              in
              line "%S <-{%s} %s;" id (layout_to_str c_ty)
                (expr_to_str true false e)
            in
            List.iter decl ls
        | AilSpar(ls)         -> not_implemented "statement par"
        | AilSreg_store(r,e)  -> not_implemented "statement store"
      in
      List.iter fn stmts
    end;
    decr indent;
    line "]}%%E;";
    decr indent;
    line "|}."
  in
  List.iter fun_def fun_defs;

  (* Closing the section. *)
  decr indent;
  line "End %s." sect


(* Reference output **********************************************************

Definition mpool_init : function := {|
  f_args := [("p", LPtr)];
  f_local_vars := [];
  f_init := "init";
  f_code := {[ "init" :=
                 (!{LPtr}"p") at{struct_mpool} "entry_list" <-{LPtr} NULL;
                 Return VOID ]}%E;
|}.

Definition mpool_get : function := {|
  f_args := [("p", LPtr)];
  f_local_vars := [("entry", LPtr)];
  f_init := "init";
  f_code := {[ "init" :=
    if: use{LPtr} (!{LPtr} "p" at{struct_mpool} "entry_list") = NULL
    then Return NULL else
    "entry" <-{LPtr} use{LPtr} (!{LPtr} "p" at{struct_mpool} "entry_list");
    (!{LPtr} "p" at{struct_mpool} "entry_list") <-{LPtr}
      use{LPtr} (!{LPtr} "entry" at{struct_mpool_entry} "next");
    Return (use{LPtr} "entry") ]}%E;
|}.

Definition mpool_put : function := {|
  f_args := [("p", LPtr); ("ptr", LPtr)];
  f_local_vars := [("e", LPtr)];
  f_init := "init";
  f_code := {[ "init" :=
                 "e" <-{LPtr} use{LPtr} "ptr";
                 (!{LPtr} "e" at{struct_mpool_entry} "next") <-{LPtr}
                   use{LPtr} (!{LPtr} "p" at{struct_mpool} "entry_list");
                 (!{LPtr} "p" at{struct_mpool} "entry_list") <-{LPtr}
                   use{LPtr} "e";
                 Return VOID ]}%E;
|}.

Definition main : function := {|
  f_args := [];
  f_local_vars := [("p", layout_of struct_mpool); ("p1", LPtr); ("p2", LPtr)];
  f_init := "init";
  f_code := {[ "init" :=
                 "_" <- mpool_init with [& "p"];
                 "_" <- mpool_put with [& "p"; &e1 ];
                 "_" <- mpool_put with [& "p"; &e2 ];
                 "r1" <- mpool_get with [& "p" ];
                 "p1" <-{LPtr} "r1";
                 if: use{LPtr} "p1" = NULL then Goto "abort" else
                 "r2" <- mpool_get with [& "p" ];
                 "p2" <-{LPtr} "r2";
                 if: use{LPtr} "p2" = NULL then Goto "abort" else
                 Return VOID ]}%E;
|}.
*****************************************************************************)
