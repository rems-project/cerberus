module Make(C : sig include Types.Global_defs val consts : Typed_ast.NameSet.t end) = 
struct

  open Typed_ast

  module T = Trans.Macros(struct let d = C.d let i = C.i end)

  type trans =
      { defs : Def_trans.def_macro list;
        exps : env -> (exp -> exp option) list;
        pats : env -> (Macro_expander.pat_position -> pat -> pat option) list; 
        get_prec : Precedence.op -> Precedence.t; 
        (* Perform the extra translations after the above, left-to-right *)
        extra : (Name.t -> env -> def list -> def list) list}

  let ident =
    { defs = [];
      exps = (fun _ -> []);
      pats = (fun _ -> []);
      get_prec = Precedence.get_prec; 
      extra = []; }

  let tex =
    { defs = [];
      exps = (fun _ -> []);
      pats = (fun _ -> []);
      get_prec = Precedence.get_prec;
      extra = []; }

  let hol =
    { defs = [Def_trans.remove_vals;
              Def_trans.remove_classes;
              Def_trans.remove_opens;
              Def_trans.instance_to_module;
              (*Def_trans.flatten_modules*)];
      exps = 
        (fun env ->
           let module T = T(struct let env = env end) in
             [T.remove_function;
              T.remove_letfun false;
              T.remove_fun_pats true;
              T.remove_list_comprehension;
              T.list_quant_to_set_quant;
              T.remove_set_restr_quant;
              T.remove_class_const;
              T.do_substitutions Target_hol]);
      pats = (fun _ -> []);
      get_prec = Precedence.get_prec_hol;
      extra = [(fun n -> Rename_top_level.rename_nested_module [n]);
               Rename_top_level.flatten_modules]; }

  let ocaml =
    { defs = [Def_trans.remove_vals;
              Def_trans.remove_classes;
              Def_trans.remove_indrelns;
              Def_trans.instance_to_module];
      exps = 
        (fun env ->
           let module T = T(struct let env = env end) in
             [T.hack;
              T.tup_ctor (fun e -> e) Seplist.empty;
              T.do_substitutions Target_ocaml;
              T.remove_class_const;
              T.remove_sets;
              T.remove_list_comprehension;
              T.remove_quant]);
      pats = 
        (fun env ->
           let module T = T(struct let env = env end) in
             []);
      get_prec = Precedence.get_prec_ocaml;
      extra = [(fun n -> Rename_top_level.rename_ocaml [n])]; }

  let isa =
    { defs = [Def_trans.remove_vals;
              Def_trans.remove_opens;
              (*Def_trans.flatten_modules*)];
      exps = 
        (fun env ->
           let module T = T(struct let env = env end) in
             [T.remove_function;
              T.remove_letfun true;
              T.remove_fun_pats true;
              T.list_quant_to_set_quant;
              T.remove_list_comprehension;
              T.remove_set_restr_quant; 
              T.do_substitutions Target_isa]);
      pats = 
        (fun env ->
           let module T = T(struct let env = env end) in
             [T.peanoize_num_pats]);
      get_prec = Precedence.get_prec_isa;
      extra = [(fun n -> Rename_top_level.rename_nested_module [n]);
               Rename_top_level.flatten_modules]; }

  (* TODO: (Trans.coq_synt_records defs) *)
  let coq =
    { defs = [Def_trans.type_annotate_definitions]; 
      exps = 
        (fun env -> 
           let module T = T(struct let env = env end) in
             [T.build_records;
              T.remove_function;
              T.remove_fun_pats false;
(*              T.remove_sets_coq; *)
              T.remove_list_comprehension;
              T.remove_quant]);
      pats = 
        (fun env ->
           let module T = T(struct let env = env end) in
             [T.coq_type_annot_pat_vars]);
      (* TODO: coq_get_prec *)
      get_prec = Precedence.get_prec;
      extra = []; }

  let default_avoid_f = 
    let is_good n = not (NameSet.mem n C.consts) in
      (is_good, 
       (fun n check -> 
          Name.fresh n (fun n -> check n && is_good n)))

  let ocaml_avoid_f = 
    let is_good n = 
      not (NameSet.mem n C.consts) && not (Name.starts_with_upper_letter n)
    in
      (is_good,
       (fun n check -> 
          Name.fresh 
            (if Name.starts_with_upper_letter (Name.from_rope n) then
               Name.to_rope (Name.uncapitalize (Name.from_rope n))
             else 
               n)
            (fun n -> check n && is_good n)))

  let get_avoid_f targ = 
    match targ with
      | Some(Target_ocaml) -> ocaml_avoid_f
      | _ -> default_avoid_f

  let rename_def_params targ =
    let module Ctxt = Exps_in_context(struct 
                                        let check = None
                                        (* TODO *)
                                        let avoid = Some(get_avoid_f targ)
                                      end) 
    in
      fun ((d,lex_skips),l) ->
        let d = 
          match d with
            | Val_def(Rec_def(s1,s2,topt,clauses),tvs) ->
                let clauses = 
                  Seplist.map
                    (fun (n,ps,topt,s,e) ->
                       let (ps,e) =
                         Ctxt.push_subst (Types.TVfmap.empty, Nfmap.empty) ps e
                       in
                         (n,ps,topt,s,e))
                    clauses
                in
                  Val_def(Rec_def(s1,s2,topt,clauses),tvs)
            | Val_def(Let_def(s1,topt,(Let_fun(n,ps,t,s2,e),l)),tvs) ->
                let (ps, e) = 
                  Ctxt.push_subst (Types.TVfmap.empty, Nfmap.empty) ps e
                in
                  Val_def(Let_def(s1,topt,(Let_fun(n,ps,t,s2,e),l)),tvs)
            | Indreln(s1,topt,clauses) ->
                let clauses =
                  Seplist.map
                    (fun (s1,ns,s2,e,s3,n,es) ->
                       (* TODO: rename to avoid conflicts *)
                       (s1,ns,s2,e,s3,n,es))
                    clauses
                in
                  Indreln(s1,topt,clauses)      
            | d -> d
        in
          ((d,lex_skips),l)

  let trans targ ttarg params env m =
    let module Ctxt = struct let avoid = None let check = Some(C.d) end in
    let module M = Macro_expander.Expander(Ctxt) in
    let (defs, end_lex_skips) = m.typed_ast in
    let (env,defs) = 
      Def_trans.process_defs 
        []
        (Def_trans.list_to_mac params.defs)
        (Name.from_rope (Ulib.Text.of_latin1 m.module_name))
        env
        defs
    in
    let defs =
      M.expand_defs
        (* TODO: Move this to a definition macro, and remove the targ
         * argument *)
        (match targ with 
           | None -> defs 
           | Some(targ) -> Def_trans.prune_target_bindings targ defs)
        (Macro_expander.list_to_mac (params.exps env),
         Macro_expander.list_to_bool_mac (params.pats env))
    in
    let defs =
      List.fold_left
        (fun defs e -> e (Name.from_rope (Ulib.Text.of_latin1 m.module_name)) env defs)
        defs
        params.extra
    in
    let rdp = rename_def_params ttarg in
    let defs = List.map rdp defs in
    let defs = 
      match ttarg with
        | None -> defs
        | Some(ttarg) ->
            Target_binding.fix_binding (target_to_mname ttarg) defs 
    in
    let defs = Target_syntax.fix_infix_and_parens params.get_prec defs in
      (* Note: this is the environment from the macro translations, ignoring the
       * extra translations *)
      (env,
       { m with typed_ast = (defs, end_lex_skips) })

  let get_transformation targ =
    match targ with
      | Some(Target_hol) -> 
          (trans (Some(Ast.Target_hol(None))) targ hol,
           get_avoid_f targ)
      | Some(Target_ocaml) -> 
          (* TODO *)
          (trans (Some(Ast.Target_ocaml(None))) targ ocaml,
           get_avoid_f targ)
      | Some(Target_coq) -> 
          (trans (Some(Ast.Target_coq(None))) targ coq,
           get_avoid_f targ)
      | Some(Target_isa) -> 
          (trans (Some(Ast.Target_isa(None))) targ isa,
           get_avoid_f targ)
      | Some(Target_tex) -> 
          (trans (Some(Ast.Target_tex(None))) targ tex,
           get_avoid_f targ)
      | Some(Target_html) -> 
          (trans None targ ident,
           get_avoid_f targ)
      | None -> 
          (trans None targ ident,
           get_avoid_f targ)

end
