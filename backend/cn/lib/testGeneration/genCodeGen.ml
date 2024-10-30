module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module BT = BaseTypes
module IT = IndexTerms
module LC = LogicalConstraints
module GT = GenTerms
module GR = GenRuntime
module SymSet = Set.Make (Sym)

let mk_expr = Utils.mk_expr

let mk_stmt = Utils.mk_stmt

let bt_to_ctype (pred_sym : Sym.t) (bt : BT.t) : C.ctype =
  let pred_sym = Some pred_sym in
  CtA.bt_to_ail_ctype ~pred_sym bt


let name_of_bt (pred_sym : Sym.t) (bt : BT.t) : string =
  let ct = bt_to_ctype pred_sym bt in
  let ct' =
    match bt_to_ctype pred_sym bt with
    | Ctype (_, Pointer (_, ct')) -> ct'
    | _ -> failwith ""
  in
  let default =
    CF.Pp_utils.to_plain_string
      (CF.Pp_ail.pp_ctype ~executable_spec:true C.no_qualifiers ct')
  in
  Utils.get_typedef_string ct |> Option.value ~default


let _str_name_of_bt (pred_sym : Sym.t) (bt : BT.t) : string =
  name_of_bt pred_sym bt |> String.split_on_char ' ' |> String.concat "_"


let compile_it (sigma : CF.GenTypes.genTypeCategory A.sigma) (name : Sym.t) (it : IT.t) =
  CtA.cn_to_ail_expr sigma.cn_datatypes [] (Some name) it


let compile_lc (sigma : CF.GenTypes.genTypeCategory A.sigma) (lc : LC.t) =
  CtA.cn_to_ail_logical_constraint sigma.cn_datatypes [] lc


let rec compile_term
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (name : Sym.t)
  (tm : GR.term)
  : A.bindings
    * CF.GenTypes.genTypeCategory A.statement_ list
    * CF.GenTypes.genTypeCategory A.expression
  =
  let loc = Locations.other __LOC__ in
  match tm with
  | Uniform { bt; sz } ->
    ( [],
      [],
      A.(
        mk_expr
          (AilEcall
             ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_UNIFORM")),
               List.map
                 mk_expr
                 [ AilEident (Sym.fresh_named (name_of_bt name bt));
                   AilEconst (ConstantInteger (IConstant (Z.of_int sz, Decimal, None)))
                 ] ))) )
  | Pick { bt; choice_var; choices; last_var } ->
    let var = Sym.fresh () in
    let bs, ss =
      List.split
        (List.mapi
           (fun i (_, gr) ->
             let bs, ss, e = compile_term sigma name gr in
             ( bs,
               A.(
                 [ AilSexpr
                     (mk_expr
                        (AilEcall
                           ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_PICK_CASE_BEGIN")),
                             List.map
                               mk_expr
                               [ AilEconst
                                   (ConstantInteger
                                      (IConstant (Z.of_int i, Decimal, None)))
                               ] )))
                 ]
                 @ ss
                 @ [ AilSexpr
                       (mk_expr
                          (AilEcall
                             ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_PICK_CASE_END")),
                               [ mk_expr (AilEident var); e ] )))
                   ]) ))
           choices)
    in
    ( List.flatten bs,
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_PICK_BEGIN")),
                    List.map
                      mk_expr
                      [ AilEident (Sym.fresh_named (name_of_bt name bt));
                        AilEident var;
                        AilEident choice_var;
                        AilEident last_var
                      ]
                    @ List.flatten
                        (List.mapi
                           (fun i (w, _) ->
                             List.map
                               mk_expr
                               [ AilEconst
                                   (ConstantInteger
                                      (IConstant (Z.of_int w, Decimal, None)));
                                 AilEconst
                                   (ConstantInteger
                                      (IConstant (Z.of_int i, Decimal, None)))
                               ])
                           choices) )))
        ]
      @ List.flatten ss
      @ [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_PICK_END")),
                    [ mk_expr (AilEident choice_var) ] )))
        ],
      A.(mk_expr (AilEident var)) )
  | Alloc { bytes = it } ->
    let alloc_sym = Sym.fresh_named "cn_gen_alloc" in
    let b, s, e = compile_it sigma name it in
    (b, s, mk_expr (AilEcall (mk_expr (AilEident alloc_sym), [ e ])))
  | Call { fsym; iargs; oarg_bt } ->
    let sym = GenUtils.get_mangled_name (fsym :: List.map fst iargs) in
    let es = iargs |> List.map snd |> List.map (fun x -> A.(mk_expr (AilEident x))) in
    let x = Sym.fresh () in
    let b = Utils.create_binding x (bt_to_ctype fsym oarg_bt) in
    let wrap_to_string (sym : Sym.t) =
      A.(
        AilEcast
          ( C.no_qualifiers,
            C.pointer_to_char,
            mk_expr (AilEstr (None, [ (Locations.other __LOC__, [ Sym.pp_string sym ]) ]))
          ))
    in
    let from_vars = iargs |> List.map fst |> List.map wrap_to_string in
    let to_vars = iargs |> List.map snd |> List.map wrap_to_string in
    let macro_call name vars =
      A.AilSexpr
        (mk_expr
           (AilEcall (mk_expr (AilEident (Sym.fresh_named name)), List.map mk_expr vars)))
    in
    ( [ b ],
      [ AilSdeclaration [ (x, Some (mk_expr (AilEcall (mk_expr (AilEident sym), es)))) ];
        macro_call "CN_GEN_CALL_FROM" from_vars;
        macro_call "CN_GEN_CALL_TO" to_vars
      ],
      mk_expr (AilEident x) )
  | Asgn { pointer; offset; sct; value; last_var; rest } ->
    let tmp_sym = Sym.fresh () in
    let bt = BT.Bits (Unsigned, 64) in
    let offset =
      if BT.equal (IT.bt offset) bt then
        offset
      else
        IT.cast_ bt offset (Locations.other __LOC__)
    in
    let b1, s1, e1 = compile_it sigma name offset in
    let b2, s2, AnnotatedExpression (_, _, _, e2_) = compile_it sigma name value in
    let b3 = [ Utils.create_binding tmp_sym C.(mk_ctype_pointer no_qualifiers void) ] in
    let s3 =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_ASSIGN")),
                    [ mk_expr (AilEident pointer);
                      e1;
                      mk_expr
                        (AilEident
                           (Sym.fresh_named
                              (CF.Pp_utils.to_plain_string
                                 (CF.Pp_ail.pp_ctype
                                    ~executable_spec:true
                                    C.no_qualifiers
                                    (Sctypes.to_ctype sct)))));
                      mk_expr (CtA.wrap_with_convert_from e2_ (IT.bt value));
                      mk_expr (AilEident (Sym.fresh ()));
                      mk_expr
                        (AilEcast
                           ( C.no_qualifiers,
                             C.pointer_to_char,
                             mk_expr (AilEstr (None, [ (loc, [ Sym.pp_string name ]) ]))
                           ));
                      mk_expr (AilEident last_var)
                    ]
                    @ List.map
                        (fun x ->
                          mk_expr
                            (AilEcast
                               ( C.no_qualifiers,
                                 C.pointer_to_char,
                                 mk_expr
                                   (AilEstr
                                      ( None,
                                        [ (Locations.other __LOC__, [ Sym.pp_string x ]) ]
                                      )) )))
                        (List.of_seq
                           (SymSet.to_seq (SymSet.add pointer (IT.free_vars offset))))
                    @ [ mk_expr (AilEconst ConstantNull) ] )))
        ]
    in
    let b4, s4, e4 = compile_term sigma name rest in
    (b1 @ b2 @ b3 @ b4, s1 @ s2 @ s3 @ s4, e4)
  | Let { backtracks; x; x_bt; value; last_var; rest } ->
    let s1 =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_LET_BEGIN")),
                    List.map
                      mk_expr
                      [ AilEconst
                          (ConstantInteger
                             (IConstant (Z.of_int backtracks, Decimal, None)));
                        AilEident x
                      ] )))
        ]
    in
    let b2, s2, e2 = compile_term sigma name value in
    let s3 =
      A.(
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_LET_BODY")),
                    List.map
                      mk_expr
                      [ AilEident
                          (Sym.fresh_named
                             (name_of_bt
                                (Option.value
                                   ~default:name
                                   (match value with
                                    | Call { fsym; iargs; oarg_bt = _ } ->
                                      Some
                                        (GenUtils.get_mangled_name
                                           (fsym :: List.map fst iargs))
                                    | _ -> None))
                                x_bt));
                        AilEident x
                      ]
                    @ [ e2 ] )))
        ]
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_LET_END")),
                      List.map
                        mk_expr
                        [ AilEconst
                            (ConstantInteger
                               (IConstant (Z.of_int backtracks, Decimal, None)));
                          AilEident x;
                          AilEident last_var
                        ]
                      @ List.map
                          (fun x ->
                            mk_expr
                              (AilEcast
                                 ( C.no_qualifiers,
                                   C.pointer_to_char,
                                   mk_expr
                                     (AilEstr
                                        ( None,
                                          [ (Locations.other __LOC__, [ Sym.pp_string x ])
                                          ] )) )))
                          (List.of_seq (GR.SymSet.to_seq (GR.free_vars_term value)))
                      @ [ mk_expr (AilEconst ConstantNull) ] )))
          ])
    in
    let b4, s4, e4 = compile_term sigma name rest in
    (b2 @ [ Utils.create_binding x (bt_to_ctype name x_bt) ] @ b4, s1 @ s2 @ s3 @ s4, e4)
  | Return { value } ->
    let b, s, e = compile_it sigma name value in
    (b, s, e)
  | Assert { prop; last_var; rest } ->
    let b1, s1, e1 = compile_lc sigma prop in
    let s_assert =
      A.
        [ AilSexpr
            (mk_expr
               (AilEcall
                  ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_ASSERT")),
                    [ e1 ]
                    @ [ mk_expr (AilEident last_var) ]
                    @ List.map
                        (fun x ->
                          mk_expr
                            (AilEcast
                               ( C.no_qualifiers,
                                 C.pointer_to_char,
                                 mk_expr
                                   (AilEstr
                                      ( None,
                                        [ (Locations.other __LOC__, [ Sym.pp_string x ]) ]
                                      )) )))
                        (List.of_seq (SymSet.to_seq (LC.free_vars prop)))
                    @ [ mk_expr (AilEconst ConstantNull) ] )))
        ]
    in
    let b2, s2, e2 = compile_term sigma name rest in
    (b1 @ b2, s1 @ s_assert @ s2, e2)
  | ITE { bt; cond; t; f } ->
    let b_if, s_if, e_if = compile_it sigma name cond in
    let b_then, s_then, e_then = compile_term sigma name t in
    let b_else, s_else, e_else = compile_term sigma name f in
    let res_sym = Sym.fresh () in
    let res_expr = mk_expr (AilEident res_sym) in
    let res_binding = Utils.create_binding res_sym (bt_to_ctype name bt) in
    let res_stmt_ e = A.(AilSexpr (mk_expr (AilEassign (res_expr, e)))) in
    ( b_if @ [ res_binding ],
      (s_if
       @ A.
           [ AilSdeclaration [ (res_sym, None) ];
             AilSif
               ( CtA.wrap_with_convert_from_cn_bool e_if,
                 mk_stmt
                   (AilSblock (b_then, List.map mk_stmt (s_then @ [ res_stmt_ e_then ]))),
                 mk_stmt
                   (AilSblock (b_else, List.map mk_stmt (s_else @ [ res_stmt_ e_else ])))
               )
           ]),
      res_expr )
  | Map { i; bt; min; max; perm; inner; last_var } ->
    let sym_map = Sym.fresh () in
    let b_map = Utils.create_binding sym_map (bt_to_ctype name bt) in
    let i_bt, _ = BT.map_bt bt in
    let b_i = Utils.create_binding i (bt_to_ctype name i_bt) in
    let b_min, s_min, e_min = compile_it sigma name min in
    let b_max, s_max, e_max = compile_it sigma name max in
    assert (b_max == []);
    assert (s_max == []);
    let e_args =
      [ mk_expr (AilEident sym_map);
        mk_expr (AilEident i);
        mk_expr (AilEident (Sym.fresh_named (name_of_bt name i_bt)))
      ]
    in
    let b_perm, s_perm, e_perm = compile_it sigma name perm in
    let s_begin =
      A.(
        s_min
        @ s_perm
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_MAP_BEGIN")),
                      e_args
                      @ [ e_perm; e_max; mk_expr (AilEident last_var) ]
                      @ List.map
                          (fun x ->
                            mk_expr
                              (AilEcast
                                 ( C.no_qualifiers,
                                   C.pointer_to_char,
                                   mk_expr
                                     (AilEstr
                                        ( None,
                                          [ (Locations.other __LOC__, [ Sym.pp_string x ])
                                          ] )) )))
                          (List.of_seq
                             (SymSet.to_seq (SymSet.remove i (IT.free_vars perm))))
                      @ [ mk_expr (AilEconst ConstantNull) ] )))
          ])
    in
    let s_body =
      A.(
        s_perm
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    (mk_expr (AilEident (Sym.fresh_named "CN_GEN_MAP_BODY")), [ e_perm ])))
          ])
    in
    let b_val, s_val, e_val = compile_term sigma name inner in
    let s_end =
      A.(
        s_val
        @ [ AilSexpr
              (mk_expr
                 (AilEcall
                    ( mk_expr (AilEident (Sym.fresh_named "CN_GEN_MAP_END")),
                      e_args @ [ e_min; e_val ] )))
          ])
    in
    ( [ b_map; b_i ] @ b_min @ b_perm @ b_val,
      s_begin @ s_body @ s_end,
      mk_expr (AilEident sym_map) )


let compile_gen_def
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  ((name, gr) : Sym.t * GR.definition)
  : A.sigma_tag_definition * (A.sigma_declaration * 'a A.sigma_function_definition)
  =
  let loc = Locations.other __LOC__ in
  let bt_ret =
    BT.Record (List.map (fun (x, bt) -> (Id.id (Sym.pp_string x), bt)) gr.oargs)
  in
  let struct_def = CtA.generate_record_opt name bt_ret |> Option.get in
  let ct_ret = C.(mk_ctype_pointer no_qualifiers (Ctype ([], Struct (fst struct_def)))) in
  let decl : A.declaration =
    A.Decl_function
      ( false,
        (C.no_qualifiers, ct_ret),
        List.map (fun (_, bt) -> (C.no_qualifiers, bt_to_ctype name bt, false)) gr.iargs,
        false,
        false,
        false )
  in
  let sigma_decl : A.sigma_declaration = (name, (loc, CF.Annot.Attrs [], decl)) in
  let s1 =
    A.(
      AilSexpr
        (mk_expr (AilEcall (mk_expr (AilEident (Sym.fresh_named "CN_GEN_INIT")), []))))
  in
  let b2, s2, e2 = compile_term sigma name gr.body in
  let sigma_def : CF.GenTypes.genTypeCategory A.sigma_function_definition =
    ( name,
      ( loc,
        0,
        CF.Annot.Attrs [],
        List.map fst gr.iargs,
        mk_stmt
          (A.AilSblock
             ( b2,
               List.map
                 mk_stmt
                 ([ s1 ]
                  @ s2
                  @ A.
                      [ AilSreturn
                          (mk_expr
                             (AilEcast
                                ( C.no_qualifiers,
                                  C.(
                                    mk_ctype_pointer
                                      no_qualifiers
                                      (Ctype ([], Struct (fst struct_def)))),
                                  e2 )))
                      ]) )) ) )
  in
  (struct_def, (sigma_decl, sigma_def))


let compile (sigma : CF.GenTypes.genTypeCategory A.sigma) (ctx : GR.context) : Pp.document
  =
  let defs =
    ctx
    |> List.map (fun (_, defs) ->
      List.map
        (fun ((_, gr) : _ * GR.definition) ->
          (GenUtils.get_mangled_name (gr.name :: List.map fst gr.iargs), gr))
        defs)
    |> List.flatten
  in
  defs
  |> List.iter (fun ((name, def) : Sym.t * GR.definition) ->
    let bt =
      BT.Record (List.map (fun (x, bt) -> (Id.id (Sym.pp_string x), bt)) def.oargs)
    in
    CtA.augment_record_map ~cn_sym:name bt);
  let tag_definitions, funcs = List.split (List.map (compile_gen_def sigma) defs) in
  let declarations, function_definitions = List.split funcs in
  let sigma : 'a A.sigma =
    { A.empty_sigma with tag_definitions; declarations; function_definitions }
  in
  let open Pp in
  string "#ifndef CN_GEN_H"
  ^^ hardline
  ^^ string "#define CN_GEN_H"
  ^^ twice hardline
  ^^ string "#include <cn-testing/prelude.h>"
  ^^ twice hardline
  ^^ string "#include \"cn.h\""
  ^^ twice hardline
  ^^ separate_map
       (twice hardline)
       (CF.Pp_ail.pp_tag_definition ~executable_spec:true)
       tag_definitions
  ^^ twice hardline
  ^^ separate_map
       (twice hardline)
       (fun (tag, (_, _, decl)) ->
         CF.Pp_ail.pp_function_prototype ~executable_spec:true tag decl)
       declarations
  ^^ twice hardline
  ^^ CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, sigma)
  ^^ hardline
  ^^ string "#endif // CN_GEN_H"
  ^^ hardline
