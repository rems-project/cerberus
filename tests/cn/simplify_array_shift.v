From MuCore Require Import Annot ArgumentTypes Core BaseTypes CN CNProgs Ctype False Id ImplMem IndexTerms IntegerType Location Locations LogicalArgumentTypes LogicalConstraints LogicalReturnTypes Memory MuCore Request ReturnTypes SCtypes Sym Symbol Terms Undefined Utils.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import ZArith.


(* Global definitions *)
(* Function definitions *)
Definition __builtin_ctzl  := (ProcDecl unit Loc_unknown None).

Definition __builtin_ctzll  := (ProcDecl unit Loc_unknown None).

Definition cn_malloc  := (ProcDecl unit Loc_unknown None).

Definition cn_free_sized  := (ProcDecl unit Loc_unknown None).

Definition freeIntQueueCell  := (Proc
  unit
  Loc_unknown
  (MuCore.Computational
    _
    (
      (
        (Symbol "e86941afa238f384c6ba57e49e4ef1db" 723 (SD_FunArgValue "p"))
        ,
        (BaseTypes.Loc unit tt)
      )
      ,
      (Loc_unknown , None)
      ,
      (MuCore.L
        _
        (MuCore.Resource
          _
          (
            (Symbol "e86941afa238f384c6ba57e49e4ef1db" 746 (SD_CN_Id "u"))
            ,
            (
              (P
                {|
                  Predicate.name :=
                    (Owned
                      (SCtypes.Struct
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          629
                          (SD_Id "int_queueCell")))
                      Uninit);
                  Predicate.pointer :=
                    (IT
                      _
                      (Sym
                        _
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          723
                          (SD_FunArgValue "p")))
                      (BaseTypes.Loc unit tt)
                      Loc_unknown);
                  Predicate.iargs := [  ]
                |})
              ,
              (BaseTypes.Struct
                unit
                (Symbol
                  "e86941afa238f384c6ba57e49e4ef1db"
                  629
                  (SD_Id "int_queueCell")))
            )
            ,
            (Loc_unknown , None)
            ,
            (MuCore.Constraint
              _
              (
                (T
                  (IT
                    _
                    (Good
                      _
                      (SCtypes.Pointer
                        (SCtypes.Struct
                          (Symbol
                            "e86941afa238f384c6ba57e49e4ef1db"
                            629
                            (SD_Id "int_queueCell"))))
                      (IT
                        _
                        (Sym
                          _
                          (Symbol
                            "e86941afa238f384c6ba57e49e4ef1db"
                            723
                            (SD_FunArgValue "p")))
                        (BaseTypes.Loc unit tt)
                        Loc_unknown))
                    (BaseTypes.Bool unit)
                    Loc_unknown))
                ,
                (Loc_unknown , None)
                ,
                (MuCore.I
                  _
                  (
                    (Expr
                      _
                      Loc_unknown
                      [  ]
                      tt
                      (Esseq
                        _
                        (
                          (Pattern
                            _
                            Loc_unknown
                            [  ]
                            tt
                            (CaseBase _ (None , BTy_unit)))
                          ,
                          (Expr
                            _
                            Loc_unknown
                            [  ]
                            tt
                            (Esseq
                              _
                              (
                                (Pattern
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (CaseBase
                                    _
                                    (
                                      (Some
                                        (Symbol
                                          "e86941afa238f384c6ba57e49e4ef1db"
                                          635
                                          (SD_ObjectAddress "p")))
                                      ,
                                      (BTy_object OTy_pointer)
                                    )))
                                ,
                                (Expr
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (Eaction
                                    _
                                    {|
                                      paction_polarity := Pos;
                                      paction_action :=
                                        {|
                                          action_loc := Loc_unknown;
                                          action_content :=
                                            (Create
                                              _
                                              (Pexpr
                                                _
                                                Loc_unknown
                                                [  ]
                                                tt
                                                (PEapply_fun
                                                  _
                                                  F_align_of
                                                  [ (Pexpr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (PEval
                                                      _
                                                      (V
                                                        _
                                                        tt
                                                        (Vctype
                                                          _
                                                          (Ctype
                                                            [ (Aloc
                                                              Loc_unknown) ]
                                                            (Ctype.Pointer
                                                              {|
                                                                Ctype.const :=
                                                                  false;
                                                                Ctype.restrict :=
                                                                  false;
                                                                Ctype.volatile :=
                                                                  false
                                                              |}
                                                              (Ctype
                                                                [  ]
                                                                (Ctype.Struct
                                                                  (Symbol
                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                    629
                                                                    (SD_Id
                                                                      "int_queueCell")))))))))) ]))
                                              {|
                                                MuCore.loc := Loc_unknown;
                                                MuCore.annot := [  ];
                                                MuCore.ct :=
                                                  (SCtypes.Pointer
                                                    (SCtypes.Struct
                                                      (Symbol
                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                        629
                                                        (SD_Id "int_queueCell"))))
                                              |}
                                              (PrefFunArg
                                                Loc_unknown
                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                0%Z))
                                        |}
                                    |}))
                                ,
                                (Expr
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (Esseq
                                    _
                                    (
                                      (Pattern
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (CaseBase _ (None , BTy_unit)))
                                      ,
                                      (Expr
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (Eaction
                                          _
                                          {|
                                            paction_polarity := Pos;
                                            paction_action :=
                                              {|
                                                action_loc := Loc_unknown;
                                                action_content :=
                                                  (Store
                                                    _
                                                    false
                                                    {|
                                                      MuCore.loc := Loc_unknown;
                                                      MuCore.annot := [  ];
                                                      MuCore.ct :=
                                                        (SCtypes.Pointer
                                                          (SCtypes.Struct
                                                            (Symbol
                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                              629
                                                              (SD_Id
                                                                "int_queueCell"))))
                                                    |}
                                                    (Pexpr
                                                      _
                                                      Loc_unknown
                                                      [  ]
                                                      tt
                                                      (PEsym
                                                        _
                                                        (Symbol
                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                          635
                                                          (SD_ObjectAddress
                                                            "p"))))
                                                    (Pexpr
                                                      _
                                                      Loc_unknown
                                                      [  ]
                                                      tt
                                                      (PEsym
                                                        _
                                                        (Symbol
                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                          723
                                                          (SD_FunArgValue "p"))))
                                                    NA)
                                              |}
                                          |}))
                                      ,
                                      (Expr
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (Esseq
                                          _
                                          (
                                            (Pattern
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (CaseBase _ (None , BTy_unit)))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [ (Aloc Loc_unknown); Astmt ]
                                              tt
                                              (Esseq
                                                _
                                                (
                                                  (Pattern
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (CaseBase
                                                      _
                                                      (None , BTy_unit)))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [ (Aloc Loc_unknown); Astmt ]
                                                    tt
                                                    (Esseq
                                                      _
                                                      (
                                                        (Pattern
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (CaseBase
                                                            _
                                                            (None , BTy_unit)))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [ (Astd
                                                            "\194\1676.5#2") ]
                                                          tt
                                                          (Ebound
                                                            _
                                                            (Expr
                                                              _
                                                              Loc_unknown
                                                              [ (Aloc
                                                                Loc_unknown); Aexpr; (Astd
                                                                "\194\1676.5.2.2#10, sentence 1") ]
                                                              tt
                                                              (Esseq
                                                                _
                                                                (
                                                                  (Pattern
                                                                    _
                                                                    Loc_unknown
                                                                    [  ]
                                                                    tt
                                                                    (CaseCtor
                                                                      _
                                                                      Ctuple
                                                                      [ (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseCtor
                                                                          _
                                                                          Ctuple
                                                                          [ (Pattern
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (CaseBase
                                                                              _
                                                                              (
                                                                                (Some
                                                                                  (Symbol
                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                    726
                                                                                    SD_None))
                                                                                ,
                                                                                (BTy_loaded
                                                                                  OTy_pointer)
                                                                              ))); (Pattern
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (CaseCtor
                                                                              _
                                                                              Ctuple
                                                                              [ (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        727
                                                                                        SD_None))
                                                                                    ,
                                                                                    BTy_ctype
                                                                                  ))); (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        728
                                                                                        SD_None))
                                                                                    ,
                                                                                    (BTy_list
                                                                                      BTy_ctype)
                                                                                  ))); (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        729
                                                                                        SD_None))
                                                                                    ,
                                                                                    BTy_boolean
                                                                                  ))); (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        730
                                                                                        SD_None))
                                                                                    ,
                                                                                    BTy_boolean
                                                                                  ))) ])) ])); (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseBase
                                                                          _
                                                                          (
                                                                            (Some
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                733
                                                                                SD_None))
                                                                            ,
                                                                            (BTy_loaded
                                                                              OTy_pointer)
                                                                          ))); (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseBase
                                                                          _
                                                                          (
                                                                            (Some
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                735
                                                                                SD_None))
                                                                            ,
                                                                            (BTy_loaded
                                                                              OTy_integer)
                                                                          ))) ]))
                                                                  ,
                                                                  (Expr
                                                                    _
                                                                    Loc_unknown
                                                                    [ (Astd
                                                                      "\194\1676.5.2.2#4, sentence 2") ]
                                                                    tt
                                                                    (Eunseq
                                                                      _
                                                                      [ (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (Esseq
                                                                          _
                                                                          (
                                                                            (Pattern
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (CaseBase
                                                                                _
                                                                                (
                                                                                  (Some
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      725
                                                                                      SD_None))
                                                                                  ,
                                                                                  (BTy_loaded
                                                                                    OTy_pointer)
                                                                                )))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [ (Aloc
                                                                                Loc_unknown); Aexpr ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEval
                                                                                    _
                                                                                    (V
                                                                                      _
                                                                                      tt
                                                                                      (Vobject
                                                                                        _
                                                                                        (OV
                                                                                          _
                                                                                          tt
                                                                                          (OVpointer
                                                                                            _
                                                                                            (Mem.PVfunptr (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              627
                                                                                              (SD_Id
                                                                                                "cn_free_sized")))))))))))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEctor
                                                                                    _
                                                                                    Ctuple
                                                                                    [ (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEsym
                                                                                        _
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          725
                                                                                          SD_None))); (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEcfunction
                                                                                        _
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEsym
                                                                                            _
                                                                                            (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              725
                                                                                              SD_None))))) ]))))
                                                                          ))); (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [ (Aloc
                                                                          Loc_unknown); Aexpr ]
                                                                        tt
                                                                        (Ewseq
                                                                          _
                                                                          (
                                                                            (Pattern
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (CaseBase
                                                                                _
                                                                                (
                                                                                  (Some
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      734
                                                                                      SD_None))
                                                                                  ,
                                                                                  (BTy_object
                                                                                    OTy_pointer)
                                                                                )))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [ (Aloc
                                                                                Loc_unknown); Aexpr ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEsym
                                                                                    _
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      635
                                                                                      (SD_ObjectAddress
                                                                                        "p"))))))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (Eaction
                                                                                _
                                                                                {|
                                                                                  paction_polarity :=
                                                                                    Pos;
                                                                                  paction_action :=
                                                                                    {|
                                                                                      action_loc :=
                                                                                        Loc_unknown;
                                                                                      action_content :=
                                                                                        (Load
                                                                                          _
                                                                                          {|
                                                                                            MuCore.loc :=
                                                                                              Loc_unknown;
                                                                                            MuCore.annot :=
                                                                                              [  ];
                                                                                            MuCore.ct :=
                                                                                              (SCtypes.Pointer
                                                                                                (SCtypes.Struct
                                                                                                  (Symbol
                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                    629
                                                                                                    (SD_Id
                                                                                                      "int_queueCell"))))
                                                                                          |}
                                                                                          (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEsym
                                                                                              _
                                                                                              (Symbol
                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                734
                                                                                                SD_None)))
                                                                                          NA)
                                                                                    |}
                                                                                |}))
                                                                          ))); (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [ (Aloc
                                                                          Loc_unknown); Aexpr; (Avalue
                                                                          (Ainteger
                                                                            Size_t)) ]
                                                                        tt
                                                                        (Epure
                                                                          _
                                                                          (Pexpr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (PEapply_fun
                                                                              _
                                                                              F_size_of
                                                                              [ (Pexpr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (PEval
                                                                                  _
                                                                                  (V
                                                                                    _
                                                                                    tt
                                                                                    (Vctype
                                                                                      _
                                                                                      (Ctype
                                                                                        [  ]
                                                                                        (Ctype.Struct
                                                                                          (Symbol
                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                            629
                                                                                            (SD_Id
                                                                                              "int_queueCell")))))))) ])))) ]))
                                                                  ,
                                                                  (Expr
                                                                    _
                                                                    Loc_unknown
                                                                    [ Anot_explode ]
                                                                    tt
                                                                    (Eif
                                                                      _
                                                                      (
                                                                        (Pexpr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (PEnot
                                                                            _
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (PEop
                                                                                _
                                                                                Core.OpEq
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEapply_fun
                                                                                    _
                                                                                    F_params_length
                                                                                    [ (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEsym
                                                                                        _
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          728
                                                                                          SD_None))) ]))
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEval
                                                                                    _
                                                                                    (V
                                                                                      _
                                                                                      tt
                                                                                      (Vobject
                                                                                        _
                                                                                        (OV
                                                                                          _
                                                                                          tt
                                                                                          (OVinteger
                                                                                            _
                                                                                            (Mem.IVint 2)))))))))))
                                                                        ,
                                                                        (Expr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (Epure
                                                                            _
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [ (Astd
                                                                                "\194\1676.5.2.2#6, sentence 3") ]
                                                                              tt
                                                                              (PEundef
                                                                                _
                                                                                Loc_unknown
                                                                                UB038_number_of_args))))
                                                                        ,
                                                                        (Expr
                                                                          _
                                                                          Loc_unknown
                                                                          [ Anot_explode ]
                                                                          tt
                                                                          (Eif
                                                                            _
                                                                            (
                                                                              (Pexpr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (PEop
                                                                                  _
                                                                                  Core.OpOr
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [  ]
                                                                                    tt
                                                                                    (PEsym
                                                                                      _
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        729
                                                                                        SD_None)))
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [  ]
                                                                                    tt
                                                                                    (PEnot
                                                                                      _
                                                                                      (Pexpr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (PEapply_fun
                                                                                          _
                                                                                          F_are_compatible
                                                                                          [ (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEval
                                                                                              _
                                                                                              (V
                                                                                                _
                                                                                                tt
                                                                                                (Vctype
                                                                                                  _
                                                                                                  (Ctype
                                                                                                    [ (Aloc
                                                                                                      Loc_unknown) ]
                                                                                                    Ctype.Void))))); (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEsym
                                                                                              _
                                                                                              (Symbol
                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                727
                                                                                                SD_None))) ]))))))
                                                                              ,
                                                                              (Expr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (Epure
                                                                                  _
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [ (Astd
                                                                                      "\194\1676.5.2.2#9") ]
                                                                                    tt
                                                                                    (PEundef
                                                                                      _
                                                                                      Loc_unknown
                                                                                      UB041_function_not_compatible))))
                                                                              ,
                                                                              (Expr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (Eccall
                                                                                  _
                                                                                  (
                                                                                    {|
                                                                                      MuCore.loc :=
                                                                                        Loc_unknown;
                                                                                      MuCore.annot :=
                                                                                        [  ];
                                                                                      MuCore.ct :=
                                                                                        (SCtypes.Pointer
                                                                                          (SCtypes.SCFunction
                                                                                            (
                                                                                              (
                                                                                                {|
                                                                                                  Ctype.const :=
                                                                                                    false;
                                                                                                  Ctype.restrict :=
                                                                                                    false;
                                                                                                  Ctype.volatile :=
                                                                                                    false
                                                                                                |}
                                                                                                ,
                                                                                                SCtypes.Void
                                                                                              )
                                                                                              ,
                                                                                              [ (
                                                                                                (SCtypes.Pointer
                                                                                                  SCtypes.Void)
                                                                                                ,
                                                                                                false
                                                                                              ); (
                                                                                                (SCtypes.Integer
                                                                                                  (Unsigned
                                                                                                    LongLong))
                                                                                                ,
                                                                                                false
                                                                                              ) ]
                                                                                              ,
                                                                                              false
                                                                                            )))
                                                                                    |}
                                                                                    ,
                                                                                    (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEsym
                                                                                        _
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          726
                                                                                          SD_None)))
                                                                                    ,
                                                                                    [ (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PElet
                                                                                        _
                                                                                        (Pattern
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (CaseBase
                                                                                            _
                                                                                            (
                                                                                              (Some
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  740
                                                                                                  SD_None))
                                                                                              ,
                                                                                              BTy_ctype
                                                                                            )))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEapply_fun
                                                                                            _
                                                                                            F_params_nth
                                                                                            [ (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  728
                                                                                                  SD_None))); (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEval
                                                                                                _
                                                                                                (V
                                                                                                  _
                                                                                                  tt
                                                                                                  (Vobject
                                                                                                    _
                                                                                                    (OV
                                                                                                      _
                                                                                                      tt
                                                                                                      (OVinteger
                                                                                                        _
                                                                                                        (Mem.IVint 0))))))) ]))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [ Anot_explode ]
                                                                                          tt
                                                                                          (PEif
                                                                                            _
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEnot
                                                                                                _
                                                                                                (Pexpr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (PEapply_fun
                                                                                                    _
                                                                                                    F_are_compatible
                                                                                                    [ (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEval
                                                                                                        _
                                                                                                        (V
                                                                                                          _
                                                                                                          tt
                                                                                                          (Vctype
                                                                                                            _
                                                                                                            (Ctype
                                                                                                              [ (Aloc
                                                                                                                Loc_unknown) ]
                                                                                                              (Ctype.Pointer
                                                                                                                {|
                                                                                                                  Ctype.const :=
                                                                                                                    false;
                                                                                                                  Ctype.restrict :=
                                                                                                                    false;
                                                                                                                  Ctype.volatile :=
                                                                                                                    false
                                                                                                                |}
                                                                                                                (Ctype
                                                                                                                  [ (Aloc
                                                                                                                    Loc_unknown) ]
                                                                                                                  Ctype.Void))))))); (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEsym
                                                                                                        _
                                                                                                        (Symbol
                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                          740
                                                                                                          SD_None))) ]))))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [ (Astd
                                                                                                "\194\1676.5.2.2#9") ]
                                                                                              tt
                                                                                              (PEundef
                                                                                                _
                                                                                                Loc_unknown
                                                                                                UB041_function_not_compatible))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  733
                                                                                                  SD_None))))))); (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PElet
                                                                                        _
                                                                                        (Pattern
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (CaseBase
                                                                                            _
                                                                                            (
                                                                                              (Some
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  742
                                                                                                  SD_None))
                                                                                              ,
                                                                                              BTy_ctype
                                                                                            )))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEapply_fun
                                                                                            _
                                                                                            F_params_nth
                                                                                            [ (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  728
                                                                                                  SD_None))); (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEval
                                                                                                _
                                                                                                (V
                                                                                                  _
                                                                                                  tt
                                                                                                  (Vobject
                                                                                                    _
                                                                                                    (OV
                                                                                                      _
                                                                                                      tt
                                                                                                      (OVinteger
                                                                                                        _
                                                                                                        (Mem.IVint 1))))))) ]))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [ Anot_explode ]
                                                                                          tt
                                                                                          (PEif
                                                                                            _
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEnot
                                                                                                _
                                                                                                (Pexpr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (PEapply_fun
                                                                                                    _
                                                                                                    F_are_compatible
                                                                                                    [ (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEval
                                                                                                        _
                                                                                                        (V
                                                                                                          _
                                                                                                          tt
                                                                                                          (Vctype
                                                                                                            _
                                                                                                            (Ctype
                                                                                                              [ (Aloc
                                                                                                                Loc_unknown) ]
                                                                                                              (Ctype.Basic
                                                                                                                (Ctype.Integer
                                                                                                                  (Unsigned
                                                                                                                    LongLong)))))))); (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEsym
                                                                                                        _
                                                                                                        (Symbol
                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                          742
                                                                                                          SD_None))) ]))))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [ (Astd
                                                                                                "\194\1676.5.2.2#9") ]
                                                                                              tt
                                                                                              (PEundef
                                                                                                _
                                                                                                Loc_unknown
                                                                                                UB041_function_not_compatible))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEconv_loaded_int
                                                                                                _
                                                                                                (Pexpr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (PEval
                                                                                                    _
                                                                                                    (V
                                                                                                      _
                                                                                                      tt
                                                                                                      (Vctype
                                                                                                        _
                                                                                                        (Ctype
                                                                                                          [ (Aloc
                                                                                                            Loc_unknown) ]
                                                                                                          (Ctype.Basic
                                                                                                            (Ctype.Integer
                                                                                                              (Unsigned
                                                                                                                LongLong))))))))
                                                                                                (Pexpr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (PEsym
                                                                                                    _
                                                                                                    (Symbol
                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                      735
                                                                                                      SD_None))))))))) ]
                                                                                  )))
                                                                            )))
                                                                      )))
                                                                )))))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (Epure
                                                            _
                                                            (Pexpr
                                                              _
                                                              Loc_unknown
                                                              [  ]
                                                              tt
                                                              (PEval
                                                                _
                                                                (V
                                                                  _
                                                                  tt
                                                                  (Vunit _))))))
                                                      )))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Epure
                                                      _
                                                      (Pexpr
                                                        _
                                                        Loc_unknown
                                                        [  ]
                                                        tt
                                                        (PEval
                                                          _
                                                          (V _ tt (Vunit _))))))
                                                )))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (Esseq
                                                _
                                                (
                                                  (Pattern
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (CaseBase
                                                      _
                                                      (None , BTy_unit)))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Eaction
                                                      _
                                                      {|
                                                        paction_polarity := Pos;
                                                        paction_action :=
                                                          {|
                                                            action_loc :=
                                                              Loc_unknown;
                                                            action_content :=
                                                              (Kill
                                                                _
                                                                (Static
                                                                  (SCtypes.Pointer
                                                                    (SCtypes.Struct
                                                                      (Symbol
                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                        629
                                                                        (SD_Id
                                                                          "int_queueCell")))))
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEsym
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      635
                                                                      (SD_ObjectAddress
                                                                        "p")))))
                                                          |}
                                                      |}))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Epure
                                                      _
                                                      (Pexpr
                                                        _
                                                        Loc_unknown
                                                        [  ]
                                                        tt
                                                        (PEval
                                                          _
                                                          (V _ tt (Vunit _))))))
                                                )))
                                          )))
                                    )))
                              )))
                          ,
                          (Expr
                            _
                            Loc_unknown
                            [ (Alabel LAreturn); (Aloc Loc_unknown) ]
                            tt
                            (Erun
                              _
                              (
                                (Symbol
                                  "e86941afa238f384c6ba57e49e4ef1db"
                                  724
                                  (SD_Id "ret_724"))
                                ,
                                [ (Pexpr
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (PEval _ (V _ tt (Vunit _)))) ]
                              )))
                        )))
                    ,
                    (Sym.map_from_list [ (
                      (Symbol
                        "e86941afa238f384c6ba57e49e4ef1db"
                        724
                        (SD_Id "ret_724"))
                      ,
                      (Return _ Loc_unknown)
                    ) ])
                    ,
                    (ReturnTypes.Computational
                      (
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          747
                          (SD_CN_Id "return"))
                        ,
                        (BaseTypes.Unit unit)
                      )
                      (Loc_unknown , None)
                      (LogicalReturnTypes.Constraint
                        (T
                          (IT
                            _
                            (Const _ (Bool true))
                            (BaseTypes.Bool unit)
                            Loc_unknown))
                        (Loc_unknown , None)
                        LogicalReturnTypes.I))
                  ))
              ))
          )))
    ))
  (Trusted Loc_unknown)
  {|
    accesses := [  ];
    requires :=
      [ (CN_cletResource
        _
        _
        Loc_unknown
        (Symbol "e86941afa238f384c6ba57e49e4ef1db" 746 (SD_CN_Id "u"))
        (CN_pred
          _
          _
          Loc_unknown
          (CN_block
            _
            _
            (Some
              (Ctype
                [  ]
                (Ctype.Struct
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    629
                    (SD_Id "int_queueCell"))))))
          [ (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_value_of_c_atom
                _
                _
                (
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    635
                    (SD_ObjectAddress "p"))
                  ,
                  C_kind_var
                ))
            )) ])) ];
    ensures :=
      [ (CN_cconstr
        _
        _
        Loc_unknown
        (CN_assert_exp
          _
          _
          (CNExpr _ _ (Loc_unknown , (CNExpr_const _ _ (CNConst_bool true)))))) ]
  |}).

Definition IntQueue_pop  := (Proc
  unit
  Loc_unknown
  (MuCore.Computational
    _
    (
      (
        (Symbol "e86941afa238f384c6ba57e49e4ef1db" 672 (SD_FunArgValue "q"))
        ,
        (BaseTypes.Loc unit tt)
      )
      ,
      (Loc_unknown , None)
      ,
      (MuCore.L
        _
        (MuCore.Resource
          _
          (
            (Symbol "e86941afa238f384c6ba57e49e4ef1db" 748 (SD_CN_Id "Q"))
            ,
            (
              (P
                {|
                  Predicate.name :=
                    (Owned
                      (SCtypes.Struct
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          628
                          (SD_Id "int_queue")))
                      Init);
                  Predicate.pointer :=
                    (IT
                      _
                      (Sym
                        _
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          672
                          (SD_FunArgValue "q")))
                      (BaseTypes.Loc unit tt)
                      Loc_unknown);
                  Predicate.iargs := [  ]
                |})
              ,
              (BaseTypes.Struct
                unit
                (Symbol
                  "e86941afa238f384c6ba57e49e4ef1db"
                  628
                  (SD_Id "int_queue")))
            )
            ,
            (Loc_unknown , None)
            ,
            (MuCore.Constraint
              _
              (
                (T
                  (IT
                    _
                    (Good
                      _
                      (SCtypes.Pointer
                        (SCtypes.Struct
                          (Symbol
                            "e86941afa238f384c6ba57e49e4ef1db"
                            628
                            (SD_Id "int_queue"))))
                      (IT
                        _
                        (Sym
                          _
                          (Symbol
                            "e86941afa238f384c6ba57e49e4ef1db"
                            672
                            (SD_FunArgValue "q")))
                        (BaseTypes.Loc unit tt)
                        Loc_unknown))
                    (BaseTypes.Bool unit)
                    Loc_unknown))
                ,
                (Loc_unknown , None)
                ,
                (MuCore.Constraint
                  _
                  (
                    (T
                      (IT
                        _
                        (Binop
                          _
                          Terms.And
                          (IT
                            _
                            (Unop
                              _
                              Not
                              (IT
                                _
                                (Binop
                                  _
                                  Terms.EQ
                                  (IT
                                    _
                                    (StructMember
                                      _
                                      (IT
                                        _
                                        (Sym
                                          _
                                          (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            748
                                            (SD_CN_Id "Q")))
                                        (BaseTypes.Struct
                                          unit
                                          (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            628
                                            (SD_Id "int_queue")))
                                        Loc_unknown)
                                      (Identifier Loc_unknown "front"))
                                    (BaseTypes.Loc unit tt)
                                    Loc_unknown)
                                  (IT
                                    _
                                    (Const _ Null)
                                    (BaseTypes.Loc unit tt)
                                    Loc_unknown))
                                (BaseTypes.Bool unit)
                                Loc_unknown))
                            (BaseTypes.Bool unit)
                            Loc_unknown)
                          (IT
                            _
                            (Unop
                              _
                              Not
                              (IT
                                _
                                (Binop
                                  _
                                  Terms.EQ
                                  (IT
                                    _
                                    (StructMember
                                      _
                                      (IT
                                        _
                                        (Sym
                                          _
                                          (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            748
                                            (SD_CN_Id "Q")))
                                        (BaseTypes.Struct
                                          unit
                                          (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            628
                                            (SD_Id "int_queue")))
                                        Loc_unknown)
                                      (Identifier Loc_unknown "back"))
                                    (BaseTypes.Loc unit tt)
                                    Loc_unknown)
                                  (IT
                                    _
                                    (Const _ Null)
                                    (BaseTypes.Loc unit tt)
                                    Loc_unknown))
                                (BaseTypes.Bool unit)
                                Loc_unknown))
                            (BaseTypes.Bool unit)
                            Loc_unknown))
                        (BaseTypes.Bool unit)
                        Loc_unknown))
                    ,
                    (Loc_unknown , None)
                    ,
                    (MuCore.Constraint
                      _
                      (
                        (T
                          (IT
                            _
                            (Apply
                              _
                              (Symbol
                                "e86941afa238f384c6ba57e49e4ef1db"
                                606
                                (SD_CN_Id "eq_testable"))
                              [ (IT
                                _
                                (StructMember
                                  _
                                  (IT
                                    _
                                    (Sym
                                      _
                                      (Symbol
                                        "e86941afa238f384c6ba57e49e4ef1db"
                                        748
                                        (SD_CN_Id "Q")))
                                    (BaseTypes.Struct
                                      unit
                                      (Symbol
                                        "e86941afa238f384c6ba57e49e4ef1db"
                                        628
                                        (SD_Id "int_queue")))
                                    Loc_unknown)
                                  (Identifier Loc_unknown "front"))
                                (BaseTypes.Loc unit tt)
                                Loc_unknown); (IT
                                _
                                (StructMember
                                  _
                                  (IT
                                    _
                                    (Sym
                                      _
                                      (Symbol
                                        "e86941afa238f384c6ba57e49e4ef1db"
                                        748
                                        (SD_CN_Id "Q")))
                                    (BaseTypes.Struct
                                      unit
                                      (Symbol
                                        "e86941afa238f384c6ba57e49e4ef1db"
                                        628
                                        (SD_Id "int_queue")))
                                    Loc_unknown)
                                  (Identifier Loc_unknown "back"))
                                (BaseTypes.Loc unit tt)
                                Loc_unknown) ])
                            (BaseTypes.Bool unit)
                            Loc_unknown))
                        ,
                        (Loc_unknown , None)
                        ,
                        (MuCore.Resource
                          _
                          (
                            (Symbol
                              "e86941afa238f384c6ba57e49e4ef1db"
                              749
                              (SD_CN_Id "B"))
                            ,
                            (
                              (P
                                {|
                                  Predicate.name :=
                                    (PName
                                      (Symbol
                                        "e86941afa238f384c6ba57e49e4ef1db"
                                        605
                                        (SD_CN_Id "Test")));
                                  Predicate.pointer :=
                                    (IT
                                      _
                                      (StructMember
                                        _
                                        (IT
                                          _
                                          (Sym
                                            _
                                            (Symbol
                                              "e86941afa238f384c6ba57e49e4ef1db"
                                              748
                                              (SD_CN_Id "Q")))
                                          (BaseTypes.Struct
                                            unit
                                            (Symbol
                                              "e86941afa238f384c6ba57e49e4ef1db"
                                              628
                                              (SD_Id "int_queue")))
                                          Loc_unknown)
                                        (Identifier Loc_unknown "front"))
                                      (BaseTypes.Loc unit tt)
                                      Loc_unknown);
                                  Predicate.iargs :=
                                    [ (IT
                                      _
                                      (StructMember
                                        _
                                        (IT
                                          _
                                          (Sym
                                            _
                                            (Symbol
                                              "e86941afa238f384c6ba57e49e4ef1db"
                                              748
                                              (SD_CN_Id "Q")))
                                          (BaseTypes.Struct
                                            unit
                                            (Symbol
                                              "e86941afa238f384c6ba57e49e4ef1db"
                                              628
                                              (SD_Id "int_queue")))
                                          Loc_unknown)
                                        (Identifier Loc_unknown "back"))
                                      (BaseTypes.Loc unit tt)
                                      Loc_unknown) ]
                                |})
                              ,
                              (BaseTypes.Unit unit)
                            )
                            ,
                            (Loc_unknown , None)
                            ,
                            (MuCore.I
                              _
                              (
                                (Expr
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (Esseq
                                    _
                                    (
                                      (Pattern
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (CaseBase _ (None , BTy_unit)))
                                      ,
                                      (Expr
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (Esseq
                                          _
                                          (
                                            (Pattern
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (CaseBase
                                                _
                                                (
                                                  (Some
                                                    (Symbol
                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                      638
                                                      (SD_ObjectAddress "q")))
                                                  ,
                                                  (BTy_object OTy_pointer)
                                                )))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (Eaction
                                                _
                                                {|
                                                  paction_polarity := Pos;
                                                  paction_action :=
                                                    {|
                                                      action_loc := Loc_unknown;
                                                      action_content :=
                                                        (Create
                                                          _
                                                          (Pexpr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (PEapply_fun
                                                              _
                                                              F_align_of
                                                              [ (Pexpr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (PEval
                                                                  _
                                                                  (V
                                                                    _
                                                                    tt
                                                                    (Vctype
                                                                      _
                                                                      (Ctype
                                                                        [ (Aloc
                                                                          Loc_unknown) ]
                                                                        (Ctype.Pointer
                                                                          {|
                                                                            Ctype.const :=
                                                                              false;
                                                                            Ctype.restrict :=
                                                                              false;
                                                                            Ctype.volatile :=
                                                                              false
                                                                          |}
                                                                          (Ctype
                                                                            [  ]
                                                                            (Ctype.Struct
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                628
                                                                                (SD_Id
                                                                                  "int_queue")))))))))) ]))
                                                          {|
                                                            MuCore.loc :=
                                                              Loc_unknown;
                                                            MuCore.annot :=
                                                              [  ];
                                                            MuCore.ct :=
                                                              (SCtypes.Pointer
                                                                (SCtypes.Struct
                                                                  (Symbol
                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                    628
                                                                    (SD_Id
                                                                      "int_queue"))))
                                                          |}
                                                          (PrefFunArg
                                                            Loc_unknown
                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                            0%Z))
                                                    |}
                                                |}))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (Esseq
                                                _
                                                (
                                                  (Pattern
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (CaseBase
                                                      _
                                                      (None , BTy_unit)))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Eaction
                                                      _
                                                      {|
                                                        paction_polarity := Pos;
                                                        paction_action :=
                                                          {|
                                                            action_loc :=
                                                              Loc_unknown;
                                                            action_content :=
                                                              (Store
                                                                _
                                                                false
                                                                {|
                                                                  MuCore.loc :=
                                                                    Loc_unknown;
                                                                  MuCore.annot :=
                                                                    [  ];
                                                                  MuCore.ct :=
                                                                    (SCtypes.Pointer
                                                                      (SCtypes.Struct
                                                                        (Symbol
                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                          628
                                                                          (SD_Id
                                                                            "int_queue"))))
                                                                |}
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEsym
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      638
                                                                      (SD_ObjectAddress
                                                                        "q"))))
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEsym
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      672
                                                                      (SD_FunArgValue
                                                                        "q"))))
                                                                NA)
                                                          |}
                                                      |}))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Esseq
                                                      _
                                                      (
                                                        (Pattern
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (CaseBase
                                                            _
                                                            (None , BTy_unit)))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [ (Aloc Loc_unknown); Astmt ]
                                                          tt
                                                          (Esseq
                                                            _
                                                            (
                                                              (Pattern
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (CaseBase
                                                                  _
                                                                  (
                                                                    (Some
                                                                      (Symbol
                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                        641
                                                                        (SD_ObjectAddress
                                                                          "h")))
                                                                    ,
                                                                    (BTy_object
                                                                      OTy_pointer)
                                                                  )))
                                                              ,
                                                              (Expr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (Eaction
                                                                  _
                                                                  {|
                                                                    paction_polarity :=
                                                                      Pos;
                                                                    paction_action :=
                                                                      {|
                                                                        action_loc :=
                                                                          Loc_unknown;
                                                                        action_content :=
                                                                          (Create
                                                                            _
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (PEapply_fun
                                                                                _
                                                                                F_align_of
                                                                                [ (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEval
                                                                                    _
                                                                                    (V
                                                                                      _
                                                                                      tt
                                                                                      (Vctype
                                                                                        _
                                                                                        (Ctype
                                                                                          [ (Aloc
                                                                                            Loc_unknown) ]
                                                                                          (Ctype.Pointer
                                                                                            {|
                                                                                              Ctype.const :=
                                                                                                false;
                                                                                              Ctype.restrict :=
                                                                                                false;
                                                                                              Ctype.volatile :=
                                                                                                false
                                                                                            |}
                                                                                            (Ctype
                                                                                              [  ]
                                                                                              (Ctype.Struct
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  629
                                                                                                  (SD_Id
                                                                                                    "int_queueCell")))))))))) ]))
                                                                            {|
                                                                              MuCore.loc :=
                                                                                Loc_unknown;
                                                                              MuCore.annot :=
                                                                                [  ];
                                                                              MuCore.ct :=
                                                                                (SCtypes.Pointer
                                                                                  (SCtypes.Struct
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      629
                                                                                      (SD_Id
                                                                                        "int_queueCell"))))
                                                                            |}
                                                                            (PrefSource
                                                                              Loc_unknown
                                                                              [ (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                639
                                                                                (SD_Id
                                                                                  "IntQueue_pop")); (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                641
                                                                                (SD_ObjectAddress
                                                                                  "h")) ]))
                                                                      |}
                                                                  |}))
                                                              ,
                                                              (Expr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (Esseq
                                                                  _
                                                                  (
                                                                    (Pattern
                                                                      _
                                                                      Loc_unknown
                                                                      [  ]
                                                                      tt
                                                                      (CaseBase
                                                                        _
                                                                        (
                                                                          None
                                                                          ,
                                                                          BTy_unit
                                                                        )))
                                                                    ,
                                                                    (Expr
                                                                      _
                                                                      Loc_unknown
                                                                      [ (Aloc
                                                                        Loc_unknown); Astmt ]
                                                                      tt
                                                                      (Esseq
                                                                        _
                                                                        (
                                                                          (Pattern
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (CaseBase
                                                                              _
                                                                              (
                                                                                (Some
                                                                                  (Symbol
                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                    675
                                                                                    SD_None))
                                                                                ,
                                                                                (BTy_loaded
                                                                                  OTy_pointer)
                                                                              )))
                                                                          ,
                                                                          (Expr
                                                                            _
                                                                            Loc_unknown
                                                                            [ (Astd
                                                                              "\194\1676.5#2") ]
                                                                            tt
                                                                            (Ebound
                                                                              _
                                                                              (Expr
                                                                                _
                                                                                Loc_unknown
                                                                                [ (Aloc
                                                                                  Loc_unknown); Aexpr ]
                                                                                tt
                                                                                (Ewseq
                                                                                  _
                                                                                  (
                                                                                    (Pattern
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (CaseBase
                                                                                        _
                                                                                        (
                                                                                          (Some
                                                                                            (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              681
                                                                                              SD_None))
                                                                                          ,
                                                                                          (BTy_object
                                                                                            OTy_pointer)
                                                                                        )))
                                                                                    ,
                                                                                    (Expr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [ (Aloc
                                                                                        Loc_unknown); Aexpr; (Astd
                                                                                        "\194\1676.5.2.3#4, sentence 2") ]
                                                                                      tt
                                                                                      (Esseq
                                                                                        _
                                                                                        (
                                                                                          (Pattern
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (CaseBase
                                                                                              _
                                                                                              (
                                                                                                (Some
                                                                                                  (Symbol
                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                    676
                                                                                                    SD_None))
                                                                                                ,
                                                                                                (BTy_loaded
                                                                                                  OTy_pointer)
                                                                                              )))
                                                                                          ,
                                                                                          (Expr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [ (Aloc
                                                                                              Loc_unknown); Aexpr ]
                                                                                            tt
                                                                                            (Ewseq
                                                                                              _
                                                                                              (
                                                                                                (Pattern
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (CaseBase
                                                                                                    _
                                                                                                    (
                                                                                                      (Some
                                                                                                        (Symbol
                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                          680
                                                                                                          SD_None))
                                                                                                      ,
                                                                                                      (BTy_object
                                                                                                        OTy_pointer)
                                                                                                    )))
                                                                                                ,
                                                                                                (Expr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [ (Aloc
                                                                                                    Loc_unknown); Aexpr ]
                                                                                                  tt
                                                                                                  (Epure
                                                                                                    _
                                                                                                    (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEsym
                                                                                                        _
                                                                                                        (Symbol
                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                          638
                                                                                                          (SD_ObjectAddress
                                                                                                            "q"))))))
                                                                                                ,
                                                                                                (Expr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (Eaction
                                                                                                    _
                                                                                                    {|
                                                                                                      paction_polarity :=
                                                                                                        Pos;
                                                                                                      paction_action :=
                                                                                                        {|
                                                                                                          action_loc :=
                                                                                                            Loc_unknown;
                                                                                                          action_content :=
                                                                                                            (Load
                                                                                                              _
                                                                                                              {|
                                                                                                                MuCore.loc :=
                                                                                                                  Loc_unknown;
                                                                                                                MuCore.annot :=
                                                                                                                  [  ];
                                                                                                                MuCore.ct :=
                                                                                                                  (SCtypes.Pointer
                                                                                                                    (SCtypes.Struct
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        628
                                                                                                                        (SD_Id
                                                                                                                          "int_queue"))))
                                                                                                              |}
                                                                                                              (Pexpr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (PEsym
                                                                                                                  _
                                                                                                                  (Symbol
                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                    680
                                                                                                                    SD_None)))
                                                                                                              NA)
                                                                                                        |}
                                                                                                    |}))
                                                                                              )))
                                                                                          ,
                                                                                          (Expr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (Epure
                                                                                              _
                                                                                              (Pexpr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [  ]
                                                                                                tt
                                                                                                (PEmember_shift
                                                                                                  _
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (PEsym
                                                                                                      _
                                                                                                      (Symbol
                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                        676
                                                                                                        SD_None)))
                                                                                                  (Symbol
                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                    628
                                                                                                    (SD_Id
                                                                                                      "int_queue"))
                                                                                                  (Identifier
                                                                                                    Loc_unknown
                                                                                                    "front")))))
                                                                                        )))
                                                                                    ,
                                                                                    (Expr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (Eaction
                                                                                        _
                                                                                        {|
                                                                                          paction_polarity :=
                                                                                            Pos;
                                                                                          paction_action :=
                                                                                            {|
                                                                                              action_loc :=
                                                                                                Loc_unknown;
                                                                                              action_content :=
                                                                                                (Load
                                                                                                  _
                                                                                                  {|
                                                                                                    MuCore.loc :=
                                                                                                      Loc_unknown;
                                                                                                    MuCore.annot :=
                                                                                                      [  ];
                                                                                                    MuCore.ct :=
                                                                                                      (SCtypes.Pointer
                                                                                                        (SCtypes.Struct
                                                                                                          (Symbol
                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                            629
                                                                                                            (SD_Id
                                                                                                              "int_queueCell"))))
                                                                                                  |}
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (PEsym
                                                                                                      _
                                                                                                      (Symbol
                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                        681
                                                                                                        SD_None)))
                                                                                                  NA)
                                                                                            |}
                                                                                        |}))
                                                                                  )))))
                                                                          ,
                                                                          (Expr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (Eaction
                                                                              _
                                                                              {|
                                                                                paction_polarity :=
                                                                                  Pos;
                                                                                paction_action :=
                                                                                  {|
                                                                                    action_loc :=
                                                                                      Loc_unknown;
                                                                                    action_content :=
                                                                                      (Store
                                                                                        _
                                                                                        false
                                                                                        {|
                                                                                          MuCore.loc :=
                                                                                            Loc_unknown;
                                                                                          MuCore.annot :=
                                                                                            [  ];
                                                                                          MuCore.ct :=
                                                                                            (SCtypes.Pointer
                                                                                              (SCtypes.Struct
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  629
                                                                                                  (SD_Id
                                                                                                    "int_queueCell"))))
                                                                                        |}
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEsym
                                                                                            _
                                                                                            (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              641
                                                                                              (SD_ObjectAddress
                                                                                                "h"))))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEsym
                                                                                            _
                                                                                            (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              675
                                                                                              SD_None)))
                                                                                        NA)
                                                                                  |}
                                                                              |}))
                                                                        )))
                                                                    ,
                                                                    (Expr
                                                                      _
                                                                      Loc_unknown
                                                                      [  ]
                                                                      tt
                                                                      (Esseq
                                                                        _
                                                                        (
                                                                          (Pattern
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (CaseBase
                                                                              _
                                                                              (
                                                                                None
                                                                                ,
                                                                                BTy_unit
                                                                              )))
                                                                          ,
                                                                          (Expr
                                                                            _
                                                                            Loc_unknown
                                                                            [ (Aloc
                                                                              Loc_unknown); Astmt ]
                                                                            tt
                                                                            (Esseq
                                                                              _
                                                                              (
                                                                                (Pattern
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (CaseBase
                                                                                    _
                                                                                    (
                                                                                      (Some
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          682
                                                                                          SD_None))
                                                                                      ,
                                                                                      (BTy_loaded
                                                                                        OTy_integer)
                                                                                    )))
                                                                                ,
                                                                                (Expr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [ (Astd
                                                                                    "\194\1676.5#2") ]
                                                                                  tt
                                                                                  (Ebound
                                                                                    _
                                                                                    (Expr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [ (Aloc
                                                                                        Loc_unknown); Aexpr; (Avalue
                                                                                        (Ainteger
                                                                                          (Signed
                                                                                            Int_))) ]
                                                                                      tt
                                                                                      (Ewseq
                                                                                        _
                                                                                        (
                                                                                          (Pattern
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (CaseCtor
                                                                                              _
                                                                                              Ctuple
                                                                                              [ (Pattern
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [  ]
                                                                                                tt
                                                                                                (CaseBase
                                                                                                  _
                                                                                                  (
                                                                                                    (Some
                                                                                                      (Symbol
                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                        684
                                                                                                        SD_None))
                                                                                                    ,
                                                                                                    (BTy_loaded
                                                                                                      OTy_integer)
                                                                                                  ))); (Pattern
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [  ]
                                                                                                tt
                                                                                                (CaseBase
                                                                                                  _
                                                                                                  (
                                                                                                    (Some
                                                                                                      (Symbol
                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                        685
                                                                                                        SD_None))
                                                                                                    ,
                                                                                                    (BTy_loaded
                                                                                                      OTy_integer)
                                                                                                  ))) ]))
                                                                                          ,
                                                                                          (Expr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (Eunseq
                                                                                              _
                                                                                              [ (Expr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [ (Aloc
                                                                                                  Loc_unknown); Aexpr; (Avalue
                                                                                                  (Ainteger
                                                                                                    (Signed
                                                                                                      Int_))) ]
                                                                                                tt
                                                                                                (Ewseq
                                                                                                  _
                                                                                                  (
                                                                                                    (Pattern
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (CaseCtor
                                                                                                        _
                                                                                                        Ctuple
                                                                                                        [ (Pattern
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [  ]
                                                                                                          tt
                                                                                                          (CaseBase
                                                                                                            _
                                                                                                            (
                                                                                                              (Some
                                                                                                                (Symbol
                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                  689
                                                                                                                  SD_None))
                                                                                                              ,
                                                                                                              (BTy_loaded
                                                                                                                OTy_pointer)
                                                                                                            ))); (Pattern
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [  ]
                                                                                                          tt
                                                                                                          (CaseBase
                                                                                                            _
                                                                                                            (
                                                                                                              (Some
                                                                                                                (Symbol
                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                  690
                                                                                                                  SD_None))
                                                                                                              ,
                                                                                                              (BTy_loaded
                                                                                                                OTy_pointer)
                                                                                                            ))) ]))
                                                                                                    ,
                                                                                                    (Expr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (Eunseq
                                                                                                        _
                                                                                                        [ (Expr
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [ (Aloc
                                                                                                            Loc_unknown); Aexpr ]
                                                                                                          tt
                                                                                                          (Ewseq
                                                                                                            _
                                                                                                            (
                                                                                                              (Pattern
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (CaseBase
                                                                                                                  _
                                                                                                                  (
                                                                                                                    (Some
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        694
                                                                                                                        SD_None))
                                                                                                                    ,
                                                                                                                    (BTy_object
                                                                                                                      OTy_pointer)
                                                                                                                  )))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Aloc
                                                                                                                  Loc_unknown); Aexpr ]
                                                                                                                tt
                                                                                                                (Epure
                                                                                                                  _
                                                                                                                  (Pexpr
                                                                                                                    _
                                                                                                                    Loc_unknown
                                                                                                                    [  ]
                                                                                                                    tt
                                                                                                                    (PEsym
                                                                                                                      _
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        641
                                                                                                                        (SD_ObjectAddress
                                                                                                                          "h"))))))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (Eaction
                                                                                                                  _
                                                                                                                  {|
                                                                                                                    paction_polarity :=
                                                                                                                      Pos;
                                                                                                                    paction_action :=
                                                                                                                      {|
                                                                                                                        action_loc :=
                                                                                                                          Loc_unknown;
                                                                                                                        action_content :=
                                                                                                                          (Load
                                                                                                                            _
                                                                                                                            {|
                                                                                                                              MuCore.loc :=
                                                                                                                                Loc_unknown;
                                                                                                                              MuCore.annot :=
                                                                                                                                [  ];
                                                                                                                              MuCore.ct :=
                                                                                                                                (SCtypes.Pointer
                                                                                                                                  (SCtypes.Struct
                                                                                                                                    (Symbol
                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                      629
                                                                                                                                      (SD_Id
                                                                                                                                        "int_queueCell"))))
                                                                                                                            |}
                                                                                                                            (Pexpr
                                                                                                                              _
                                                                                                                              Loc_unknown
                                                                                                                              [  ]
                                                                                                                              tt
                                                                                                                              (PEsym
                                                                                                                                _
                                                                                                                                (Symbol
                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                  694
                                                                                                                                  SD_None)))
                                                                                                                            NA)
                                                                                                                      |}
                                                                                                                  |}))
                                                                                                            ))); (Expr
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [ (Aloc
                                                                                                            Loc_unknown); Aexpr ]
                                                                                                          tt
                                                                                                          (Ewseq
                                                                                                            _
                                                                                                            (
                                                                                                              (Pattern
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (CaseBase
                                                                                                                  _
                                                                                                                  (
                                                                                                                    (Some
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        700
                                                                                                                        SD_None))
                                                                                                                    ,
                                                                                                                    (BTy_object
                                                                                                                      OTy_pointer)
                                                                                                                  )))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Aloc
                                                                                                                  Loc_unknown); Aexpr; (Astd
                                                                                                                  "\194\1676.5.2.3#4, sentence 2") ]
                                                                                                                tt
                                                                                                                (Esseq
                                                                                                                  _
                                                                                                                  (
                                                                                                                    (Pattern
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (CaseBase
                                                                                                                        _
                                                                                                                        (
                                                                                                                          (Some
                                                                                                                            (Symbol
                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                              695
                                                                                                                              SD_None))
                                                                                                                          ,
                                                                                                                          (BTy_loaded
                                                                                                                            OTy_pointer)
                                                                                                                        )))
                                                                                                                    ,
                                                                                                                    (Expr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [ (Aloc
                                                                                                                        Loc_unknown); Aexpr ]
                                                                                                                      tt
                                                                                                                      (Ewseq
                                                                                                                        _
                                                                                                                        (
                                                                                                                          (Pattern
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (CaseBase
                                                                                                                              _
                                                                                                                              (
                                                                                                                                (Some
                                                                                                                                  (Symbol
                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                    699
                                                                                                                                    SD_None))
                                                                                                                                ,
                                                                                                                                (BTy_object
                                                                                                                                  OTy_pointer)
                                                                                                                              )))
                                                                                                                          ,
                                                                                                                          (Expr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [ (Aloc
                                                                                                                              Loc_unknown); Aexpr ]
                                                                                                                            tt
                                                                                                                            (Epure
                                                                                                                              _
                                                                                                                              (Pexpr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (PEsym
                                                                                                                                  _
                                                                                                                                  (Symbol
                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                    638
                                                                                                                                    (SD_ObjectAddress
                                                                                                                                      "q"))))))
                                                                                                                          ,
                                                                                                                          (Expr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (Eaction
                                                                                                                              _
                                                                                                                              {|
                                                                                                                                paction_polarity :=
                                                                                                                                  Pos;
                                                                                                                                paction_action :=
                                                                                                                                  {|
                                                                                                                                    action_loc :=
                                                                                                                                      Loc_unknown;
                                                                                                                                    action_content :=
                                                                                                                                      (Load
                                                                                                                                        _
                                                                                                                                        {|
                                                                                                                                          MuCore.loc :=
                                                                                                                                            Loc_unknown;
                                                                                                                                          MuCore.annot :=
                                                                                                                                            [  ];
                                                                                                                                          MuCore.ct :=
                                                                                                                                            (SCtypes.Pointer
                                                                                                                                              (SCtypes.Struct
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  628
                                                                                                                                                  (SD_Id
                                                                                                                                                    "int_queue"))))
                                                                                                                                        |}
                                                                                                                                        (Pexpr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (PEsym
                                                                                                                                            _
                                                                                                                                            (Symbol
                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                              699
                                                                                                                                              SD_None)))
                                                                                                                                        NA)
                                                                                                                                  |}
                                                                                                                              |}))
                                                                                                                        )))
                                                                                                                    ,
                                                                                                                    (Expr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (Epure
                                                                                                                        _
                                                                                                                        (Pexpr
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [  ]
                                                                                                                          tt
                                                                                                                          (PEmember_shift
                                                                                                                            _
                                                                                                                            (Pexpr
                                                                                                                              _
                                                                                                                              Loc_unknown
                                                                                                                              [  ]
                                                                                                                              tt
                                                                                                                              (PEsym
                                                                                                                                _
                                                                                                                                (Symbol
                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                  695
                                                                                                                                  SD_None)))
                                                                                                                            (Symbol
                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                              628
                                                                                                                              (SD_Id
                                                                                                                                "int_queue"))
                                                                                                                            (Identifier
                                                                                                                              Loc_unknown
                                                                                                                              "back")))))
                                                                                                                  )))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (Eaction
                                                                                                                  _
                                                                                                                  {|
                                                                                                                    paction_polarity :=
                                                                                                                      Pos;
                                                                                                                    paction_action :=
                                                                                                                      {|
                                                                                                                        action_loc :=
                                                                                                                          Loc_unknown;
                                                                                                                        action_content :=
                                                                                                                          (Load
                                                                                                                            _
                                                                                                                            {|
                                                                                                                              MuCore.loc :=
                                                                                                                                Loc_unknown;
                                                                                                                              MuCore.annot :=
                                                                                                                                [  ];
                                                                                                                              MuCore.ct :=
                                                                                                                                (SCtypes.Pointer
                                                                                                                                  (SCtypes.Struct
                                                                                                                                    (Symbol
                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                      629
                                                                                                                                      (SD_Id
                                                                                                                                        "int_queueCell"))))
                                                                                                                            |}
                                                                                                                            (Pexpr
                                                                                                                              _
                                                                                                                              Loc_unknown
                                                                                                                              [  ]
                                                                                                                              tt
                                                                                                                              (PEsym
                                                                                                                                _
                                                                                                                                (Symbol
                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                  700
                                                                                                                                  SD_None)))
                                                                                                                            NA)
                                                                                                                      |}
                                                                                                                  |}))
                                                                                                            ))) ]))
                                                                                                    ,
                                                                                                    (Expr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (Ewseq
                                                                                                        _
                                                                                                        (
                                                                                                          (Pattern
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (CaseBase
                                                                                                              _
                                                                                                              (
                                                                                                                (Some
                                                                                                                  (Symbol
                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                    693
                                                                                                                    SD_None))
                                                                                                                ,
                                                                                                                BTy_boolean
                                                                                                              )))
                                                                                                          ,
                                                                                                          (Expr
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (Ememop
                                                                                                              _
                                                                                                              (PtrEq
                                                                                                                _
                                                                                                                (
                                                                                                                  (Pexpr
                                                                                                                    _
                                                                                                                    Loc_unknown
                                                                                                                    [  ]
                                                                                                                    tt
                                                                                                                    (PEsym
                                                                                                                      _
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        689
                                                                                                                        SD_None)))
                                                                                                                  ,
                                                                                                                  (Pexpr
                                                                                                                    _
                                                                                                                    Loc_unknown
                                                                                                                    [  ]
                                                                                                                    tt
                                                                                                                    (PEsym
                                                                                                                      _
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        690
                                                                                                                        SD_None)))
                                                                                                                ))))
                                                                                                          ,
                                                                                                          (Expr
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (Epure
                                                                                                              _
                                                                                                              (Pexpr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Astd
                                                                                                                  "\194\1676.5.9#3"); Anot_explode ]
                                                                                                                tt
                                                                                                                (PEbool_to_integer
                                                                                                                  _
                                                                                                                  (Pexpr
                                                                                                                    _
                                                                                                                    Loc_unknown
                                                                                                                    [  ]
                                                                                                                    tt
                                                                                                                    (PEsym
                                                                                                                      _
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        693
                                                                                                                        SD_None)))))))
                                                                                                        )))
                                                                                                  ))); (Expr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [ (Aloc
                                                                                                  Loc_unknown); Aexpr; (Avalue
                                                                                                  (Ainteger
                                                                                                    (Signed
                                                                                                      Int_))) ]
                                                                                                tt
                                                                                                (Epure
                                                                                                  _
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (PEval
                                                                                                      _
                                                                                                      (V
                                                                                                        _
                                                                                                        tt
                                                                                                        (Vobject
                                                                                                          _
                                                                                                          (OV
                                                                                                            _
                                                                                                            tt
                                                                                                            (OVinteger
                                                                                                              _
                                                                                                              (Mem.IVint 0))))))))) ]))
                                                                                          ,
                                                                                          (Expr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (Epure
                                                                                              _
                                                                                              (Pexpr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [ (Astd
                                                                                                  "\194\1676.5.9#3"); Anot_explode ]
                                                                                                tt
                                                                                                (PEbool_to_integer
                                                                                                  _
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [ (Astd
                                                                                                      "\194\1676.5.9#4, sentence 3") ]
                                                                                                    tt
                                                                                                    (PEop
                                                                                                      _
                                                                                                      Core.OpEq
                                                                                                      (Pexpr
                                                                                                        _
                                                                                                        Loc_unknown
                                                                                                        [ (Astd
                                                                                                          "\194\1676.5.9#4, sentence 1") ]
                                                                                                        tt
                                                                                                        (PEconv_int
                                                                                                          _
                                                                                                          (Pexpr
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (PEval
                                                                                                              _
                                                                                                              (V
                                                                                                                _
                                                                                                                tt
                                                                                                                (Vctype
                                                                                                                  _
                                                                                                                  (Ctype
                                                                                                                    [  ]
                                                                                                                    (Ctype.Basic
                                                                                                                      (Ctype.Integer
                                                                                                                        (Signed
                                                                                                                          Int_))))))))
                                                                                                          (Pexpr
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (PEsym
                                                                                                              _
                                                                                                              (Symbol
                                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                684
                                                                                                                SD_None)))))
                                                                                                      (Pexpr
                                                                                                        _
                                                                                                        Loc_unknown
                                                                                                        [ (Astd
                                                                                                          "\194\1676.5.9#4, sentence 1") ]
                                                                                                        tt
                                                                                                        (PEconv_int
                                                                                                          _
                                                                                                          (Pexpr
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (PEval
                                                                                                              _
                                                                                                              (V
                                                                                                                _
                                                                                                                tt
                                                                                                                (Vctype
                                                                                                                  _
                                                                                                                  (Ctype
                                                                                                                    [  ]
                                                                                                                    (Ctype.Basic
                                                                                                                      (Ctype.Integer
                                                                                                                        (Signed
                                                                                                                          Int_))))))))
                                                                                                          (Pexpr
                                                                                                            _
                                                                                                            Loc_unknown
                                                                                                            [  ]
                                                                                                            tt
                                                                                                            (PEsym
                                                                                                              _
                                                                                                              (Symbol
                                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                685
                                                                                                                SD_None)))))))))))
                                                                                        )))))
                                                                                ,
                                                                                (Expr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (Esseq
                                                                                    _
                                                                                    (
                                                                                      (Pattern
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (CaseBase
                                                                                          _
                                                                                          (
                                                                                            (Some
                                                                                              (Symbol
                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                674
                                                                                                SD_None))
                                                                                            ,
                                                                                            BTy_boolean
                                                                                          )))
                                                                                      ,
                                                                                      (Expr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (Epure
                                                                                          _
                                                                                          (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEnot
                                                                                              _
                                                                                              (Pexpr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [  ]
                                                                                                tt
                                                                                                (PEop
                                                                                                  _
                                                                                                  Core.OpEq
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (PEsym
                                                                                                      _
                                                                                                      (Symbol
                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                        682
                                                                                                        SD_None)))
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (PEval
                                                                                                      _
                                                                                                      (V
                                                                                                        _
                                                                                                        tt
                                                                                                        (Vobject
                                                                                                          _
                                                                                                          (OV
                                                                                                            _
                                                                                                            tt
                                                                                                            (OVinteger
                                                                                                              _
                                                                                                              (Mem.IVint 1)))))))))))))
                                                                                      ,
                                                                                      (Expr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (Eif
                                                                                          _
                                                                                          (
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  674
                                                                                                  SD_None)))
                                                                                            ,
                                                                                            (Expr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [ (Aloc
                                                                                                Loc_unknown); Astmt ]
                                                                                              tt
                                                                                              (Esseq
                                                                                                _
                                                                                                (
                                                                                                  (Pattern
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (CaseBase
                                                                                                      _
                                                                                                      (
                                                                                                        (Some
                                                                                                          (Symbol
                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                            642
                                                                                                            (SD_ObjectAddress
                                                                                                              "x")))
                                                                                                        ,
                                                                                                        (BTy_object
                                                                                                          OTy_pointer)
                                                                                                      )))
                                                                                                  ,
                                                                                                  (Expr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (Eaction
                                                                                                      _
                                                                                                      {|
                                                                                                        paction_polarity :=
                                                                                                          Pos;
                                                                                                        paction_action :=
                                                                                                          {|
                                                                                                            action_loc :=
                                                                                                              Loc_unknown;
                                                                                                            action_content :=
                                                                                                              (Create
                                                                                                                _
                                                                                                                (Pexpr
                                                                                                                  _
                                                                                                                  Loc_unknown
                                                                                                                  [  ]
                                                                                                                  tt
                                                                                                                  (PEapply_fun
                                                                                                                    _
                                                                                                                    F_align_of
                                                                                                                    [ (Pexpr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (PEval
                                                                                                                        _
                                                                                                                        (V
                                                                                                                          _
                                                                                                                          tt
                                                                                                                          (Vctype
                                                                                                                            _
                                                                                                                            (Ctype
                                                                                                                              [ (Aloc
                                                                                                                                Loc_unknown) ]
                                                                                                                              (Ctype.Basic
                                                                                                                                (Ctype.Integer
                                                                                                                                  (Signed
                                                                                                                                    Int_)))))))) ]))
                                                                                                                {|
                                                                                                                  MuCore.loc :=
                                                                                                                    Loc_unknown;
                                                                                                                  MuCore.annot :=
                                                                                                                    [  ];
                                                                                                                  MuCore.ct :=
                                                                                                                    (SCtypes.Integer
                                                                                                                      (Signed
                                                                                                                        Int_))
                                                                                                                |}
                                                                                                                (PrefSource
                                                                                                                  Loc_unknown
                                                                                                                  [ (Symbol
                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                    639
                                                                                                                    (SD_Id
                                                                                                                      "IntQueue_pop")); (Symbol
                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                    642
                                                                                                                    (SD_ObjectAddress
                                                                                                                      "x")) ]))
                                                                                                          |}
                                                                                                      |}))
                                                                                                  ,
                                                                                                  (Expr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [  ]
                                                                                                    tt
                                                                                                    (Esseq
                                                                                                      _
                                                                                                      (
                                                                                                        (Pattern
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [  ]
                                                                                                          tt
                                                                                                          (CaseBase
                                                                                                            _
                                                                                                            (
                                                                                                              None
                                                                                                              ,
                                                                                                              BTy_unit
                                                                                                            )))
                                                                                                        ,
                                                                                                        (Expr
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [ (Aloc
                                                                                                            Loc_unknown); Astmt ]
                                                                                                          tt
                                                                                                          (Esseq
                                                                                                            _
                                                                                                            (
                                                                                                              (Pattern
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (CaseBase
                                                                                                                  _
                                                                                                                  (
                                                                                                                    (Some
                                                                                                                      (Symbol
                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                        701
                                                                                                                        SD_None))
                                                                                                                    ,
                                                                                                                    (BTy_loaded
                                                                                                                      OTy_integer)
                                                                                                                  )))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Astd
                                                                                                                  "\194\1676.5#2") ]
                                                                                                                tt
                                                                                                                (Ebound
                                                                                                                  _
                                                                                                                  (Expr
                                                                                                                    _
                                                                                                                    Loc_unknown
                                                                                                                    [ (Aloc
                                                                                                                      Loc_unknown); Aexpr; (Avalue
                                                                                                                      (Ainteger
                                                                                                                        (Signed
                                                                                                                          Int_))) ]
                                                                                                                    tt
                                                                                                                    (Ewseq
                                                                                                                      _
                                                                                                                      (
                                                                                                                        (Pattern
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [  ]
                                                                                                                          tt
                                                                                                                          (CaseBase
                                                                                                                            _
                                                                                                                            (
                                                                                                                              (Some
                                                                                                                                (Symbol
                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                  707
                                                                                                                                  SD_None))
                                                                                                                              ,
                                                                                                                              (BTy_object
                                                                                                                                OTy_pointer)
                                                                                                                            )))
                                                                                                                        ,
                                                                                                                        (Expr
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [ (Aloc
                                                                                                                            Loc_unknown); Aexpr; (Astd
                                                                                                                            "\194\1676.5.2.3#4, sentence 2") ]
                                                                                                                          tt
                                                                                                                          (Esseq
                                                                                                                            _
                                                                                                                            (
                                                                                                                              (Pattern
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (CaseBase
                                                                                                                                  _
                                                                                                                                  (
                                                                                                                                    (Some
                                                                                                                                      (Symbol
                                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                        702
                                                                                                                                        SD_None))
                                                                                                                                    ,
                                                                                                                                    (BTy_loaded
                                                                                                                                      OTy_pointer)
                                                                                                                                  )))
                                                                                                                              ,
                                                                                                                              (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [ (Aloc
                                                                                                                                  Loc_unknown); Aexpr ]
                                                                                                                                tt
                                                                                                                                (Ewseq
                                                                                                                                  _
                                                                                                                                  (
                                                                                                                                    (Pattern
                                                                                                                                      _
                                                                                                                                      Loc_unknown
                                                                                                                                      [  ]
                                                                                                                                      tt
                                                                                                                                      (CaseBase
                                                                                                                                        _
                                                                                                                                        (
                                                                                                                                          (Some
                                                                                                                                            (Symbol
                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                              706
                                                                                                                                              SD_None))
                                                                                                                                          ,
                                                                                                                                          (BTy_object
                                                                                                                                            OTy_pointer)
                                                                                                                                        )))
                                                                                                                                    ,
                                                                                                                                    (Expr
                                                                                                                                      _
                                                                                                                                      Loc_unknown
                                                                                                                                      [ (Aloc
                                                                                                                                        Loc_unknown); Aexpr ]
                                                                                                                                      tt
                                                                                                                                      (Epure
                                                                                                                                        _
                                                                                                                                        (Pexpr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (PEsym
                                                                                                                                            _
                                                                                                                                            (Symbol
                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                              641
                                                                                                                                              (SD_ObjectAddress
                                                                                                                                                "h"))))))
                                                                                                                                    ,
                                                                                                                                    (Expr
                                                                                                                                      _
                                                                                                                                      Loc_unknown
                                                                                                                                      [  ]
                                                                                                                                      tt
                                                                                                                                      (Eaction
                                                                                                                                        _
                                                                                                                                        {|
                                                                                                                                          paction_polarity :=
                                                                                                                                            Pos;
                                                                                                                                          paction_action :=
                                                                                                                                            {|
                                                                                                                                              action_loc :=
                                                                                                                                                Loc_unknown;
                                                                                                                                              action_content :=
                                                                                                                                                (Load
                                                                                                                                                  _
                                                                                                                                                  {|
                                                                                                                                                    MuCore.loc :=
                                                                                                                                                      Loc_unknown;
                                                                                                                                                    MuCore.annot :=
                                                                                                                                                      [  ];
                                                                                                                                                    MuCore.ct :=
                                                                                                                                                      (SCtypes.Pointer
                                                                                                                                                        (SCtypes.Struct
                                                                                                                                                          (Symbol
                                                                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                            629
                                                                                                                                                            (SD_Id
                                                                                                                                                              "int_queueCell"))))
                                                                                                                                                  |}
                                                                                                                                                  (Pexpr
                                                                                                                                                    _
                                                                                                                                                    Loc_unknown
                                                                                                                                                    [  ]
                                                                                                                                                    tt
                                                                                                                                                    (PEsym
                                                                                                                                                      _
                                                                                                                                                      (Symbol
                                                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                        706
                                                                                                                                                        SD_None)))
                                                                                                                                                  NA)
                                                                                                                                            |}
                                                                                                                                        |}))
                                                                                                                                  )))
                                                                                                                              ,
                                                                                                                              (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (Epure
                                                                                                                                  _
                                                                                                                                  (Pexpr
                                                                                                                                    _
                                                                                                                                    Loc_unknown
                                                                                                                                    [  ]
                                                                                                                                    tt
                                                                                                                                    (PEmember_shift
                                                                                                                                      _
                                                                                                                                      (Pexpr
                                                                                                                                        _
                                                                                                                                        Loc_unknown
                                                                                                                                        [  ]
                                                                                                                                        tt
                                                                                                                                        (PEsym
                                                                                                                                          _
                                                                                                                                          (Symbol
                                                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                            702
                                                                                                                                            SD_None)))
                                                                                                                                      (Symbol
                                                                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                        629
                                                                                                                                        (SD_Id
                                                                                                                                          "int_queueCell"))
                                                                                                                                      (Identifier
                                                                                                                                        Loc_unknown
                                                                                                                                        "first")))))
                                                                                                                            )))
                                                                                                                        ,
                                                                                                                        (Expr
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [  ]
                                                                                                                          tt
                                                                                                                          (Eaction
                                                                                                                            _
                                                                                                                            {|
                                                                                                                              paction_polarity :=
                                                                                                                                Pos;
                                                                                                                              paction_action :=
                                                                                                                                {|
                                                                                                                                  action_loc :=
                                                                                                                                    Loc_unknown;
                                                                                                                                  action_content :=
                                                                                                                                    (Load
                                                                                                                                      _
                                                                                                                                      {|
                                                                                                                                        MuCore.loc :=
                                                                                                                                          Loc_unknown;
                                                                                                                                        MuCore.annot :=
                                                                                                                                          [  ];
                                                                                                                                        MuCore.ct :=
                                                                                                                                          (SCtypes.Integer
                                                                                                                                            (Signed
                                                                                                                                              Int_))
                                                                                                                                      |}
                                                                                                                                      (Pexpr
                                                                                                                                        _
                                                                                                                                        Loc_unknown
                                                                                                                                        [  ]
                                                                                                                                        tt
                                                                                                                                        (PEsym
                                                                                                                                          _
                                                                                                                                          (Symbol
                                                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                            707
                                                                                                                                            SD_None)))
                                                                                                                                      NA)
                                                                                                                                |}
                                                                                                                            |}))
                                                                                                                      )))))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (Eaction
                                                                                                                  _
                                                                                                                  {|
                                                                                                                    paction_polarity :=
                                                                                                                      Pos;
                                                                                                                    paction_action :=
                                                                                                                      {|
                                                                                                                        action_loc :=
                                                                                                                          Loc_unknown;
                                                                                                                        action_content :=
                                                                                                                          (Store
                                                                                                                            _
                                                                                                                            false
                                                                                                                            {|
                                                                                                                              MuCore.loc :=
                                                                                                                                Loc_unknown;
                                                                                                                              MuCore.annot :=
                                                                                                                                [  ];
                                                                                                                              MuCore.ct :=
                                                                                                                                (SCtypes.Integer
                                                                                                                                  (Signed
                                                                                                                                    Int_))
                                                                                                                            |}
                                                                                                                            (Pexpr
                                                                                                                              _
                                                                                                                              Loc_unknown
                                                                                                                              [  ]
                                                                                                                              tt
                                                                                                                              (PEsym
                                                                                                                                _
                                                                                                                                (Symbol
                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                  642
                                                                                                                                  (SD_ObjectAddress
                                                                                                                                    "x"))))
                                                                                                                            (Pexpr
                                                                                                                              _
                                                                                                                              Loc_unknown
                                                                                                                              [  ]
                                                                                                                              tt
                                                                                                                              (PEconv_loaded_int
                                                                                                                                _
                                                                                                                                (Pexpr
                                                                                                                                  _
                                                                                                                                  Loc_unknown
                                                                                                                                  [  ]
                                                                                                                                  tt
                                                                                                                                  (PEval
                                                                                                                                    _
                                                                                                                                    (V
                                                                                                                                      _
                                                                                                                                      tt
                                                                                                                                      (Vctype
                                                                                                                                        _
                                                                                                                                        (Ctype
                                                                                                                                          [ (Aloc
                                                                                                                                            Loc_unknown) ]
                                                                                                                                          (Ctype.Basic
                                                                                                                                            (Ctype.Integer
                                                                                                                                              (Signed
                                                                                                                                                Int_))))))))
                                                                                                                                (Pexpr
                                                                                                                                  _
                                                                                                                                  Loc_unknown
                                                                                                                                  [  ]
                                                                                                                                  tt
                                                                                                                                  (PEsym
                                                                                                                                    _
                                                                                                                                    (Symbol
                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                      701
                                                                                                                                      SD_None)))))
                                                                                                                            NA)
                                                                                                                      |}
                                                                                                                  |}))
                                                                                                            )))
                                                                                                        ,
                                                                                                        (Expr
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [  ]
                                                                                                          tt
                                                                                                          (Esseq
                                                                                                            _
                                                                                                            (
                                                                                                              (Pattern
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (CaseBase
                                                                                                                  _
                                                                                                                  (
                                                                                                                    None
                                                                                                                    ,
                                                                                                                    BTy_unit
                                                                                                                  )))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Aloc
                                                                                                                  Loc_unknown); Astmt ]
                                                                                                                tt
                                                                                                                (Esseq
                                                                                                                  _
                                                                                                                  (
                                                                                                                    (Pattern
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (CaseBase
                                                                                                                        _
                                                                                                                        (
                                                                                                                          None
                                                                                                                          ,
                                                                                                                          BTy_unit
                                                                                                                        )))
                                                                                                                    ,
                                                                                                                    (Expr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [ (Astd
                                                                                                                        "\194\1676.5#2") ]
                                                                                                                      tt
                                                                                                                      (Ebound
                                                                                                                        _
                                                                                                                        (Expr
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [ (Aloc
                                                                                                                            Loc_unknown); Aexpr; (Astd
                                                                                                                            "\194\1676.5.2.2#10, sentence 1") ]
                                                                                                                          tt
                                                                                                                          (Esseq
                                                                                                                            _
                                                                                                                            (
                                                                                                                              (Pattern
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (CaseCtor
                                                                                                                                  _
                                                                                                                                  Ctuple
                                                                                                                                  [ (Pattern
                                                                                                                                    _
                                                                                                                                    Loc_unknown
                                                                                                                                    [  ]
                                                                                                                                    tt
                                                                                                                                    (CaseCtor
                                                                                                                                      _
                                                                                                                                      Ctuple
                                                                                                                                      [ (Pattern
                                                                                                                                        _
                                                                                                                                        Loc_unknown
                                                                                                                                        [  ]
                                                                                                                                        tt
                                                                                                                                        (CaseBase
                                                                                                                                          _
                                                                                                                                          (
                                                                                                                                            (Some
                                                                                                                                              (Symbol
                                                                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                709
                                                                                                                                                SD_None))
                                                                                                                                            ,
                                                                                                                                            (BTy_loaded
                                                                                                                                              OTy_pointer)
                                                                                                                                          ))); (Pattern
                                                                                                                                        _
                                                                                                                                        Loc_unknown
                                                                                                                                        [  ]
                                                                                                                                        tt
                                                                                                                                        (CaseCtor
                                                                                                                                          _
                                                                                                                                          Ctuple
                                                                                                                                          [ (Pattern
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (CaseBase
                                                                                                                                              _
                                                                                                                                              (
                                                                                                                                                (Some
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    710
                                                                                                                                                    SD_None))
                                                                                                                                                ,
                                                                                                                                                BTy_ctype
                                                                                                                                              ))); (Pattern
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (CaseBase
                                                                                                                                              _
                                                                                                                                              (
                                                                                                                                                (Some
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    711
                                                                                                                                                    SD_None))
                                                                                                                                                ,
                                                                                                                                                (BTy_list
                                                                                                                                                  BTy_ctype)
                                                                                                                                              ))); (Pattern
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (CaseBase
                                                                                                                                              _
                                                                                                                                              (
                                                                                                                                                (Some
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    712
                                                                                                                                                    SD_None))
                                                                                                                                                ,
                                                                                                                                                BTy_boolean
                                                                                                                                              ))); (Pattern
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (CaseBase
                                                                                                                                              _
                                                                                                                                              (
                                                                                                                                                (Some
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    713
                                                                                                                                                    SD_None))
                                                                                                                                                ,
                                                                                                                                                BTy_boolean
                                                                                                                                              ))) ])) ])); (Pattern
                                                                                                                                    _
                                                                                                                                    Loc_unknown
                                                                                                                                    [  ]
                                                                                                                                    tt
                                                                                                                                    (CaseBase
                                                                                                                                      _
                                                                                                                                      (
                                                                                                                                        (Some
                                                                                                                                          (Symbol
                                                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                            715
                                                                                                                                            SD_None))
                                                                                                                                        ,
                                                                                                                                        (BTy_loaded
                                                                                                                                          OTy_pointer)
                                                                                                                                      ))) ]))
                                                                                                                              ,
                                                                                                                              (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [ (Astd
                                                                                                                                  "\194\1676.5.2.2#4, sentence 2") ]
                                                                                                                                tt
                                                                                                                                (Eunseq
                                                                                                                                  _
                                                                                                                                  [ (Expr
                                                                                                                                    _
                                                                                                                                    Loc_unknown
                                                                                                                                    [  ]
                                                                                                                                    tt
                                                                                                                                    (Esseq
                                                                                                                                      _
                                                                                                                                      (
                                                                                                                                        (Pattern
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (CaseBase
                                                                                                                                            _
                                                                                                                                            (
                                                                                                                                              (Some
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  708
                                                                                                                                                  SD_None))
                                                                                                                                              ,
                                                                                                                                              (BTy_loaded
                                                                                                                                                OTy_pointer)
                                                                                                                                            )))
                                                                                                                                        ,
                                                                                                                                        (Expr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [ (Aloc
                                                                                                                                            Loc_unknown); Aexpr ]
                                                                                                                                          tt
                                                                                                                                          (Epure
                                                                                                                                            _
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEval
                                                                                                                                                _
                                                                                                                                                (V
                                                                                                                                                  _
                                                                                                                                                  tt
                                                                                                                                                  (Vobject
                                                                                                                                                    _
                                                                                                                                                    (OV
                                                                                                                                                      _
                                                                                                                                                      tt
                                                                                                                                                      (OVpointer
                                                                                                                                                        _
                                                                                                                                                        (Mem.PVfunptr (Symbol
                                                                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                          636
                                                                                                                                                          (SD_Id
                                                                                                                                                            "freeIntQueueCell")))))))))))
                                                                                                                                        ,
                                                                                                                                        (Expr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (Epure
                                                                                                                                            _
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEctor
                                                                                                                                                _
                                                                                                                                                Ctuple
                                                                                                                                                [ (Pexpr
                                                                                                                                                  _
                                                                                                                                                  Loc_unknown
                                                                                                                                                  [  ]
                                                                                                                                                  tt
                                                                                                                                                  (PEsym
                                                                                                                                                    _
                                                                                                                                                    (Symbol
                                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                      708
                                                                                                                                                      SD_None))); (Pexpr
                                                                                                                                                  _
                                                                                                                                                  Loc_unknown
                                                                                                                                                  [  ]
                                                                                                                                                  tt
                                                                                                                                                  (PEcfunction
                                                                                                                                                    _
                                                                                                                                                    (Pexpr
                                                                                                                                                      _
                                                                                                                                                      Loc_unknown
                                                                                                                                                      [  ]
                                                                                                                                                      tt
                                                                                                                                                      (PEsym
                                                                                                                                                        _
                                                                                                                                                        (Symbol
                                                                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                          708
                                                                                                                                                          SD_None))))) ]))))
                                                                                                                                      ))); (Expr
                                                                                                                                    _
                                                                                                                                    Loc_unknown
                                                                                                                                    [ (Aloc
                                                                                                                                      Loc_unknown); Aexpr ]
                                                                                                                                    tt
                                                                                                                                    (Ewseq
                                                                                                                                      _
                                                                                                                                      (
                                                                                                                                        (Pattern
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (CaseBase
                                                                                                                                            _
                                                                                                                                            (
                                                                                                                                              (Some
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  716
                                                                                                                                                  SD_None))
                                                                                                                                              ,
                                                                                                                                              (BTy_object
                                                                                                                                                OTy_pointer)
                                                                                                                                            )))
                                                                                                                                        ,
                                                                                                                                        (Expr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [ (Aloc
                                                                                                                                            Loc_unknown); Aexpr ]
                                                                                                                                          tt
                                                                                                                                          (Epure
                                                                                                                                            _
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEsym
                                                                                                                                                _
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  641
                                                                                                                                                  (SD_ObjectAddress
                                                                                                                                                    "h"))))))
                                                                                                                                        ,
                                                                                                                                        (Expr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (Eaction
                                                                                                                                            _
                                                                                                                                            {|
                                                                                                                                              paction_polarity :=
                                                                                                                                                Pos;
                                                                                                                                              paction_action :=
                                                                                                                                                {|
                                                                                                                                                  action_loc :=
                                                                                                                                                    Loc_unknown;
                                                                                                                                                  action_content :=
                                                                                                                                                    (Load
                                                                                                                                                      _
                                                                                                                                                      {|
                                                                                                                                                        MuCore.loc :=
                                                                                                                                                          Loc_unknown;
                                                                                                                                                        MuCore.annot :=
                                                                                                                                                          [  ];
                                                                                                                                                        MuCore.ct :=
                                                                                                                                                          (SCtypes.Pointer
                                                                                                                                                            (SCtypes.Struct
                                                                                                                                                              (Symbol
                                                                                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                                629
                                                                                                                                                                (SD_Id
                                                                                                                                                                  "int_queueCell"))))
                                                                                                                                                      |}
                                                                                                                                                      (Pexpr
                                                                                                                                                        _
                                                                                                                                                        Loc_unknown
                                                                                                                                                        [  ]
                                                                                                                                                        tt
                                                                                                                                                        (PEsym
                                                                                                                                                          _
                                                                                                                                                          (Symbol
                                                                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                            716
                                                                                                                                                            SD_None)))
                                                                                                                                                      NA)
                                                                                                                                                |}
                                                                                                                                            |}))
                                                                                                                                      ))) ]))
                                                                                                                              ,
                                                                                                                              (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [ Anot_explode ]
                                                                                                                                tt
                                                                                                                                (Eif
                                                                                                                                  _
                                                                                                                                  (
                                                                                                                                    (Pexpr
                                                                                                                                      _
                                                                                                                                      Loc_unknown
                                                                                                                                      [  ]
                                                                                                                                      tt
                                                                                                                                      (PEnot
                                                                                                                                        _
                                                                                                                                        (Pexpr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (PEop
                                                                                                                                            _
                                                                                                                                            Core.OpEq
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEapply_fun
                                                                                                                                                _
                                                                                                                                                F_params_length
                                                                                                                                                [ (Pexpr
                                                                                                                                                  _
                                                                                                                                                  Loc_unknown
                                                                                                                                                  [  ]
                                                                                                                                                  tt
                                                                                                                                                  (PEsym
                                                                                                                                                    _
                                                                                                                                                    (Symbol
                                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                      711
                                                                                                                                                      SD_None))) ]))
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEval
                                                                                                                                                _
                                                                                                                                                (V
                                                                                                                                                  _
                                                                                                                                                  tt
                                                                                                                                                  (Vobject
                                                                                                                                                    _
                                                                                                                                                    (OV
                                                                                                                                                      _
                                                                                                                                                      tt
                                                                                                                                                      (OVinteger
                                                                                                                                                        _
                                                                                                                                                        (Mem.IVint 1)))))))))))
                                                                                                                                    ,
                                                                                                                                    (Expr
                                                                                                                                      _
                                                                                                                                      Loc_unknown
                                                                                                                                      [  ]
                                                                                                                                      tt
                                                                                                                                      (Epure
                                                                                                                                        _
                                                                                                                                        (Pexpr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [ (Astd
                                                                                                                                            "\194\1676.5.2.2#6, sentence 3") ]
                                                                                                                                          tt
                                                                                                                                          (PEundef
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            UB038_number_of_args))))
                                                                                                                                    ,
                                                                                                                                    (Expr
                                                                                                                                      _
                                                                                                                                      Loc_unknown
                                                                                                                                      [ Anot_explode ]
                                                                                                                                      tt
                                                                                                                                      (Eif
                                                                                                                                        _
                                                                                                                                        (
                                                                                                                                          (Pexpr
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (PEop
                                                                                                                                              _
                                                                                                                                              Core.OpOr
                                                                                                                                              (Pexpr
                                                                                                                                                _
                                                                                                                                                Loc_unknown
                                                                                                                                                [  ]
                                                                                                                                                tt
                                                                                                                                                (PEsym
                                                                                                                                                  _
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    712
                                                                                                                                                    SD_None)))
                                                                                                                                              (Pexpr
                                                                                                                                                _
                                                                                                                                                Loc_unknown
                                                                                                                                                [  ]
                                                                                                                                                tt
                                                                                                                                                (PEnot
                                                                                                                                                  _
                                                                                                                                                  (Pexpr
                                                                                                                                                    _
                                                                                                                                                    Loc_unknown
                                                                                                                                                    [  ]
                                                                                                                                                    tt
                                                                                                                                                    (PEapply_fun
                                                                                                                                                      _
                                                                                                                                                      F_are_compatible
                                                                                                                                                      [ (Pexpr
                                                                                                                                                        _
                                                                                                                                                        Loc_unknown
                                                                                                                                                        [  ]
                                                                                                                                                        tt
                                                                                                                                                        (PEval
                                                                                                                                                          _
                                                                                                                                                          (V
                                                                                                                                                            _
                                                                                                                                                            tt
                                                                                                                                                            (Vctype
                                                                                                                                                              _
                                                                                                                                                              (Ctype
                                                                                                                                                                [ (Aloc
                                                                                                                                                                  Loc_unknown) ]
                                                                                                                                                                Ctype.Void))))); (Pexpr
                                                                                                                                                        _
                                                                                                                                                        Loc_unknown
                                                                                                                                                        [  ]
                                                                                                                                                        tt
                                                                                                                                                        (PEsym
                                                                                                                                                          _
                                                                                                                                                          (Symbol
                                                                                                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                            710
                                                                                                                                                            SD_None))) ]))))))
                                                                                                                                          ,
                                                                                                                                          (Expr
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (Epure
                                                                                                                                              _
                                                                                                                                              (Pexpr
                                                                                                                                                _
                                                                                                                                                Loc_unknown
                                                                                                                                                [ (Astd
                                                                                                                                                  "\194\1676.5.2.2#9") ]
                                                                                                                                                tt
                                                                                                                                                (PEundef
                                                                                                                                                  _
                                                                                                                                                  Loc_unknown
                                                                                                                                                  UB041_function_not_compatible))))
                                                                                                                                          ,
                                                                                                                                          (Expr
                                                                                                                                            _
                                                                                                                                            Loc_unknown
                                                                                                                                            [  ]
                                                                                                                                            tt
                                                                                                                                            (Eccall
                                                                                                                                              _
                                                                                                                                              (
                                                                                                                                                {|
                                                                                                                                                  MuCore.loc :=
                                                                                                                                                    Loc_unknown;
                                                                                                                                                  MuCore.annot :=
                                                                                                                                                    [  ];
                                                                                                                                                  MuCore.ct :=
                                                                                                                                                    (SCtypes.Pointer
                                                                                                                                                      (SCtypes.SCFunction
                                                                                                                                                        (
                                                                                                                                                          (
                                                                                                                                                            {|
                                                                                                                                                              Ctype.const :=
                                                                                                                                                                false;
                                                                                                                                                              Ctype.restrict :=
                                                                                                                                                                false;
                                                                                                                                                              Ctype.volatile :=
                                                                                                                                                                false
                                                                                                                                                            |}
                                                                                                                                                            ,
                                                                                                                                                            SCtypes.Void
                                                                                                                                                          )
                                                                                                                                                          ,
                                                                                                                                                          [ (
                                                                                                                                                            (SCtypes.Pointer
                                                                                                                                                              (SCtypes.Struct
                                                                                                                                                                (Symbol
                                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                                  629
                                                                                                                                                                  (SD_Id
                                                                                                                                                                    "int_queueCell"))))
                                                                                                                                                            ,
                                                                                                                                                            false
                                                                                                                                                          ) ]
                                                                                                                                                          ,
                                                                                                                                                          false
                                                                                                                                                        )))
                                                                                                                                                |}
                                                                                                                                                ,
                                                                                                                                                (Pexpr
                                                                                                                                                  _
                                                                                                                                                  Loc_unknown
                                                                                                                                                  [  ]
                                                                                                                                                  tt
                                                                                                                                                  (PEsym
                                                                                                                                                    _
                                                                                                                                                    (Symbol
                                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                      709
                                                                                                                                                      SD_None)))
                                                                                                                                                ,
                                                                                                                                                [ (Pexpr
                                                                                                                                                  _
                                                                                                                                                  Loc_unknown
                                                                                                                                                  [  ]
                                                                                                                                                  tt
                                                                                                                                                  (PElet
                                                                                                                                                    _
                                                                                                                                                    (Pattern
                                                                                                                                                      _
                                                                                                                                                      Loc_unknown
                                                                                                                                                      [  ]
                                                                                                                                                      tt
                                                                                                                                                      (CaseBase
                                                                                                                                                        _
                                                                                                                                                        (
                                                                                                                                                          (Some
                                                                                                                                                            (Symbol
                                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                              719
                                                                                                                                                              SD_None))
                                                                                                                                                          ,
                                                                                                                                                          BTy_ctype
                                                                                                                                                        )))
                                                                                                                                                    (Pexpr
                                                                                                                                                      _
                                                                                                                                                      Loc_unknown
                                                                                                                                                      [  ]
                                                                                                                                                      tt
                                                                                                                                                      (PEapply_fun
                                                                                                                                                        _
                                                                                                                                                        F_params_nth
                                                                                                                                                        [ (Pexpr
                                                                                                                                                          _
                                                                                                                                                          Loc_unknown
                                                                                                                                                          [  ]
                                                                                                                                                          tt
                                                                                                                                                          (PEsym
                                                                                                                                                            _
                                                                                                                                                            (Symbol
                                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                              711
                                                                                                                                                              SD_None))); (Pexpr
                                                                                                                                                          _
                                                                                                                                                          Loc_unknown
                                                                                                                                                          [  ]
                                                                                                                                                          tt
                                                                                                                                                          (PEval
                                                                                                                                                            _
                                                                                                                                                            (V
                                                                                                                                                              _
                                                                                                                                                              tt
                                                                                                                                                              (Vobject
                                                                                                                                                                _
                                                                                                                                                                (OV
                                                                                                                                                                  _
                                                                                                                                                                  tt
                                                                                                                                                                  (OVinteger
                                                                                                                                                                    _
                                                                                                                                                                    (Mem.IVint 0))))))) ]))
                                                                                                                                                    (Pexpr
                                                                                                                                                      _
                                                                                                                                                      Loc_unknown
                                                                                                                                                      [ Anot_explode ]
                                                                                                                                                      tt
                                                                                                                                                      (PEif
                                                                                                                                                        _
                                                                                                                                                        (Pexpr
                                                                                                                                                          _
                                                                                                                                                          Loc_unknown
                                                                                                                                                          [  ]
                                                                                                                                                          tt
                                                                                                                                                          (PEnot
                                                                                                                                                            _
                                                                                                                                                            (Pexpr
                                                                                                                                                              _
                                                                                                                                                              Loc_unknown
                                                                                                                                                              [  ]
                                                                                                                                                              tt
                                                                                                                                                              (PEapply_fun
                                                                                                                                                                _
                                                                                                                                                                F_are_compatible
                                                                                                                                                                [ (Pexpr
                                                                                                                                                                  _
                                                                                                                                                                  Loc_unknown
                                                                                                                                                                  [  ]
                                                                                                                                                                  tt
                                                                                                                                                                  (PEval
                                                                                                                                                                    _
                                                                                                                                                                    (V
                                                                                                                                                                      _
                                                                                                                                                                      tt
                                                                                                                                                                      (Vctype
                                                                                                                                                                        _
                                                                                                                                                                        (Ctype
                                                                                                                                                                          [ (Aloc
                                                                                                                                                                            Loc_unknown) ]
                                                                                                                                                                          (Ctype.Pointer
                                                                                                                                                                            {|
                                                                                                                                                                              Ctype.const :=
                                                                                                                                                                                false;
                                                                                                                                                                              Ctype.restrict :=
                                                                                                                                                                                false;
                                                                                                                                                                              Ctype.volatile :=
                                                                                                                                                                                false
                                                                                                                                                                            |}
                                                                                                                                                                            (Ctype
                                                                                                                                                                              [  ]
                                                                                                                                                                              (Ctype.Struct
                                                                                                                                                                                (Symbol
                                                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                                                  629
                                                                                                                                                                                  (SD_Id
                                                                                                                                                                                    "int_queueCell")))))))))); (Pexpr
                                                                                                                                                                  _
                                                                                                                                                                  Loc_unknown
                                                                                                                                                                  [  ]
                                                                                                                                                                  tt
                                                                                                                                                                  (PEsym
                                                                                                                                                                    _
                                                                                                                                                                    (Symbol
                                                                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                                      719
                                                                                                                                                                      SD_None))) ]))))
                                                                                                                                                        (Pexpr
                                                                                                                                                          _
                                                                                                                                                          Loc_unknown
                                                                                                                                                          [ (Astd
                                                                                                                                                            "\194\1676.5.2.2#9") ]
                                                                                                                                                          tt
                                                                                                                                                          (PEundef
                                                                                                                                                            _
                                                                                                                                                            Loc_unknown
                                                                                                                                                            UB041_function_not_compatible))
                                                                                                                                                        (Pexpr
                                                                                                                                                          _
                                                                                                                                                          Loc_unknown
                                                                                                                                                          [  ]
                                                                                                                                                          tt
                                                                                                                                                          (PEsym
                                                                                                                                                            _
                                                                                                                                                            (Symbol
                                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                              715
                                                                                                                                                              SD_None))))))) ]
                                                                                                                                              )))
                                                                                                                                        )))
                                                                                                                                  )))
                                                                                                                            )))))
                                                                                                                    ,
                                                                                                                    (Expr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (Epure
                                                                                                                        _
                                                                                                                        (Pexpr
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [  ]
                                                                                                                          tt
                                                                                                                          (PEval
                                                                                                                            _
                                                                                                                            (V
                                                                                                                              _
                                                                                                                              tt
                                                                                                                              (Vunit
                                                                                                                                _))))))
                                                                                                                  )))
                                                                                                              ,
                                                                                                              (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (Esseq
                                                                                                                  _
                                                                                                                  (
                                                                                                                    (Pattern
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (CaseBase
                                                                                                                        _
                                                                                                                        (
                                                                                                                          None
                                                                                                                          ,
                                                                                                                          BTy_unit
                                                                                                                        )))
                                                                                                                    ,
                                                                                                                    (Expr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [ (Aloc
                                                                                                                        Loc_unknown); Astmt ]
                                                                                                                      tt
                                                                                                                      (Esseq
                                                                                                                        _
                                                                                                                        (
                                                                                                                          (Pattern
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (CaseBase
                                                                                                                              _
                                                                                                                              (
                                                                                                                                None
                                                                                                                                ,
                                                                                                                                (BTy_tuple
                                                                                                                                  [ BTy_unit; BTy_unit; BTy_unit ])
                                                                                                                              )))
                                                                                                                          ,
                                                                                                                          (Expr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (Eunseq
                                                                                                                              _
                                                                                                                              [ (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (Eaction
                                                                                                                                  _
                                                                                                                                  {|
                                                                                                                                    paction_polarity :=
                                                                                                                                      Pos;
                                                                                                                                    paction_action :=
                                                                                                                                      {|
                                                                                                                                        action_loc :=
                                                                                                                                          Loc_unknown;
                                                                                                                                        action_content :=
                                                                                                                                          (Kill
                                                                                                                                            _
                                                                                                                                            (Static
                                                                                                                                              (SCtypes.Integer
                                                                                                                                                (Signed
                                                                                                                                                  Int_)))
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEsym
                                                                                                                                                _
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  642
                                                                                                                                                  (SD_ObjectAddress
                                                                                                                                                    "x")))))
                                                                                                                                      |}
                                                                                                                                  |})); (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (Eaction
                                                                                                                                  _
                                                                                                                                  {|
                                                                                                                                    paction_polarity :=
                                                                                                                                      Pos;
                                                                                                                                    paction_action :=
                                                                                                                                      {|
                                                                                                                                        action_loc :=
                                                                                                                                          Loc_unknown;
                                                                                                                                        action_content :=
                                                                                                                                          (Kill
                                                                                                                                            _
                                                                                                                                            (Static
                                                                                                                                              (SCtypes.Pointer
                                                                                                                                                (SCtypes.Struct
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    629
                                                                                                                                                    (SD_Id
                                                                                                                                                      "int_queueCell")))))
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEsym
                                                                                                                                                _
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  641
                                                                                                                                                  (SD_ObjectAddress
                                                                                                                                                    "h")))))
                                                                                                                                      |}
                                                                                                                                  |})); (Expr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (Eaction
                                                                                                                                  _
                                                                                                                                  {|
                                                                                                                                    paction_polarity :=
                                                                                                                                      Pos;
                                                                                                                                    paction_action :=
                                                                                                                                      {|
                                                                                                                                        action_loc :=
                                                                                                                                          Loc_unknown;
                                                                                                                                        action_content :=
                                                                                                                                          (Kill
                                                                                                                                            _
                                                                                                                                            (Static
                                                                                                                                              (SCtypes.Pointer
                                                                                                                                                (SCtypes.Struct
                                                                                                                                                  (Symbol
                                                                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                    628
                                                                                                                                                    (SD_Id
                                                                                                                                                      "int_queue")))))
                                                                                                                                            (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEsym
                                                                                                                                                _
                                                                                                                                                (Symbol
                                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                                  638
                                                                                                                                                  (SD_ObjectAddress
                                                                                                                                                    "q")))))
                                                                                                                                      |}
                                                                                                                                  |})) ]))
                                                                                                                          ,
                                                                                                                          (Expr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (Erun
                                                                                                                              _
                                                                                                                              (
                                                                                                                                (Symbol
                                                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                  673
                                                                                                                                  (SD_Id
                                                                                                                                    "ret_673"))
                                                                                                                                ,
                                                                                                                                [ (Pexpr
                                                                                                                                  _
                                                                                                                                  Loc_unknown
                                                                                                                                  [  ]
                                                                                                                                  tt
                                                                                                                                  (PEval
                                                                                                                                    _
                                                                                                                                    (V
                                                                                                                                      _
                                                                                                                                      tt
                                                                                                                                      (Vunit
                                                                                                                                        _)))) ]
                                                                                                                              )))
                                                                                                                        )))
                                                                                                                    ,
                                                                                                                    (Expr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [  ]
                                                                                                                      tt
                                                                                                                      (Esseq
                                                                                                                        _
                                                                                                                        (
                                                                                                                          (Pattern
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (CaseBase
                                                                                                                              _
                                                                                                                              (
                                                                                                                                None
                                                                                                                                ,
                                                                                                                                BTy_unit
                                                                                                                              )))
                                                                                                                          ,
                                                                                                                          (Expr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (Eaction
                                                                                                                              _
                                                                                                                              {|
                                                                                                                                paction_polarity :=
                                                                                                                                  Pos;
                                                                                                                                paction_action :=
                                                                                                                                  {|
                                                                                                                                    action_loc :=
                                                                                                                                      Loc_unknown;
                                                                                                                                    action_content :=
                                                                                                                                      (Kill
                                                                                                                                        _
                                                                                                                                        (Static
                                                                                                                                          (SCtypes.Integer
                                                                                                                                            (Signed
                                                                                                                                              Int_)))
                                                                                                                                        (Pexpr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (PEsym
                                                                                                                                            _
                                                                                                                                            (Symbol
                                                                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                                              642
                                                                                                                                              (SD_ObjectAddress
                                                                                                                                                "x")))))
                                                                                                                                  |}
                                                                                                                              |}))
                                                                                                                          ,
                                                                                                                          (Expr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (Epure
                                                                                                                              _
                                                                                                                              (Pexpr
                                                                                                                                _
                                                                                                                                Loc_unknown
                                                                                                                                [  ]
                                                                                                                                tt
                                                                                                                                (PEval
                                                                                                                                  _
                                                                                                                                  (V
                                                                                                                                    _
                                                                                                                                    tt
                                                                                                                                    (Vunit
                                                                                                                                      _))))))
                                                                                                                        )))
                                                                                                                  )))
                                                                                                            )))
                                                                                                      )))
                                                                                                )))
                                                                                            ,
                                                                                            (Expr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [ (Aloc
                                                                                                Loc_unknown); Astmt ]
                                                                                              tt
                                                                                              (Epure
                                                                                                _
                                                                                                (Pexpr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (PEval
                                                                                                    _
                                                                                                    (V
                                                                                                      _
                                                                                                      tt
                                                                                                      (Vunit
                                                                                                        _))))))
                                                                                          )))
                                                                                    )))
                                                                              )))
                                                                          ,
                                                                          (Expr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (Esseq
                                                                              _
                                                                              (
                                                                                (Pattern
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (CaseBase
                                                                                    _
                                                                                    (
                                                                                      None
                                                                                      ,
                                                                                      BTy_unit
                                                                                    )))
                                                                                ,
                                                                                (Expr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (Eaction
                                                                                    _
                                                                                    {|
                                                                                      paction_polarity :=
                                                                                        Pos;
                                                                                      paction_action :=
                                                                                        {|
                                                                                          action_loc :=
                                                                                            Loc_unknown;
                                                                                          action_content :=
                                                                                            (Kill
                                                                                              _
                                                                                              (Static
                                                                                                (SCtypes.Pointer
                                                                                                  (SCtypes.Struct
                                                                                                    (Symbol
                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                      629
                                                                                                      (SD_Id
                                                                                                        "int_queueCell")))))
                                                                                              (Pexpr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [  ]
                                                                                                tt
                                                                                                (PEsym
                                                                                                  _
                                                                                                  (Symbol
                                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                    641
                                                                                                    (SD_ObjectAddress
                                                                                                      "h")))))
                                                                                        |}
                                                                                    |}))
                                                                                ,
                                                                                (Expr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (Epure
                                                                                    _
                                                                                    (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEval
                                                                                        _
                                                                                        (V
                                                                                          _
                                                                                          tt
                                                                                          (Vunit
                                                                                            _))))))
                                                                              )))
                                                                        )))
                                                                  )))
                                                            )))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (Esseq
                                                            _
                                                            (
                                                              (Pattern
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (CaseBase
                                                                  _
                                                                  (
                                                                    None
                                                                    ,
                                                                    BTy_unit
                                                                  )))
                                                              ,
                                                              (Expr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (Eaction
                                                                  _
                                                                  {|
                                                                    paction_polarity :=
                                                                      Pos;
                                                                    paction_action :=
                                                                      {|
                                                                        action_loc :=
                                                                          Loc_unknown;
                                                                        action_content :=
                                                                          (Kill
                                                                            _
                                                                            (Static
                                                                              (SCtypes.Pointer
                                                                                (SCtypes.Struct
                                                                                  (Symbol
                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                    628
                                                                                    (SD_Id
                                                                                      "int_queue")))))
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (PEsym
                                                                                _
                                                                                (Symbol
                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                  638
                                                                                  (SD_ObjectAddress
                                                                                    "q")))))
                                                                      |}
                                                                  |}))
                                                              ,
                                                              (Expr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (Epure
                                                                  _
                                                                  (Pexpr
                                                                    _
                                                                    Loc_unknown
                                                                    [  ]
                                                                    tt
                                                                    (PEval
                                                                      _
                                                                      (V
                                                                        _
                                                                        tt
                                                                        (Vunit
                                                                          _))))))
                                                            )))
                                                      )))
                                                )))
                                          )))
                                      ,
                                      (Expr
                                        _
                                        Loc_unknown
                                        [ (Alabel LAreturn); (Aloc Loc_unknown) ]
                                        tt
                                        (Erun
                                          _
                                          (
                                            (Symbol
                                              "e86941afa238f384c6ba57e49e4ef1db"
                                              673
                                              (SD_Id "ret_673"))
                                            ,
                                            [ (Pexpr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (PEval _ (V _ tt (Vunit _)))) ]
                                          )))
                                    )))
                                ,
                                (Sym.map_from_list [ (
                                  (Symbol
                                    "e86941afa238f384c6ba57e49e4ef1db"
                                    673
                                    (SD_Id "ret_673"))
                                  ,
                                  (Return _ Loc_unknown)
                                ) ])
                                ,
                                (ReturnTypes.Computational
                                  (
                                    (Symbol
                                      "e86941afa238f384c6ba57e49e4ef1db"
                                      750
                                      (SD_CN_Id "return"))
                                    ,
                                    (BaseTypes.Unit unit)
                                  )
                                  (Loc_unknown , None)
                                  (LogicalReturnTypes.Resource
                                    (
                                      (Symbol
                                        "e86941afa238f384c6ba57e49e4ef1db"
                                        751
                                        (SD_CN_Id "Q2"))
                                      ,
                                      (
                                        (P
                                          {|
                                            Predicate.name :=
                                              (Owned
                                                (SCtypes.Struct
                                                  (Symbol
                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                    628
                                                    (SD_Id "int_queue")))
                                                Uninit);
                                            Predicate.pointer :=
                                              (IT
                                                _
                                                (Sym
                                                  _
                                                  (Symbol
                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                    672
                                                    (SD_FunArgValue "q")))
                                                (BaseTypes.Loc unit tt)
                                                Loc_unknown);
                                            Predicate.iargs := [  ]
                                          |})
                                        ,
                                        (BaseTypes.Struct
                                          unit
                                          (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            628
                                            (SD_Id "int_queue")))
                                      )
                                    )
                                    (Loc_unknown , None)
                                    (LogicalReturnTypes.Constraint
                                      (T
                                        (IT
                                          _
                                          (Good
                                            _
                                            (SCtypes.Pointer
                                              (SCtypes.Struct
                                                (Symbol
                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                  628
                                                  (SD_Id "int_queue"))))
                                            (IT
                                              _
                                              (Sym
                                                _
                                                (Symbol
                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                  672
                                                  (SD_FunArgValue "q")))
                                              (BaseTypes.Loc unit tt)
                                              Loc_unknown))
                                          (BaseTypes.Bool unit)
                                          Loc_unknown))
                                      (Loc_unknown , None)
                                      LogicalReturnTypes.I)))
                              ))
                          ))
                      ))
                  ))
              ))
          )))
    ))
  Checked
  {|
    accesses := [  ];
    requires :=
      [ (CN_cletResource
        _
        _
        Loc_unknown
        (Symbol "e86941afa238f384c6ba57e49e4ef1db" 748 (SD_CN_Id "Q"))
        (CN_pred
          _
          _
          Loc_unknown
          (CN_owned
            _
            _
            (Some
              (Ctype
                [  ]
                (Ctype.Struct
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    628
                    (SD_Id "int_queue"))))))
          [ (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_value_of_c_atom
                _
                _
                (
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    638
                    (SD_ObjectAddress "q"))
                  ,
                  C_kind_var
                ))
            )) ])); (CN_cconstr
        _
        _
        Loc_unknown
        (CN_assert_exp
          _
          _
          (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_binop
                _
                _
                (
                  CN_and
                  ,
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_not
                        _
                        _
                        (CNExpr
                          _
                          _
                          (
                            Loc_unknown
                            ,
                            (CNExpr_call
                              _
                              _
                              (
                                (Symbol "" 24 (SD_CN_Id "is_null"))
                                ,
                                [ (CNExpr
                                  _
                                  _
                                  (
                                    Loc_unknown
                                    ,
                                    (CNExpr_memberof
                                      _
                                      _
                                      (
                                        (CNExpr
                                          _
                                          _
                                          (
                                            Loc_unknown
                                            ,
                                            (CNExpr_var
                                              _
                                              _
                                              (Symbol
                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                748
                                                (SD_CN_Id "Q")))
                                          ))
                                        ,
                                        (Identifier Loc_unknown "front")
                                      ))
                                  )) ]
                              ))
                          )))
                    ))
                  ,
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_not
                        _
                        _
                        (CNExpr
                          _
                          _
                          (
                            Loc_unknown
                            ,
                            (CNExpr_call
                              _
                              _
                              (
                                (Symbol "" 24 (SD_CN_Id "is_null"))
                                ,
                                [ (CNExpr
                                  _
                                  _
                                  (
                                    Loc_unknown
                                    ,
                                    (CNExpr_memberof
                                      _
                                      _
                                      (
                                        (CNExpr
                                          _
                                          _
                                          (
                                            Loc_unknown
                                            ,
                                            (CNExpr_var
                                              _
                                              _
                                              (Symbol
                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                748
                                                (SD_CN_Id "Q")))
                                          ))
                                        ,
                                        (Identifier Loc_unknown "back")
                                      ))
                                  )) ]
                              ))
                          )))
                    ))
                ))
            )))); (CN_cconstr
        _
        _
        Loc_unknown
        (CN_assert_exp
          _
          _
          (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_call
                _
                _
                (
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    606
                    (SD_CN_Id "eq_testable"))
                  ,
                  [ (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_memberof
                        _
                        _
                        (
                          (CNExpr
                            _
                            _
                            (
                              Loc_unknown
                              ,
                              (CNExpr_var
                                _
                                _
                                (Symbol
                                  "e86941afa238f384c6ba57e49e4ef1db"
                                  748
                                  (SD_CN_Id "Q")))
                            ))
                          ,
                          (Identifier Loc_unknown "front")
                        ))
                    )); (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_memberof
                        _
                        _
                        (
                          (CNExpr
                            _
                            _
                            (
                              Loc_unknown
                              ,
                              (CNExpr_var
                                _
                                _
                                (Symbol
                                  "e86941afa238f384c6ba57e49e4ef1db"
                                  748
                                  (SD_CN_Id "Q")))
                            ))
                          ,
                          (Identifier Loc_unknown "back")
                        ))
                    )) ]
                ))
            )))); (CN_cletResource
        _
        _
        Loc_unknown
        (Symbol "e86941afa238f384c6ba57e49e4ef1db" 749 (SD_CN_Id "B"))
        (CN_pred
          _
          _
          Loc_unknown
          (CN_named
            _
            _
            (Symbol "e86941afa238f384c6ba57e49e4ef1db" 605 (SD_CN_Id "Test")))
          [ (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_memberof
                _
                _
                (
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_var
                        _
                        _
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          748
                          (SD_CN_Id "Q")))
                    ))
                  ,
                  (Identifier Loc_unknown "front")
                ))
            )); (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_memberof
                _
                _
                (
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_var
                        _
                        _
                        (Symbol
                          "e86941afa238f384c6ba57e49e4ef1db"
                          748
                          (SD_CN_Id "Q")))
                    ))
                  ,
                  (Identifier Loc_unknown "back")
                ))
            )) ])) ];
    ensures :=
      [ (CN_cletResource
        _
        _
        Loc_unknown
        (Symbol "e86941afa238f384c6ba57e49e4ef1db" 751 (SD_CN_Id "Q2"))
        (CN_pred
          _
          _
          Loc_unknown
          (CN_block
            _
            _
            (Some
              (Ctype
                [  ]
                (Ctype.Struct
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    628
                    (SD_Id "int_queue"))))))
          [ (CNExpr
            _
            _
            (
              Loc_unknown
              ,
              (CNExpr_value_of_c_atom
                _
                _
                (
                  (Symbol
                    "e86941afa238f384c6ba57e49e4ef1db"
                    638
                    (SD_ObjectAddress "q"))
                  ,
                  C_kind_var
                ))
            )) ])) ]
  |}).

Definition main  := (Proc
  unit
  Loc_unknown
  (MuCore.L
    _
    (MuCore.I
      _
      (
        (Expr
          _
          Loc_unknown
          [  ]
          tt
          (Esseq
            _
            (
              (Pattern _ Loc_unknown [  ] tt (CaseBase _ (None , BTy_unit)))
              ,
              (Expr
                _
                Loc_unknown
                [  ]
                tt
                (Esseq
                  _
                  (
                    (Pattern
                      _
                      Loc_unknown
                      [  ]
                      tt
                      (CaseBase _ (None , BTy_unit)))
                    ,
                    (Expr
                      _
                      Loc_unknown
                      [ (Aloc Loc_unknown); Astmt ]
                      tt
                      (Esseq
                        _
                        (
                          (Pattern
                            _
                            Loc_unknown
                            [  ]
                            tt
                            (CaseBase
                              _
                              (
                                (Some
                                  (Symbol
                                    "e86941afa238f384c6ba57e49e4ef1db"
                                    645
                                    (SD_ObjectAddress "cell")))
                                ,
                                (BTy_object OTy_pointer)
                              )))
                          ,
                          (Expr
                            _
                            Loc_unknown
                            [  ]
                            tt
                            (Eaction
                              _
                              {|
                                paction_polarity := Pos;
                                paction_action :=
                                  {|
                                    action_loc := Loc_unknown;
                                    action_content :=
                                      (Create
                                        _
                                        (Pexpr
                                          _
                                          Loc_unknown
                                          [  ]
                                          tt
                                          (PEapply_fun
                                            _
                                            F_align_of
                                            [ (Pexpr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (PEval
                                                _
                                                (V
                                                  _
                                                  tt
                                                  (Vctype
                                                    _
                                                    (Ctype
                                                      [  ]
                                                      (Ctype.Struct
                                                        (Symbol
                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                          629
                                                          (SD_Id
                                                            "int_queueCell")))))))) ]))
                                        {|
                                          MuCore.loc := Loc_unknown;
                                          MuCore.annot := [  ];
                                          MuCore.ct :=
                                            (SCtypes.Struct
                                              (Symbol
                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                629
                                                (SD_Id "int_queueCell")))
                                        |}
                                        (PrefSource
                                          Loc_unknown
                                          [ (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            643
                                            (SD_Id "main")); (Symbol
                                            "e86941afa238f384c6ba57e49e4ef1db"
                                            645
                                            (SD_ObjectAddress "cell")) ]))
                                  |}
                              |}))
                          ,
                          (Expr
                            _
                            Loc_unknown
                            [  ]
                            tt
                            (Esseq
                              _
                              (
                                (Pattern
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (CaseBase
                                    _
                                    (
                                      (Some
                                        (Symbol
                                          "e86941afa238f384c6ba57e49e4ef1db"
                                          646
                                          (SD_ObjectAddress "q")))
                                      ,
                                      (BTy_object OTy_pointer)
                                    )))
                                ,
                                (Expr
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (Eaction
                                    _
                                    {|
                                      paction_polarity := Pos;
                                      paction_action :=
                                        {|
                                          action_loc := Loc_unknown;
                                          action_content :=
                                            (Create
                                              _
                                              (Pexpr
                                                _
                                                Loc_unknown
                                                [  ]
                                                tt
                                                (PEapply_fun
                                                  _
                                                  F_align_of
                                                  [ (Pexpr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (PEval
                                                      _
                                                      (V
                                                        _
                                                        tt
                                                        (Vctype
                                                          _
                                                          (Ctype
                                                            [  ]
                                                            (Ctype.Struct
                                                              (Symbol
                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                628
                                                                (SD_Id
                                                                  "int_queue")))))))) ]))
                                              {|
                                                MuCore.loc := Loc_unknown;
                                                MuCore.annot := [  ];
                                                MuCore.ct :=
                                                  (SCtypes.Struct
                                                    (Symbol
                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                      628
                                                      (SD_Id "int_queue")))
                                              |}
                                              (PrefSource
                                                Loc_unknown
                                                [ (Symbol
                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                  643
                                                  (SD_Id "main")); (Symbol
                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                  646
                                                  (SD_ObjectAddress "q")) ]))
                                        |}
                                    |}))
                                ,
                                (Expr
                                  _
                                  Loc_unknown
                                  [  ]
                                  tt
                                  (Esseq
                                    _
                                    (
                                      (Pattern
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (CaseBase _ (None , BTy_unit)))
                                      ,
                                      (Expr
                                        _
                                        Loc_unknown
                                        [ (Aloc Loc_unknown); Astmt ]
                                        tt
                                        (Esseq
                                          _
                                          (
                                            (Pattern
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (CaseBase
                                                _
                                                (
                                                  (Some
                                                    (Symbol
                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                      649
                                                      SD_None))
                                                  ,
                                                  (BTy_loaded
                                                    (OTy_struct
                                                      (Symbol
                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                        629
                                                        (SD_Id "int_queueCell"))))
                                                )))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [ (Astd "\194\1676.5#2") ]
                                              tt
                                              (Ebound
                                                _
                                                (Expr
                                                  _
                                                  Loc_unknown
                                                  [ (Aloc Loc_unknown); Aexpr ]
                                                  tt
                                                  (Ewseq
                                                    _
                                                    (
                                                      (Pattern
                                                        _
                                                        Loc_unknown
                                                        [  ]
                                                        tt
                                                        (CaseCtor
                                                          _
                                                          Ctuple
                                                          [ (Pattern
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (CaseBase
                                                              _
                                                              (
                                                                (Some
                                                                  (Symbol
                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                    651
                                                                    SD_None))
                                                                ,
                                                                (BTy_loaded
                                                                  OTy_pointer)
                                                              ))); (Pattern
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (CaseBase
                                                              _
                                                              (
                                                                (Some
                                                                  (Symbol
                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                    650
                                                                    SD_None))
                                                                ,
                                                                (BTy_loaded
                                                                  OTy_integer)
                                                              ))) ]))
                                                      ,
                                                      (Expr
                                                        _
                                                        Loc_unknown
                                                        [ (Astd
                                                          "\194\1676.7.9#23") ]
                                                        tt
                                                        (Eunseq
                                                          _
                                                          [ (Expr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (Epure
                                                              _
                                                              (Pexpr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (PEval
                                                                  _
                                                                  (V
                                                                    _
                                                                    tt
                                                                    (Vobject
                                                                      _
                                                                      (OV
                                                                        _
                                                                        tt
                                                                        (OVpointer
                                                                          _
                                                                          Mem.PVnull)))))))); (Expr
                                                            _
                                                            Loc_unknown
                                                            [ (Aloc
                                                              Loc_unknown); Aexpr; (Avalue
                                                              (Ainteger
                                                                (Signed Int_))) ]
                                                            tt
                                                            (Epure
                                                              _
                                                              (Pexpr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (PEval
                                                                  _
                                                                  (V
                                                                    _
                                                                    tt
                                                                    (Vobject
                                                                      _
                                                                      (OV
                                                                        _
                                                                        tt
                                                                        (OVinteger
                                                                          _
                                                                          (Mem.IVint 0))))))))) ]))
                                                      ,
                                                      (Expr
                                                        _
                                                        Loc_unknown
                                                        [  ]
                                                        tt
                                                        (Epure
                                                          _
                                                          (Pexpr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (PEstruct
                                                              _
                                                              (Symbol
                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                629
                                                                (SD_Id
                                                                  "int_queueCell"))
                                                              [ (
                                                                (Identifier
                                                                  Loc_unknown
                                                                  "first")
                                                                ,
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEconv_loaded_int
                                                                    _
                                                                    (Pexpr
                                                                      _
                                                                      Loc_unknown
                                                                      [  ]
                                                                      tt
                                                                      (PEval
                                                                        _
                                                                        (V
                                                                          _
                                                                          tt
                                                                          (Vctype
                                                                            _
                                                                            (Ctype
                                                                              [ (Aloc
                                                                                Loc_unknown) ]
                                                                              (Ctype.Basic
                                                                                (Ctype.Integer
                                                                                  (Signed
                                                                                    Int_))))))))
                                                                    (Pexpr
                                                                      _
                                                                      Loc_unknown
                                                                      [  ]
                                                                      tt
                                                                      (PEsym
                                                                        _
                                                                        (Symbol
                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                          650
                                                                          SD_None)))))
                                                              ); (
                                                                (Identifier
                                                                  Loc_unknown
                                                                  "next")
                                                                ,
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEsym
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      651
                                                                      SD_None)))
                                                              ) ]))))
                                                    )))))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (Eaction
                                                _
                                                {|
                                                  paction_polarity := Pos;
                                                  paction_action :=
                                                    {|
                                                      action_loc := Loc_unknown;
                                                      action_content :=
                                                        (Store
                                                          _
                                                          false
                                                          {|
                                                            MuCore.loc :=
                                                              Loc_unknown;
                                                            MuCore.annot :=
                                                              [  ];
                                                            MuCore.ct :=
                                                              (SCtypes.Struct
                                                                (Symbol
                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                  629
                                                                  (SD_Id
                                                                    "int_queueCell")))
                                                          |}
                                                          (Pexpr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (PEsym
                                                              _
                                                              (Symbol
                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                645
                                                                (SD_ObjectAddress
                                                                  "cell"))))
                                                          (Pexpr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (PEsym
                                                              _
                                                              (Symbol
                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                649
                                                                SD_None)))
                                                          NA)
                                                    |}
                                                |}))
                                          )))
                                      ,
                                      (Expr
                                        _
                                        Loc_unknown
                                        [  ]
                                        tt
                                        (Esseq
                                          _
                                          (
                                            (Pattern
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (CaseBase _ (None , BTy_unit)))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [ (Aloc Loc_unknown); Astmt ]
                                              tt
                                              (Esseq
                                                _
                                                (
                                                  (Pattern
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (CaseBase
                                                      _
                                                      (
                                                        (Some
                                                          (Symbol
                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                            652
                                                            SD_None))
                                                        ,
                                                        (BTy_loaded
                                                          (OTy_struct
                                                            (Symbol
                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                              628
                                                              (SD_Id
                                                                "int_queue"))))
                                                      )))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [ (Astd "\194\1676.5#2") ]
                                                    tt
                                                    (Ebound
                                                      _
                                                      (Expr
                                                        _
                                                        Loc_unknown
                                                        [ (Aloc Loc_unknown); Aexpr ]
                                                        tt
                                                        (Ewseq
                                                          _
                                                          (
                                                            (Pattern
                                                              _
                                                              Loc_unknown
                                                              [  ]
                                                              tt
                                                              (CaseCtor
                                                                _
                                                                Ctuple
                                                                [ (Pattern
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (CaseBase
                                                                    _
                                                                    (
                                                                      (Some
                                                                        (Symbol
                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                          656
                                                                          SD_None))
                                                                      ,
                                                                      (BTy_loaded
                                                                        OTy_pointer)
                                                                    ))); (Pattern
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (CaseBase
                                                                    _
                                                                    (
                                                                      (Some
                                                                        (Symbol
                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                          654
                                                                          SD_None))
                                                                      ,
                                                                      (BTy_loaded
                                                                        OTy_pointer)
                                                                    ))) ]))
                                                            ,
                                                            (Expr
                                                              _
                                                              Loc_unknown
                                                              [ (Astd
                                                                "\194\1676.7.9#23") ]
                                                              tt
                                                              (Eunseq
                                                                _
                                                                [ (Expr
                                                                  _
                                                                  Loc_unknown
                                                                  [ (Aloc
                                                                    Loc_unknown); Aexpr; (Astd
                                                                    "\194\1676.5.3.2#3, sentence 5") ]
                                                                  tt
                                                                  (Ewseq
                                                                    _
                                                                    (
                                                                      (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseBase
                                                                          _
                                                                          (
                                                                            (Some
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                655
                                                                                SD_None))
                                                                            ,
                                                                            (BTy_object
                                                                              OTy_pointer)
                                                                          )))
                                                                      ,
                                                                      (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [ (Aloc
                                                                          Loc_unknown); Aexpr ]
                                                                        tt
                                                                        (Epure
                                                                          _
                                                                          (Pexpr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (PEsym
                                                                              _
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                645
                                                                                (SD_ObjectAddress
                                                                                  "cell"))))))
                                                                      ,
                                                                      (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (Epure
                                                                          _
                                                                          (Pexpr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (PEsym
                                                                              _
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                655
                                                                                SD_None)))))
                                                                    ))); (Expr
                                                                  _
                                                                  Loc_unknown
                                                                  [ (Aloc
                                                                    Loc_unknown); Aexpr; (Astd
                                                                    "\194\1676.5.3.2#3, sentence 5") ]
                                                                  tt
                                                                  (Ewseq
                                                                    _
                                                                    (
                                                                      (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseBase
                                                                          _
                                                                          (
                                                                            (Some
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                653
                                                                                SD_None))
                                                                            ,
                                                                            (BTy_object
                                                                              OTy_pointer)
                                                                          )))
                                                                      ,
                                                                      (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [ (Aloc
                                                                          Loc_unknown); Aexpr ]
                                                                        tt
                                                                        (Epure
                                                                          _
                                                                          (Pexpr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (PEsym
                                                                              _
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                645
                                                                                (SD_ObjectAddress
                                                                                  "cell"))))))
                                                                      ,
                                                                      (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (Epure
                                                                          _
                                                                          (Pexpr
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (PEsym
                                                                              _
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                653
                                                                                SD_None)))))
                                                                    ))) ]))
                                                            ,
                                                            (Expr
                                                              _
                                                              Loc_unknown
                                                              [  ]
                                                              tt
                                                              (Epure
                                                                _
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEstruct
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      628
                                                                      (SD_Id
                                                                        "int_queue"))
                                                                    [ (
                                                                      (Identifier
                                                                        Loc_unknown
                                                                        "front")
                                                                      ,
                                                                      (Pexpr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (PEsym
                                                                          _
                                                                          (Symbol
                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                            654
                                                                            SD_None)))
                                                                    ); (
                                                                      (Identifier
                                                                        Loc_unknown
                                                                        "back")
                                                                      ,
                                                                      (Pexpr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (PEsym
                                                                          _
                                                                          (Symbol
                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                            656
                                                                            SD_None)))
                                                                    ) ]))))
                                                          )))))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Eaction
                                                      _
                                                      {|
                                                        paction_polarity := Pos;
                                                        paction_action :=
                                                          {|
                                                            action_loc :=
                                                              Loc_unknown;
                                                            action_content :=
                                                              (Store
                                                                _
                                                                false
                                                                {|
                                                                  MuCore.loc :=
                                                                    Loc_unknown;
                                                                  MuCore.annot :=
                                                                    [  ];
                                                                  MuCore.ct :=
                                                                    (SCtypes.Struct
                                                                      (Symbol
                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                        628
                                                                        (SD_Id
                                                                          "int_queue")))
                                                                |}
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEsym
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      646
                                                                      (SD_ObjectAddress
                                                                        "q"))))
                                                                (Pexpr
                                                                  _
                                                                  Loc_unknown
                                                                  [  ]
                                                                  tt
                                                                  (PEsym
                                                                    _
                                                                    (Symbol
                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                      652
                                                                      SD_None)))
                                                                NA)
                                                          |}
                                                      |}))
                                                )))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [  ]
                                              tt
                                              (Esseq
                                                _
                                                (
                                                  (Pattern
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (CaseBase
                                                      _
                                                      (None , BTy_unit)))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [ (Aloc Loc_unknown); Astmt ]
                                                    tt
                                                    (Esseq
                                                      _
                                                      (
                                                        (Pattern
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (CaseBase
                                                            _
                                                            (None , BTy_unit)))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [ (Astd
                                                            "\194\1676.5#2") ]
                                                          tt
                                                          (Ebound
                                                            _
                                                            (Expr
                                                              _
                                                              Loc_unknown
                                                              [ (Aloc
                                                                Loc_unknown); Aexpr; (Astd
                                                                "\194\1676.5.2.2#10, sentence 1") ]
                                                              tt
                                                              (Esseq
                                                                _
                                                                (
                                                                  (Pattern
                                                                    _
                                                                    Loc_unknown
                                                                    [  ]
                                                                    tt
                                                                    (CaseCtor
                                                                      _
                                                                      Ctuple
                                                                      [ (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseCtor
                                                                          _
                                                                          Ctuple
                                                                          [ (Pattern
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (CaseBase
                                                                              _
                                                                              (
                                                                                (Some
                                                                                  (Symbol
                                                                                    "e86941afa238f384c6ba57e49e4ef1db"
                                                                                    658
                                                                                    SD_None))
                                                                                ,
                                                                                (BTy_loaded
                                                                                  OTy_pointer)
                                                                              ))); (Pattern
                                                                            _
                                                                            Loc_unknown
                                                                            [  ]
                                                                            tt
                                                                            (CaseCtor
                                                                              _
                                                                              Ctuple
                                                                              [ (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        659
                                                                                        SD_None))
                                                                                    ,
                                                                                    BTy_ctype
                                                                                  ))); (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        660
                                                                                        SD_None))
                                                                                    ,
                                                                                    (BTy_list
                                                                                      BTy_ctype)
                                                                                  ))); (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        661
                                                                                        SD_None))
                                                                                    ,
                                                                                    BTy_boolean
                                                                                  ))); (Pattern
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (CaseBase
                                                                                  _
                                                                                  (
                                                                                    (Some
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        662
                                                                                        SD_None))
                                                                                    ,
                                                                                    BTy_boolean
                                                                                  ))) ])) ])); (Pattern
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (CaseBase
                                                                          _
                                                                          (
                                                                            (Some
                                                                              (Symbol
                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                664
                                                                                SD_None))
                                                                            ,
                                                                            (BTy_loaded
                                                                              OTy_pointer)
                                                                          ))) ]))
                                                                  ,
                                                                  (Expr
                                                                    _
                                                                    Loc_unknown
                                                                    [ (Astd
                                                                      "\194\1676.5.2.2#4, sentence 2") ]
                                                                    tt
                                                                    (Eunseq
                                                                      _
                                                                      [ (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (Esseq
                                                                          _
                                                                          (
                                                                            (Pattern
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (CaseBase
                                                                                _
                                                                                (
                                                                                  (Some
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      657
                                                                                      SD_None))
                                                                                  ,
                                                                                  (BTy_loaded
                                                                                    OTy_pointer)
                                                                                )))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [ (Aloc
                                                                                Loc_unknown); Aexpr ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEval
                                                                                    _
                                                                                    (V
                                                                                      _
                                                                                      tt
                                                                                      (Vobject
                                                                                        _
                                                                                        (OV
                                                                                          _
                                                                                          tt
                                                                                          (OVpointer
                                                                                            _
                                                                                            (Mem.PVfunptr (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              639
                                                                                              (SD_Id
                                                                                                "IntQueue_pop")))))))))))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEctor
                                                                                    _
                                                                                    Ctuple
                                                                                    [ (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEsym
                                                                                        _
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          657
                                                                                          SD_None))); (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEcfunction
                                                                                        _
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEsym
                                                                                            _
                                                                                            (Symbol
                                                                                              "e86941afa238f384c6ba57e49e4ef1db"
                                                                                              657
                                                                                              SD_None))))) ]))))
                                                                          ))); (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [ (Aloc
                                                                          Loc_unknown); Aexpr; (Astd
                                                                          "\194\1676.5.3.2#3, sentence 5") ]
                                                                        tt
                                                                        (Ewseq
                                                                          _
                                                                          (
                                                                            (Pattern
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (CaseBase
                                                                                _
                                                                                (
                                                                                  (Some
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      665
                                                                                      SD_None))
                                                                                  ,
                                                                                  (BTy_object
                                                                                    OTy_pointer)
                                                                                )))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [ (Aloc
                                                                                Loc_unknown); Aexpr ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEsym
                                                                                    _
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      646
                                                                                      (SD_ObjectAddress
                                                                                        "q"))))))
                                                                            ,
                                                                            (Expr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (Epure
                                                                                _
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEsym
                                                                                    _
                                                                                    (Symbol
                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                      665
                                                                                      SD_None)))))
                                                                          ))) ]))
                                                                  ,
                                                                  (Expr
                                                                    _
                                                                    Loc_unknown
                                                                    [ Anot_explode ]
                                                                    tt
                                                                    (Eif
                                                                      _
                                                                      (
                                                                        (Pexpr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (PEnot
                                                                            _
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (PEop
                                                                                _
                                                                                Core.OpEq
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEapply_fun
                                                                                    _
                                                                                    F_params_length
                                                                                    [ (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEsym
                                                                                        _
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          660
                                                                                          SD_None))) ]))
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEval
                                                                                    _
                                                                                    (V
                                                                                      _
                                                                                      tt
                                                                                      (Vobject
                                                                                        _
                                                                                        (OV
                                                                                          _
                                                                                          tt
                                                                                          (OVinteger
                                                                                            _
                                                                                            (Mem.IVint 1)))))))))))
                                                                        ,
                                                                        (Expr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (Epure
                                                                            _
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [ (Astd
                                                                                "\194\1676.5.2.2#6, sentence 3") ]
                                                                              tt
                                                                              (PEundef
                                                                                _
                                                                                Loc_unknown
                                                                                UB038_number_of_args))))
                                                                        ,
                                                                        (Expr
                                                                          _
                                                                          Loc_unknown
                                                                          [ Anot_explode ]
                                                                          tt
                                                                          (Eif
                                                                            _
                                                                            (
                                                                              (Pexpr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (PEop
                                                                                  _
                                                                                  Core.OpOr
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [  ]
                                                                                    tt
                                                                                    (PEsym
                                                                                      _
                                                                                      (Symbol
                                                                                        "e86941afa238f384c6ba57e49e4ef1db"
                                                                                        661
                                                                                        SD_None)))
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [  ]
                                                                                    tt
                                                                                    (PEnot
                                                                                      _
                                                                                      (Pexpr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (PEapply_fun
                                                                                          _
                                                                                          F_are_compatible
                                                                                          [ (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEval
                                                                                              _
                                                                                              (V
                                                                                                _
                                                                                                tt
                                                                                                (Vctype
                                                                                                  _
                                                                                                  (Ctype
                                                                                                    [ (Aloc
                                                                                                      Loc_unknown) ]
                                                                                                    Ctype.Void))))); (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEsym
                                                                                              _
                                                                                              (Symbol
                                                                                                "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                659
                                                                                                SD_None))) ]))))))
                                                                              ,
                                                                              (Expr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (Epure
                                                                                  _
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [ (Astd
                                                                                      "\194\1676.5.2.2#9") ]
                                                                                    tt
                                                                                    (PEundef
                                                                                      _
                                                                                      Loc_unknown
                                                                                      UB041_function_not_compatible))))
                                                                              ,
                                                                              (Expr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (Eccall
                                                                                  _
                                                                                  (
                                                                                    {|
                                                                                      MuCore.loc :=
                                                                                        Loc_unknown;
                                                                                      MuCore.annot :=
                                                                                        [  ];
                                                                                      MuCore.ct :=
                                                                                        (SCtypes.Pointer
                                                                                          (SCtypes.SCFunction
                                                                                            (
                                                                                              (
                                                                                                {|
                                                                                                  Ctype.const :=
                                                                                                    false;
                                                                                                  Ctype.restrict :=
                                                                                                    false;
                                                                                                  Ctype.volatile :=
                                                                                                    false
                                                                                                |}
                                                                                                ,
                                                                                                SCtypes.Void
                                                                                              )
                                                                                              ,
                                                                                              [ (
                                                                                                (SCtypes.Pointer
                                                                                                  (SCtypes.Struct
                                                                                                    (Symbol
                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                      628
                                                                                                      (SD_Id
                                                                                                        "int_queue"))))
                                                                                                ,
                                                                                                false
                                                                                              ) ]
                                                                                              ,
                                                                                              false
                                                                                            )))
                                                                                    |}
                                                                                    ,
                                                                                    (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PEsym
                                                                                        _
                                                                                        (Symbol
                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                          658
                                                                                          SD_None)))
                                                                                    ,
                                                                                    [ (Pexpr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [  ]
                                                                                      tt
                                                                                      (PElet
                                                                                        _
                                                                                        (Pattern
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (CaseBase
                                                                                            _
                                                                                            (
                                                                                              (Some
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  668
                                                                                                  SD_None))
                                                                                              ,
                                                                                              BTy_ctype
                                                                                            )))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [  ]
                                                                                          tt
                                                                                          (PEapply_fun
                                                                                            _
                                                                                            F_params_nth
                                                                                            [ (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  660
                                                                                                  SD_None))); (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEval
                                                                                                _
                                                                                                (V
                                                                                                  _
                                                                                                  tt
                                                                                                  (Vobject
                                                                                                    _
                                                                                                    (OV
                                                                                                      _
                                                                                                      tt
                                                                                                      (OVinteger
                                                                                                        _
                                                                                                        (Mem.IVint 0))))))) ]))
                                                                                        (Pexpr
                                                                                          _
                                                                                          Loc_unknown
                                                                                          [ Anot_explode ]
                                                                                          tt
                                                                                          (PEif
                                                                                            _
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEnot
                                                                                                _
                                                                                                (Pexpr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [  ]
                                                                                                  tt
                                                                                                  (PEapply_fun
                                                                                                    _
                                                                                                    F_are_compatible
                                                                                                    [ (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEval
                                                                                                        _
                                                                                                        (V
                                                                                                          _
                                                                                                          tt
                                                                                                          (Vctype
                                                                                                            _
                                                                                                            (Ctype
                                                                                                              [ (Aloc
                                                                                                                Loc_unknown) ]
                                                                                                              (Ctype.Pointer
                                                                                                                {|
                                                                                                                  Ctype.const :=
                                                                                                                    false;
                                                                                                                  Ctype.restrict :=
                                                                                                                    false;
                                                                                                                  Ctype.volatile :=
                                                                                                                    false
                                                                                                                |}
                                                                                                                (Ctype
                                                                                                                  [  ]
                                                                                                                  (Ctype.Struct
                                                                                                                    (Symbol
                                                                                                                      "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                                      628
                                                                                                                      (SD_Id
                                                                                                                        "int_queue")))))))))); (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEsym
                                                                                                        _
                                                                                                        (Symbol
                                                                                                          "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                          668
                                                                                                          SD_None))) ]))))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [ (Astd
                                                                                                "\194\1676.5.2.2#9") ]
                                                                                              tt
                                                                                              (PEundef
                                                                                                _
                                                                                                Loc_unknown
                                                                                                UB041_function_not_compatible))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                                  664
                                                                                                  SD_None))))))) ]
                                                                                  )))
                                                                            )))
                                                                      )))
                                                                )))))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (Epure
                                                            _
                                                            (Pexpr
                                                              _
                                                              Loc_unknown
                                                              [  ]
                                                              tt
                                                              (PEval
                                                                _
                                                                (V
                                                                  _
                                                                  tt
                                                                  (Vunit _))))))
                                                      )))
                                                  ,
                                                  (Expr
                                                    _
                                                    Loc_unknown
                                                    [  ]
                                                    tt
                                                    (Esseq
                                                      _
                                                      (
                                                        (Pattern
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (CaseBase
                                                            _
                                                            (None , BTy_unit)))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (Eaction
                                                            _
                                                            {|
                                                              paction_polarity :=
                                                                Pos;
                                                              paction_action :=
                                                                {|
                                                                  action_loc :=
                                                                    Loc_unknown;
                                                                  action_content :=
                                                                    (Kill
                                                                      _
                                                                      (Static
                                                                        (SCtypes.Struct
                                                                          (Symbol
                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                            629
                                                                            (SD_Id
                                                                              "int_queueCell"))))
                                                                      (Pexpr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (PEsym
                                                                          _
                                                                          (Symbol
                                                                            "e86941afa238f384c6ba57e49e4ef1db"
                                                                            645
                                                                            (SD_ObjectAddress
                                                                              "cell")))))
                                                                |}
                                                            |}))
                                                        ,
                                                        (Expr
                                                          _
                                                          Loc_unknown
                                                          [  ]
                                                          tt
                                                          (Esseq
                                                            _
                                                            (
                                                              (Pattern
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (CaseBase
                                                                  _
                                                                  (
                                                                    None
                                                                    ,
                                                                    BTy_unit
                                                                  )))
                                                              ,
                                                              (Expr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (Eaction
                                                                  _
                                                                  {|
                                                                    paction_polarity :=
                                                                      Pos;
                                                                    paction_action :=
                                                                      {|
                                                                        action_loc :=
                                                                          Loc_unknown;
                                                                        action_content :=
                                                                          (Kill
                                                                            _
                                                                            (Static
                                                                              (SCtypes.Struct
                                                                                (Symbol
                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                  628
                                                                                  (SD_Id
                                                                                    "int_queue"))))
                                                                            (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (PEsym
                                                                                _
                                                                                (Symbol
                                                                                  "e86941afa238f384c6ba57e49e4ef1db"
                                                                                  646
                                                                                  (SD_ObjectAddress
                                                                                    "q")))))
                                                                      |}
                                                                  |}))
                                                              ,
                                                              (Expr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (Epure
                                                                  _
                                                                  (Pexpr
                                                                    _
                                                                    Loc_unknown
                                                                    [  ]
                                                                    tt
                                                                    (PEval
                                                                      _
                                                                      (V
                                                                        _
                                                                        tt
                                                                        (Vunit
                                                                          _))))))
                                                            )))
                                                      )))
                                                )))
                                          )))
                                    )))
                              )))
                        )))
                    ,
                    (Expr
                      _
                      Loc_unknown
                      [  ]
                      tt
                      (Epure
                        _
                        (Pexpr
                          _
                          Loc_unknown
                          [  ]
                          tt
                          (PEval _ (V _ tt (Vunit _))))))
                  )))
              ,
              (Expr
                _
                Loc_unknown
                [ (Alabel LAreturn); (Aloc Loc_unknown) ]
                tt
                (Erun
                  _
                  (
                    (Symbol
                      "e86941afa238f384c6ba57e49e4ef1db"
                      648
                      (SD_Id "ret_648"))
                    ,
                    [ (Pexpr
                      _
                      Loc_unknown
                      [  ]
                      tt
                      (PEval
                        _
                        (V
                          _
                          tt
                          (Vobject _ (OV _ tt (OVinteger _ (Mem.IVint 0))))))) ]
                  )))
            )))
        ,
        (Sym.map_from_list [ (
          (Symbol "e86941afa238f384c6ba57e49e4ef1db" 648 (SD_Id "ret_648"))
          ,
          (Return _ Loc_unknown)
        ) ])
        ,
        (ReturnTypes.Computational
          (
            (Symbol "e86941afa238f384c6ba57e49e4ef1db" 752 (SD_CN_Id "return"))
            ,
            (BaseTypes.Bits unit BaseTypes.Signed 32)
          )
          (Loc_unknown , None)
          LogicalReturnTypes.I)
      )))
  (Trusted Loc_unknown)
  {| accesses := [  ]; requires := [  ]; ensures := [  ] |}).


