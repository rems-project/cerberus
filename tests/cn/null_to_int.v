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

Definition f  := (Proc
  unit
  Loc_unknown
  (MuCore.Computational
    _
    (
      (
        (Symbol "827e1098ba57b2ed423ee68ba8dba0c8" 649 (SD_FunArgValue "p"))
        ,
        (BaseTypes.Loc unit tt)
      )
      ,
      (Loc_unknown , None)
      ,
      (MuCore.L
        _
        (MuCore.Constraint
          _
          (
            (T
              (IT
                _
                (Binop
                  _
                  Terms.EQ
                  (IT
                    _
                    (Sym
                      _
                      (Symbol
                        "827e1098ba57b2ed423ee68ba8dba0c8"
                        649
                        (SD_FunArgValue "p")))
                    (BaseTypes.Loc unit tt)
                    Loc_unknown)
                  (IT _ (Const _ Null) (BaseTypes.Loc unit tt) Loc_unknown))
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
                                      "827e1098ba57b2ed423ee68ba8dba0c8"
                                      624
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
                                                        [ (Aloc Loc_unknown) ]
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
                                                            (Ctype.Basic
                                                              (Ctype.Integer
                                                                (Signed Int_)))))))))) ]))
                                          {|
                                            MuCore.loc := Loc_unknown;
                                            MuCore.annot := [  ];
                                            MuCore.ct :=
                                              (SCtypes.Pointer
                                                (SCtypes.Integer (Signed Int_)))
                                          |}
                                          (PrefFunArg
                                            Loc_unknown
                                            "827e1098ba57b2ed423ee68ba8dba0c8"
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
                                                      (SCtypes.Integer
                                                        (Signed Int_)))
                                                |}
                                                (Pexpr
                                                  _
                                                  Loc_unknown
                                                  [  ]
                                                  tt
                                                  (PEsym
                                                    _
                                                    (Symbol
                                                      "827e1098ba57b2ed423ee68ba8dba0c8"
                                                      624
                                                      (SD_ObjectAddress "p"))))
                                                (Pexpr
                                                  _
                                                  Loc_unknown
                                                  [  ]
                                                  tt
                                                  (PEsym
                                                    _
                                                    (Symbol
                                                      "827e1098ba57b2ed423ee68ba8dba0c8"
                                                      649
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
                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
                                                              655
                                                              SD_None))
                                                          ,
                                                          (BTy_loaded
                                                            OTy_integer)
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
                                                          [ (Aloc Loc_unknown); Aexpr; (Avalue
                                                            (Ainteger
                                                              (Unsigned
                                                                LongLong))); (Astd
                                                            "\194\1676.5.4") ]
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
                                                                        "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                        651
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
                                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
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
                                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                              624
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
                                                                                        (SCtypes.Integer
                                                                                          (Signed
                                                                                            Int_)))
                                                                                  |}
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [  ]
                                                                                    tt
                                                                                    (PEsym
                                                                                      _
                                                                                      (Symbol
                                                                                        "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                                        653
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
                                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                              654
                                                                              SD_None))
                                                                          ,
                                                                          (BTy_object
                                                                            OTy_integer)
                                                                        )))
                                                                    ,
                                                                    (Expr
                                                                      _
                                                                      Loc_unknown
                                                                      [  ]
                                                                      tt
                                                                      (Ememop
                                                                        _
                                                                        (IntFromPtr
                                                                          _
                                                                          (
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
                                                                            ,
                                                                            {|
                                                                              MuCore.loc :=
                                                                                Loc_unknown;
                                                                              MuCore.annot :=
                                                                                [  ];
                                                                              MuCore.ct :=
                                                                                (SCtypes.Integer
                                                                                  (Unsigned
                                                                                    LongLong))
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
                                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                                  651
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
                                                                          [  ]
                                                                          tt
                                                                          (PEsym
                                                                            _
                                                                            (Symbol
                                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                              654
                                                                              SD_None)))))
                                                                  )))
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
                                                                          (SCtypes.Pointer
                                                                            (SCtypes.Integer
                                                                              (Signed
                                                                                Int_))))
                                                                        (Pexpr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (PEsym
                                                                            _
                                                                            (Symbol
                                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                              624
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
                                                            (Erun
                                                              _
                                                              (
                                                                (Symbol
                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                  650
                                                                  (SD_Id
                                                                    "ret_650"))
                                                                ,
                                                                [ (Pexpr
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
                                                                          "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                          655
                                                                          SD_None))))) ]
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
                                                        action_loc :=
                                                          Loc_unknown;
                                                        action_content :=
                                                          (Kill
                                                            _
                                                            (Static
                                                              (SCtypes.Pointer
                                                                (SCtypes.Integer
                                                                  (Signed Int_))))
                                                            (Pexpr
                                                              _
                                                              Loc_unknown
                                                              [  ]
                                                              tt
                                                              (PEsym
                                                                _
                                                                (Symbol
                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                  624
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
                              "827e1098ba57b2ed423ee68ba8dba0c8"
                              650
                              (SD_Id "ret_650"))
                            ,
                            [ (Pexpr
                              _
                              Loc_unknown
                              [ (Astd "\194\1676.9.1#12") ]
                              tt
                              (PEundef
                                _
                                Loc_unknown
                                UB088_reached_end_of_function)) ]
                          )))
                    )))
                ,
                (Sym.map_from_list [ (
                  (Symbol
                    "827e1098ba57b2ed423ee68ba8dba0c8"
                    650
                    (SD_Id "ret_650"))
                  ,
                  (Return _ Loc_unknown)
                ) ])
                ,
                (ReturnTypes.Computational
                  (
                    (Symbol
                      "827e1098ba57b2ed423ee68ba8dba0c8"
                      657
                      (SD_CN_Id "return"))
                    ,
                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                  )
                  (Loc_unknown , None)
                  (LogicalReturnTypes.Constraint
                    (T
                      (IT
                        _
                        (Binop
                          _
                          Terms.EQ
                          (IT
                            _
                            (Sym
                              _
                              (Symbol
                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                657
                                (SD_CN_Id "return")))
                            (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                            Loc_unknown)
                          (IT
                            _
                            (Const _ (Bits ((BaseTypes.Unsigned , 64) , 0%Z)))
                            (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                            Loc_unknown))
                        (BaseTypes.Bool unit)
                        Loc_unknown))
                    (Loc_unknown , None)
                    LogicalReturnTypes.I))
              ))
          )))
    ))
  Checked
  {|
    accesses := [  ];
    requires :=
      [ (CN_cconstr
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
                  (Symbol "" 26 (SD_CN_Id "ptr_eq"))
                  ,
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
                            "827e1098ba57b2ed423ee68ba8dba0c8"
                            624
                            (SD_ObjectAddress "p"))
                          ,
                          C_kind_var
                        ))
                    )); (CNExpr
                    _
                    _
                    (Loc_unknown , (CNExpr_const _ _ CNConst_NULL))) ]
                ))
            )))) ];
    ensures :=
      [ (CN_cconstr
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
                  CN_equal
                  ,
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
                          "827e1098ba57b2ed423ee68ba8dba0c8"
                          657
                          (SD_CN_Id "return")))
                    ))
                  ,
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_const
                        _
                        _
                        (CNConst_bits ((CN_unsigned , 64) , 0%Z)))
                    ))
                ))
            )))) ]
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
                                          "827e1098ba57b2ed423ee68ba8dba0c8"
                                          647
                                          SD_None))
                                      ,
                                      (BTy_loaded OTy_integer)
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
                                      [ (Aloc Loc_unknown); Aexpr; (Avalue
                                        (Ainteger (Unsigned LongLong))); (Astd
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
                                                            "827e1098ba57b2ed423ee68ba8dba0c8"
                                                            632
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
                                                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                633
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
                                                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                634
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
                                                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                635
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
                                                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                636
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
                                                        "827e1098ba57b2ed423ee68ba8dba0c8"
                                                        638
                                                        SD_None))
                                                    ,
                                                    (BTy_loaded OTy_pointer)
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
                                                              "827e1098ba57b2ed423ee68ba8dba0c8"
                                                              631
                                                              SD_None))
                                                          ,
                                                          (BTy_loaded
                                                            OTy_pointer)
                                                        )))
                                                    ,
                                                    (Expr
                                                      _
                                                      Loc_unknown
                                                      [ (Aloc Loc_unknown); Aexpr ]
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
                                                                      "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                      625
                                                                      (SD_Id
                                                                        "f")))))))))))
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
                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                  631
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
                                                                      "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                      631
                                                                      SD_None))))) ]))))
                                                  ))); (Expr
                                                _
                                                Loc_unknown
                                                [ (Aloc Loc_unknown); Aexpr; (Astd
                                                  "\194\1676.5.4") ]
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
                                                              Mem.PVnull)))))))) ]))
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
                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                  634
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
                                                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                635
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
                                                                        "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                        633
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
                                                                        (SCtypes.Integer
                                                                          (Unsigned
                                                                            LongLong))
                                                                      )
                                                                      ,
                                                                      [ (
                                                                        (SCtypes.Pointer
                                                                          (SCtypes.Integer
                                                                            (Signed
                                                                              Int_)))
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
                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                  632
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
                                                                          "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                          644
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
                                                                          "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                          634
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
                                                                                          (Ctype.Basic
                                                                                            (Ctype.Integer
                                                                                              (Signed
                                                                                                Int_)))))))))); (Pexpr
                                                                              _
                                                                              Loc_unknown
                                                                              [  ]
                                                                              tt
                                                                              (PEsym
                                                                                _
                                                                                (Symbol
                                                                                  "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                                  644
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
                                                                          "827e1098ba57b2ed423ee68ba8dba0c8"
                                                                          638
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
                                  (Erun
                                    _
                                    (
                                      (Symbol
                                        "827e1098ba57b2ed423ee68ba8dba0c8"
                                        630
                                        (SD_Id "ret_630"))
                                      ,
                                      [ (Pexpr
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
                                                    [ (Aloc Loc_unknown) ]
                                                    (Ctype.Basic
                                                      (Ctype.Integer
                                                        (Signed Int_))))))))
                                          (Pexpr
                                            _
                                            Loc_unknown
                                            [  ]
                                            tt
                                            (PEsym
                                              _
                                              (Symbol
                                                "827e1098ba57b2ed423ee68ba8dba0c8"
                                                647
                                                SD_None))))) ]
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
                      "827e1098ba57b2ed423ee68ba8dba0c8"
                      630
                      (SD_Id "ret_630"))
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
          (Symbol "827e1098ba57b2ed423ee68ba8dba0c8" 630 (SD_Id "ret_630"))
          ,
          (Return _ Loc_unknown)
        ) ])
        ,
        (ReturnTypes.Computational
          (
            (Symbol "827e1098ba57b2ed423ee68ba8dba0c8" 658 (SD_CN_Id "return"))
            ,
            (BaseTypes.Bits unit BaseTypes.Signed 32)
          )
          (Loc_unknown , None)
          LogicalReturnTypes.I)
      )))
  Checked
  {| accesses := [  ]; requires := [  ]; ensures := [  ] |}).


