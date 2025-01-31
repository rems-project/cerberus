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
        (Symbol "e8f56c85841b4047a4c3215e1d5425a0" 658 (SD_FunArgValue "p"))
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
                (HasAllocId
                  _
                  (IT
                    _
                    (Sym
                      _
                      (Symbol
                        "e8f56c85841b4047a4c3215e1d5425a0"
                        658
                        (SD_FunArgValue "p")))
                    (BaseTypes.Loc unit tt)
                    Loc_unknown))
                (BaseTypes.Bool unit)
                Loc_unknown))
            ,
            (Loc_unknown , None)
            ,
            (MuCore.Define
              _
              (
                (
                  (Symbol
                    "e8f56c85841b4047a4c3215e1d5425a0"
                    668
                    (SD_CN_Id "A"))
                  ,
                  (IT
                    _
                    (MapGet
                      _
                      (IT
                        _
                        (Sym _ (Symbol "" 1 (SD_CN_Id "allocs")))
                        (BaseTypes.Map
                          unit
                          (BaseTypes.Alloc_id unit)
                          (BaseTypes.Record
                            unit
                            [ (
                              (Identifier Loc_unknown "base")
                              ,
                              (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                            ); (
                              (Identifier Loc_unknown "size")
                              ,
                              (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                            ) ]))
                        Loc_unknown)
                      (IT
                        _
                        (Cast
                          _
                          (BaseTypes.Alloc_id unit)
                          (IT
                            _
                            (Sym
                              _
                              (Symbol
                                "e8f56c85841b4047a4c3215e1d5425a0"
                                658
                                (SD_FunArgValue "p")))
                            (BaseTypes.Loc unit tt)
                            Loc_unknown))
                        (BaseTypes.Alloc_id unit)
                        Loc_unknown))
                    (BaseTypes.Record
                      unit
                      [ (
                        (Identifier Loc_unknown "base")
                        ,
                        (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                      ); (
                        (Identifier Loc_unknown "size")
                        ,
                        (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                      ) ])
                    Loc_unknown)
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
                        (Binop
                          _
                          Terms.LE
                          (IT
                            _
                            (RecordMember
                              _
                              (IT
                                _
                                (Sym
                                  _
                                  (Symbol
                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                    668
                                    (SD_CN_Id "A")))
                                (BaseTypes.Record
                                  unit
                                  [ (
                                    (Identifier Loc_unknown "base")
                                    ,
                                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                  ); (
                                    (Identifier Loc_unknown "size")
                                    ,
                                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                  ) ])
                                Loc_unknown)
                              (Identifier Loc_unknown "base"))
                            (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                            Loc_unknown)
                          (IT
                            _
                            (Binop
                              _
                              Terms.Sub
                              (IT
                                _
                                (Cast
                                  _
                                  (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                  (IT
                                    _
                                    (Sym
                                      _
                                      (Symbol
                                        "e8f56c85841b4047a4c3215e1d5425a0"
                                        658
                                        (SD_FunArgValue "p")))
                                    (BaseTypes.Loc unit tt)
                                    Loc_unknown))
                                (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                Loc_unknown)
                              (IT
                                _
                                (Const
                                  _
                                  (Bits ((BaseTypes.Unsigned , 64) , 4%Z)))
                                (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                Loc_unknown))
                            (BaseTypes.Bits unit BaseTypes.Unsigned 64)
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
                              Terms.LT
                              (IT
                                _
                                (Binop
                                  _
                                  Terms.Sub
                                  (IT
                                    _
                                    (Cast
                                      _
                                      (BaseTypes.Bits
                                        unit
                                        BaseTypes.Unsigned
                                        64)
                                      (IT
                                        _
                                        (Sym
                                          _
                                          (Symbol
                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                            658
                                            (SD_FunArgValue "p")))
                                        (BaseTypes.Loc unit tt)
                                        Loc_unknown))
                                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                    Loc_unknown)
                                  (IT
                                    _
                                    (Const
                                      _
                                      (Bits ((BaseTypes.Unsigned , 64) , 4%Z)))
                                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                    Loc_unknown))
                                (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                Loc_unknown)
                              (IT
                                _
                                (Cast
                                  _
                                  (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                  (IT
                                    _
                                    (Sym
                                      _
                                      (Symbol
                                        "e8f56c85841b4047a4c3215e1d5425a0"
                                        658
                                        (SD_FunArgValue "p")))
                                    (BaseTypes.Loc unit tt)
                                    Loc_unknown))
                                (BaseTypes.Bits unit BaseTypes.Unsigned 64)
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
                                  Terms.LE
                                  (IT
                                    _
                                    (Cast
                                      _
                                      (BaseTypes.Bits
                                        unit
                                        BaseTypes.Unsigned
                                        64)
                                      (IT
                                        _
                                        (Sym
                                          _
                                          (Symbol
                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                            658
                                            (SD_FunArgValue "p")))
                                        (BaseTypes.Loc unit tt)
                                        Loc_unknown))
                                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
                                    Loc_unknown)
                                  (IT
                                    _
                                    (Binop
                                      _
                                      Terms.Add
                                      (IT
                                        _
                                        (RecordMember
                                          _
                                          (IT
                                            _
                                            (Sym
                                              _
                                              (Symbol
                                                "e8f56c85841b4047a4c3215e1d5425a0"
                                                668
                                                (SD_CN_Id "A")))
                                            (BaseTypes.Record
                                              unit
                                              [ (
                                                (Identifier Loc_unknown "base")
                                                ,
                                                (BaseTypes.Bits
                                                  unit
                                                  BaseTypes.Unsigned
                                                  64)
                                              ); (
                                                (Identifier Loc_unknown "size")
                                                ,
                                                (BaseTypes.Bits
                                                  unit
                                                  BaseTypes.Unsigned
                                                  64)
                                              ) ])
                                            Loc_unknown)
                                          (Identifier Loc_unknown "base"))
                                        (BaseTypes.Bits
                                          unit
                                          BaseTypes.Unsigned
                                          64)
                                        Loc_unknown)
                                      (IT
                                        _
                                        (RecordMember
                                          _
                                          (IT
                                            _
                                            (Sym
                                              _
                                              (Symbol
                                                "e8f56c85841b4047a4c3215e1d5425a0"
                                                668
                                                (SD_CN_Id "A")))
                                            (BaseTypes.Record
                                              unit
                                              [ (
                                                (Identifier Loc_unknown "base")
                                                ,
                                                (BaseTypes.Bits
                                                  unit
                                                  BaseTypes.Unsigned
                                                  64)
                                              ); (
                                                (Identifier Loc_unknown "size")
                                                ,
                                                (BaseTypes.Bits
                                                  unit
                                                  BaseTypes.Unsigned
                                                  64)
                                              ) ])
                                            Loc_unknown)
                                          (Identifier Loc_unknown "size"))
                                        (BaseTypes.Bits
                                          unit
                                          BaseTypes.Unsigned
                                          64)
                                        Loc_unknown))
                                    (BaseTypes.Bits unit BaseTypes.Unsigned 64)
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
                                                      "e8f56c85841b4047a4c3215e1d5425a0"
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
                                                                                  Int_)))))))))) ]))
                                                          {|
                                                            MuCore.loc :=
                                                              Loc_unknown;
                                                            MuCore.annot :=
                                                              [  ];
                                                            MuCore.ct :=
                                                              (SCtypes.Pointer
                                                                (SCtypes.Integer
                                                                  (Signed Int_)))
                                                          |}
                                                          (PrefFunArg
                                                            Loc_unknown
                                                            "e8f56c85841b4047a4c3215e1d5425a0"
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
                                                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                                                      624
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
                                                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                                                      658
                                                                      (SD_FunArgValue
                                                                        "p"))))
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
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              666
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
                                                                            Loc_unknown); Aexpr; (Astd
                                                                            "\194\1676.5.6") ]
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
                                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                            661
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
                                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                            662
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
                                                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                                  660
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
                                                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
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
                                                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                                            660
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
                                                                                                  (Mem.IVint 1))))))))) ]))
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
                                                                                      "\194\1676.5.6#8, sentences 2-3") ]
                                                                                    tt
                                                                                    (PEarray_shift
                                                                                      _
                                                                                      (Pexpr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (PEsym
                                                                                          _
                                                                                          (Symbol
                                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                            661
                                                                                            SD_None)))
                                                                                      (SCtypes.Integer
                                                                                        (Signed
                                                                                          Int_))
                                                                                      (Pexpr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [  ]
                                                                                        tt
                                                                                        (PEop
                                                                                          _
                                                                                          Core.OpSub
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
                                                                                                      (Mem.IVint 0)))))))
                                                                                          (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEsym
                                                                                              _
                                                                                              (Symbol
                                                                                                "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                                662
                                                                                                SD_None)))))))))
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
                                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
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
                                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                  659
                                                                                  (SD_Id
                                                                                    "ret_659"))
                                                                                ,
                                                                                [ (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEsym
                                                                                    _
                                                                                    (Symbol
                                                                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                      666
                                                                                      SD_None))) ]
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
                                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
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
                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                              659
                                              (SD_Id "ret_659"))
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
                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                    659
                                    (SD_Id "ret_659"))
                                  ,
                                  (Return _ Loc_unknown)
                                ) ])
                                ,
                                (ReturnTypes.Computational
                                  (
                                    (Symbol
                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                      669
                                      (SD_CN_Id "return"))
                                    ,
                                    (BaseTypes.Loc unit tt)
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
                                                "e8f56c85841b4047a4c3215e1d5425a0"
                                                669
                                                (SD_CN_Id "return")))
                                            (BaseTypes.Loc unit tt)
                                            Loc_unknown)
                                          (IT
                                            _
                                            (ArrayShift
                                              _
                                              (IT
                                                _
                                                (Sym
                                                  _
                                                  (Symbol
                                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                                    658
                                                    (SD_FunArgValue "p")))
                                                (BaseTypes.Loc unit tt)
                                                Loc_unknown)
                                              (SCtypes.Integer (Signed Int_))
                                              (IT
                                                _
                                                (Const
                                                  _
                                                  (Bits
                                                    (
                                                      (BaseTypes.Signed , 32)
                                                      ,
                                                      (-1)%Z
                                                    )))
                                                (BaseTypes.Bits
                                                  unit
                                                  BaseTypes.Signed
                                                  32)
                                                Loc_unknown))
                                            (BaseTypes.Loc unit tt)
                                            Loc_unknown))
                                        (BaseTypes.Bool unit)
                                        Loc_unknown))
                                    (Loc_unknown , None)
                                    LogicalReturnTypes.I))
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
                  (Symbol "" 25 (SD_CN_Id "has_alloc_id"))
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
                            "e8f56c85841b4047a4c3215e1d5425a0"
                            624
                            (SD_ObjectAddress "p"))
                          ,
                          C_kind_var
                        ))
                    )) ]
                ))
            )))); (CN_cletExpr
        _
        _
        Loc_unknown
        (Symbol "e8f56c85841b4047a4c3215e1d5425a0" 668 (SD_CN_Id "A"))
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
                CN_map_get
                ,
                (CNExpr
                  _
                  _
                  (
                    Loc_unknown
                    ,
                    (CNExpr_var _ _ (Symbol "" 1 (SD_CN_Id "allocs")))
                  ))
                ,
                (CNExpr
                  _
                  _
                  (
                    Loc_unknown
                    ,
                    (CNExpr_cast
                      _
                      _
                      (
                        (CN_alloc_id _)
                        ,
                        (CNExpr
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
                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                  624
                                  (SD_ObjectAddress "p"))
                                ,
                                C_kind_var
                              ))
                          ))
                      ))
                  ))
              ))
          ))); (CN_cconstr
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
                  CN_le
                  ,
                  (CNExpr
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
                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                  668
                                  (SD_CN_Id "A")))
                            ))
                          ,
                          (Identifier Loc_unknown "base")
                        ))
                    ))
                  ,
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
                          CN_sub
                          ,
                          (CNExpr
                            _
                            _
                            (
                              Loc_unknown
                              ,
                              (CNExpr_cast
                                _
                                _
                                (
                                  (CN_bits _ (CN_unsigned , 64))
                                  ,
                                  (CNExpr
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
                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                            624
                                            (SD_ObjectAddress "p"))
                                          ,
                                          C_kind_var
                                        ))
                                    ))
                                ))
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
                                (CNConst_bits ((CN_unsigned , 64) , 4%Z)))
                            ))
                        ))
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
              (CNExpr_binop
                _
                _
                (
                  CN_lt
                  ,
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
                          CN_sub
                          ,
                          (CNExpr
                            _
                            _
                            (
                              Loc_unknown
                              ,
                              (CNExpr_cast
                                _
                                _
                                (
                                  (CN_bits _ (CN_unsigned , 64))
                                  ,
                                  (CNExpr
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
                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                            624
                                            (SD_ObjectAddress "p"))
                                          ,
                                          C_kind_var
                                        ))
                                    ))
                                ))
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
                                (CNConst_bits ((CN_unsigned , 64) , 4%Z)))
                            ))
                        ))
                    ))
                  ,
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_cast
                        _
                        _
                        (
                          (CN_bits _ (CN_unsigned , 64))
                          ,
                          (CNExpr
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
                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                    624
                                    (SD_ObjectAddress "p"))
                                  ,
                                  C_kind_var
                                ))
                            ))
                        ))
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
              (CNExpr_binop
                _
                _
                (
                  CN_le
                  ,
                  (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_cast
                        _
                        _
                        (
                          (CN_bits _ (CN_unsigned , 64))
                          ,
                          (CNExpr
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
                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                    624
                                    (SD_ObjectAddress "p"))
                                  ,
                                  C_kind_var
                                ))
                            ))
                        ))
                    ))
                  ,
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
                          CN_add
                          ,
                          (CNExpr
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
                                          "e8f56c85841b4047a4c3215e1d5425a0"
                                          668
                                          (SD_CN_Id "A")))
                                    ))
                                  ,
                                  (Identifier Loc_unknown "base")
                                ))
                            ))
                          ,
                          (CNExpr
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
                                          "e8f56c85841b4047a4c3215e1d5425a0"
                                          668
                                          (SD_CN_Id "A")))
                                    ))
                                  ,
                                  (Identifier Loc_unknown "size")
                                ))
                            ))
                        ))
                    ))
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
                      (CNExpr_var
                        _
                        _
                        (Symbol
                          "e8f56c85841b4047a4c3215e1d5425a0"
                          669
                          (SD_CN_Id "return")))
                    )); (CNExpr
                    _
                    _
                    (
                      Loc_unknown
                      ,
                      (CNExpr_array_shift
                        _
                        _
                        (
                          (CNExpr
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
                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                    624
                                    (SD_ObjectAddress "p"))
                                  ,
                                  C_kind_var
                                ))
                            ))
                          ,
                          None
                          ,
                          (CNExpr
                            _
                            _
                            (
                              Loc_unknown
                              ,
                              (CNExpr_negate
                                _
                                _
                                (CNExpr
                                  _
                                  _
                                  (
                                    Loc_unknown
                                    ,
                                    (CNExpr_const
                                      _
                                      _
                                      (CNConst_bits ((CN_signed , 32) , 1%Z)))
                                  )))
                            ))
                        ))
                    )) ]
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
                            (CaseBase
                              _
                              (
                                (Some
                                  (Symbol
                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                    631
                                    (SD_ObjectAddress "arr")))
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
                                                      (Ctype.Array
                                                        (Ctype
                                                          [ (Aloc Loc_unknown) ]
                                                          (Ctype.Basic
                                                            (Ctype.Integer
                                                              (Signed Int_))))
                                                        (Some 2))))))) ]))
                                        {|
                                          MuCore.loc := Loc_unknown;
                                          MuCore.annot := [  ];
                                          MuCore.ct :=
                                            (SCtypes.Array
                                              (
                                                (SCtypes.Integer (Signed Int_))
                                                ,
                                                (Some 2)
                                              ))
                                        |}
                                        (PrefSource
                                          Loc_unknown
                                          [ (Symbol
                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                            627
                                            (SD_Id "main")); (Symbol
                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                            631
                                            (SD_ObjectAddress "arr")) ]))
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
                                                "e8f56c85841b4047a4c3215e1d5425a0"
                                                634
                                                SD_None))
                                            ,
                                            (BTy_loaded
                                              (OTy_array OTy_integer))
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
                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                              636
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
                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                              635
                                                              SD_None))
                                                          ,
                                                          (BTy_loaded
                                                            OTy_integer)
                                                        ))) ]))
                                                ,
                                                (Expr
                                                  _
                                                  Loc_unknown
                                                  [ (Astd "\194\1676.7.9#23") ]
                                                  tt
                                                  (Eunseq
                                                    _
                                                    [ (Expr
                                                      _
                                                      Loc_unknown
                                                      [ (Aloc Loc_unknown); Aexpr; (Avalue
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
                                                                    (Mem.IVint 0))))))))); (Expr
                                                      _
                                                      Loc_unknown
                                                      [ (Aloc Loc_unknown); Aexpr; (Avalue
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
                                                      (PEctor
                                                        _
                                                        Carray
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
                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                                                  635
                                                                  SD_None))))); (Pexpr
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
                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                                                  636
                                                                  SD_None))))) ]))))
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
                                                      MuCore.loc := Loc_unknown;
                                                      MuCore.annot := [  ];
                                                      MuCore.ct :=
                                                        (SCtypes.Array
                                                          (
                                                            (SCtypes.Integer
                                                              (Signed Int_))
                                                            ,
                                                            (Some 2)
                                                          ))
                                                    |}
                                                    (Pexpr
                                                      _
                                                      Loc_unknown
                                                      [  ]
                                                      tt
                                                      (PEsym
                                                        _
                                                        (Symbol
                                                          "e8f56c85841b4047a4c3215e1d5425a0"
                                                          631
                                                          (SD_ObjectAddress
                                                            "arr"))))
                                                    (Pexpr
                                                      _
                                                      Loc_unknown
                                                      [  ]
                                                      tt
                                                      (PEsym
                                                        _
                                                        (Symbol
                                                          "e8f56c85841b4047a4c3215e1d5425a0"
                                                          634
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
                                                  None
                                                  ,
                                                  (BTy_loaded OTy_pointer)
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
                                                  [ (Aloc Loc_unknown); Aexpr; (Astd
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
                                                                        "e8f56c85841b4047a4c3215e1d5425a0"
                                                                        638
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
                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                            639
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
                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                            640
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
                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                            641
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
                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                            642
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
                                                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                                                    644
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
                                                                          "e8f56c85841b4047a4c3215e1d5425a0"
                                                                          637
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
                                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
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
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              637
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
                                                                                  "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                  637
                                                                                  SD_None))))) ]))))
                                                              ))); (Expr
                                                            _
                                                            Loc_unknown
                                                            [ (Aloc
                                                              Loc_unknown); Aexpr; (Astd
                                                              "\194\1676.5.6") ]
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
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              645
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
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              647
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
                                                                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                    650
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
                                                                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                    631
                                                                                    (SD_ObjectAddress
                                                                                      "arr"))))))
                                                                          ,
                                                                          (Expr
                                                                            _
                                                                            Loc_unknown
                                                                            [ (Astd
                                                                              "\194\1676.3.2.1#3") ]
                                                                            tt
                                                                            (Epure
                                                                              _
                                                                              (Pexpr
                                                                                _
                                                                                Loc_unknown
                                                                                [  ]
                                                                                tt
                                                                                (PEarray_shift
                                                                                  _
                                                                                  (Pexpr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [  ]
                                                                                    tt
                                                                                    (PEsym
                                                                                      _
                                                                                      (Symbol
                                                                                        "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                        650
                                                                                        SD_None)))
                                                                                  (SCtypes.Integer
                                                                                    (Signed
                                                                                      Int_))
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
                                                                                              (Mem.IVint 0)))))))))))
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
                                                                                    (Mem.IVint 1))))))))) ]))
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
                                                                        "\194\1676.5.6#8, sentences 2-3") ]
                                                                      tt
                                                                      (PEarray_shift
                                                                        _
                                                                        (Pexpr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (PEsym
                                                                            _
                                                                            (Symbol
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              645
                                                                              SD_None)))
                                                                        (SCtypes.Integer
                                                                          (Signed
                                                                            Int_))
                                                                        (Pexpr
                                                                          _
                                                                          Loc_unknown
                                                                          [  ]
                                                                          tt
                                                                          (PEsym
                                                                            _
                                                                            (Symbol
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              647
                                                                              SD_None)))))))
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
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              640
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
                                                                            "e8f56c85841b4047a4c3215e1d5425a0"
                                                                            641
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
                                                                                    "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                    639
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
                                                                                    (SCtypes.Pointer
                                                                                      (SCtypes.Integer
                                                                                        (Signed
                                                                                          Int_)))
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
                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                              638
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
                                                                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                      654
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
                                                                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                      640
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
                                                                                              "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                              654
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
                                                                                      "e8f56c85841b4047a4c3215e1d5425a0"
                                                                                      644
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
                                                  (PEval _ (V _ tt (Vunit _))))))
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
                                                      action_loc := Loc_unknown;
                                                      action_content :=
                                                        (Kill
                                                          _
                                                          (Static
                                                            (SCtypes.Array
                                                              (
                                                                (SCtypes.Integer
                                                                  (Signed Int_))
                                                                ,
                                                                (Some 2)
                                                              )))
                                                          (Pexpr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (PEsym
                                                              _
                                                              (Symbol
                                                                "e8f56c85841b4047a4c3215e1d5425a0"
                                                                631
                                                                (SD_ObjectAddress
                                                                  "arr")))))
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
                                                  (PEval _ (V _ tt (Vunit _))))))
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
                      "e8f56c85841b4047a4c3215e1d5425a0"
                      633
                      (SD_Id "ret_633"))
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
          (Symbol "e8f56c85841b4047a4c3215e1d5425a0" 633 (SD_Id "ret_633"))
          ,
          (Return _ Loc_unknown)
        ) ])
        ,
        (ReturnTypes.Computational
          (
            (Symbol "e8f56c85841b4047a4c3215e1d5425a0" 670 (SD_CN_Id "return"))
            ,
            (BaseTypes.Bits unit BaseTypes.Signed 32)
          )
          (Loc_unknown , None)
          LogicalReturnTypes.I)
      )))
  Checked
  {| accesses := [  ]; requires := [  ]; ensures := [  ] |}).


