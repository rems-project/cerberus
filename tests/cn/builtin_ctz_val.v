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
                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                    629
                                    (SD_ObjectAddress "x")))
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
                                                      (Ctype.Basic
                                                        (Ctype.Integer
                                                          (Unsigned Int_)))))))) ]))
                                        {|
                                          MuCore.loc := Loc_unknown;
                                          MuCore.annot := [  ];
                                          MuCore.ct :=
                                            (SCtypes.Integer (Unsigned Int_))
                                        |}
                                        (PrefSource
                                          Loc_unknown
                                          [ (Symbol
                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                            624
                                            (SD_Id "f")); (Symbol
                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                            629
                                            (SD_ObjectAddress "x")) ]))
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
                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                          630
                                          (SD_ObjectAddress "y")))
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
                                                            (Ctype.Basic
                                                              (Ctype.Integer
                                                                (Unsigned Int_)))))))) ]))
                                              {|
                                                MuCore.loc := Loc_unknown;
                                                MuCore.annot := [  ];
                                                MuCore.ct :=
                                                  (SCtypes.Integer
                                                    (Unsigned Int_))
                                              |}
                                              (PrefSource
                                                Loc_unknown
                                                [ (Symbol
                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                  624
                                                  (SD_Id "f")); (Symbol
                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                  630
                                                  (SD_ObjectAddress "y")) ]))
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
                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                      646
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
                                                    (Ainteger (Signed Int_))) ]
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
                                                                (Mem.IVint 1)))))))))))
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
                                                              (SCtypes.Integer
                                                                (Unsigned Int_))
                                                          |}
                                                          (Pexpr
                                                            _
                                                            Loc_unknown
                                                            [  ]
                                                            tt
                                                            (PEsym
                                                              _
                                                              (Symbol
                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                629
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
                                                                            (Unsigned
                                                                              Int_))))))))
                                                              (Pexpr
                                                                _
                                                                Loc_unknown
                                                                [  ]
                                                                tt
                                                                (PEsym
                                                                  _
                                                                  (Symbol
                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                    646
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
                                              (CaseBase _ (None , BTy_unit)))
                                            ,
                                            (Expr
                                              _
                                              Loc_unknown
                                              [ (Aloc Loc_unknown); Astmt ]
                                              tt
                                              (Epure
                                                _
                                                (Pexpr
                                                  _
                                                  Loc_unknown
                                                  [  ]
                                                  tt
                                                  (PEval _ (V _ tt (Vunit _))))))
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
                                                                  (Unsigned
                                                                    Int_))); (Astd
                                                                "\194\1676.5.16#3, sentence 4") ]
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
                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                645
                                                                                SD_None))
                                                                            ,
                                                                            (BTy_object
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
                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                661
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
                                                                      "\194\1676.5.16#3, sentence 5") ]
                                                                    tt
                                                                    (Eunseq
                                                                      _
                                                                      [ (Expr
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
                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                630
                                                                                (SD_ObjectAddress
                                                                                  "y")))))); (Expr
                                                                        _
                                                                        Loc_unknown
                                                                        [ (Aloc
                                                                          Loc_unknown); Aexpr; (Avalue
                                                                          (Ainteger
                                                                            (Signed
                                                                              Int_))); (Astd
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
                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                              648
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
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  649
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
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  650
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
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  651
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
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  652
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
                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                          654
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
                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                647
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
                                                                                                        ""
                                                                                                        300
                                                                                                        (SD_Id
                                                                                                          "ffs_proxy")))))))))))
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
                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                    647
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
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                        647
                                                                                                        SD_None))))) ]))))
                                                                                    ))); (Expr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [ (Aloc
                                                                                    Loc_unknown); Aexpr; (Avalue
                                                                                    (Ainteger
                                                                                      (Unsigned
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
                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
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
                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                629
                                                                                                (SD_ObjectAddress
                                                                                                  "x"))))))
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
                                                                                                          (Unsigned
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
                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                          655
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
                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                    650
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
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  651
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
                                                                                                                  (Signed
                                                                                                                    Int_)))))))); (Pexpr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [  ]
                                                                                                      tt
                                                                                                      (PEsym
                                                                                                        _
                                                                                                        (Symbol
                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                          649
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
                                                                                                            (Signed
                                                                                                              Int_))
                                                                                                        )
                                                                                                        ,
                                                                                                        [ (
                                                                                                          (SCtypes.Integer
                                                                                                            (Signed
                                                                                                              Int_))
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
                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                    648
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
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            658
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
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            650
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
                                                                                                                        (Ctype.Basic
                                                                                                                          (Ctype.Integer
                                                                                                                            (Signed
                                                                                                                              Int_)))))))); (Pexpr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (PEsym
                                                                                                                  _
                                                                                                                  (Symbol
                                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                    658
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
                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                654
                                                                                                                SD_None))))))))) ]
                                                                                            )))
                                                                                      )))
                                                                                )))
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
                                                                              None
                                                                              ,
                                                                              BTy_unit
                                                                            )))
                                                                        ,
                                                                        (Expr
                                                                          _
                                                                          Loc_unknown
                                                                          [ (Astd
                                                                            "\194\1676.5.16.1#2, store") ]
                                                                          tt
                                                                          (Eaction
                                                                            _
                                                                            {|
                                                                              paction_polarity :=
                                                                                Neg;
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
                                                                                            (Unsigned
                                                                                              Int_))
                                                                                      |}
                                                                                      (Pexpr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [ (Astd
                                                                                          "\194\1676.5.16#3, sentence 1") ]
                                                                                        tt
                                                                                        (PEsym
                                                                                          _
                                                                                          (Symbol
                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                            645
                                                                                            SD_None)))
                                                                                      (Pexpr
                                                                                        _
                                                                                        Loc_unknown
                                                                                        [ (Astd
                                                                                          "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                          Int_))))))))
                                                                                          (Pexpr
                                                                                            _
                                                                                            Loc_unknown
                                                                                            [  ]
                                                                                            tt
                                                                                            (PEsym
                                                                                              _
                                                                                              (Symbol
                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                661
                                                                                                SD_None)))))
                                                                                      NA)
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
                                                                              [ (Astd
                                                                                "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                Int_))))))))
                                                                                (Pexpr
                                                                                  _
                                                                                  Loc_unknown
                                                                                  [  ]
                                                                                  tt
                                                                                  (PEsym
                                                                                    _
                                                                                    (Symbol
                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                      661
                                                                                      SD_None)))))))
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
                                                          [ (Aloc Loc_unknown); Astmt; (Aattrs
                                                            (Attrs
                                                              [ {|
                                                                attr_ns :=
                                                                  (Some
                                                                    (Identifier
                                                                      Loc_unknown
                                                                      "cerb"));
                                                                attr_id :=
                                                                  (Identifier
                                                                    Loc_unknown
                                                                    "magic");
                                                                attr_args :=
                                                                  [ (
                                                                    Loc_unknown
                                                                    ,
                                                                    " assert (y == 1u32); "
                                                                    ,
                                                                    [ (
                                                                      Loc_unknown
                                                                      ,
                                                                      " assert (y == 1u32); "
                                                                    ) ]
                                                                  ) ]
                                                              |} ])); (Amarker_object_types
                                                            662); (Amarker 628) ]
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
                                                                (CN_progs
                                                                  _
                                                                  (
                                                                    [ (CN_statement
                                                                      _
                                                                      _
                                                                      Loc_unknown
                                                                      (CN_assert_stmt
                                                                        _
                                                                        _
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
                                                                                      (CNExpr_value_of_c_atom
                                                                                        _
                                                                                        _
                                                                                        (
                                                                                          (Symbol
                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                            630
                                                                                            (SD_ObjectAddress
                                                                                              "y"))
                                                                                          ,
                                                                                          C_kind_var
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
                                                                                        (CNConst_bits
                                                                                          (
                                                                                            (
                                                                                              CN_unsigned
                                                                                              ,
                                                                                              32
                                                                                            )
                                                                                            ,
                                                                                            1%Z
                                                                                          )))
                                                                                    ))
                                                                                ))
                                                                            ))))) ]
                                                                    ,
                                                                    [ (CLet
                                                                      Loc_unknown
                                                                      (
                                                                        (Symbol
                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                          705
                                                                          (SD_CN_Id
                                                                            "read_&y0"))
                                                                        ,
                                                                        {|
                                                                          CNProgs.ct :=
                                                                            (SCtypes.Integer
                                                                              (Unsigned
                                                                                Int_));
                                                                          CNProgs.pointer :=
                                                                            (IT
                                                                              _
                                                                              (Sym
                                                                                _
                                                                                (Symbol
                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                  630
                                                                                  (SD_ObjectAddress
                                                                                    "y")))
                                                                              (BaseTypes.Loc
                                                                                unit
                                                                                tt)
                                                                              Loc_unknown)
                                                                        |}
                                                                      )
                                                                      (Statement
                                                                        Loc_unknown
                                                                        (Assert
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
                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                      705
                                                                                      (SD_CN_Id
                                                                                        "read_&y0")))
                                                                                  (BaseTypes.Bits
                                                                                    unit
                                                                                    BaseTypes.Unsigned
                                                                                    32)
                                                                                  Loc_unknown)
                                                                                (IT
                                                                                  _
                                                                                  (Const
                                                                                    _
                                                                                    (Bits
                                                                                      (
                                                                                        (
                                                                                          BaseTypes.Unsigned
                                                                                          ,
                                                                                          32
                                                                                        )
                                                                                        ,
                                                                                        1%Z
                                                                                      )))
                                                                                  (BaseTypes.Bits
                                                                                    unit
                                                                                    BaseTypes.Unsigned
                                                                                    32)
                                                                                  Loc_unknown))
                                                                              (BaseTypes.Bool
                                                                                unit)
                                                                              Loc_unknown))))) ]
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
                                                                              (Unsigned
                                                                                Int_))); (Astd
                                                                            "\194\1676.5.16#3, sentence 4") ]
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
                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                            644
                                                                                            SD_None))
                                                                                        ,
                                                                                        (BTy_object
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
                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                            677
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
                                                                                  "\194\1676.5.16#3, sentence 5") ]
                                                                                tt
                                                                                (Eunseq
                                                                                  _
                                                                                  [ (Expr
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
                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                            630
                                                                                            (SD_ObjectAddress
                                                                                              "y")))))); (Expr
                                                                                    _
                                                                                    Loc_unknown
                                                                                    [ (Aloc
                                                                                      Loc_unknown); Aexpr; (Avalue
                                                                                      (Ainteger
                                                                                        (Signed
                                                                                          Int_))); (Astd
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
                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                          664
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              665
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              666
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              667
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              668
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
                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                      670
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
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            663
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
                                                                                                                    ""
                                                                                                                    307
                                                                                                                    (SD_Id
                                                                                                                      "ctz_proxy")))))))))))
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
                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                663
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
                                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                    663
                                                                                                                    SD_None))))) ]))))
                                                                                                ))); (Expr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [ (Aloc
                                                                                                Loc_unknown); Aexpr; (Avalue
                                                                                                (Ainteger
                                                                                                  (Unsigned
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
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            671
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
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            629
                                                                                                            (SD_ObjectAddress
                                                                                                              "x"))))))
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
                                                                                                                      (Unsigned
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
                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                      671
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
                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                666
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              667
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
                                                                                                                              (Signed
                                                                                                                                Int_)))))))); (Pexpr
                                                                                                                  _
                                                                                                                  Loc_unknown
                                                                                                                  [  ]
                                                                                                                  tt
                                                                                                                  (PEsym
                                                                                                                    _
                                                                                                                    (Symbol
                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                      665
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
                                                                                                                        (Signed
                                                                                                                          Int_))
                                                                                                                    )
                                                                                                                    ,
                                                                                                                    [ (
                                                                                                                      (SCtypes.Integer
                                                                                                                        (Unsigned
                                                                                                                          Int_))
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
                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                664
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
                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                        674
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
                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                        666
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
                                                                                                                                    (Ctype.Basic
                                                                                                                                      (Ctype.Integer
                                                                                                                                        (Unsigned
                                                                                                                                          Int_)))))))); (Pexpr
                                                                                                                            _
                                                                                                                            Loc_unknown
                                                                                                                            [  ]
                                                                                                                            tt
                                                                                                                            (PEsym
                                                                                                                              _
                                                                                                                              (Symbol
                                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                674
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
                                                                                                                                      Int_))))))))
                                                                                                                      (Pexpr
                                                                                                                        _
                                                                                                                        Loc_unknown
                                                                                                                        [  ]
                                                                                                                        tt
                                                                                                                        (PEsym
                                                                                                                          _
                                                                                                                          (Symbol
                                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                            670
                                                                                                                            SD_None))))))))) ]
                                                                                                        )))
                                                                                                  )))
                                                                                            )))
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
                                                                                          None
                                                                                          ,
                                                                                          BTy_unit
                                                                                        )))
                                                                                    ,
                                                                                    (Expr
                                                                                      _
                                                                                      Loc_unknown
                                                                                      [ (Astd
                                                                                        "\194\1676.5.16.1#2, store") ]
                                                                                      tt
                                                                                      (Eaction
                                                                                        _
                                                                                        {|
                                                                                          paction_polarity :=
                                                                                            Neg;
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
                                                                                                        (Unsigned
                                                                                                          Int_))
                                                                                                  |}
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [ (Astd
                                                                                                      "\194\1676.5.16#3, sentence 1") ]
                                                                                                    tt
                                                                                                    (PEsym
                                                                                                      _
                                                                                                      (Symbol
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                        644
                                                                                                        SD_None)))
                                                                                                  (Pexpr
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    [ (Astd
                                                                                                      "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                                      Int_))))))))
                                                                                                      (Pexpr
                                                                                                        _
                                                                                                        Loc_unknown
                                                                                                        [  ]
                                                                                                        tt
                                                                                                        (PEsym
                                                                                                          _
                                                                                                          (Symbol
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            677
                                                                                                            SD_None)))))
                                                                                                  NA)
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
                                                                                          [ (Astd
                                                                                            "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                            Int_))))))))
                                                                                            (Pexpr
                                                                                              _
                                                                                              Loc_unknown
                                                                                              [  ]
                                                                                              tt
                                                                                              (PEsym
                                                                                                _
                                                                                                (Symbol
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  677
                                                                                                  SD_None)))))))
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
                                                                        Loc_unknown); Astmt; (Aattrs
                                                                        (Attrs
                                                                          [ {|
                                                                            attr_ns :=
                                                                              (Some
                                                                                (Identifier
                                                                                  Loc_unknown
                                                                                  "cerb"));
                                                                            attr_id :=
                                                                              (Identifier
                                                                                Loc_unknown
                                                                                "magic");
                                                                            attr_args :=
                                                                              [ (
                                                                                Loc_unknown
                                                                                ,
                                                                                " assert (y == 0u32); "
                                                                                ,
                                                                                [ (
                                                                                  Loc_unknown
                                                                                  ,
                                                                                  " assert (y == 0u32); "
                                                                                ) ]
                                                                              ) ]
                                                                          |} ])); (Amarker_object_types
                                                                        678); (Amarker
                                                                        627) ]
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
                                                                            (CN_progs
                                                                              _
                                                                              (
                                                                                [ (CN_statement
                                                                                  _
                                                                                  _
                                                                                  Loc_unknown
                                                                                  (CN_assert_stmt
                                                                                    _
                                                                                    _
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
                                                                                                  (CNExpr_value_of_c_atom
                                                                                                    _
                                                                                                    _
                                                                                                    (
                                                                                                      (Symbol
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                        630
                                                                                                        (SD_ObjectAddress
                                                                                                          "y"))
                                                                                                      ,
                                                                                                      C_kind_var
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
                                                                                                    (CNConst_bits
                                                                                                      (
                                                                                                        (
                                                                                                          CN_unsigned
                                                                                                          ,
                                                                                                          32
                                                                                                        )
                                                                                                        ,
                                                                                                        0%Z
                                                                                                      )))
                                                                                                ))
                                                                                            ))
                                                                                        ))))) ]
                                                                                ,
                                                                                [ (CLet
                                                                                  Loc_unknown
                                                                                  (
                                                                                    (Symbol
                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                      706
                                                                                      (SD_CN_Id
                                                                                        "read_&y1"))
                                                                                    ,
                                                                                    {|
                                                                                      CNProgs.ct :=
                                                                                        (SCtypes.Integer
                                                                                          (Unsigned
                                                                                            Int_));
                                                                                      CNProgs.pointer :=
                                                                                        (IT
                                                                                          _
                                                                                          (Sym
                                                                                            _
                                                                                            (Symbol
                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                              630
                                                                                              (SD_ObjectAddress
                                                                                                "y")))
                                                                                          (BaseTypes.Loc
                                                                                            unit
                                                                                            tt)
                                                                                          Loc_unknown)
                                                                                    |}
                                                                                  )
                                                                                  (Statement
                                                                                    Loc_unknown
                                                                                    (Assert
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
                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                  706
                                                                                                  (SD_CN_Id
                                                                                                    "read_&y1")))
                                                                                              (BaseTypes.Bits
                                                                                                unit
                                                                                                BaseTypes.Unsigned
                                                                                                32)
                                                                                              Loc_unknown)
                                                                                            (IT
                                                                                              _
                                                                                              (Const
                                                                                                _
                                                                                                (Bits
                                                                                                  (
                                                                                                    (
                                                                                                      BaseTypes.Unsigned
                                                                                                      ,
                                                                                                      32
                                                                                                    )
                                                                                                    ,
                                                                                                    0%Z
                                                                                                  )))
                                                                                              (BaseTypes.Bits
                                                                                                unit
                                                                                                BaseTypes.Unsigned
                                                                                                32)
                                                                                              Loc_unknown))
                                                                                          (BaseTypes.Bool
                                                                                            unit)
                                                                                          Loc_unknown))))) ]
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
                                                                                          (Unsigned
                                                                                            Int_))); Aexpr; (Avalue
                                                                                        (Ainteger
                                                                                          (Unsigned
                                                                                            Int_))); (Astd
                                                                                        "\194\1676.5.16#3, sentence 4") ]
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
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                        643
                                                                                                        SD_None))
                                                                                                    ,
                                                                                                    (BTy_object
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
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
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
                                                                                            [ (Astd
                                                                                              "\194\1676.5.16#3, sentence 5") ]
                                                                                            tt
                                                                                            (Eunseq
                                                                                              _
                                                                                              [ (Expr
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
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                        629
                                                                                                        (SD_ObjectAddress
                                                                                                          "x")))))); (Expr
                                                                                                _
                                                                                                Loc_unknown
                                                                                                [ (Aloc
                                                                                                  Loc_unknown); Aexpr; (Avalue
                                                                                                  (Ainteger
                                                                                                    (Unsigned
                                                                                                      Int_))); (Astd
                                                                                                  "\194\1676.5.5") ]
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
                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                  680
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
                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                  681
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
                                                                                                              (Unsigned
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
                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                        679
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
                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                        629
                                                                                                                        (SD_ObjectAddress
                                                                                                                          "x"))))))
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
                                                                                                                                  (Unsigned
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
                                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                  679
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
                                                                                                                        (Mem.IVint 2))))))))) ]))
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
                                                                                                            "\194\1676.5.5#4") ]
                                                                                                          tt
                                                                                                          (PEbounded_binop
                                                                                                            _
                                                                                                            (Bound_Wrap
                                                                                                              {|
                                                                                                                MuCore.loc :=
                                                                                                                  Loc_unknown;
                                                                                                                MuCore.annot :=
                                                                                                                  [  ];
                                                                                                                MuCore.ct :=
                                                                                                                  (SCtypes.Integer
                                                                                                                    (Unsigned
                                                                                                                      Int_))
                                                                                                              |})
                                                                                                            Core.IOpMul
                                                                                                            (Pexpr
                                                                                                              _
                                                                                                              Loc_unknown
                                                                                                              [ (Astd
                                                                                                                "\194\1676.5.5#3") ]
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
                                                                                                                              (Unsigned
                                                                                                                                Int_))))))))
                                                                                                                (Pexpr
                                                                                                                  _
                                                                                                                  Loc_unknown
                                                                                                                  [  ]
                                                                                                                  tt
                                                                                                                  (PEsym
                                                                                                                    _
                                                                                                                    (Symbol
                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                      680
                                                                                                                      SD_None)))))
                                                                                                            (Pexpr
                                                                                                              _
                                                                                                              Loc_unknown
                                                                                                              [ (Astd
                                                                                                                "\194\1676.5.5#3") ]
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
                                                                                                                              (Unsigned
                                                                                                                                Int_))))))))
                                                                                                                (Pexpr
                                                                                                                  _
                                                                                                                  Loc_unknown
                                                                                                                  [  ]
                                                                                                                  tt
                                                                                                                  (PEsym
                                                                                                                    _
                                                                                                                    (Symbol
                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                      681
                                                                                                                      SD_None)))))))))
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
                                                                                                      None
                                                                                                      ,
                                                                                                      BTy_unit
                                                                                                    )))
                                                                                                ,
                                                                                                (Expr
                                                                                                  _
                                                                                                  Loc_unknown
                                                                                                  [ (Astd
                                                                                                    "\194\1676.5.16.1#2, store") ]
                                                                                                  tt
                                                                                                  (Eaction
                                                                                                    _
                                                                                                    {|
                                                                                                      paction_polarity :=
                                                                                                        Neg;
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
                                                                                                                    (Unsigned
                                                                                                                      Int_))
                                                                                                              |}
                                                                                                              (Pexpr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Astd
                                                                                                                  "\194\1676.5.16#3, sentence 1") ]
                                                                                                                tt
                                                                                                                (PEsym
                                                                                                                  _
                                                                                                                  (Symbol
                                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                    643
                                                                                                                    SD_None)))
                                                                                                              (Pexpr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Astd
                                                                                                                  "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                                                  Int_))))))))
                                                                                                                  (Pexpr
                                                                                                                    _
                                                                                                                    Loc_unknown
                                                                                                                    [  ]
                                                                                                                    tt
                                                                                                                    (PEsym
                                                                                                                      _
                                                                                                                      (Symbol
                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                        685
                                                                                                                        SD_None)))))
                                                                                                              NA)
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
                                                                                                      [ (Astd
                                                                                                        "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                                        Int_))))))))
                                                                                                        (Pexpr
                                                                                                          _
                                                                                                          Loc_unknown
                                                                                                          [  ]
                                                                                                          tt
                                                                                                          (PEsym
                                                                                                            _
                                                                                                            (Symbol
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              685
                                                                                                              SD_None)))))))
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
                                                                                                (Unsigned
                                                                                                  Int_))); (Astd
                                                                                              "\194\1676.5.16#3, sentence 4") ]
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              642
                                                                                                              SD_None))
                                                                                                          ,
                                                                                                          (BTy_object
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              700
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
                                                                                                    "\194\1676.5.16#3, sentence 5") ]
                                                                                                  tt
                                                                                                  (Eunseq
                                                                                                    _
                                                                                                    [ (Expr
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
                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                              630
                                                                                                              (SD_ObjectAddress
                                                                                                                "y")))))); (Expr
                                                                                                      _
                                                                                                      Loc_unknown
                                                                                                      [ (Aloc
                                                                                                        Loc_unknown); Aexpr; (Avalue
                                                                                                        (Ainteger
                                                                                                          (Signed
                                                                                                            Int_))); (Astd
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
                                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                            687
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
                                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                688
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
                                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                689
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
                                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                690
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
                                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                691
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
                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                        693
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
                                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                              686
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
                                                                                                                                      ""
                                                                                                                                      307
                                                                                                                                      (SD_Id
                                                                                                                                        "ctz_proxy")))))))))))
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
                                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                  686
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
                                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                      686
                                                                                                                                      SD_None))))) ]))))
                                                                                                                  ))); (Expr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [ (Aloc
                                                                                                                  Loc_unknown); Aexpr; (Avalue
                                                                                                                  (Ainteger
                                                                                                                    (Unsigned
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
                                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
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
                                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                              629
                                                                                                                              (SD_ObjectAddress
                                                                                                                                "x"))))))
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
                                                                                                                                        (Unsigned
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
                                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                        694
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
                                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                  689
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
                                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                690
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
                                                                                                                                                (Signed
                                                                                                                                                  Int_)))))))); (Pexpr
                                                                                                                                    _
                                                                                                                                    Loc_unknown
                                                                                                                                    [  ]
                                                                                                                                    tt
                                                                                                                                    (PEsym
                                                                                                                                      _
                                                                                                                                      (Symbol
                                                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                        688
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
                                                                                                                                          (Signed
                                                                                                                                            Int_))
                                                                                                                                      )
                                                                                                                                      ,
                                                                                                                                      [ (
                                                                                                                                        (SCtypes.Integer
                                                                                                                                          (Unsigned
                                                                                                                                            Int_))
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
                                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                  687
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
                                                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                          697
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
                                                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                          689
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
                                                                                                                                                      (Ctype.Basic
                                                                                                                                                        (Ctype.Integer
                                                                                                                                                          (Unsigned
                                                                                                                                                            Int_)))))))); (Pexpr
                                                                                                                                              _
                                                                                                                                              Loc_unknown
                                                                                                                                              [  ]
                                                                                                                                              tt
                                                                                                                                              (PEsym
                                                                                                                                                _
                                                                                                                                                (Symbol
                                                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                                  697
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
                                                                                                                                                        Int_))))))))
                                                                                                                                        (Pexpr
                                                                                                                                          _
                                                                                                                                          Loc_unknown
                                                                                                                                          [  ]
                                                                                                                                          tt
                                                                                                                                          (PEsym
                                                                                                                                            _
                                                                                                                                            (Symbol
                                                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                              693
                                                                                                                                              SD_None))))))))) ]
                                                                                                                          )))
                                                                                                                    )))
                                                                                                              )))
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
                                                                                                            None
                                                                                                            ,
                                                                                                            BTy_unit
                                                                                                          )))
                                                                                                      ,
                                                                                                      (Expr
                                                                                                        _
                                                                                                        Loc_unknown
                                                                                                        [ (Astd
                                                                                                          "\194\1676.5.16.1#2, store") ]
                                                                                                        tt
                                                                                                        (Eaction
                                                                                                          _
                                                                                                          {|
                                                                                                            paction_polarity :=
                                                                                                              Neg;
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
                                                                                                                          (Unsigned
                                                                                                                            Int_))
                                                                                                                    |}
                                                                                                                    (Pexpr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [ (Astd
                                                                                                                        "\194\1676.5.16#3, sentence 1") ]
                                                                                                                      tt
                                                                                                                      (PEsym
                                                                                                                        _
                                                                                                                        (Symbol
                                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                          642
                                                                                                                          SD_None)))
                                                                                                                    (Pexpr
                                                                                                                      _
                                                                                                                      Loc_unknown
                                                                                                                      [ (Astd
                                                                                                                        "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                                                        Int_))))))))
                                                                                                                        (Pexpr
                                                                                                                          _
                                                                                                                          Loc_unknown
                                                                                                                          [  ]
                                                                                                                          tt
                                                                                                                          (PEsym
                                                                                                                            _
                                                                                                                            (Symbol
                                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                              700
                                                                                                                              SD_None)))))
                                                                                                                    NA)
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
                                                                                                            [ (Astd
                                                                                                              "\194\1676.5.16.1#2, conversion") ]
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
                                                                                                                              Int_))))))))
                                                                                                              (Pexpr
                                                                                                                _
                                                                                                                Loc_unknown
                                                                                                                [  ]
                                                                                                                tt
                                                                                                                (PEsym
                                                                                                                  _
                                                                                                                  (Symbol
                                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                    700
                                                                                                                    SD_None)))))))
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
                                                                                          Loc_unknown); Astmt; (Aattrs
                                                                                          (Attrs
                                                                                            [ {|
                                                                                              attr_ns :=
                                                                                                (Some
                                                                                                  (Identifier
                                                                                                    Loc_unknown
                                                                                                    "cerb"));
                                                                                              attr_id :=
                                                                                                (Identifier
                                                                                                  Loc_unknown
                                                                                                  "magic");
                                                                                              attr_args :=
                                                                                                [ (
                                                                                                  Loc_unknown
                                                                                                  ,
                                                                                                  " assert (y == 1u32); "
                                                                                                  ,
                                                                                                  [ (
                                                                                                    Loc_unknown
                                                                                                    ,
                                                                                                    " assert (y == 1u32); "
                                                                                                  ) ]
                                                                                                ) ]
                                                                                            |} ])); (Amarker_object_types
                                                                                          701); (Amarker
                                                                                          626) ]
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
                                                                                              (CN_progs
                                                                                                _
                                                                                                (
                                                                                                  [ (CN_statement
                                                                                                    _
                                                                                                    _
                                                                                                    Loc_unknown
                                                                                                    (CN_assert_stmt
                                                                                                      _
                                                                                                      _
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
                                                                                                                    (CNExpr_value_of_c_atom
                                                                                                                      _
                                                                                                                      _
                                                                                                                      (
                                                                                                                        (Symbol
                                                                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                          630
                                                                                                                          (SD_ObjectAddress
                                                                                                                            "y"))
                                                                                                                        ,
                                                                                                                        C_kind_var
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
                                                                                                                      (CNConst_bits
                                                                                                                        (
                                                                                                                          (
                                                                                                                            CN_unsigned
                                                                                                                            ,
                                                                                                                            32
                                                                                                                          )
                                                                                                                          ,
                                                                                                                          1%Z
                                                                                                                        )))
                                                                                                                  ))
                                                                                                              ))
                                                                                                          ))))) ]
                                                                                                  ,
                                                                                                  [ (CLet
                                                                                                    Loc_unknown
                                                                                                    (
                                                                                                      (Symbol
                                                                                                        "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                        707
                                                                                                        (SD_CN_Id
                                                                                                          "read_&y2"))
                                                                                                      ,
                                                                                                      {|
                                                                                                        CNProgs.ct :=
                                                                                                          (SCtypes.Integer
                                                                                                            (Unsigned
                                                                                                              Int_));
                                                                                                        CNProgs.pointer :=
                                                                                                          (IT
                                                                                                            _
                                                                                                            (Sym
                                                                                                              _
                                                                                                              (Symbol
                                                                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                630
                                                                                                                (SD_ObjectAddress
                                                                                                                  "y")))
                                                                                                            (BaseTypes.Loc
                                                                                                              unit
                                                                                                              tt)
                                                                                                            Loc_unknown)
                                                                                                      |}
                                                                                                    )
                                                                                                    (Statement
                                                                                                      Loc_unknown
                                                                                                      (Assert
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
                                                                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                    707
                                                                                                                    (SD_CN_Id
                                                                                                                      "read_&y2")))
                                                                                                                (BaseTypes.Bits
                                                                                                                  unit
                                                                                                                  BaseTypes.Unsigned
                                                                                                                  32)
                                                                                                                Loc_unknown)
                                                                                                              (IT
                                                                                                                _
                                                                                                                (Const
                                                                                                                  _
                                                                                                                  (Bits
                                                                                                                    (
                                                                                                                      (
                                                                                                                        BaseTypes.Unsigned
                                                                                                                        ,
                                                                                                                        32
                                                                                                                      )
                                                                                                                      ,
                                                                                                                      1%Z
                                                                                                                    )))
                                                                                                                (BaseTypes.Bits
                                                                                                                  unit
                                                                                                                  BaseTypes.Unsigned
                                                                                                                  32)
                                                                                                                Loc_unknown))
                                                                                                            (BaseTypes.Bool
                                                                                                              unit)
                                                                                                            Loc_unknown))))) ]
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
                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                            702
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
                                                                                                                      (Mem.IVint 1)))))))))))
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
                                                                                                                          (Unsigned
                                                                                                                            Int_)))
                                                                                                                      (Pexpr
                                                                                                                        _
                                                                                                                        Loc_unknown
                                                                                                                        [  ]
                                                                                                                        tt
                                                                                                                        (PEsym
                                                                                                                          _
                                                                                                                          (Symbol
                                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                            629
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
                                                                                                                                (Unsigned
                                                                                                                                  Int_)))
                                                                                                                            (Pexpr
                                                                                                                              _
                                                                                                                              Loc_unknown
                                                                                                                              [  ]
                                                                                                                              tt
                                                                                                                              (PEsym
                                                                                                                                _
                                                                                                                                (Symbol
                                                                                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                                  630
                                                                                                                                  (SD_ObjectAddress
                                                                                                                                    "y")))))
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
                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                      641
                                                                                                                      (SD_Id
                                                                                                                        "ret_641"))
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
                                                                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                              702
                                                                                                                              SD_None))))) ]
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
                                                                                                                  (SCtypes.Integer
                                                                                                                    (Unsigned
                                                                                                                      Int_)))
                                                                                                                (Pexpr
                                                                                                                  _
                                                                                                                  Loc_unknown
                                                                                                                  [  ]
                                                                                                                  tt
                                                                                                                  (PEsym
                                                                                                                    _
                                                                                                                    (Symbol
                                                                                                                      "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                      629
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
                                                                                                                          (Unsigned
                                                                                                                            Int_)))
                                                                                                                      (Pexpr
                                                                                                                        _
                                                                                                                        Loc_unknown
                                                                                                                        [  ]
                                                                                                                        tt
                                                                                                                        (PEsym
                                                                                                                          _
                                                                                                                          (Symbol
                                                                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                                                                            630
                                                                                                                            (SD_ObjectAddress
                                                                                                                              "y")))))
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
                      "faf5cbc6865467f9b3d2855b7fcc4774"
                      641
                      (SD_Id "ret_641"))
                    ,
                    [ (Pexpr
                      _
                      Loc_unknown
                      [ (Astd "\194\1676.9.1#12") ]
                      tt
                      (PEundef _ Loc_unknown UB088_reached_end_of_function)) ]
                  )))
            )))
        ,
        (Sym.map_from_list [ (
          (Symbol "faf5cbc6865467f9b3d2855b7fcc4774" 641 (SD_Id "ret_641"))
          ,
          (Return _ Loc_unknown)
        ) ])
        ,
        (ReturnTypes.Computational
          (
            (Symbol "faf5cbc6865467f9b3d2855b7fcc4774" 704 (SD_CN_Id "return"))
            ,
            (BaseTypes.Bits unit BaseTypes.Signed 32)
          )
          (Loc_unknown , None)
          LogicalReturnTypes.I)
      )))
  Checked
  {| accesses := [  ]; requires := [  ]; ensures := [  ] |}).

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
                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                    633
                                    (SD_ObjectAddress "r")))
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
                                                      (Ctype.Basic
                                                        (Ctype.Integer
                                                          (Signed Int_)))))))) ]))
                                        {|
                                          MuCore.loc := Loc_unknown;
                                          MuCore.annot := [  ];
                                          MuCore.ct :=
                                            (SCtypes.Integer (Signed Int_))
                                        |}
                                        (PrefSource
                                          Loc_unknown
                                          [ (Symbol
                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                            631
                                            (SD_Id "main")); (Symbol
                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                            633
                                            (SD_ObjectAddress "r")) ]))
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
                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                636
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
                                              (Ainteger (Signed Int_))) ]
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
                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                          637
                                                          SD_None))
                                                      ,
                                                      (BTy_loaded OTy_pointer)
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
                                                                  "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                  624
                                                                  (SD_Id "f")))))))))))
                                                ,
                                                (Expr
                                                  _
                                                  Loc_unknown
                                                  [  ]
                                                  tt
                                                  (Elet
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
                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                    638
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
                                                                    "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                    639
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
                                                                None
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
                                                                None
                                                                ,
                                                                BTy_boolean
                                                              ))) ]))
                                                      ,
                                                      (Pexpr
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
                                                                "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                637
                                                                SD_None)))))
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
                                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                          639
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
                                                                            (Mem.IVint 0)))))))))
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
                                                                                    (Signed
                                                                                      Int_)))))))); (Pexpr
                                                                        _
                                                                        Loc_unknown
                                                                        [  ]
                                                                        tt
                                                                        (PEsym
                                                                          _
                                                                          (Symbol
                                                                            "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                            638
                                                                            SD_None))) ]))
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
                                                                                      (Signed
                                                                                        Int_))
                                                                                  )
                                                                                  ,
                                                                                  [  ]
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
                                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                                              637
                                                                              SD_None)))
                                                                        ,
                                                                        [  ]
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
                                                                        [ (Astd
                                                                          "\194\1676.5.2.2#9") ]
                                                                        tt
                                                                        (PEundef
                                                                          _
                                                                          Loc_unknown
                                                                          UB041_function_not_compatible))))
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
                                                                  [ (Astd
                                                                    "\194\1676.5.2.2#6, sentence 3") ]
                                                                  tt
                                                                  (PEundef
                                                                    _
                                                                    Loc_unknown
                                                                    UB038_number_of_args))))
                                                          )))
                                                    )))
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
                                                        (SCtypes.Integer
                                                          (Signed Int_))
                                                    |}
                                                    (Pexpr
                                                      _
                                                      Loc_unknown
                                                      [  ]
                                                      tt
                                                      (PEsym
                                                        _
                                                        (Symbol
                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                          633
                                                          (SD_ObjectAddress
                                                            "r"))))
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
                                                              "faf5cbc6865467f9b3d2855b7fcc4774"
                                                              636
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
                                                      (SCtypes.Integer
                                                        (Signed Int_)))
                                                    (Pexpr
                                                      _
                                                      Loc_unknown
                                                      [  ]
                                                      tt
                                                      (PEsym
                                                        _
                                                        (Symbol
                                                          "faf5cbc6865467f9b3d2855b7fcc4774"
                                                          633
                                                          (SD_ObjectAddress
                                                            "r")))))
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
                      "faf5cbc6865467f9b3d2855b7fcc4774"
                      635
                      (SD_Id "ret_635"))
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
          (Symbol "faf5cbc6865467f9b3d2855b7fcc4774" 635 (SD_Id "ret_635"))
          ,
          (Return _ Loc_unknown)
        ) ])
        ,
        (ReturnTypes.Computational
          (
            (Symbol "faf5cbc6865467f9b3d2855b7fcc4774" 708 (SD_CN_Id "return"))
            ,
            (BaseTypes.Bits unit BaseTypes.Signed 32)
          )
          (Loc_unknown , None)
          LogicalReturnTypes.I)
      )))
  (Trusted Loc_unknown)
  {| accesses := [  ]; requires := [  ]; ensures := [  ] |}).


