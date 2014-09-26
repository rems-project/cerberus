exception Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> Tokens.token;
  _menhir_lexbuf: Lexing.lexbuf;
  mutable _menhir_token: Tokens.token;
  mutable _menhir_startp: Lexing.position;
  mutable _menhir_endp: Lexing.position;
  mutable _menhir_shifted: int
}

and _menhir_state = 
  | MenhirState501
  | MenhirState496
  | MenhirState485
  | MenhirState482
  | MenhirState480
  | MenhirState478
  | MenhirState468
  | MenhirState466
  | MenhirState465
  | MenhirState460
  | MenhirState456
  | MenhirState454
  | MenhirState452
  | MenhirState451
  | MenhirState446
  | MenhirState431
  | MenhirState429
  | MenhirState426
  | MenhirState424
  | MenhirState423
  | MenhirState421
  | MenhirState419
  | MenhirState417
  | MenhirState415
  | MenhirState414
  | MenhirState412
  | MenhirState410
  | MenhirState408
  | MenhirState403
  | MenhirState401
  | MenhirState399
  | MenhirState397
  | MenhirState395
  | MenhirState393
  | MenhirState391
  | MenhirState389
  | MenhirState387
  | MenhirState385
  | MenhirState380
  | MenhirState379
  | MenhirState377
  | MenhirState375
  | MenhirState373
  | MenhirState371
  | MenhirState370
  | MenhirState367
  | MenhirState366
  | MenhirState364
  | MenhirState360
  | MenhirState355
  | MenhirState347
  | MenhirState345
  | MenhirState342
  | MenhirState336
  | MenhirState328
  | MenhirState325
  | MenhirState323
  | MenhirState320
  | MenhirState319
  | MenhirState314
  | MenhirState313
  | MenhirState312
  | MenhirState309
  | MenhirState304
  | MenhirState301
  | MenhirState299
  | MenhirState284
  | MenhirState277
  | MenhirState274
  | MenhirState273
  | MenhirState270
  | MenhirState269
  | MenhirState268
  | MenhirState252
  | MenhirState251
  | MenhirState243
  | MenhirState242
  | MenhirState241
  | MenhirState238
  | MenhirState229
  | MenhirState228
  | MenhirState220
  | MenhirState219
  | MenhirState218
  | MenhirState212
  | MenhirState210
  | MenhirState207
  | MenhirState201
  | MenhirState196
  | MenhirState194
  | MenhirState193
  | MenhirState192
  | MenhirState191
  | MenhirState188
  | MenhirState185
  | MenhirState176
  | MenhirState172
  | MenhirState167
  | MenhirState164
  | MenhirState161
  | MenhirState160
  | MenhirState159
  | MenhirState155
  | MenhirState154
  | MenhirState151
  | MenhirState149
  | MenhirState148
  | MenhirState146
  | MenhirState132
  | MenhirState130
  | MenhirState123
  | MenhirState120
  | MenhirState117
  | MenhirState111
  | MenhirState108
  | MenhirState106
  | MenhirState104
  | MenhirState102
  | MenhirState100
  | MenhirState98
  | MenhirState95
  | MenhirState93
  | MenhirState91
  | MenhirState88
  | MenhirState85
  | MenhirState83
  | MenhirState81
  | MenhirState77
  | MenhirState75
  | MenhirState72
  | MenhirState70
  | MenhirState68
  | MenhirState55
  | MenhirState47
  | MenhirState46
  | MenhirState42
  | MenhirState38
  | MenhirState35
  | MenhirState33
  | MenhirState28
  | MenhirState24
  | MenhirState20
  | MenhirState18
  | MenhirState16
  | MenhirState15
  | MenhirState10
  | MenhirState0


# 1 "Parser.mly"
  
open Cabs

let id =
  fun z -> z

let option d f = function
  | Some z -> f z
  | None   -> d


let empty_specs = {
  storage_classes= [];
  type_specifiers= [];
  type_qualifiers= [];
  function_specifiers= [];
  alignment_specifiers= [];
}



# 185 "Parser.ml"
let _eRR =
  Error

let rec _menhir_goto_initializer_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 192 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState320 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2521 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 202 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2519 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 210 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2511 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 219 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2509 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 226 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.DOT ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState323
            | Tokens.LBRACKET ->
                _menhir_run314 _menhir_env (Obj.magic _menhir_stack) MenhirState323
            | Tokens.RBRACE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2507 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 239 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState323 in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2505 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 247 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                let (_ : _menhir_state) = _menhir_s in
                ((let ((_menhir_stack, _menhir_s), _, inits) = _menhir_stack in
                let _v : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 254 "Parser.ml"
                ) = 
# 814 "Parser.mly"
    ( Init_list (List.rev inits) )
# 258 "Parser.ml"
                 in
                _menhir_goto_initializer_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2506)) : 'freshtv2508)
            | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LBRACE | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
                _menhir_reduce153 _menhir_env (Obj.magic _menhir_stack) MenhirState323
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState323) : 'freshtv2510)) : 'freshtv2512)
        | Tokens.RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2515 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 272 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2513 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 279 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, inits) = _menhir_stack in
            let _v : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 285 "Parser.ml"
            ) = 
# 814 "Parser.mly"
    ( Init_list (List.rev inits) )
# 289 "Parser.ml"
             in
            _menhir_goto_initializer_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2514)) : 'freshtv2516)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2517 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 299 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2518)) : 'freshtv2520)) : 'freshtv2522)
    | MenhirState313 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2539 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 308 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 312 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2537 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 320 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 324 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2529 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 333 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 337 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2527 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 344 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 348 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.DOT ->
                _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState336
            | Tokens.LBRACKET ->
                _menhir_run314 _menhir_env (Obj.magic _menhir_stack) MenhirState336
            | Tokens.RBRACE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv2525 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 361 "Parser.ml"
                )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 365 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState336 in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv2523 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 373 "Parser.ml"
                )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 377 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                let (_ : _menhir_state) = _menhir_s in
                ((let ((((_menhir_stack, _menhir_s), _, ty), _), _, inits) = _menhir_stack in
                let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 384 "Parser.ml"
                ) = 
# 282 "Parser.mly"
    ( CabsEcompound (ty, List.rev inits) )
# 388 "Parser.ml"
                 in
                _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2524)) : 'freshtv2526)
            | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LBRACE | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
                _menhir_reduce153 _menhir_env (Obj.magic _menhir_stack) MenhirState336
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState336) : 'freshtv2528)) : 'freshtv2530)
        | Tokens.RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2533 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 402 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 406 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2531 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 413 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 417 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), _, ty), _), _, inits) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 423 "Parser.ml"
            ) = 
# 282 "Parser.mly"
    ( CabsEcompound (ty, List.rev inits) )
# 427 "Parser.ml"
             in
            _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2532)) : 'freshtv2534)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2535 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 437 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 441 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2536)) : 'freshtv2538)) : 'freshtv2540)
    | _ ->
        _menhir_fail ()

and _menhir_goto_generic_assoc_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 451 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv2503 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 459 "Parser.ml"
    )) * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 463 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv2501 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 471 "Parser.ml"
    )) * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 475 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2487 * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 484 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2485 * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 491 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.DEFAULT ->
            _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState309 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState309
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState309) : 'freshtv2486)) : 'freshtv2488)
    | Tokens.RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2497 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 546 "Parser.ml"
        )) * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 550 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2495 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 557 "Parser.ml"
        )) * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 561 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, gas) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 567 "Parser.ml"
        ) = 
# 249 "Parser.mly"
    ( CabsEgeneric (expr, gas) )
# 571 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2493) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 579 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2491) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 587 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2489) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (gs : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 595 "Parser.ml"
        )) = _v in
        ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 600 "Parser.ml"
        ) = 
# 243 "Parser.mly"
    ( gs )
# 604 "Parser.ml"
         in
        _menhir_goto_primary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2490)) : 'freshtv2492)) : 'freshtv2494)) : 'freshtv2496)) : 'freshtv2498)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2499 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 614 "Parser.ml"
        )) * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 618 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2500)) : 'freshtv2502)) : 'freshtv2504)

and _menhir_reduce114 : _menhir_env -> (('ttv_tail * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 626 "Parser.ml"
)) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 630 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (((_menhir_stack, _menhir_s), _, stmt), _, expr) = _menhir_stack in
    let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 637 "Parser.ml"
    ) = 
# 920 "Parser.mly"
    ( CabsSdo (expr, stmt) )
# 641 "Parser.ml"
     in
    _menhir_goto_iteration_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run117 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 648 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2483 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 656 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState117
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState117 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState117) : 'freshtv2484)

and _menhir_goto_initializer_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 698 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState325 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2473 * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 707 "Parser.ml"
        )) * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 713 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2471 * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 719 "Parser.ml"
        )) * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (init : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 725 "Parser.ml"
        )) = _v in
        ((let ((_menhir_stack, _menhir_s, inits), _, design_opt) = _menhir_stack in
        let _v : (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 731 "Parser.ml"
        ) = 
# 820 "Parser.mly"
    ( (design_opt, init)::inits )
# 735 "Parser.ml"
         in
        _menhir_goto_initializer_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2472)) : 'freshtv2474)
    | MenhirState319 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2477 * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 745 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2475 * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (init : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 753 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, design_opt) = _menhir_stack in
        let _v : (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 759 "Parser.ml"
        ) = 
# 818 "Parser.mly"
    ( [(design_opt, init)] )
# 763 "Parser.ml"
         in
        _menhir_goto_initializer_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2476)) : 'freshtv2478)
    | MenhirState367 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2481 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 771 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 777 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2479 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 783 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (init : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 789 "Parser.ml"
        )) = _v in
        ((let ((_menhir_stack, _menhir_s, decl), _) = _menhir_stack in
        let _v : (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 795 "Parser.ml"
        ) = 
# 520 "Parser.mly"
    ( InitDecl (decl, Some init) )
# 799 "Parser.ml"
         in
        _menhir_goto_init_declarator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2480)) : 'freshtv2482)
    | _ ->
        _menhir_fail ()

and _menhir_goto_generic_association : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 808 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState299 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2465) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 819 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2463) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (ga : (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 827 "Parser.ml"
        )) = _v in
        ((let _v : (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 832 "Parser.ml"
        ) = 
# 253 "Parser.mly"
    ( [ga] )
# 836 "Parser.ml"
         in
        _menhir_goto_generic_assoc_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2464)) : 'freshtv2466)
    | MenhirState309 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2469 * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 844 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 850 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2467 * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 856 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (ga : (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 862 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, gas) = _menhir_stack in
        let _v : (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 868 "Parser.ml"
        ) = 
# 255 "Parser.mly"
    ( ga::gas )
# 872 "Parser.ml"
         in
        _menhir_goto_generic_assoc_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2468)) : 'freshtv2470)
    | _ ->
        _menhir_fail ()

and _menhir_run300 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2461 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2457 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2455 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState301 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState301 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState301
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState301 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState301) : 'freshtv2456)) : 'freshtv2458)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2459 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2460)) : 'freshtv2462)

and _menhir_goto_argument_expression_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 939 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2453 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 947 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2451 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 955 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2445 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 964 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2443 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 971 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState130
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState130 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState130) : 'freshtv2444)) : 'freshtv2446)
    | Tokens.RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2447 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 1014 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_argument_expression_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 1020 "Parser.ml"
         in
        _menhir_goto_option_argument_expression_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2448)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2449 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 1030 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2450)) : 'freshtv2452)) : 'freshtv2454)

and _menhir_goto_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1038 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2319 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1048 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1052 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2317 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1060 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1064 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2313 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1073 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1077 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2311 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1084 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1088 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState120
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120) : 'freshtv2312)) : 'freshtv2314)
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2315 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1135 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1139 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2316)) : 'freshtv2318)) : 'freshtv2320)
    | MenhirState132 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2329 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1148 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1152 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2327 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1160 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1164 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2323 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1175 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1179 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2321 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1186 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1190 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1196 "Parser.ml"
            ) = 
# 269 "Parser.mly"
    ( CabsEsubscript (expr1, expr2) )
# 1200 "Parser.ml"
             in
            _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2322)) : 'freshtv2324)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2325 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1210 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1214 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2326)) : 'freshtv2328)) : 'freshtv2330)
    | MenhirState345 | MenhirState20 | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2339 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1223 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2337 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1231 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2333 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1242 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2331 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1249 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1255 "Parser.ml"
            ) = 
# 241 "Parser.mly"
    ( expr )
# 1259 "Parser.ml"
             in
            _menhir_goto_primary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2332)) : 'freshtv2334)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2335 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1269 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2336)) : 'freshtv2338)) : 'freshtv2340)
    | MenhirState373 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2349 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1278 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2347 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1286 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2343 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1297 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2341 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1304 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.CASE ->
                _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.DEFAULT ->
                _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.DO ->
                _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.FOR ->
                _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.IF ->
                _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.OTHER_NAME _v ->
                _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
            | Tokens.SWITCH ->
                _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
            | Tokens.WHILE ->
                _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState375
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState375) : 'freshtv2342)) : 'freshtv2344)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2345 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1377 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2346)) : 'freshtv2348)) : 'freshtv2350)
    | MenhirState377 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2359 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1386 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2357 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1394 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2353 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1405 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2351 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1412 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.CASE ->
                _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState379 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.DEFAULT ->
                _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.DO ->
                _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.FOR ->
                _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.IF ->
                _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.OTHER_NAME _v ->
                _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState379 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState379 _v
            | Tokens.SWITCH ->
                _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState379 _v
            | Tokens.WHILE ->
                _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState379
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState379) : 'freshtv2352)) : 'freshtv2354)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2355 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1485 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2356)) : 'freshtv2358)) : 'freshtv2360)
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState408 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState415 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState417 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState426 | MenhirState431 | MenhirState380 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2367 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1494 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2365 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1502 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv2361 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1513 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
            let _v : 'tv_option_expression_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 1519 "Parser.ml"
             in
            _menhir_goto_option_expression_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2362)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv2363 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1529 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2364)) : 'freshtv2366)) : 'freshtv2368)
    | MenhirState387 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2377 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1538 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2375 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1546 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2371 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1557 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2369 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1564 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState389 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState389 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState389 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState389 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState389
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState389) : 'freshtv2370)) : 'freshtv2372)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2373 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1637 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2374)) : 'freshtv2376)) : 'freshtv2378)
    | MenhirState391 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2387 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1646 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2385 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1654 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2381 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1665 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2379 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1672 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState393 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState393 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState393 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState393 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState393
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState393) : 'freshtv2380)) : 'freshtv2382)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2383 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1745 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2384)) : 'freshtv2386)) : 'freshtv2388)
    | MenhirState395 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2397 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1754 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2395 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1762 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2391 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1773 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2389 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1780 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState397 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState397 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState397 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState397 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState397
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState397) : 'freshtv2390)) : 'freshtv2392)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2393 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1853 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2394)) : 'freshtv2396)) : 'freshtv2398)
    | MenhirState401 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2407 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1862 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2405 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1870 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2401 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1881 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2399 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1888 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState403 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState403 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState403 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState403 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState403
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState403) : 'freshtv2400)) : 'freshtv2402)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2403 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1961 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2404)) : 'freshtv2406)) : 'freshtv2408)
    | MenhirState446 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2421 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 1970 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1974 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2419 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 1982 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 1986 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2415 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 1997 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2001 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2413 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2008 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2012 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv2409 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2021 "Parser.ml"
                )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2025 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv2410)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv2411 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2036 "Parser.ml"
                )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2040 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2412)) : 'freshtv2414)) : 'freshtv2416)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2417 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2051 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2055 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2418)) : 'freshtv2420)) : 'freshtv2422)
    | MenhirState460 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2441 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2064 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2068 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2439 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2076 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2080 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2435 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2091 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2095 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2433 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2102 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2106 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv2429 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2115 "Parser.ml"
                )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2119 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv2427 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2126 "Parser.ml"
                )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2130 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ELSE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv2423 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2139 "Parser.ml"
                    )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2143 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _, stmt), _, expr) = _menhir_stack in
                    let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2149 "Parser.ml"
                    ) = 
# 920 "Parser.mly"
    ( CabsSdo (expr, stmt) )
# 2153 "Parser.ml"
                     in
                    _menhir_goto_iteration_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2424)
                | Tokens.ALIGNAS | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.ATOMIC | Tokens.ATOMIC_LPAREN | Tokens.AUTO | Tokens.BANG | Tokens.BOOL | Tokens.BREAK | Tokens.CASE | Tokens.CHAR | Tokens.COMPLEX | Tokens.CONST | Tokens.CONSTANT _ | Tokens.CONTINUE | Tokens.DEFAULT | Tokens.DO | Tokens.DOUBLE | Tokens.ENUM | Tokens.EXTERN | Tokens.FLOAT | Tokens.FOR | Tokens.GENERIC | Tokens.GOTO | Tokens.IF | Tokens.INLINE | Tokens.INT | Tokens.LBRACE | Tokens.LONG | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.NORETURN | Tokens.OTHER_NAME _ | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RBRACE | Tokens.REGISTER | Tokens.RESTRICT | Tokens.RETURN | Tokens.SEMICOLON | Tokens.SHORT | Tokens.SIGNED | Tokens.SIZEOF | Tokens.STAR | Tokens.STATIC | Tokens.STATIC_ASSERT | Tokens.STRING_LITERAL _ | Tokens.STRUCT | Tokens.SWITCH | Tokens.THREAD_LOCAL | Tokens.TILDE | Tokens.TYPEDEF | Tokens.TYPEDEF_NAME2 _ | Tokens.UNION | Tokens.UNSIGNED | Tokens.VAR_NAME2 _ | Tokens.VOID | Tokens.VOLATILE | Tokens.WHILE ->
                    _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv2425 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2165 "Parser.ml"
                    )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2169 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2426)) : 'freshtv2428)) : 'freshtv2430)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv2431 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2180 "Parser.ml"
                )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2184 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2432)) : 'freshtv2434)) : 'freshtv2436)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2437 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 2195 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2199 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2438)) : 'freshtv2440)) : 'freshtv2442)
    | _ ->
        _menhir_fail ()

and _menhir_goto_assignment_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2209 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState117 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2147 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2219 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2223 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2145 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2229 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2233 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2239 "Parser.ml"
        ) = 
# 472 "Parser.mly"
    ( CabsEcomma (expr1, expr2) )
# 2243 "Parser.ml"
         in
        _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2146)) : 'freshtv2148)
    | MenhirState371 | MenhirState501 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState408 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState415 | MenhirState460 | MenhirState417 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState380 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState132 | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2151 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2251 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2149 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2257 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2263 "Parser.ml"
        ) = 
# 470 "Parser.mly"
    ( expr )
# 2267 "Parser.ml"
         in
        _menhir_goto_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2150)) : 'freshtv2152)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2155 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2275 "Parser.ml"
        )) * (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 2279 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2283 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2153 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2289 "Parser.ml"
        )) * (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 2293 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2297 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s, expr1), op), _, expr2) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2303 "Parser.ml"
        ) = 
# 440 "Parser.mly"
    ( CabsEassign (op, expr1, expr2) )
# 2307 "Parser.ml"
         in
        _menhir_goto_assignment_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2154)) : 'freshtv2156)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2159 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2315 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2157 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2321 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 2327 "Parser.ml"
        ) = 
# 286 "Parser.mly"
    ( [expr] )
# 2331 "Parser.ml"
         in
        _menhir_goto_argument_expression_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2158)) : 'freshtv2160)
    | MenhirState130 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2163 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 2339 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2343 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2161 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 2349 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2353 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, exprs), _, expr) = _menhir_stack in
        let _v : (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 2359 "Parser.ml"
        ) = 
# 288 "Parser.mly"
    ( expr::exprs )
# 2363 "Parser.ml"
         in
        _menhir_goto_argument_expression_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2162)) : 'freshtv2164)
    | MenhirState220 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2173) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2371 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2375 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2171) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2383 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2387 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2167) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2396 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2400 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2165) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2407 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2411 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _), _, tquals), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2417 "Parser.ml"
            ) = 
# 779 "Parser.mly"
    ( DAbs_array (None, ADecl (tquals, true, Some (ADeclSize_expression expr))) )
# 2421 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2166)) : 'freshtv2168)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2169) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2431 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2435 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2170)) : 'freshtv2172)) : 'freshtv2174)
    | MenhirState219 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2183) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2444 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2181) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2452 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2177) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2461 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2175) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2468 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2474 "Parser.ml"
            ) = 
# 783 "Parser.mly"
    ( DAbs_array (None, ADecl ([], true, Some (ADeclSize_expression expr))) )
# 2478 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2176)) : 'freshtv2178)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2179) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2488 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2180)) : 'freshtv2182)) : 'freshtv2184)
    | MenhirState229 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2193) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2497 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2501 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2191) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2509 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2513 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2187) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2522 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2526 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2185) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2533 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2537 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _, tquals), _), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2543 "Parser.ml"
            ) = 
# 788 "Parser.mly"
    ( DAbs_array (None, ADecl (tquals, true, Some (ADeclSize_expression expr))) )
# 2547 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2186)) : 'freshtv2188)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2189) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2557 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2561 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2190)) : 'freshtv2192)) : 'freshtv2194)
    | MenhirState228 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2203) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2570 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2574 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2201) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2582 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2586 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2197) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2595 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2599 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2195) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2606 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2610 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _, tquals), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2616 "Parser.ml"
            ) = 
# 768 "Parser.mly"
    ( DAbs_array (None, ADecl (tquals, false, Some (ADeclSize_expression expr))) )
# 2620 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2196)) : 'freshtv2198)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2199) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2630 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2634 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2200)) : 'freshtv2202)) : 'freshtv2204)
    | MenhirState218 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2213) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2643 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2211) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2651 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2207) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2660 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2205) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2667 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2673 "Parser.ml"
            ) = 
# 770 "Parser.mly"
    ( DAbs_array (None, ADecl ([], false, Some (ADeclSize_expression expr))) )
# 2677 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2206)) : 'freshtv2208)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2209) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2687 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2210)) : 'freshtv2212)) : 'freshtv2214)
    | MenhirState243 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2223 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2696 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2700 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2704 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2221 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2712 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2716 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2720 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2217 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2729 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2733 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2737 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2215 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2744 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2748 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2752 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, dabs_decltor), _), _, tquals), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2758 "Parser.ml"
            ) = 
# 777 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl (tquals, true, Some (ADeclSize_expression expr))) )
# 2762 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2216)) : 'freshtv2218)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2219 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2772 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2776 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2780 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2220)) : 'freshtv2222)) : 'freshtv2224)
    | MenhirState242 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2233 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2789 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2793 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2231 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2801 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2805 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2227 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2814 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2818 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2225 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2825 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2829 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, dabs_decltor), _), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2835 "Parser.ml"
            ) = 
# 781 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl ([], true, Some (ADeclSize_expression expr))) )
# 2839 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2226)) : 'freshtv2228)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2229 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2849 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2853 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2230)) : 'freshtv2232)) : 'freshtv2234)
    | MenhirState252 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2243 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2862 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2866 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2870 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2241 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2878 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2882 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2886 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2237 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2895 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2899 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2903 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2235 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2910 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2914 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2918 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, dabs_decltor), _, tquals), _), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2924 "Parser.ml"
            ) = 
# 786 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl (tquals, true, Some (ADeclSize_expression expr))) )
# 2928 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2236)) : 'freshtv2238)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2239 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2938 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2942 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2946 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2240)) : 'freshtv2242)) : 'freshtv2244)
    | MenhirState251 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2253 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2955 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2959 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2963 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv2251 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2971 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2975 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2979 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2247 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 2988 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 2992 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 2996 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2245 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3003 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3007 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3011 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, dabs_decltor), _, tquals), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3017 "Parser.ml"
            ) = 
# 760 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl (tquals, false, Some (ADeclSize_expression expr))) )
# 3021 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2246)) : 'freshtv2248)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv2249 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3031 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3035 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3039 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2250)) : 'freshtv2252)) : 'freshtv2254)
    | MenhirState241 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2263 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3048 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3052 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2261 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3060 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3064 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2257 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3073 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3077 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2255 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3084 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3088 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, dabs_decltor), _, expr) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3094 "Parser.ml"
            ) = 
# 764 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl ([], false, Some (ADeclSize_expression expr))) )
# 3098 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv2256)) : 'freshtv2258)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2259 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 3108 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3112 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2260)) : 'freshtv2262)) : 'freshtv2264)
    | MenhirState270 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2273 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3121 "Parser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3125 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2271 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3133 "Parser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3137 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2267 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3146 "Parser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3150 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2265 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3157 "Parser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3161 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, ddecltor), _), _, tquals_opt), _, expr) = _menhir_stack in
            let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3167 "Parser.ml"
            ) = 
# 692 "Parser.mly"
    ( DDecl_array (ddecltor, ADecl (option [] List.rev tquals_opt, true, Some (ADeclSize_expression expr))) )
# 3171 "Parser.ml"
             in
            _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv2266)) : 'freshtv2268)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2269 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3181 "Parser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3185 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2270)) : 'freshtv2272)) : 'freshtv2274)
    | MenhirState274 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2283 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3194 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3198 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3202 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv2281 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3210 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3214 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3218 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2277 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3227 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3231 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3235 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2275 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3242 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3246 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3250 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, ddecltor), _, tquals), _), _, expr) = _menhir_stack in
            let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3256 "Parser.ml"
            ) = 
# 694 "Parser.mly"
    ( DDecl_array (ddecltor, ADecl (List.rev tquals, true, Some (ADeclSize_expression expr))) )
# 3260 "Parser.ml"
             in
            _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv2276)) : 'freshtv2278)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv2279 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 3270 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 3274 "Parser.ml"
            )) * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3278 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2280)) : 'freshtv2282)) : 'freshtv2284)
    | MenhirState277 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2287 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3287 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2285 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3293 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_assignment_expression_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 3299 "Parser.ml"
         in
        _menhir_goto_option_assignment_expression_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2286)) : 'freshtv2288)
    | MenhirState28 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2297 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3307 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2295 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3315 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2291 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3324 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2289 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3331 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ATOMIC ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.ATOMIC_LPAREN ->
                _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.BOOL ->
                _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.CHAR ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.COMPLEX ->
                _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.CONST ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.DEFAULT ->
                _menhir_run300 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.DOUBLE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.ENUM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.FLOAT ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.INT ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.LONG ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.RESTRICT ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.SHORT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.SIGNED ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.STRUCT ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.TYPEDEF_NAME2 _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState299 _v
            | Tokens.UNION ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.UNSIGNED ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.VOID ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | Tokens.VOLATILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState299
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState299) : 'freshtv2290)) : 'freshtv2292)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2293 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3388 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2294)) : 'freshtv2296)) : 'freshtv2298)
    | MenhirState301 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2301 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3397 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2299 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3403 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
        let _v : (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 3409 "Parser.ml"
        ) = 
# 261 "Parser.mly"
    ( GA_default expr )
# 3413 "Parser.ml"
         in
        _menhir_goto_generic_association _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2300)) : 'freshtv2302)
    | MenhirState304 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2305 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 3421 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3425 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2303 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 3431 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3435 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, ty), _, expr) = _menhir_stack in
        let _v : (
# 67 "Parser.mly"
     (Cabs.cabs_generic_association)
# 3441 "Parser.ml"
        ) = 
# 259 "Parser.mly"
    ( GA_type (ty, expr) )
# 3445 "Parser.ml"
         in
        _menhir_goto_generic_association _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2304)) : 'freshtv2306)
    | MenhirState367 | MenhirState319 | MenhirState325 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2309 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3453 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2307 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3459 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 168 "Parser.mly"
     (Cabs.initializer_)
# 3465 "Parser.ml"
        ) = 
# 811 "Parser.mly"
    ( Init_expr expr )
# 3469 "Parser.ml"
         in
        _menhir_goto_initializer_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2308)) : 'freshtv2310)
    | _ ->
        _menhir_fail ()

and _menhir_goto_conditional_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3478 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState408 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState415 | MenhirState460 | MenhirState417 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState380 | MenhirState367 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState68 | MenhirState98 | MenhirState117 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2047) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3489 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2045) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (expr : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3497 "Parser.ml"
        )) = _v in
        ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3502 "Parser.ml"
        ) = 
# 438 "Parser.mly"
    ( expr )
# 3506 "Parser.ml"
         in
        _menhir_goto_assignment_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2046)) : 'freshtv2048)
    | MenhirState120 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2051 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3514 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3518 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3524 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2049 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3530 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3534 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (expr3 : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3540 "Parser.ml"
        )) = _v in
        ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3546 "Parser.ml"
        ) = 
# 432 "Parser.mly"
    ( CabsEcond (expr1, expr2, expr3) )
# 3550 "Parser.ml"
         in
        _menhir_goto_conditional_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2050)) : 'freshtv2052)
    | MenhirState466 | MenhirState429 | MenhirState10 | MenhirState314 | MenhirState284 | MenhirState185 | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2143) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3560 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2141) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (expr : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3568 "Parser.ml"
        )) = _v in
        ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3573 "Parser.ml"
        ) = 
# 478 "Parser.mly"
    ( expr )
# 3577 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2139) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3585 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        match _menhir_s with
        | MenhirState46 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2055 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 3594 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3598 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2053 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 3604 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3608 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, enum_cst), _, expr) = _menhir_stack in
            let _v : (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 3614 "Parser.ml"
            ) = 
# 642 "Parser.mly"
    ( (enum_cst, Some expr) )
# 3618 "Parser.ml"
             in
            _menhir_goto_enumerator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2054)) : 'freshtv2056)
        | MenhirState185 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2065 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3626 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2063 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3634 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2059 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3643 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2057 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3650 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
                let _v : (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 3656 "Parser.ml"
                ) = 
# 676 "Parser.mly"
    ( AS_expr expr )
# 3660 "Parser.ml"
                 in
                _menhir_goto_alignment_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2058)) : 'freshtv2060)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2061 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3670 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2062)) : 'freshtv2064)) : 'freshtv2066)
        | MenhirState284 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2069 * _menhir_state * 'tv_option_declarator_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3679 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2067 * _menhir_state * 'tv_option_declarator_) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3685 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, decltor_opt), _, expr) = _menhir_stack in
            let _v : (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 3691 "Parser.ml"
            ) = 
# 621 "Parser.mly"
    ( SDecl_bitfield (decltor_opt, expr) )
# 3695 "Parser.ml"
             in
            _menhir_goto_struct_declarator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2068)) : 'freshtv2070)
        | MenhirState314 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2079 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3703 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2077 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3711 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RBRACKET ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2073 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3720 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2071 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3727 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
                let _v : (
# 180 "Parser.mly"
     (Cabs.designator)
# 3733 "Parser.ml"
                ) = 
# 834 "Parser.mly"
    ( Desig_array expr )
# 3737 "Parser.ml"
                 in
                _menhir_goto_designator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2072)) : 'freshtv2074)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2075 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3747 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2076)) : 'freshtv2078)) : 'freshtv2080)
        | MenhirState10 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2117 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3756 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2115 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3764 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.COMMA ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2111 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3773 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2109 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3780 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.STRING_LITERAL _v ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ('freshtv2105 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3789 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    let (_v : (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3794 "Parser.ml"
                    )) = _v in
                    ((let _menhir_stack = (_menhir_stack, _v) in
                    let _tok = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv2103 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3802 "Parser.ml"
                    )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3806 "Parser.ml"
                    )) = _menhir_stack in
                    let (_tok : Tokens.token) = _tok in
                    ((match _tok with
                    | Tokens.RPAREN ->
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : (('freshtv2099 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3815 "Parser.ml"
                        )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3819 "Parser.ml"
                        )) = Obj.magic _menhir_stack in
                        ((let _tok = _menhir_discard _menhir_env in
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : (('freshtv2097 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3826 "Parser.ml"
                        )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3830 "Parser.ml"
                        )) = _menhir_stack in
                        let (_tok : Tokens.token) = _tok in
                        ((match _tok with
                        | Tokens.SEMICOLON ->
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : (('freshtv2093 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3839 "Parser.ml"
                            )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3843 "Parser.ml"
                            )) = Obj.magic _menhir_stack in
                            ((let _ = _menhir_discard _menhir_env in
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : (('freshtv2091 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3850 "Parser.ml"
                            )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3854 "Parser.ml"
                            )) = Obj.magic _menhir_stack in
                            ((let (((_menhir_stack, _menhir_s), _, expr), lit) = _menhir_stack in
                            let _v : (
# 183 "Parser.mly"
     (Cabs.static_assert_declaration)
# 3860 "Parser.ml"
                            ) = 
# 842 "Parser.mly"
    ( Static_assert (expr, lit) )
# 3864 "Parser.ml"
                             in
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : 'freshtv2089) = _menhir_stack in
                            let (_menhir_s : _menhir_state) = _menhir_s in
                            let (_v : (
# 183 "Parser.mly"
     (Cabs.static_assert_declaration)
# 3872 "Parser.ml"
                            )) = _v in
                            ((match _menhir_s with
                            | MenhirState154 | MenhirState155 ->
                                let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : 'freshtv2083) = Obj.magic _menhir_stack in
                                let (_menhir_s : _menhir_state) = _menhir_s in
                                let (_v : (
# 183 "Parser.mly"
     (Cabs.static_assert_declaration)
# 3882 "Parser.ml"
                                )) = _v in
                                ((let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : 'freshtv2081) = Obj.magic _menhir_stack in
                                let (_menhir_s : _menhir_state) = _menhir_s in
                                let (sa_decl : (
# 183 "Parser.mly"
     (Cabs.static_assert_declaration)
# 3890 "Parser.ml"
                                )) = _v in
                                ((let _v : (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 3895 "Parser.ml"
                                ) = 
# 596 "Parser.mly"
    ( Struct_assert sa_decl )
# 3899 "Parser.ml"
                                 in
                                _menhir_goto_struct_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2082)) : 'freshtv2084)
                            | MenhirState0 | MenhirState501 | MenhirState371 | MenhirState417 | MenhirState408 | MenhirState355 ->
                                let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : 'freshtv2087) = Obj.magic _menhir_stack in
                                let (_menhir_s : _menhir_state) = _menhir_s in
                                let (_v : (
# 183 "Parser.mly"
     (Cabs.static_assert_declaration)
# 3909 "Parser.ml"
                                )) = _v in
                                ((let (_menhir_env : _menhir_env) = _menhir_env in
                                let (_menhir_stack : 'freshtv2085) = Obj.magic _menhir_stack in
                                let (_menhir_s : _menhir_state) = _menhir_s in
                                let (sa : (
# 183 "Parser.mly"
     (Cabs.static_assert_declaration)
# 3917 "Parser.ml"
                                )) = _v in
                                ((let _v : (
# 78 "Parser.mly"
     (Cabs.declaration)
# 3922 "Parser.ml"
                                ) = 
# 486 "Parser.mly"
    ( Declaration_static_assert sa )
# 3926 "Parser.ml"
                                 in
                                _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2086)) : 'freshtv2088)
                            | _ ->
                                _menhir_fail ()) : 'freshtv2090)) : 'freshtv2092)) : 'freshtv2094)
                        | _ ->
                            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                            _menhir_env._menhir_shifted <- (-1);
                            let (_menhir_env : _menhir_env) = _menhir_env in
                            let (_menhir_stack : (('freshtv2095 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3938 "Parser.ml"
                            )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3942 "Parser.ml"
                            )) = Obj.magic _menhir_stack in
                            ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2096)) : 'freshtv2098)) : 'freshtv2100)
                    | _ ->
                        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                        _menhir_env._menhir_shifted <- (-1);
                        let (_menhir_env : _menhir_env) = _menhir_env in
                        let (_menhir_stack : (('freshtv2101 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3953 "Parser.ml"
                        )) * (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 3957 "Parser.ml"
                        )) = Obj.magic _menhir_stack in
                        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2102)) : 'freshtv2104)) : 'freshtv2106)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ('freshtv2107 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3968 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2108)) : 'freshtv2110)) : 'freshtv2112)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2113 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3979 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2114)) : 'freshtv2116)) : 'freshtv2118)
        | MenhirState429 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2127 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3988 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2125 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 3996 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.COLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2121 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4005 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2119 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4012 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ALIGNOF ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.AMPERSAND ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.BANG ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.BREAK ->
                    _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.CASE ->
                    _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.CONSTANT _v ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState431 _v
                | Tokens.CONTINUE ->
                    _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.DEFAULT ->
                    _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.DO ->
                    _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.FOR ->
                    _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.GENERIC ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.GOTO ->
                    _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.IF ->
                    _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.LBRACE ->
                    _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.LPAREN ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.MINUS ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.MINUS_MINUS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.OTHER_NAME _v ->
                    _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState431 _v
                | Tokens.PLUS ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.PLUS_PLUS ->
                    _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.RETURN ->
                    _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.SIZEOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.STAR ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.STRING_LITERAL _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState431 _v
                | Tokens.SWITCH ->
                    _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.TILDE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.VAR_NAME2 _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState431 _v
                | Tokens.WHILE ->
                    _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | Tokens.SEMICOLON ->
                    _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState431
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState431) : 'freshtv2120)) : 'freshtv2122)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2123 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4085 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2124)) : 'freshtv2126)) : 'freshtv2128)
        | MenhirState466 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2137 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4094 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2135 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4102 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.COLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2131 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4111 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2129 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4118 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ALIGNOF ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.AMPERSAND ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.BANG ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.BREAK ->
                    _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.CASE ->
                    _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.CONSTANT _v ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState468 _v
                | Tokens.CONTINUE ->
                    _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.DEFAULT ->
                    _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.DO ->
                    _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.FOR ->
                    _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.GENERIC ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.GOTO ->
                    _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.IF ->
                    _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.LBRACE ->
                    _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.LPAREN ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.MINUS ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.MINUS_MINUS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.OTHER_NAME _v ->
                    _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState468 _v
                | Tokens.PLUS ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.PLUS_PLUS ->
                    _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.RETURN ->
                    _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.SIZEOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.STAR ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.STRING_LITERAL _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState468 _v
                | Tokens.SWITCH ->
                    _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.TILDE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.VAR_NAME2 _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState468 _v
                | Tokens.WHILE ->
                    _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | Tokens.SEMICOLON ->
                    _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState468
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState468) : 'freshtv2130)) : 'freshtv2132)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv2133 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4191 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2134)) : 'freshtv2136)) : 'freshtv2138)
        | _ ->
            _menhir_fail ()) : 'freshtv2140)) : 'freshtv2142)) : 'freshtv2144)
    | _ ->
        _menhir_fail ()

and _menhir_goto_logical_OR_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4203 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2043 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4211 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2041 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4219 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.PIPE_PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2031 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4228 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2029 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4235 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState123
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123) : 'freshtv2030)) : 'freshtv2032)
    | Tokens.QUESTION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2035 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4278 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2033 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4285 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState98
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98) : 'freshtv2034)) : 'freshtv2036)
    | Tokens.COLON | Tokens.COMMA | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2037 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4328 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4334 "Parser.ml"
        ) = 
# 430 "Parser.mly"
    ( expr )
# 4338 "Parser.ml"
         in
        _menhir_goto_conditional_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2038)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2039 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4348 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2040)) : 'freshtv2042)) : 'freshtv2044)

and _menhir_run100 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4356 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2027 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4364 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState100
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100) : 'freshtv2028)

and _menhir_goto_logical_AND_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4406 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState408 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState417 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState401 | MenhirState395 | MenhirState391 | MenhirState387 | MenhirState380 | MenhirState377 | MenhirState373 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState68 | MenhirState120 | MenhirState117 | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2017 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4416 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2015 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4424 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.AMPERSAND_AMPERSAND ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COLON | Tokens.COMMA | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv2011 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4435 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4441 "Parser.ml"
            ) = 
# 422 "Parser.mly"
    ( expr )
# 4445 "Parser.ml"
             in
            _menhir_goto_logical_OR_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2012)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv2013 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4455 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2014)) : 'freshtv2016)) : 'freshtv2018)
    | MenhirState123 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2025 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4464 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4468 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv2023 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4476 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4480 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.AMPERSAND_AMPERSAND ->
            _menhir_run100 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COLON | Tokens.COMMA | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2019 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4491 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4495 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4501 "Parser.ml"
            ) = 
# 424 "Parser.mly"
    ( CabsEbinary (CabsOr, expr1, expr2) )
# 4505 "Parser.ml"
             in
            _menhir_goto_logical_OR_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2020)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv2021 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4515 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4519 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2022)) : 'freshtv2024)) : 'freshtv2026)
    | _ ->
        _menhir_fail ()

and _menhir_run102 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4529 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv2009 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4537 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState102
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102) : 'freshtv2010)

and _menhir_goto_inclusive_OR_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4579 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1999 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4589 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4593 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1997 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4601 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4605 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.PIPE ->
            _menhir_run102 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND_AMPERSAND | Tokens.COLON | Tokens.COMMA | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1993 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4616 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4620 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4626 "Parser.ml"
            ) = 
# 416 "Parser.mly"
    ( CabsEbinary (CabsAnd, expr1, expr2) )
# 4630 "Parser.ml"
             in
            _menhir_goto_logical_AND_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1994)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1995 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4640 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4644 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1996)) : 'freshtv1998)) : 'freshtv2000)
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState408 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState417 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState401 | MenhirState395 | MenhirState391 | MenhirState387 | MenhirState380 | MenhirState377 | MenhirState373 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState68 | MenhirState123 | MenhirState120 | MenhirState117 | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2007 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4653 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv2005 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4661 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.PIPE ->
            _menhir_run102 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND_AMPERSAND | Tokens.COLON | Tokens.COMMA | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv2001 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4672 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4678 "Parser.ml"
            ) = 
# 414 "Parser.mly"
    ( expr )
# 4682 "Parser.ml"
             in
            _menhir_goto_logical_AND_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2002)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv2003 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4692 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv2004)) : 'freshtv2006)) : 'freshtv2008)
    | _ ->
        _menhir_fail ()

and _menhir_run104 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4702 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1991 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4710 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState104
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104) : 'freshtv1992)

and _menhir_goto_exclusive_OR_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4752 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1981 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4762 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4766 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1979 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4774 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4778 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.CARET ->
            _menhir_run104 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND_AMPERSAND | Tokens.COLON | Tokens.COMMA | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1975 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4789 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4793 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4799 "Parser.ml"
            ) = 
# 408 "Parser.mly"
    ( CabsEbinary (CabsBor, expr1, expr2) )
# 4803 "Parser.ml"
             in
            _menhir_goto_inclusive_OR_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1976)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1977 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4813 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4817 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1978)) : 'freshtv1980)) : 'freshtv1982)
    | MenhirState501 | MenhirState371 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState408 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState417 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState380 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState68 | MenhirState123 | MenhirState98 | MenhirState120 | MenhirState117 | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1989 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4826 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1987 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4834 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.CARET ->
            _menhir_run104 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND_AMPERSAND | Tokens.COLON | Tokens.COMMA | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1983 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4845 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4851 "Parser.ml"
            ) = 
# 406 "Parser.mly"
    ( expr )
# 4855 "Parser.ml"
             in
            _menhir_goto_inclusive_OR_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1984)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1985 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4865 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1986)) : 'freshtv1988)) : 'freshtv1990)
    | _ ->
        _menhir_fail ()

and _menhir_run111 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4875 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1973 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4883 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState111
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState111 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState111) : 'freshtv1974)

and _menhir_goto__AND_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4925 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1963 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4935 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4939 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1961 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4947 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4951 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.AMPERSAND ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND_AMPERSAND | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1957 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4962 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4966 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4972 "Parser.ml"
            ) = 
# 400 "Parser.mly"
    ( CabsEbinary (CabsBxor, expr1, expr2) )
# 4976 "Parser.ml"
             in
            _menhir_goto_exclusive_OR_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1958)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1959 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4986 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4990 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1960)) : 'freshtv1962)) : 'freshtv1964)
    | MenhirState371 | MenhirState501 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState408 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState466 | MenhirState468 | MenhirState415 | MenhirState460 | MenhirState417 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState429 | MenhirState431 | MenhirState380 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState28 | MenhirState304 | MenhirState301 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState55 | MenhirState130 | MenhirState68 | MenhirState123 | MenhirState98 | MenhirState120 | MenhirState117 | MenhirState100 | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1971 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 4999 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1969 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5007 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.AMPERSAND ->
            _menhir_run111 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND_AMPERSAND | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1965 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5018 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5024 "Parser.ml"
            ) = 
# 398 "Parser.mly"
    ( expr )
# 5028 "Parser.ml"
             in
            _menhir_goto_exclusive_OR_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1966)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1967 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5038 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1968)) : 'freshtv1970)) : 'freshtv1972)
    | _ ->
        _menhir_fail ()

and _menhir_run106 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5048 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1955 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5056 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState106
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106) : 'freshtv1956)

and _menhir_run108 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5098 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1953 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5106 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState108
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108) : 'freshtv1954)

and _menhir_goto_equality_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5148 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState408 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState417 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState380 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState68 | MenhirState123 | MenhirState98 | MenhirState120 | MenhirState117 | MenhirState100 | MenhirState102 | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1943 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5158 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1941 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5166 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.BANG_EQ ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.EQ_EQ ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1937 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5179 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5185 "Parser.ml"
            ) = 
# 390 "Parser.mly"
    ( expr )
# 5189 "Parser.ml"
             in
            _menhir_goto__AND_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1938)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1939 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5199 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1940)) : 'freshtv1942)) : 'freshtv1944)
    | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1951 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5208 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5212 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1949 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5220 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5224 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.BANG_EQ ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.EQ_EQ ->
            _menhir_run106 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1945 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5237 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5241 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5247 "Parser.ml"
            ) = 
# 392 "Parser.mly"
    ( CabsEbinary (CabsBand, expr1, expr2) )
# 5251 "Parser.ml"
             in
            _menhir_goto__AND_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1946)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1947 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5261 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5265 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1948)) : 'freshtv1950)) : 'freshtv1952)
    | _ ->
        _menhir_fail ()

and _menhir_run88 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5275 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1935 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5283 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState88
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88) : 'freshtv1936)

and _menhir_run91 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5325 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1933 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5333 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState91
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv1934)

and _menhir_run93 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5375 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1931 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5383 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState93
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93) : 'freshtv1932)

and _menhir_run95 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5425 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1929 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5433 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState95
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95) : 'freshtv1930)

and _menhir_goto_selection_statement_dangerous : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5475 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1927) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5484 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1925) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (stmt : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5492 "Parser.ml"
    )) = _v in
    ((let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5497 "Parser.ml"
    ) = 
# 853 "Parser.mly"
    ( stmt )
# 5501 "Parser.ml"
     in
    _menhir_goto_statement_dangerous _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1926)) : 'freshtv1928)

and _menhir_goto_iteration_statement_statement_dangerous_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5508 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1923) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5517 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1921) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (stmt : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5525 "Parser.ml"
    )) = _v in
    ((let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5530 "Parser.ml"
    ) = 
# 853 "Parser.mly"
    ( stmt )
# 5534 "Parser.ml"
     in
    _menhir_goto_statement_dangerous _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1922)) : 'freshtv1924)

and _menhir_goto_labeled_statement_statement_dangerous_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5541 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1919) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5550 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1917) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (stmt : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5558 "Parser.ml"
    )) = _v in
    ((let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 5563 "Parser.ml"
    ) = 
# 853 "Parser.mly"
    ( stmt )
# 5567 "Parser.ml"
     in
    _menhir_goto_statement_dangerous _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1918)) : 'freshtv1920)

and _menhir_goto_relational_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5574 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState482 | MenhirState480 | MenhirState478 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState456 | MenhirState454 | MenhirState452 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState421 | MenhirState419 | MenhirState417 | MenhirState412 | MenhirState410 | MenhirState408 | MenhirState401 | MenhirState395 | MenhirState391 | MenhirState387 | MenhirState380 | MenhirState377 | MenhirState373 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState123 | MenhirState120 | MenhirState117 | MenhirState111 | MenhirState104 | MenhirState102 | MenhirState100 | MenhirState98 | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1899 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5584 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1897 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5592 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT_EQ ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_EQ ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1893 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5609 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5615 "Parser.ml"
            ) = 
# 380 "Parser.mly"
    ( expr )
# 5619 "Parser.ml"
             in
            _menhir_goto_equality_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1894)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1895 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5629 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1896)) : 'freshtv1898)) : 'freshtv1900)
    | MenhirState106 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1907 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5638 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5642 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1905 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5650 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5654 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT_EQ ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_EQ ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1901 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5671 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5675 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5681 "Parser.ml"
            ) = 
# 382 "Parser.mly"
    ( CabsEbinary (CabsEq, expr1, expr2) )
# 5685 "Parser.ml"
             in
            _menhir_goto_equality_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1902)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1903 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5695 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5699 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1904)) : 'freshtv1906)) : 'freshtv1908)
    | MenhirState108 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1915 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5708 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5712 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1913 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5720 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5724 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT ->
            _menhir_run95 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.GT_EQ ->
            _menhir_run93 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT ->
            _menhir_run91 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_EQ ->
            _menhir_run88 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1909 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5741 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5745 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5751 "Parser.ml"
            ) = 
# 384 "Parser.mly"
    ( CabsEbinary (CabsNe, expr1, expr2) )
# 5755 "Parser.ml"
             in
            _menhir_goto_equality_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1910)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1911 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5765 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5769 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1912)) : 'freshtv1914)) : 'freshtv1916)
    | _ ->
        _menhir_fail ()

and _menhir_run70 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5779 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1891 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5787 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState70
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70) : 'freshtv1892)

and _menhir_run85 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5829 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1889 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 5837 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState85
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85) : 'freshtv1890)

and _menhir_goto_block_item_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 5879 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1887 * _menhir_state * (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 5887 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1885 * _menhir_state * (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 5895 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.BREAK ->
        _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.CASE ->
        _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState501 _v
    | Tokens.CONTINUE ->
        _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.DEFAULT ->
        _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.DO ->
        _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.FOR ->
        _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.GOTO ->
        _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.IF ->
        _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.LBRACE ->
        _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.OTHER_NAME _v ->
        _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState501 _v
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.RETURN ->
        _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.STATIC_ASSERT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState501 _v
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.SWITCH ->
        _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState501 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState501 _v
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.WHILE ->
        _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.SEMICOLON ->
        _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState501
    | Tokens.RBRACE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1883 * _menhir_state * (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 6022 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_block_item_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 6028 "Parser.ml"
         in
        _menhir_goto_option_block_item_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1884)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState501) : 'freshtv1886)) : 'freshtv1888)

and _menhir_goto_designator_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 177 "Parser.mly"
     (Cabs.designator list)
# 6039 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1881 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 6047 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1879 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 6055 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.DOT ->
        _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState328
    | Tokens.EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1877 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 6066 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState328 in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1875 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 6074 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        ((let (_menhir_stack, _menhir_s, design) = _menhir_stack in
        let _v : (
# 174 "Parser.mly"
     (Cabs.designator list)
# 6081 "Parser.ml"
        ) = 
# 824 "Parser.mly"
    ( List.rev design )
# 6085 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1873) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 174 "Parser.mly"
     (Cabs.designator list)
# 6093 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1871) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 174 "Parser.mly"
     (Cabs.designator list)
# 6101 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1869) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (x : (
# 174 "Parser.mly"
     (Cabs.designator list)
# 6109 "Parser.ml"
        )) = _v in
        ((let _v : 'tv_option_designation_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 6114 "Parser.ml"
         in
        _menhir_goto_option_designation_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1870)) : 'freshtv1872)) : 'freshtv1874)) : 'freshtv1876)) : 'freshtv1878)
    | Tokens.LBRACKET ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) MenhirState328
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState328) : 'freshtv1880)) : 'freshtv1882)

and _menhir_goto_translation_unit : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 6127 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1867 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 6135 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1865 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 6143 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1863 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 6172 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState355 in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1861 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 6179 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        ((let (_menhir_stack, _menhir_s, edecls) = _menhir_stack in
        let _v : (
# 212 "Parser.mly"
      (Cabs.translation_unit)
# 6186 "Parser.ml"
        ) = 
# 218 "Parser.mly"
    ( TUnit (List.rev edecls) )
# 6190 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1859) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 212 "Parser.mly"
      (Cabs.translation_unit)
# 6198 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1857) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 212 "Parser.mly"
      (Cabs.translation_unit)
# 6206 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1855) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_1 : (
# 212 "Parser.mly"
      (Cabs.translation_unit)
# 6214 "Parser.ml"
        )) = _v in
        (Obj.magic _1 : 'freshtv1856)) : 'freshtv1858)) : 'freshtv1860)) : 'freshtv1862)) : 'freshtv1864)
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.STATIC_ASSERT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState355 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState355
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState355) : 'freshtv1866)) : 'freshtv1868)

and _menhir_goto_selection_statement_safe : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6265 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1853) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6274 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1851) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (stmt : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6282 "Parser.ml"
    )) = _v in
    ((let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6287 "Parser.ml"
    ) = 
# 862 "Parser.mly"
    ( stmt )
# 6291 "Parser.ml"
     in
    _menhir_goto_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1852)) : 'freshtv1854)

and _menhir_goto_iteration_statement_statement_safe_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6298 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1849) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6307 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1847) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (stmt : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6315 "Parser.ml"
    )) = _v in
    ((let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6320 "Parser.ml"
    ) = 
# 862 "Parser.mly"
    ( stmt )
# 6324 "Parser.ml"
     in
    _menhir_goto_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1848)) : 'freshtv1850)

and _menhir_goto_labeled_statement_statement_safe_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6331 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1845) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6340 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1843) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (stmt : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6348 "Parser.ml"
    )) = _v in
    ((let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6353 "Parser.ml"
    ) = 
# 862 "Parser.mly"
    ( stmt )
# 6357 "Parser.ml"
     in
    _menhir_goto_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1844)) : 'freshtv1846)

and _menhir_goto_statement_dangerous : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6364 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState468 | MenhirState431 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1773 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6374 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6378 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1771 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6384 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6388 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6394 "Parser.ml"
        ) = 
# 870 "Parser.mly"
    ( CabsScase (expr, stmt) )
# 6398 "Parser.ml"
         in
        _menhir_goto_labeled_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1772)) : 'freshtv1774)
    | MenhirState465 | MenhirState426 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1777 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6406 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1775 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6412 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6418 "Parser.ml"
        ) = 
# 872 "Parser.mly"
    ( CabsSdefault stmt )
# 6422 "Parser.ml"
         in
        _menhir_goto_labeled_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1776)) : 'freshtv1778)
    | MenhirState424 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1793 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6430 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1791 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6438 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.WHILE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1787 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6447 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1785 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6454 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.LPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1781 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6463 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1779 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6470 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ALIGNOF ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.AMPERSAND ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.BANG ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.CONSTANT _v ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState446 _v
                | Tokens.GENERIC ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.LPAREN ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.MINUS ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.MINUS_MINUS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.PLUS ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.PLUS_PLUS ->
                    _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.SIZEOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.STAR ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.STRING_LITERAL _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState446 _v
                | Tokens.TILDE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState446
                | Tokens.VAR_NAME2 _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState446 _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState446) : 'freshtv1780)) : 'freshtv1782)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1783 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6515 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1784)) : 'freshtv1786)) : 'freshtv1788)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1789 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6526 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1790)) : 'freshtv1792)) : 'freshtv1794)
    | MenhirState414 | MenhirState423 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1797 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6535 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1795 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6541 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s), _, expr1_opt), _, expr2_opt), _, expr3_opt), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6547 "Parser.ml"
        ) = 
# 922 "Parser.mly"
    ( CabsSfor (option None (fun z -> Some (FC_expr z)) expr1_opt, expr2_opt, expr3_opt, stmt) )
# 6551 "Parser.ml"
         in
        _menhir_goto_iteration_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1796)) : 'freshtv1798)
    | MenhirState482 | MenhirState456 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1801 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 6559 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6563 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1799 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 6569 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6573 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s), _, decl), _, expr2_opt), _, expr3_opt), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6579 "Parser.ml"
        ) = 
# 924 "Parser.mly"
    ( CabsSfor (Some (FC_decl decl), expr2_opt, expr3_opt, stmt) )
# 6583 "Parser.ml"
         in
        _menhir_goto_iteration_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1800)) : 'freshtv1802)
    | MenhirState415 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1817 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6591 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1815 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6599 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.WHILE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1811 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6608 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1809 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6615 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.LPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1805 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6624 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1803 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6631 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ALIGNOF ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.AMPERSAND ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.BANG ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.CONSTANT _v ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState460 _v
                | Tokens.GENERIC ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.LPAREN ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.MINUS ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.MINUS_MINUS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.PLUS ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.PLUS_PLUS ->
                    _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.SIZEOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.STAR ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.STRING_LITERAL _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState460 _v
                | Tokens.TILDE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState460
                | Tokens.VAR_NAME2 _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState460 _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState460) : 'freshtv1804)) : 'freshtv1806)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1807 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6676 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1808)) : 'freshtv1810)) : 'freshtv1812)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1813 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6687 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1814)) : 'freshtv1816)) : 'freshtv1818)
    | MenhirState496 | MenhirState485 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1821 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6696 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6700 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6704 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1819 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6710 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6714 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6718 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s), _, expr), _, stmt1), _, stmt2) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6724 "Parser.ml"
        ) = 
# 904 "Parser.mly"
    ( CabsSif (expr, stmt1, Some stmt2) )
# 6728 "Parser.ml"
         in
        _menhir_goto_selection_statement_dangerous _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1820)) : 'freshtv1822)
    | MenhirState389 | MenhirState403 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1825 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6736 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6740 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1823 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6746 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6750 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6756 "Parser.ml"
        ) = 
# 902 "Parser.mly"
    ( CabsSif (expr, stmt, None) )
# 6760 "Parser.ml"
         in
        _menhir_goto_selection_statement_dangerous _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1824)) : 'freshtv1826)
    | MenhirState385 | MenhirState399 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1829 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 6768 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6772 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1827 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 6778 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6782 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, id), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6788 "Parser.ml"
        ) = 
# 868 "Parser.mly"
    ( CabsSlabel (id, stmt) )
# 6792 "Parser.ml"
         in
        _menhir_goto_labeled_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1828)) : 'freshtv1830)
    | MenhirState379 | MenhirState397 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1833 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6800 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6804 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1831 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6810 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6814 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6820 "Parser.ml"
        ) = 
# 906 "Parser.mly"
    ( CabsSswitch (expr, stmt) )
# 6824 "Parser.ml"
         in
        _menhir_goto_selection_statement_dangerous _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1832)) : 'freshtv1834)
    | MenhirState375 | MenhirState393 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1837 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6832 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6836 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1835 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 6842 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6846 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6852 "Parser.ml"
        ) = 
# 918 "Parser.mly"
    ( CabsSwhile (expr, stmt) )
# 6856 "Parser.ml"
         in
        _menhir_goto_iteration_statement_statement_dangerous_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1836)) : 'freshtv1838)
    | MenhirState501 | MenhirState371 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1841 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6864 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1839 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6870 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
        let _v : (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 6876 "Parser.ml"
        ) = 
# 890 "Parser.mly"
    ( stmt )
# 6880 "Parser.ml"
         in
        _menhir_goto_block_item _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1840)) : 'freshtv1842)
    | _ ->
        _menhir_fail ()

and _menhir_reduce208 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6889 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
    let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 6896 "Parser.ml"
    ) = 
# 853 "Parser.mly"
    ( stmt )
# 6900 "Parser.ml"
     in
    _menhir_goto_statement_dangerous _menhir_env _menhir_stack _menhir_s _v

and _menhir_run390 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1769 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1765 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1763 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState391 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState391 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState391
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState391 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState391) : 'freshtv1764)) : 'freshtv1766)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1767 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1768)) : 'freshtv1770)

and _menhir_run394 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1761 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1757 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1755 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState395 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState395 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState395
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState395 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState395) : 'freshtv1756)) : 'freshtv1758)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1759 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1760)) : 'freshtv1762)

and _menhir_run398 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 7023 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1753 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 7032 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1749 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 7041 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1747 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 7048 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.BREAK ->
            _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.CASE ->
            _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
        | Tokens.CONTINUE ->
            _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.DEFAULT ->
            _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.DO ->
            _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.FOR ->
            _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.GOTO ->
            _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.IF ->
            _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.LBRACE ->
            _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.OTHER_NAME _v ->
            _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.RETURN ->
            _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
        | Tokens.SWITCH ->
            _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState399 _v
        | Tokens.WHILE ->
            _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState399
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState399) : 'freshtv1748)) : 'freshtv1750)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1751 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 7121 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1752)) : 'freshtv1754)

and _menhir_run400 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1745 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1741 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1739 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState401 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState401 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState401
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState401 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState401) : 'freshtv1740)) : 'freshtv1742)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1743 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1744)) : 'freshtv1746)

and _menhir_run407 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1737 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1733 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1731 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState408 _v
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.STATIC_ASSERT ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState408 _v
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState408 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState408 _v
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState408
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState408) : 'freshtv1732)) : 'freshtv1734)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1735 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1736)) : 'freshtv1738)

and _menhir_run415 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1729 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.BREAK ->
        _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.CASE ->
        _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState415 _v
    | Tokens.CONTINUE ->
        _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.DEFAULT ->
        _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.DO ->
        _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.FOR ->
        _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.GOTO ->
        _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.IF ->
        _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.LBRACE ->
        _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.OTHER_NAME _v ->
        _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState415 _v
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.RETURN ->
        _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState415 _v
    | Tokens.SWITCH ->
        _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState415 _v
    | Tokens.WHILE ->
        _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | Tokens.SEMICOLON ->
        _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState415
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState415) : 'freshtv1730)

and _menhir_run464 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1727 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1723 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1721 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.BREAK ->
            _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.CASE ->
            _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState465 _v
        | Tokens.CONTINUE ->
            _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.DEFAULT ->
            _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.DO ->
            _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.FOR ->
            _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.GOTO ->
            _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.IF ->
            _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.LBRACE ->
            _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.OTHER_NAME _v ->
            _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState465 _v
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.RETURN ->
            _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState465 _v
        | Tokens.SWITCH ->
            _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState465 _v
        | Tokens.WHILE ->
            _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState465
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState465) : 'freshtv1722)) : 'freshtv1724)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1725 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1726)) : 'freshtv1728)

and _menhir_run466 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1719 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState466 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState466 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState466
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState466 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState466) : 'freshtv1720)

and _menhir_reduce211 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 7507 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
    let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 7514 "Parser.ml"
    ) = 
# 853 "Parser.mly"
    ( stmt )
# 7518 "Parser.ml"
     in
    _menhir_goto_statement_dangerous _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_shift_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7525 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState482 | MenhirState480 | MenhirState478 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState456 | MenhirState454 | MenhirState452 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState421 | MenhirState419 | MenhirState417 | MenhirState412 | MenhirState410 | MenhirState408 | MenhirState401 | MenhirState395 | MenhirState391 | MenhirState387 | MenhirState380 | MenhirState377 | MenhirState373 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState123 | MenhirState120 | MenhirState117 | MenhirState111 | MenhirState108 | MenhirState106 | MenhirState104 | MenhirState102 | MenhirState100 | MenhirState98 | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1685 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7535 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1683 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7543 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT_GT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_LT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1679 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7556 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7562 "Parser.ml"
            ) = 
# 366 "Parser.mly"
    ( expr )
# 7566 "Parser.ml"
             in
            _menhir_goto_relational_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1680)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1681 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7576 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1682)) : 'freshtv1684)) : 'freshtv1686)
    | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1693 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7585 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7589 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1691 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7597 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7601 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT_GT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_LT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1687 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7614 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7618 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7624 "Parser.ml"
            ) = 
# 372 "Parser.mly"
    ( CabsEbinary (CabsLe, expr1, expr2) )
# 7628 "Parser.ml"
             in
            _menhir_goto_relational_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1688)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1689 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7638 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7642 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1690)) : 'freshtv1692)) : 'freshtv1694)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1701 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7651 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7655 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1699 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7663 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7667 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT_GT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_LT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1695 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7680 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7684 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7690 "Parser.ml"
            ) = 
# 368 "Parser.mly"
    ( CabsEbinary (CabsLt, expr1, expr2) )
# 7694 "Parser.ml"
             in
            _menhir_goto_relational_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1696)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1697 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7704 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7708 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1698)) : 'freshtv1700)) : 'freshtv1702)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1709 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7717 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7721 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1707 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7729 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7733 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT_GT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_LT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1703 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7746 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7750 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7756 "Parser.ml"
            ) = 
# 374 "Parser.mly"
    ( CabsEbinary (CabsGe, expr1, expr2) )
# 7760 "Parser.ml"
             in
            _menhir_goto_relational_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1704)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1705 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7770 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7774 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1706)) : 'freshtv1708)) : 'freshtv1710)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1717 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7783 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7787 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1715 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7795 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7799 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.GT_GT ->
            _menhir_run85 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LT_LT ->
            _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1711 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7812 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7816 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7822 "Parser.ml"
            ) = 
# 370 "Parser.mly"
    ( CabsEbinary (CabsGt, expr1, expr2) )
# 7826 "Parser.ml"
             in
            _menhir_goto_relational_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1712)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1713 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7836 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7840 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1714)) : 'freshtv1716)) : 'freshtv1718)
    | _ ->
        _menhir_fail ()

and _menhir_run81 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7850 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1677 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7858 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState81
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState81 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState81) : 'freshtv1678)

and _menhir_run83 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7900 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1675 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 7908 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState83
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState83 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState83) : 'freshtv1676)

and _menhir_goto_block_item : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 7950 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState501 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1669 * _menhir_state * (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 7959 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 7965 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1667 * _menhir_state * (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 7971 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (stmt : (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 7977 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, stmts) = _menhir_stack in
        let _v : (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 7983 "Parser.ml"
        ) = 
# 884 "Parser.mly"
    ( stmt::stmts )
# 7987 "Parser.ml"
         in
        _menhir_goto_block_item_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1668)) : 'freshtv1670)
    | MenhirState371 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1673) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 7997 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1671) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (stmt : (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 8005 "Parser.ml"
        )) = _v in
        ((let _v : (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 8010 "Parser.ml"
        ) = 
# 882 "Parser.mly"
    ( [stmt] )
# 8014 "Parser.ml"
         in
        _menhir_goto_block_item_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1672)) : 'freshtv1674)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_designation_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_designation_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState320 | MenhirState313 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1661 * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1659 * _menhir_state * 'tv_option_designation_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState319 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.LBRACE ->
            _menhir_run320 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState319 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState319
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState319 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState319) : 'freshtv1660)) : 'freshtv1662)
    | MenhirState336 | MenhirState323 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1665 * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 8074 "Parser.ml"
        )) * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1663 * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 8082 "Parser.ml"
        )) * _menhir_state * 'tv_option_designation_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.LBRACE ->
            _menhir_run320 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState325
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState325 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState325) : 'freshtv1664)) : 'freshtv1666)
    | _ ->
        _menhir_fail ()

and _menhir_goto_designator : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 180 "Parser.mly"
     (Cabs.designator)
# 8128 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState328 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1653 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 8137 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 180 "Parser.mly"
     (Cabs.designator)
# 8143 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1651 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 8149 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (design : (
# 180 "Parser.mly"
     (Cabs.designator)
# 8155 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, designs) = _menhir_stack in
        let _v : (
# 177 "Parser.mly"
     (Cabs.designator list)
# 8161 "Parser.ml"
        ) = 
# 830 "Parser.mly"
    ( design::designs )
# 8165 "Parser.ml"
         in
        _menhir_goto_designator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1652)) : 'freshtv1654)
    | MenhirState313 | MenhirState336 | MenhirState320 | MenhirState323 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1657) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 180 "Parser.mly"
     (Cabs.designator)
# 8175 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1655) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (design : (
# 180 "Parser.mly"
     (Cabs.designator)
# 8183 "Parser.ml"
        )) = _v in
        ((let _v : (
# 177 "Parser.mly"
     (Cabs.designator list)
# 8188 "Parser.ml"
        ) = 
# 828 "Parser.mly"
    ( [design] )
# 8192 "Parser.ml"
         in
        _menhir_goto_designator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1656)) : 'freshtv1658)
    | _ ->
        _menhir_fail ()

and _menhir_goto_external_declaration : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 8201 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState355 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1645 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 8210 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 8216 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1643 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 8222 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (def : (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 8228 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, defs) = _menhir_stack in
        let _v : (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 8234 "Parser.ml"
        ) = 
# 944 "Parser.mly"
    ( def :: defs )
# 8238 "Parser.ml"
         in
        _menhir_goto_translation_unit _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1644)) : 'freshtv1646)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1649) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 8248 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1647) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (def : (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 8256 "Parser.ml"
        )) = _v in
        ((let _v : (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 8261 "Parser.ml"
        ) = 
# 942 "Parser.mly"
    ( [def] )
# 8265 "Parser.ml"
         in
        _menhir_goto_translation_unit _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1648)) : 'freshtv1650)
    | _ ->
        _menhir_fail ()

and _menhir_goto_statement_safe : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8274 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState468 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1593 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8284 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8288 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1591 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8294 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8298 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8304 "Parser.ml"
        ) = 
# 870 "Parser.mly"
    ( CabsScase (expr, stmt) )
# 8308 "Parser.ml"
         in
        _menhir_goto_labeled_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1592)) : 'freshtv1594)
    | MenhirState465 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1597 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8316 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1595 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8322 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8328 "Parser.ml"
        ) = 
# 872 "Parser.mly"
    ( CabsSdefault stmt )
# 8332 "Parser.ml"
         in
        _menhir_goto_labeled_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1596)) : 'freshtv1598)
    | MenhirState414 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1601 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8340 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1599 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8346 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s), _, expr1_opt), _, expr2_opt), _, expr3_opt), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8352 "Parser.ml"
        ) = 
# 922 "Parser.mly"
    ( CabsSfor (option None (fun z -> Some (FC_expr z)) expr1_opt, expr2_opt, expr3_opt, stmt) )
# 8356 "Parser.ml"
         in
        _menhir_goto_iteration_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1600)) : 'freshtv1602)
    | MenhirState482 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1605 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 8364 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8368 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv1603 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 8374 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8378 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((((_menhir_stack, _menhir_s), _, decl), _, expr2_opt), _, expr3_opt), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8384 "Parser.ml"
        ) = 
# 924 "Parser.mly"
    ( CabsSfor (Some (FC_decl decl), expr2_opt, expr3_opt, stmt) )
# 8388 "Parser.ml"
         in
        _menhir_goto_iteration_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1604)) : 'freshtv1606)
    | MenhirState403 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1615 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8396 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8400 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1613 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8408 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8412 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1609 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8421 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8425 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1607 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8432 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8436 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState485 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState485 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState485 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState485 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState485
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState485) : 'freshtv1608)) : 'freshtv1610)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1611 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8509 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8513 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1612)) : 'freshtv1614)) : 'freshtv1616)
    | MenhirState485 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1619 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8522 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8526 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8530 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1617 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8536 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8540 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8544 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s), _, expr), _, stmt1), _, stmt2) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8550 "Parser.ml"
        ) = 
# 910 "Parser.mly"
    ( CabsSif (expr, stmt1, Some stmt2) )
# 8554 "Parser.ml"
         in
        _menhir_goto_selection_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1618)) : 'freshtv1620)
    | MenhirState399 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1623 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 8562 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8566 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1621 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 8572 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8576 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, id), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8582 "Parser.ml"
        ) = 
# 868 "Parser.mly"
    ( CabsSlabel (id, stmt) )
# 8586 "Parser.ml"
         in
        _menhir_goto_labeled_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1622)) : 'freshtv1624)
    | MenhirState397 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1627 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8594 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8598 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1625 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8604 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8608 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8614 "Parser.ml"
        ) = 
# 912 "Parser.mly"
    ( CabsSswitch (expr, stmt) )
# 8618 "Parser.ml"
         in
        _menhir_goto_selection_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1626)) : 'freshtv1628)
    | MenhirState393 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1631 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8626 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8630 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1629 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8636 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8640 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, expr), _, stmt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8646 "Parser.ml"
        ) = 
# 918 "Parser.mly"
    ( CabsSwhile (expr, stmt) )
# 8650 "Parser.ml"
         in
        _menhir_goto_iteration_statement_statement_safe_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1630)) : 'freshtv1632)
    | MenhirState389 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1641 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8658 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8662 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1639 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8670 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8674 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1635 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8683 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8687 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1633 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8694 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8698 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.CASE ->
                _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState496 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.DEFAULT ->
                _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.DO ->
                _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.FOR ->
                _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.IF ->
                _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.OTHER_NAME _v ->
                _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState496 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState496 _v
            | Tokens.SWITCH ->
                _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState496 _v
            | Tokens.WHILE ->
                _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState496
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState496) : 'freshtv1634)) : 'freshtv1636)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1637 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 8771 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8775 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1638)) : 'freshtv1640)) : 'freshtv1642)
    | _ ->
        _menhir_fail ()

and _menhir_reduce207 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8785 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
    let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8792 "Parser.ml"
    ) = 
# 853 "Parser.mly"
    ( stmt )
# 8796 "Parser.ml"
     in
    _menhir_goto_statement_dangerous _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_option_expression_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_expression_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState380 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1467 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1465 * _menhir_state) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1461 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1459 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, expr_opt) = _menhir_stack in
            let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 8823 "Parser.ml"
            ) = 
# 936 "Parser.mly"
    ( CabsSreturn expr_opt )
# 8827 "Parser.ml"
             in
            _menhir_goto_jump_statement _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1460)) : 'freshtv1462)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1463 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1464)) : 'freshtv1466)) : 'freshtv1468)
    | MenhirState408 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1477 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1475 * _menhir_state) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1471 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1469 * _menhir_state) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState410 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState410 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState410 _v
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState410
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState410) : 'freshtv1470)) : 'freshtv1472)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1473 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1474)) : 'freshtv1476)) : 'freshtv1478)
    | MenhirState410 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1487 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1485 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1481 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1479 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState412 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState412 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState412 _v
            | Tokens.RPAREN ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState412
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState412) : 'freshtv1480)) : 'freshtv1482)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1483 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1484)) : 'freshtv1486)) : 'freshtv1488)
    | MenhirState412 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1497 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1495 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1491 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1489 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState414 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState414 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState414 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState414 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState414
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState414) : 'freshtv1490)) : 'freshtv1492)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1493 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1494)) : 'freshtv1496)) : 'freshtv1498)
    | MenhirState417 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1507 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1505 * _menhir_state) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1501 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1499 * _menhir_state) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState419 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState419 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState419 _v
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState419
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState419) : 'freshtv1500)) : 'freshtv1502)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1503 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1504)) : 'freshtv1506)) : 'freshtv1508)
    | MenhirState419 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1517 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1515 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1511 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1509 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState421 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState421 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState421 _v
            | Tokens.RPAREN ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState421
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState421) : 'freshtv1510)) : 'freshtv1512)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1513 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1514)) : 'freshtv1516)) : 'freshtv1518)
    | MenhirState421 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1527 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1525 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1521 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1519 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.CASE ->
                _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState423 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.DEFAULT ->
                _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.DO ->
                _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.FOR ->
                _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.IF ->
                _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.OTHER_NAME _v ->
                _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState423 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState423 _v
            | Tokens.SWITCH ->
                _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState423 _v
            | Tokens.WHILE ->
                _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState423
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState423) : 'freshtv1520)) : 'freshtv1522)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1523 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1524)) : 'freshtv1526)) : 'freshtv1528)
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState482 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState415 | MenhirState456 | MenhirState423 | MenhirState424 | MenhirState426 | MenhirState431 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1549 * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1547 * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1543 * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1541 * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr_opt) = _menhir_stack in
            let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9268 "Parser.ml"
            ) = 
# 896 "Parser.mly"
    ( option CabsSnull (fun z -> CabsSexpr z) expr_opt )
# 9272 "Parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1539) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9280 "Parser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            match _menhir_s with
            | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState496 | MenhirState415 | MenhirState456 | MenhirState423 | MenhirState424 | MenhirState426 | MenhirState431 ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv1529 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9289 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                (_menhir_reduce208 _menhir_env (Obj.magic _menhir_stack) : 'freshtv1530)
            | MenhirState389 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState482 | MenhirState414 | MenhirState465 | MenhirState468 ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv1537 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9297 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                let _tok = _menhir_env._menhir_token in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv1535 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9305 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ELSE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv1531 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9314 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
                    let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9320 "Parser.ml"
                    ) = 
# 862 "Parser.mly"
    ( stmt )
# 9324 "Parser.ml"
                     in
                    _menhir_goto_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1532)
                | Tokens.ALIGNAS | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.ATOMIC | Tokens.ATOMIC_LPAREN | Tokens.AUTO | Tokens.BANG | Tokens.BOOL | Tokens.BREAK | Tokens.CASE | Tokens.CHAR | Tokens.COMPLEX | Tokens.CONST | Tokens.CONSTANT _ | Tokens.CONTINUE | Tokens.DEFAULT | Tokens.DO | Tokens.DOUBLE | Tokens.ENUM | Tokens.EXTERN | Tokens.FLOAT | Tokens.FOR | Tokens.GENERIC | Tokens.GOTO | Tokens.IF | Tokens.INLINE | Tokens.INT | Tokens.LBRACE | Tokens.LONG | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.NORETURN | Tokens.OTHER_NAME _ | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RBRACE | Tokens.REGISTER | Tokens.RESTRICT | Tokens.RETURN | Tokens.SEMICOLON | Tokens.SHORT | Tokens.SIGNED | Tokens.SIZEOF | Tokens.STAR | Tokens.STATIC | Tokens.STATIC_ASSERT | Tokens.STRING_LITERAL _ | Tokens.STRUCT | Tokens.SWITCH | Tokens.THREAD_LOCAL | Tokens.TILDE | Tokens.TYPEDEF | Tokens.TYPEDEF_NAME2 _ | Tokens.UNION | Tokens.UNSIGNED | Tokens.VAR_NAME2 _ | Tokens.VOID | Tokens.VOLATILE | Tokens.WHILE ->
                    _menhir_reduce208 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv1533 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9336 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1534)) : 'freshtv1536)) : 'freshtv1538)
            | _ ->
                _menhir_fail ()) : 'freshtv1540)) : 'freshtv1542)) : 'freshtv1544)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1545 * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1546)) : 'freshtv1548)) : 'freshtv1550)
    | MenhirState452 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1559 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9354 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1557 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9362 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1553 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9371 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1551 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9378 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState454 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState454 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState454 _v
            | Tokens.RPAREN ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState454
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState454) : 'freshtv1552)) : 'freshtv1554)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1555 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9425 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1556)) : 'freshtv1558)) : 'freshtv1560)
    | MenhirState454 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1569 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9434 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1567 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9442 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1563 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9451 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1561 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9458 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.CASE ->
                _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState456 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.DEFAULT ->
                _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.DO ->
                _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.FOR ->
                _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.IF ->
                _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.OTHER_NAME _v ->
                _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState456 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState456 _v
            | Tokens.SWITCH ->
                _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState456 _v
            | Tokens.WHILE ->
                _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState456
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState456) : 'freshtv1562)) : 'freshtv1564)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1565 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9531 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1566)) : 'freshtv1568)) : 'freshtv1570)
    | MenhirState478 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1579 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9540 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1577 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9548 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1573 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9557 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1571 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9564 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState480 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState480 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState480 _v
            | Tokens.RPAREN ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState480
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState480) : 'freshtv1572)) : 'freshtv1574)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1575 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9611 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1576)) : 'freshtv1578)) : 'freshtv1580)
    | MenhirState480 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1589 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9620 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv1587 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9628 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1583 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9637 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1581 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9644 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.BREAK ->
                _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.CASE ->
                _menhir_run466 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState482 _v
            | Tokens.CONTINUE ->
                _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.DEFAULT ->
                _menhir_run464 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.DO ->
                _menhir_run415 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.FOR ->
                _menhir_run407 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.GOTO ->
                _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.IF ->
                _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.OTHER_NAME _v ->
                _menhir_run398 _menhir_env (Obj.magic _menhir_stack) MenhirState482 _v
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.RETURN ->
                _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState482 _v
            | Tokens.SWITCH ->
                _menhir_run394 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState482 _v
            | Tokens.WHILE ->
                _menhir_run390 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | Tokens.SEMICOLON ->
                _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState482
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState482) : 'freshtv1582)) : 'freshtv1584)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv1585 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 9717 "Parser.ml"
            )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1586)) : 'freshtv1588)) : 'freshtv1590)
    | _ ->
        _menhir_fail ()

and _menhir_goto_jump_statement : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9727 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState496 | MenhirState415 | MenhirState456 | MenhirState423 | MenhirState424 | MenhirState426 | MenhirState431 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1449 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9737 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (_menhir_reduce211 _menhir_env (Obj.magic _menhir_stack) : 'freshtv1450)
    | MenhirState389 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState482 | MenhirState414 | MenhirState465 | MenhirState468 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1457 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9745 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1455 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9753 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ELSE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1451 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9762 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
            let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9768 "Parser.ml"
            ) = 
# 862 "Parser.mly"
    ( stmt )
# 9772 "Parser.ml"
             in
            _menhir_goto_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1452)
        | Tokens.ALIGNAS | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.ATOMIC | Tokens.ATOMIC_LPAREN | Tokens.AUTO | Tokens.BANG | Tokens.BOOL | Tokens.BREAK | Tokens.CASE | Tokens.CHAR | Tokens.COMPLEX | Tokens.CONST | Tokens.CONSTANT _ | Tokens.CONTINUE | Tokens.DEFAULT | Tokens.DO | Tokens.DOUBLE | Tokens.ENUM | Tokens.EXTERN | Tokens.FLOAT | Tokens.FOR | Tokens.GENERIC | Tokens.GOTO | Tokens.IF | Tokens.INLINE | Tokens.INT | Tokens.LBRACE | Tokens.LONG | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.NORETURN | Tokens.OTHER_NAME _ | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RBRACE | Tokens.REGISTER | Tokens.RESTRICT | Tokens.RETURN | Tokens.SEMICOLON | Tokens.SHORT | Tokens.SIGNED | Tokens.SIZEOF | Tokens.STAR | Tokens.STATIC | Tokens.STATIC_ASSERT | Tokens.STRING_LITERAL _ | Tokens.STRUCT | Tokens.SWITCH | Tokens.THREAD_LOCAL | Tokens.TILDE | Tokens.TYPEDEF | Tokens.TYPEDEF_NAME2 _ | Tokens.UNION | Tokens.UNSIGNED | Tokens.VAR_NAME2 _ | Tokens.VOID | Tokens.VOLATILE | Tokens.WHILE ->
            _menhir_reduce211 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1453 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 9784 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1454)) : 'freshtv1456)) : 'freshtv1458)
    | _ ->
        _menhir_fail ()

and _menhir_goto_init_declarator_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9794 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1447 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9802 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1445 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9810 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1439 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9819 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1437 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9826 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState364
        | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState364
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState364) : 'freshtv1438)) : 'freshtv1440)
    | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1441 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9843 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_init_declarator_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 9849 "Parser.ml"
         in
        _menhir_goto_option_init_declarator_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1442)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1443 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 9859 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1444)) : 'freshtv1446)) : 'freshtv1448)

and _menhir_goto_parameter_type_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9867 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState238 | MenhirState212 | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1425 * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9877 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1423 * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9883 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_parameter_type_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 9889 "Parser.ml"
         in
        _menhir_goto_option_parameter_type_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1424)) : 'freshtv1426)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1435 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 9897 "Parser.ml"
        )) * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9901 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1433 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 9909 "Parser.ml"
        )) * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9913 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1429 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 9922 "Parser.ml"
            )) * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9926 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1427 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 9933 "Parser.ml"
            )) * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9937 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, ddecltor), _, param_tys) = _menhir_stack in
            let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 9943 "Parser.ml"
            ) = 
# 698 "Parser.mly"
    ( DDecl_function (ddecltor, param_tys) )
# 9947 "Parser.ml"
             in
            _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv1428)) : 'freshtv1430)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1431 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 9957 "Parser.ml"
            )) * _menhir_state * (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 9961 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1432)) : 'freshtv1434)) : 'freshtv1436)
    | _ ->
        _menhir_fail ()

and _menhir_goto_additive_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 9971 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState70 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1405 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 9981 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 9985 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1403 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 9993 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 9997 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.MINUS ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1399 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10010 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10014 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10020 "Parser.ml"
            ) = 
# 358 "Parser.mly"
    ( CabsEbinary (CabsShl, expr1, expr2) )
# 10024 "Parser.ml"
             in
            _menhir_goto_shift_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1400)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1401 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10034 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10038 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1402)) : 'freshtv1404)) : 'freshtv1406)
    | MenhirState85 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1413 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10047 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10051 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1411 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10059 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10063 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.MINUS ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1407 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10076 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10080 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10086 "Parser.ml"
            ) = 
# 360 "Parser.mly"
    ( CabsEbinary (CabsShr, expr1, expr2) )
# 10090 "Parser.ml"
             in
            _menhir_goto_shift_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1408)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1409 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10100 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10104 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1410)) : 'freshtv1412)) : 'freshtv1414)
    | MenhirState371 | MenhirState501 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState408 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState466 | MenhirState468 | MenhirState415 | MenhirState460 | MenhirState417 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState429 | MenhirState431 | MenhirState380 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState28 | MenhirState304 | MenhirState301 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState55 | MenhirState130 | MenhirState68 | MenhirState123 | MenhirState98 | MenhirState120 | MenhirState117 | MenhirState100 | MenhirState102 | MenhirState111 | MenhirState104 | MenhirState108 | MenhirState106 | MenhirState95 | MenhirState93 | MenhirState91 | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1421 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10113 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1419 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10121 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.MINUS ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.PLUS ->
            _menhir_run81 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1415 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10134 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10140 "Parser.ml"
            ) = 
# 356 "Parser.mly"
    ( expr )
# 10144 "Parser.ml"
             in
            _menhir_goto_shift_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1416)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1417 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10154 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1418)) : 'freshtv1420)) : 'freshtv1422)
    | _ ->
        _menhir_fail ()

and _menhir_run72 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10164 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1397 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10172 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState72
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72) : 'freshtv1398)

and _menhir_run75 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10214 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1395 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10222 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState75
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState75 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState75) : 'freshtv1396)

and _menhir_run77 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10264 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1393 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 10272 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState77
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77) : 'freshtv1394)

and _menhir_goto_declaration : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10314 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState417 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1379 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10324 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1377 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10332 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState452 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState452 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState452 _v
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState452
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState452) : 'freshtv1378)) : 'freshtv1380)
    | MenhirState408 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1383 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10377 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1381 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10385 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState478 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState478 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState478 _v
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState478
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState478) : 'freshtv1382)) : 'freshtv1384)
    | MenhirState501 | MenhirState371 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1387 * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10430 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1385 * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10436 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, decl) = _menhir_stack in
        let _v : (
# 196 "Parser.mly"
     (Cabs.cabs_statement)
# 10442 "Parser.ml"
        ) = 
# 888 "Parser.mly"
    ( CabsSdecl decl )
# 10446 "Parser.ml"
         in
        _menhir_goto_block_item _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1386)) : 'freshtv1388)
    | MenhirState0 | MenhirState355 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1391 * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10454 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1389 * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 10460 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, decl) = _menhir_stack in
        let _v : (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 10466 "Parser.ml"
        ) = 
# 950 "Parser.mly"
    ( EDecl_decl decl )
# 10470 "Parser.ml"
         in
        _menhir_goto_external_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1390)) : 'freshtv1392)
    | _ ->
        _menhir_fail ()

and _menhir_reduce153 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_designation_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 10481 "Parser.ml"
     in
    _menhir_goto_option_designation_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run314 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1375 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState314 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState314 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState314
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState314 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState314) : 'freshtv1376)

and _menhir_run317 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1373 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.OTHER_NAME _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1369 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 10542 "Parser.ml"
        )) = _v in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1367 * _menhir_state) = Obj.magic _menhir_stack in
        let (id : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 10550 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (
# 180 "Parser.mly"
     (Cabs.designator)
# 10556 "Parser.ml"
        ) = 
# 836 "Parser.mly"
    ( Desig_member id )
# 10560 "Parser.ml"
         in
        _menhir_goto_designator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1368)) : 'freshtv1370)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1371 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1372)) : 'freshtv1374)

and _menhir_goto_option_block_item_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_block_item_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1365 * _menhir_state) * _menhir_state * 'tv_option_block_item_list_) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1363 * _menhir_state) * _menhir_state * 'tv_option_block_item_list_) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.RBRACE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1359 * _menhir_state) * _menhir_state * 'tv_option_block_item_list_) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1357 * _menhir_state) * _menhir_state * 'tv_option_block_item_list_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, bis_opt) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10592 "Parser.ml"
        ) = 
# 878 "Parser.mly"
    ( CabsSblock (option [] List.rev bis_opt) )
# 10596 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1355) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10604 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        match _menhir_s with
        | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState496 | MenhirState415 | MenhirState456 | MenhirState423 | MenhirState424 | MenhirState426 | MenhirState431 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1335 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10613 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            (_menhir_reduce207 _menhir_env (Obj.magic _menhir_stack) : 'freshtv1336)
        | MenhirState389 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState482 | MenhirState414 | MenhirState465 | MenhirState468 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1343 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10621 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1341 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10629 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ELSE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv1337 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10638 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, stmt) = _menhir_stack in
                let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10644 "Parser.ml"
                ) = 
# 862 "Parser.mly"
    ( stmt )
# 10648 "Parser.ml"
                 in
                _menhir_goto_statement_safe _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1338)
            | Tokens.ALIGNAS | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.ATOMIC | Tokens.ATOMIC_LPAREN | Tokens.AUTO | Tokens.BANG | Tokens.BOOL | Tokens.BREAK | Tokens.CASE | Tokens.CHAR | Tokens.COMPLEX | Tokens.CONST | Tokens.CONSTANT _ | Tokens.CONTINUE | Tokens.DEFAULT | Tokens.DO | Tokens.DOUBLE | Tokens.ENUM | Tokens.EXTERN | Tokens.FLOAT | Tokens.FOR | Tokens.GENERIC | Tokens.GOTO | Tokens.IF | Tokens.INLINE | Tokens.INT | Tokens.LBRACE | Tokens.LONG | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.NORETURN | Tokens.OTHER_NAME _ | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RBRACE | Tokens.REGISTER | Tokens.RESTRICT | Tokens.RETURN | Tokens.SEMICOLON | Tokens.SHORT | Tokens.SIGNED | Tokens.SIZEOF | Tokens.STAR | Tokens.STATIC | Tokens.STATIC_ASSERT | Tokens.STRING_LITERAL _ | Tokens.STRUCT | Tokens.SWITCH | Tokens.THREAD_LOCAL | Tokens.TILDE | Tokens.TYPEDEF | Tokens.TYPEDEF_NAME2 _ | Tokens.UNION | Tokens.UNSIGNED | Tokens.VAR_NAME2 _ | Tokens.VOID | Tokens.VOLATILE | Tokens.WHILE ->
                _menhir_reduce207 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv1339 * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10660 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1340)) : 'freshtv1342)) : 'freshtv1344)
        | MenhirState370 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1353 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 10669 "Parser.ml"
            )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 10673 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10677 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1351 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 10683 "Parser.ml"
            )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 10687 "Parser.ml"
            )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 10691 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s, specifs), _, decltor), _, stmt) = _menhir_stack in
            let _v : (
# 205 "Parser.mly"
     (Cabs.function_definition)
# 10697 "Parser.ml"
            ) = 
# 957 "Parser.mly"
    ( FunDef (specifs, decltor, stmt) )
# 10701 "Parser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1349) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 205 "Parser.mly"
     (Cabs.function_definition)
# 10709 "Parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1347) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : (
# 205 "Parser.mly"
     (Cabs.function_definition)
# 10717 "Parser.ml"
            )) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1345) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (fdef : (
# 205 "Parser.mly"
     (Cabs.function_definition)
# 10725 "Parser.ml"
            )) = _v in
            ((let _v : (
# 202 "Parser.mly"
     (Cabs.external_declaration)
# 10730 "Parser.ml"
            ) = 
# 948 "Parser.mly"
    ( EDecl_func fdef )
# 10734 "Parser.ml"
             in
            _menhir_goto_external_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1346)) : 'freshtv1348)) : 'freshtv1350)) : 'freshtv1352)) : 'freshtv1354)
        | _ ->
            _menhir_fail ()) : 'freshtv1356)) : 'freshtv1358)) : 'freshtv1360)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1361 * _menhir_state) * _menhir_state * 'tv_option_block_item_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1362)) : 'freshtv1364)) : 'freshtv1366)

and _menhir_reduce155 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_expression_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 10752 "Parser.ml"
     in
    _menhir_goto_option_expression_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_run372 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1333 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1329 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1327 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState373 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState373 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState373
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState373 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState373) : 'freshtv1328)) : 'freshtv1330)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1331 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1332)) : 'freshtv1334)

and _menhir_run376 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1325 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1321 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1319 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState377 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState377 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState377
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState377 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState377) : 'freshtv1320)) : 'freshtv1322)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1323 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1324)) : 'freshtv1326)

and _menhir_run380 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1317 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState380 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState380 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState380 _v
    | Tokens.SEMICOLON ->
        _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState380
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState380) : 'freshtv1318)

and _menhir_run384 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 10920 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1315 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 10929 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1311 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 10938 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1309 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 10945 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.BREAK ->
            _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.CASE ->
            _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState385 _v
        | Tokens.CONTINUE ->
            _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.DEFAULT ->
            _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.DO ->
            _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.FOR ->
            _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.GOTO ->
            _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.IF ->
            _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.LBRACE ->
            _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.OTHER_NAME _v ->
            _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState385 _v
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.RETURN ->
            _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState385 _v
        | Tokens.SWITCH ->
            _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState385 _v
        | Tokens.WHILE ->
            _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState385
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState385) : 'freshtv1310)) : 'freshtv1312)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1313 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 11018 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1314)) : 'freshtv1316)

and _menhir_run386 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1307 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1303 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1301 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState387 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState387 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState387
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState387 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState387) : 'freshtv1302)) : 'freshtv1304)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1305 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1306)) : 'freshtv1308)

and _menhir_run404 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1299 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.OTHER_NAME _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1295 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 11095 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1293 * _menhir_state) * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 11103 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1289 * _menhir_state) * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 11112 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1287 * _menhir_state) * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 11119 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), id) = _menhir_stack in
            let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 11125 "Parser.ml"
            ) = 
# 930 "Parser.mly"
    ( CabsSgoto id )
# 11129 "Parser.ml"
             in
            _menhir_goto_jump_statement _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1288)) : 'freshtv1290)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1291 * _menhir_state) * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 11139 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1292)) : 'freshtv1294)) : 'freshtv1296)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1297 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1298)) : 'freshtv1300)

and _menhir_run416 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1285 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1281 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1279 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState417 _v
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.STATIC_ASSERT ->
            _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState417 _v
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState417 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState417 _v
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState417
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState417) : 'freshtv1280)) : 'freshtv1282)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1283 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1284)) : 'freshtv1286)

and _menhir_run424 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1277 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.BREAK ->
        _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.CASE ->
        _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
    | Tokens.CONTINUE ->
        _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.DEFAULT ->
        _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.DO ->
        _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.FOR ->
        _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.GOTO ->
        _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.IF ->
        _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.LBRACE ->
        _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.OTHER_NAME _v ->
        _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.RETURN ->
        _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
    | Tokens.SWITCH ->
        _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
    | Tokens.WHILE ->
        _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | Tokens.SEMICOLON ->
        _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState424
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState424) : 'freshtv1278)

and _menhir_run425 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1275 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1271 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1269 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.BREAK ->
            _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.CASE ->
            _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState426 _v
        | Tokens.CONTINUE ->
            _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.DEFAULT ->
            _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.DO ->
            _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.FOR ->
            _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.GOTO ->
            _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.IF ->
            _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.LBRACE ->
            _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.OTHER_NAME _v ->
            _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState426 _v
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.RETURN ->
            _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState426 _v
        | Tokens.SWITCH ->
            _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState426 _v
        | Tokens.WHILE ->
            _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | Tokens.SEMICOLON ->
            _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState426
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState426) : 'freshtv1270)) : 'freshtv1272)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1273 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1274)) : 'freshtv1276)

and _menhir_run427 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1267 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1263 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1261 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 11446 "Parser.ml"
        ) = 
# 932 "Parser.mly"
    ( CabsScontinue )
# 11450 "Parser.ml"
         in
        _menhir_goto_jump_statement _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1262)) : 'freshtv1264)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1265 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1266)) : 'freshtv1268)

and _menhir_run429 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1259 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState429 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState429 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState429
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState429 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState429) : 'freshtv1260)

and _menhir_run432 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1257 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1253 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1251 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _v : (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 11522 "Parser.ml"
        ) = 
# 934 "Parser.mly"
    ( CabsSbreak )
# 11526 "Parser.ml"
         in
        _menhir_goto_jump_statement _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1252)) : 'freshtv1254)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1255 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1256)) : 'freshtv1258)

and _menhir_goto_init_declarator : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 11540 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState364 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1245 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 11549 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 11555 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1243 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 11561 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (idecl : (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 11567 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, idecls) = _menhir_stack in
        let _v : (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 11573 "Parser.ml"
        ) = 
# 514 "Parser.mly"
    ( idecl::idecls )
# 11577 "Parser.ml"
         in
        _menhir_goto_init_declarator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1244)) : 'freshtv1246)
    | MenhirState451 | MenhirState360 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1249) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 11587 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1247) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (idecl : (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 11595 "Parser.ml"
        )) = _v in
        ((let _v : (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 11600 "Parser.ml"
        ) = 
# 512 "Parser.mly"
    ( [idecl] )
# 11604 "Parser.ml"
         in
        _menhir_goto_init_declarator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1248)) : 'freshtv1250)
    | _ ->
        _menhir_fail ()

and _menhir_run320 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1241 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.DOT ->
        _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState320
    | Tokens.LBRACKET ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) MenhirState320
    | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LBRACE | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
        _menhir_reduce153 _menhir_env (Obj.magic _menhir_stack) MenhirState320
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState320) : 'freshtv1242)

and _menhir_goto_struct_declarator_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11632 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1239 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11640 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1237 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11648 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1231 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11657 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1229 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11664 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | Tokens.COLON ->
            _menhir_reduce151 _menhir_env (Obj.magic _menhir_stack) MenhirState167
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167) : 'freshtv1230)) : 'freshtv1232)
    | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1233 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11683 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_struct_declarator_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 11689 "Parser.ml"
         in
        _menhir_goto_option_struct_declarator_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1234)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1235 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 11699 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1236)) : 'freshtv1238)) : 'freshtv1240)

and _menhir_goto_parameter_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11707 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1227 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11715 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1225 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11723 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1219 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11732 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1217 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11739 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.ELLIPSIS ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1215 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11766 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState207 in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1213 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11774 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_ : _menhir_state) = _menhir_s in
            ((let (_menhir_stack, _menhir_s, param_decls) = _menhir_stack in
            let _v : (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 11781 "Parser.ml"
            ) = 
# 720 "Parser.mly"
    ( Params (List.rev param_decls, true) )
# 11785 "Parser.ml"
             in
            _menhir_goto_parameter_type_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1214)) : 'freshtv1216)
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState207
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState207) : 'freshtv1218)) : 'freshtv1220)
    | Tokens.RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1221 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11837 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, param_decls) = _menhir_stack in
        let _v : (
# 150 "Parser.mly"
     (Cabs.parameter_type_list)
# 11843 "Parser.ml"
        ) = 
# 718 "Parser.mly"
    ( Params (List.rev param_decls, false) )
# 11847 "Parser.ml"
         in
        _menhir_goto_parameter_type_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1222)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1223 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 11857 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1224)) : 'freshtv1226)) : 'freshtv1228)

and _menhir_run218 : _menhir_env -> 'ttv_tail -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1211) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.RBRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1195) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState218 in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1193) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        ((let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 11904 "Parser.ml"
        ) = 
# 774 "Parser.mly"
    ( DAbs_array (None, ADecl ([], false, None)) )
# 11908 "Parser.ml"
         in
        _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv1194)) : 'freshtv1196)
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.STAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1205) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState218 in
        ((let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1203) * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1199) * _menhir_state) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1197) * _menhir_state) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 11935 "Parser.ml"
            ) = 
# 793 "Parser.mly"
    ( DAbs_array (None, ADecl ([], false, Some ADeclSize_asterisk)) )
# 11939 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv1198)) : 'freshtv1200)
        | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
            _menhir_reduce270 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1201) * _menhir_state) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1202)) : 'freshtv1204)) : 'freshtv1206)
    | Tokens.STATIC ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1209) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState218 in
        ((let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1207) * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState219
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219) : 'freshtv1208)) : 'freshtv1210)
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState218 _v
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState218
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState218) : 'freshtv1212)

and _menhir_run171 : _menhir_env -> 'ttv_tail -> (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 12019 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1191) = Obj.magic _menhir_stack in
    let (id : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 12028 "Parser.ml"
    )) = _v in
    ((let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 12033 "Parser.ml"
    ) = 
# 686 "Parser.mly"
    ( DDecl_identifier id )
# 12037 "Parser.ml"
     in
    _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv1192)

and _menhir_goto_struct_declaration_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 12044 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv1189 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 12052 "Parser.ml"
    )) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 12056 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv1187 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 12064 "Parser.ml"
    )) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 12068 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.RBRACE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1185 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 12099 "Parser.ml"
        )) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 12103 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState155 in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1183 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 12111 "Parser.ml"
        )) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 12115 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        ((let (((_menhir_stack, _menhir_s, ctor), _, id_opt), _, decls) = _menhir_stack in
        let _v : (
# 96 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 12122 "Parser.ml"
        ) = 
# 576 "Parser.mly"
    (  ctor id_opt (Some (List.rev decls)) )
# 12126 "Parser.ml"
         in
        _menhir_goto_struct_or_union_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1184)) : 'freshtv1186)
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.STATIC_ASSERT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState155 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState155
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState155) : 'freshtv1188)) : 'freshtv1190)

and _menhir_goto_multiplicative_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12157 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState389 | MenhirState496 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState403 | MenhirState485 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState408 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState466 | MenhirState415 | MenhirState460 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState417 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState431 | MenhirState429 | MenhirState401 | MenhirState395 | MenhirState391 | MenhirState387 | MenhirState380 | MenhirState377 | MenhirState373 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState123 | MenhirState120 | MenhirState117 | MenhirState111 | MenhirState108 | MenhirState106 | MenhirState104 | MenhirState102 | MenhirState100 | MenhirState98 | MenhirState68 | MenhirState95 | MenhirState93 | MenhirState91 | MenhirState88 | MenhirState85 | MenhirState70 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1165 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12167 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1163 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12175 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.PERCENT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.SLASH ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.STAR ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.MINUS | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.PLUS | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1159 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12190 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12196 "Parser.ml"
            ) = 
# 346 "Parser.mly"
    ( expr )
# 12200 "Parser.ml"
             in
            _menhir_goto_additive_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1160)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1161 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12210 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1162)) : 'freshtv1164)) : 'freshtv1166)
    | MenhirState81 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1173 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12219 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12223 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1171 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12231 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12235 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.PERCENT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.SLASH ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.STAR ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.MINUS | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.PLUS | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1167 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12250 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12254 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12260 "Parser.ml"
            ) = 
# 348 "Parser.mly"
    ( CabsEbinary (CabsAdd, expr1, expr2) )
# 12264 "Parser.ml"
             in
            _menhir_goto_additive_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1168)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1169 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12274 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12278 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1170)) : 'freshtv1172)) : 'freshtv1174)
    | MenhirState83 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1181 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12287 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12291 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1179 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12299 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12303 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.PERCENT ->
            _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.SLASH ->
            _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.STAR ->
            _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.MINUS | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.PLUS | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1175 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12318 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12322 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, expr1), _, expr2) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12328 "Parser.ml"
            ) = 
# 350 "Parser.mly"
    ( CabsEbinary (CabsSub, expr1, expr2) )
# 12332 "Parser.ml"
             in
            _menhir_goto_additive_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1176)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1177 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12342 "Parser.ml"
            )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 12346 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1178)) : 'freshtv1180)) : 'freshtv1182)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_init_declarator_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_init_declarator_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1157 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 12360 "Parser.ml"
    )) * _menhir_state * 'tv_option_init_declarator_list_) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1155 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 12368 "Parser.ml"
    )) * _menhir_state * 'tv_option_init_declarator_list_) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1151 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 12377 "Parser.ml"
        )) * _menhir_state * 'tv_option_init_declarator_list_) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1149 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 12384 "Parser.ml"
        )) * _menhir_state * 'tv_option_init_declarator_list_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, decspecs), _, idecls_opt) = _menhir_stack in
        let _v : (
# 78 "Parser.mly"
     (Cabs.declaration)
# 12390 "Parser.ml"
        ) = 
# 484 "Parser.mly"
    ( Declaration_base (decspecs, option [] id idecls_opt) )
# 12394 "Parser.ml"
         in
        _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1150)) : 'freshtv1152)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1153 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 12404 "Parser.ml"
        )) * _menhir_state * 'tv_option_init_declarator_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1154)) : 'freshtv1156)) : 'freshtv1158)

and _menhir_run313 : _menhir_env -> ('ttv_tail * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 12412 "Parser.ml"
) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv1147 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 12421 "Parser.ml"
    )) * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.DOT ->
        _menhir_run317 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | Tokens.LBRACKET ->
        _menhir_run314 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LBRACE | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
        _menhir_reduce153 _menhir_env (Obj.magic _menhir_stack) MenhirState313
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState313) : 'freshtv1148)

and _menhir_goto_alignment_specifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 12439 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1145 * _menhir_state * (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 12447 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1143 * _menhir_state * (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 12455 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
        _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack) MenhirState201
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState201) : 'freshtv1144)) : 'freshtv1146)

and _menhir_run371 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1141 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.BREAK ->
        _menhir_run432 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.CASE ->
        _menhir_run429 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState371 _v
    | Tokens.CONTINUE ->
        _menhir_run427 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.DEFAULT ->
        _menhir_run425 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.DO ->
        _menhir_run424 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.FOR ->
        _menhir_run416 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.GOTO ->
        _menhir_run404 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.IF ->
        _menhir_run386 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.LBRACE ->
        _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.OTHER_NAME _v ->
        _menhir_run384 _menhir_env (Obj.magic _menhir_stack) MenhirState371 _v
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.RETURN ->
        _menhir_run380 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.STATIC_ASSERT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState371 _v
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.SWITCH ->
        _menhir_run376 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState371 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState371 _v
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.WHILE ->
        _menhir_run372 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.SEMICOLON ->
        _menhir_reduce155 _menhir_env (Obj.magic _menhir_stack) MenhirState371
    | Tokens.RBRACE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1139) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState371 in
        ((let _v : 'tv_option_block_item_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 12657 "Parser.ml"
         in
        _menhir_goto_option_block_item_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1140)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState371) : 'freshtv1142)

and _menhir_reduce104 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 12668 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, decl) = _menhir_stack in
    let _v : (
# 87 "Parser.mly"
     (Cabs.init_declarator)
# 12675 "Parser.ml"
    ) = 
# 518 "Parser.mly"
    ( InitDecl (decl, None) )
# 12679 "Parser.ml"
     in
    _menhir_goto_init_declarator _menhir_env _menhir_stack _menhir_s _v

and _menhir_run367 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 12686 "Parser.ml"
) -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv1137 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 12695 "Parser.ml"
    )) * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState367 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.LBRACE ->
        _menhir_run320 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState367 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState367
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState367 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState367) : 'freshtv1138)

and _menhir_goto_struct_declarator : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 12739 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1131 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 12748 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 12754 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1129 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 12760 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (sdecltor : (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 12766 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, sdecltors) = _menhir_stack in
        let _v : (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 12772 "Parser.ml"
        ) = 
# 615 "Parser.mly"
    ( sdecltor::sdecltors )
# 12776 "Parser.ml"
         in
        _menhir_goto_struct_declarator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1130)) : 'freshtv1132)
    | MenhirState159 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1135) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 12786 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1133) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (sdelctor : (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 12794 "Parser.ml"
        )) = _v in
        ((let _v : (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 12799 "Parser.ml"
        ) = 
# 612 "Parser.mly"
    ( [sdelctor] )
# 12803 "Parser.ml"
         in
        _menhir_goto_struct_declarator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1134)) : 'freshtv1136)
    | _ ->
        _menhir_fail ()

and _menhir_goto_parameter_declaration : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 12812 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState207 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1123 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 12821 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 12827 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1121 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 12833 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (param_decl : (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 12839 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, param_decls) = _menhir_stack in
        let _v : (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 12845 "Parser.ml"
        ) = 
# 726 "Parser.mly"
    ( param_decl::param_decls )
# 12849 "Parser.ml"
         in
        _menhir_goto_parameter_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1122)) : 'freshtv1124)
    | MenhirState176 | MenhirState191 | MenhirState238 | MenhirState212 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1127) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 12859 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1125) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (param_decl : (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 12867 "Parser.ml"
        )) = _v in
        ((let _v : (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 12872 "Parser.ml"
        ) = 
# 724 "Parser.mly"
    ( [param_decl] )
# 12876 "Parser.ml"
         in
        _menhir_goto_parameter_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1126)) : 'freshtv1128)
    | _ ->
        _menhir_fail ()

and _menhir_reduce162 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 12885 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x) = _menhir_stack in
    let _v : 'tv_option_pointer_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 12892 "Parser.ml"
     in
    _menhir_goto_option_pointer_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_option_declarator_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_declarator_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1119 * _menhir_state * 'tv_option_declarator_) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1117 * _menhir_state * 'tv_option_declarator_) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1113 * _menhir_state * 'tv_option_declarator_) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1111 * _menhir_state * 'tv_option_declarator_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState284
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState284 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState284) : 'freshtv1112)) : 'freshtv1114)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1115 * _menhir_state * 'tv_option_declarator_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1116)) : 'freshtv1118)) : 'freshtv1120)

and _menhir_goto_option_pointer_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_pointer_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState451 | MenhirState364 | MenhirState360 | MenhirState159 | MenhirState172 | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1089 * _menhir_state * 'tv_option_pointer_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1087 * _menhir_state * 'tv_option_pointer_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1083) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1081) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.STAR ->
                _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
                _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState172
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172) : 'freshtv1082)) : 'freshtv1084)
        | Tokens.VAR_NAME2 _v ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack) _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1085 * _menhir_state * 'tv_option_pointer_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1086)) : 'freshtv1088)) : 'freshtv1090)
    | MenhirState191 | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1099 * _menhir_state * 'tv_option_pointer_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1097 * _menhir_state * 'tv_option_pointer_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LBRACKET ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1093) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1091) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNAS ->
                _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.ATOMIC ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.ATOMIC_LPAREN ->
                _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.AUTO ->
                _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.BOOL ->
                _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.CHAR ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.COMPLEX ->
                _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.CONST ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.DOUBLE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.ENUM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.EXTERN ->
                _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.FLOAT ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.INLINE ->
                _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.INT ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.LONG ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.NORETURN ->
                _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.REGISTER ->
                _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.RESTRICT ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.SHORT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.SIGNED ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.STAR ->
                _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.STATIC ->
                _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.STRUCT ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.THREAD_LOCAL ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.TYPEDEF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.TYPEDEF_NAME2 _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
            | Tokens.UNION ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.UNSIGNED ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.VOID ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.VOLATILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.LBRACKET | Tokens.LPAREN ->
                _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | Tokens.RPAREN ->
                _menhir_reduce159 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191) : 'freshtv1092)) : 'freshtv1094)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1095 * _menhir_state * 'tv_option_pointer_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1096)) : 'freshtv1098)) : 'freshtv1100)
    | MenhirState212 | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1109 * _menhir_state * 'tv_option_pointer_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1107 * _menhir_state * 'tv_option_pointer_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LBRACKET ->
            _menhir_run218 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1103) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1101) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNAS ->
                _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.ATOMIC ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.ATOMIC_LPAREN ->
                _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.AUTO ->
                _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.BOOL ->
                _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.CHAR ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.COMPLEX ->
                _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.CONST ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.DOUBLE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.ENUM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.EXTERN ->
                _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.FLOAT ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.INLINE ->
                _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.INT ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.LONG ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.NORETURN ->
                _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.REGISTER ->
                _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.RESTRICT ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.SHORT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.SIGNED ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.STAR ->
                _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.STATIC ->
                _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.STRUCT ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.THREAD_LOCAL ->
                _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.TYPEDEF ->
                _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.TYPEDEF_NAME2 _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState212 _v
            | Tokens.UNION ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.UNSIGNED ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.VOID ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.VOLATILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.LBRACKET | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
                _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | Tokens.RPAREN ->
                _menhir_reduce159 _menhir_env (Obj.magic _menhir_stack) MenhirState212
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState212) : 'freshtv1102)) : 'freshtv1104)
        | Tokens.VAR_NAME2 _v ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack) _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1105 * _menhir_state * 'tv_option_pointer_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1106)) : 'freshtv1108)) : 'freshtv1110)
    | _ ->
        _menhir_fail ()

and _menhir_goto_struct_declaration : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 13191 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1075 * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 13200 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 13206 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1073 * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 13212 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (sdecl : (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 13218 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, sdecls) = _menhir_stack in
        let _v : (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 13224 "Parser.ml"
        ) = 
# 590 "Parser.mly"
    ( sdecl::sdecls )
# 13228 "Parser.ml"
         in
        _menhir_goto_struct_declaration_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1074)) : 'freshtv1076)
    | MenhirState154 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1079) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 13238 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1077) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (sdecl : (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 13246 "Parser.ml"
        )) = _v in
        ((let _v : (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 13251 "Parser.ml"
        ) = 
# 588 "Parser.mly"
    ( [sdecl] )
# 13255 "Parser.ml"
         in
        _menhir_goto_struct_declaration_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1078)) : 'freshtv1080)
    | _ ->
        _menhir_fail ()

and _menhir_reduce167 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_type_qualifier_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 13266 "Parser.ml"
     in
    _menhir_goto_option_type_qualifier_list_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_cast_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13273 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1051 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13282 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13288 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1049 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13294 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (expr2 : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13300 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, expr1) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13306 "Parser.ml"
        ) = 
# 336 "Parser.mly"
    ( CabsEbinary (CabsMul, expr1, expr2) )
# 13310 "Parser.ml"
         in
        _menhir_goto_multiplicative_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1050)) : 'freshtv1052)
    | MenhirState75 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1055 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13318 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13324 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1053 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13330 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (expr2 : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13336 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, expr1) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13342 "Parser.ml"
        ) = 
# 338 "Parser.mly"
    ( CabsEbinary (CabsDiv, expr1, expr2) )
# 13346 "Parser.ml"
         in
        _menhir_goto_multiplicative_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1054)) : 'freshtv1056)
    | MenhirState77 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1059 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13354 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13360 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1057 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13366 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (expr2 : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13372 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, expr1) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13378 "Parser.ml"
        ) = 
# 340 "Parser.mly"
    ( CabsEbinary (CabsMod, expr1, expr2) )
# 13382 "Parser.ml"
         in
        _menhir_goto_multiplicative_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1058)) : 'freshtv1060)
    | MenhirState501 | MenhirState371 | MenhirState373 | MenhirState375 | MenhirState377 | MenhirState379 | MenhirState385 | MenhirState387 | MenhirState389 | MenhirState496 | MenhirState391 | MenhirState393 | MenhirState395 | MenhirState397 | MenhirState399 | MenhirState401 | MenhirState403 | MenhirState485 | MenhirState408 | MenhirState478 | MenhirState480 | MenhirState482 | MenhirState410 | MenhirState412 | MenhirState414 | MenhirState465 | MenhirState466 | MenhirState468 | MenhirState415 | MenhirState460 | MenhirState417 | MenhirState452 | MenhirState454 | MenhirState456 | MenhirState419 | MenhirState421 | MenhirState423 | MenhirState424 | MenhirState446 | MenhirState426 | MenhirState429 | MenhirState431 | MenhirState380 | MenhirState367 | MenhirState10 | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState319 | MenhirState325 | MenhirState314 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState284 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState185 | MenhirState241 | MenhirState251 | MenhirState252 | MenhirState242 | MenhirState243 | MenhirState218 | MenhirState228 | MenhirState229 | MenhirState219 | MenhirState220 | MenhirState46 | MenhirState132 | MenhirState130 | MenhirState55 | MenhirState68 | MenhirState123 | MenhirState98 | MenhirState120 | MenhirState117 | MenhirState100 | MenhirState102 | MenhirState111 | MenhirState104 | MenhirState108 | MenhirState106 | MenhirState95 | MenhirState93 | MenhirState91 | MenhirState88 | MenhirState85 | MenhirState83 | MenhirState81 | MenhirState70 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1063) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13392 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1061) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (expr : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13400 "Parser.ml"
        )) = _v in
        ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13405 "Parser.ml"
        ) = 
# 334 "Parser.mly"
    ( expr )
# 13409 "Parser.ml"
         in
        _menhir_goto_multiplicative_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1062)) : 'freshtv1064)
    | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1067 * _menhir_state * (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 13417 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13423 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1065 * _menhir_state * (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 13429 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (expr : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13435 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, op) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13441 "Parser.ml"
        ) = 
# 300 "Parser.mly"
    ( CabsEunary (op, expr) )
# 13445 "Parser.ml"
         in
        _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1066)) : 'freshtv1068)
    | MenhirState312 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1071 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13453 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13459 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1069 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13465 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (expr : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13471 "Parser.ml"
        )) = _v in
        ((let ((_menhir_stack, _menhir_s), _, ty) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13477 "Parser.ml"
        ) = 
# 328 "Parser.mly"
    ( CabsEcast (ty, expr) )
# 13481 "Parser.ml"
         in
        _menhir_goto_cast_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1070)) : 'freshtv1072)
    | _ ->
        _menhir_fail ()

and _menhir_goto_enumerator_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13490 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv1047 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13498 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv1045 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13506 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1037 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13515 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1035 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13522 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1033 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13531 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState42 in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1031 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13539 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_ : _menhir_state) = _menhir_s in
            ((let (((_menhir_stack, _menhir_s), _, id_opt), _, enums) = _menhir_stack in
            let _v : (
# 117 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13546 "Parser.ml"
            ) = 
# 628 "Parser.mly"
    ( TSpec_enum (id_opt, Some (List.rev enums)) )
# 13550 "Parser.ml"
             in
            _menhir_goto_enum_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1032)) : 'freshtv1034)
        | Tokens.VAR_NAME2 _v ->
            _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState42 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState42) : 'freshtv1036)) : 'freshtv1038)
    | Tokens.RBRACE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1041 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13564 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1039 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13571 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, id_opt), _, enums) = _menhir_stack in
        let _v : (
# 117 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13577 "Parser.ml"
        ) = 
# 628 "Parser.mly"
    ( TSpec_enum (id_opt, Some (List.rev enums)) )
# 13581 "Parser.ml"
         in
        _menhir_goto_enum_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1040)) : 'freshtv1042)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv1043 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 13591 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1044)) : 'freshtv1046)) : 'freshtv1048)

and _menhir_reduce157 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_init_declarator_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 13601 "Parser.ml"
     in
    _menhir_goto_option_init_declarator_list_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_option_abstract_declarator_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_abstract_declarator_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv945 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 13613 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_abstract_declarator_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv943 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 13621 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (abs_decltor_opt : 'tv_option_abstract_declarator_) = _v in
        ((let (_menhir_stack, _menhir_s, specifs) = _menhir_stack in
        let _v : (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 13629 "Parser.ml"
        ) = 
# 732 "Parser.mly"
    ( PDeclaration_abs_decl (specifs, abs_decltor_opt) )
# 13633 "Parser.ml"
         in
        _menhir_goto_parameter_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv944)) : 'freshtv946)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1029 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 13641 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_abstract_declarator_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1027 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 13649 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (abs_declr_opt : 'tv_option_abstract_declarator_) = _v in
        ((let (_menhir_stack, _menhir_s, tspecs_tquals) = _menhir_stack in
        let _v : (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13657 "Parser.ml"
        ) = 
# 745 "Parser.mly"
    ( let (tspecs, tquals) = tspecs_tquals in
      Type_name (tspecs, tquals, abs_declr_opt) )
# 13662 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1025) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13670 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        match _menhir_s with
        | MenhirState185 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv955 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13679 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv953 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13687 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv949 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13696 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv947 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13703 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, ty) = _menhir_stack in
                let _v : (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 13709 "Parser.ml"
                ) = 
# 674 "Parser.mly"
    ( AS_type ty )
# 13713 "Parser.ml"
                 in
                _menhir_goto_alignment_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv948)) : 'freshtv950)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv951 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13723 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv952)) : 'freshtv954)) : 'freshtv956)
        | MenhirState146 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv971 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13732 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv969 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13740 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv965 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13749 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv963 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13756 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, ty) = _menhir_stack in
                let _v : (
# 126 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13762 "Parser.ml"
                ) = 
# 648 "Parser.mly"
    ( TSpec_Atomic ty )
# 13766 "Parser.ml"
                 in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv961) = _menhir_stack in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (_v : (
# 126 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13774 "Parser.ml"
                )) = _v in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv959) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (_v : (
# 126 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13782 "Parser.ml"
                )) = _v in
                ((let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv957) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = _menhir_s in
                let (spec : (
# 126 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13790 "Parser.ml"
                )) = _v in
                ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 13795 "Parser.ml"
                ) = 
# 564 "Parser.mly"
    ( spec )
# 13799 "Parser.ml"
                 in
                _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv958)) : 'freshtv960)) : 'freshtv962)) : 'freshtv964)) : 'freshtv966)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv967 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13809 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv968)) : 'freshtv970)) : 'freshtv972)
        | MenhirState33 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv981 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13818 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv979 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13826 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv975 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13835 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv973 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13842 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, ty) = _menhir_stack in
                let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 13848 "Parser.ml"
                ) = 
# 306 "Parser.mly"
    ( CabsEalignof ty )
# 13852 "Parser.ml"
                 in
                _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv974)) : 'freshtv976)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv977 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13862 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv978)) : 'freshtv980)) : 'freshtv982)
        | MenhirState309 | MenhirState299 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv991 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13871 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv989 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13879 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.COLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv985 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13888 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv983 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13895 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ALIGNOF ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.AMPERSAND ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.BANG ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.CONSTANT _v ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState304 _v
                | Tokens.GENERIC ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.LPAREN ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.MINUS ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.MINUS_MINUS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.PLUS ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.PLUS_PLUS ->
                    _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.SIZEOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.STAR ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.STRING_LITERAL _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState304 _v
                | Tokens.TILDE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState304
                | Tokens.VAR_NAME2 _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState304 _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState304) : 'freshtv984)) : 'freshtv986)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv987 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13940 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv988)) : 'freshtv990)) : 'freshtv992)
        | MenhirState24 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1001 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13949 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv999 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13957 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv995 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13966 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv993 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 13973 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.ALIGNOF ->
                    _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.AMPERSAND ->
                    _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.BANG ->
                    _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.CONSTANT _v ->
                    _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _v
                | Tokens.GENERIC ->
                    _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.LBRACE ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.LPAREN ->
                    _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.MINUS ->
                    _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.MINUS_MINUS ->
                    _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.PLUS ->
                    _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.PLUS_PLUS ->
                    _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.SIZEOF ->
                    _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.STAR ->
                    _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.STRING_LITERAL _v ->
                    _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _v
                | Tokens.TILDE ->
                    _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState312
                | Tokens.VAR_NAME2 _v ->
                    _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState312 _v
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState312) : 'freshtv994)) : 'freshtv996)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv997 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14020 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv998)) : 'freshtv1000)) : 'freshtv1002)
        | MenhirState20 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1011 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14029 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv1009 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14037 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1005 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14046 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1003 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14053 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.LBRACE ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState342
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState342) : 'freshtv1004)) : 'freshtv1006)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv1007 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14070 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1008)) : 'freshtv1010)) : 'freshtv1012)
        | MenhirState345 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1023 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14079 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv1021 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14087 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv1017 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14096 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _tok = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv1015 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14103 "Parser.ml"
                )) = _menhir_stack in
                let (_tok : Tokens.token) = _tok in
                ((match _tok with
                | Tokens.LBRACE ->
                    _menhir_run313 _menhir_env (Obj.magic _menhir_stack) MenhirState347
                | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.AMPERSAND_EQ | Tokens.BANG_EQ | Tokens.CARET | Tokens.CARET_EQ | Tokens.COLON | Tokens.COMMA | Tokens.EQ | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.GT_GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.LT_LT_EQ | Tokens.MINUS | Tokens.MINUS_EQ | Tokens.PERCENT | Tokens.PERCENT_EQ | Tokens.PIPE | Tokens.PIPE_EQ | Tokens.PIPE_PIPE | Tokens.PLUS | Tokens.PLUS_EQ | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.SLASH | Tokens.SLASH_EQ | Tokens.STAR | Tokens.STAR_EQ ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv1013 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14114 "Parser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _, ty) = _menhir_stack in
                    let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 14120 "Parser.ml"
                    ) = 
# 304 "Parser.mly"
    ( CabsEsizeof_type ty )
# 14124 "Parser.ml"
                     in
                    _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1014)
                | _ ->
                    assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                    _menhir_env._menhir_shifted <- (-1);
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState347) : 'freshtv1016)) : 'freshtv1018)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv1019 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 14138 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1020)) : 'freshtv1022)) : 'freshtv1024)
        | _ ->
            _menhir_fail ()) : 'freshtv1026)) : 'freshtv1028)) : 'freshtv1030)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_parameter_type_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_parameter_type_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState191 | MenhirState212 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv931) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv929) * _menhir_state * 'tv_option_parameter_type_list_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv925) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv923) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, param_tys_opt) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14170 "Parser.ml"
            ) = 
# 798 "Parser.mly"
    ( DAbs_function (None, option (Params ([], false)) (fun z -> z) param_tys_opt) )
# 14174 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv924)) : 'freshtv926)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv927) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv928)) : 'freshtv930)) : 'freshtv932)
    | MenhirState238 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv941 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14189 "Parser.ml"
        )) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv939 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14197 "Parser.ml"
        )) * _menhir_state * 'tv_option_parameter_type_list_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv935 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14206 "Parser.ml"
            )) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv933 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14213 "Parser.ml"
            )) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, dabs_decltor), _, param_tys_opt) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14219 "Parser.ml"
            ) = 
# 796 "Parser.mly"
    ( DAbs_function (Some dabs_decltor, option (Params ([], false)) (fun z -> z) param_tys_opt) )
# 14223 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv934)) : 'freshtv936)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv937 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 14233 "Parser.ml"
            )) * _menhir_state * 'tv_option_parameter_type_list_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv938)) : 'freshtv940)) : 'freshtv942)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_assignment_expression_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_assignment_expression_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv921 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14247 "Parser.ml"
    )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * 'tv_option_assignment_expression_) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : (('freshtv919 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14255 "Parser.ml"
    )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * 'tv_option_assignment_expression_) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.RBRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv915 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14264 "Parser.ml"
        )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * 'tv_option_assignment_expression_) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv913 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14271 "Parser.ml"
        )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * 'tv_option_assignment_expression_) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, ddecltor), _, tquals_opt), _, expr_opt) = _menhir_stack in
        let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14277 "Parser.ml"
        ) = 
# 690 "Parser.mly"
    ( DDecl_array (ddecltor, ADecl (option [] List.rev tquals_opt, false, option None (fun z -> Some (ADeclSize_expression z)) expr_opt)) )
# 14281 "Parser.ml"
         in
        _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv914)) : 'freshtv916)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv917 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14291 "Parser.ml"
        )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * 'tv_option_assignment_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv918)) : 'freshtv920)) : 'freshtv922)

and _menhir_goto_direct_declarator : _menhir_env -> 'ttv_tail -> (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14299 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv911 * _menhir_state * 'tv_option_pointer_) * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14307 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv909 * _menhir_state * 'tv_option_pointer_) * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14315 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LBRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv861 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14324 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv859 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14331 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState268
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState268
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState268
        | Tokens.STATIC ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv857 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14346 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState268 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv855 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14355 "Parser.ml"
            )) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ATOMIC ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState269
            | Tokens.CONST ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState269
            | Tokens.RESTRICT ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState269
            | Tokens.VOLATILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState269
            | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
                _menhir_reduce167 _menhir_env (Obj.magic _menhir_stack) MenhirState269
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState269) : 'freshtv856)) : 'freshtv858)
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState268
        | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RBRACKET | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
            _menhir_reduce167 _menhir_env (Obj.magic _menhir_stack) MenhirState268
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState268) : 'freshtv860)) : 'freshtv862)
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv869 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14386 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv867 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14393 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv865 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14438 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState176 in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv863 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14446 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_ : _menhir_state) = _menhir_s in
            ((let (_menhir_stack, ddecltor) = _menhir_stack in
            let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14453 "Parser.ml"
            ) = 
# 701 "Parser.mly"
    ( DDecl_function (ddecltor, Params ([], false)) )
# 14457 "Parser.ml"
             in
            _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv864)) : 'freshtv866)
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState176
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176) : 'freshtv868)) : 'freshtv870)
    | Tokens.COLON | Tokens.COMMA | Tokens.EQ | Tokens.LBRACE | Tokens.RPAREN | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv905 * _menhir_state * 'tv_option_pointer_) * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14491 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, ptr_opt), ddecltor) = _menhir_stack in
        let _v : (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14497 "Parser.ml"
        ) = 
# 682 "Parser.mly"
    ( Declarator (ptr_opt, ddecltor) )
# 14501 "Parser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv903) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14509 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        match _menhir_s with
        | MenhirState212 | MenhirState172 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv879) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14518 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv877) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14526 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RPAREN ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv873) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14535 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv871) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14542 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _, decltor) = _menhir_stack in
                let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14548 "Parser.ml"
                ) = 
# 688 "Parser.mly"
    ( DDecl_declarator decltor )
# 14552 "Parser.ml"
                 in
                _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv872)) : 'freshtv874)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv875) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14562 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv876)) : 'freshtv878)) : 'freshtv880)
        | MenhirState210 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv883 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 14571 "Parser.ml"
            )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14575 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv881 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 14581 "Parser.ml"
            )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14585 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, specifs), _, decltor) = _menhir_stack in
            let _v : (
# 156 "Parser.mly"
     (Cabs.parameter_declaration)
# 14591 "Parser.ml"
            ) = 
# 730 "Parser.mly"
    ( PDeclaration_decl (specifs, decltor) )
# 14595 "Parser.ml"
             in
            _menhir_goto_parameter_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv882)) : 'freshtv884)
        | MenhirState159 | MenhirState167 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv893 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14603 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv891 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14611 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.COMMA | Tokens.SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv885 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14620 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, decltor) = _menhir_stack in
                let _v : (
# 114 "Parser.mly"
     (Cabs.struct_declarator)
# 14626 "Parser.ml"
                ) = 
# 619 "Parser.mly"
    ( SDecl_simple decltor )
# 14630 "Parser.ml"
                 in
                _menhir_goto_struct_declarator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv886)
            | Tokens.COLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv887 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14638 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
                let _v : 'tv_option_declarator_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 14644 "Parser.ml"
                 in
                _menhir_goto_option_declarator_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv888)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv889 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14654 "Parser.ml"
                )) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv890)) : 'freshtv892)) : 'freshtv894)
        | MenhirState451 | MenhirState364 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv897 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14663 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv895 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14671 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.EQ ->
                _menhir_run367 _menhir_env (Obj.magic _menhir_stack) MenhirState366
            | Tokens.COMMA | Tokens.SEMICOLON ->
                _menhir_reduce104 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState366) : 'freshtv896)) : 'freshtv898)
        | MenhirState360 ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv901 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 14688 "Parser.ml"
            )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14692 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            let _tok = _menhir_env._menhir_token in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv899 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 14700 "Parser.ml"
            )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 14704 "Parser.ml"
            )) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.EQ ->
                _menhir_run367 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | Tokens.LBRACE ->
                _menhir_run371 _menhir_env (Obj.magic _menhir_stack) MenhirState370
            | Tokens.COMMA | Tokens.SEMICOLON ->
                _menhir_reduce104 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState370) : 'freshtv900)) : 'freshtv902)
        | _ ->
            _menhir_fail ()) : 'freshtv904)) : 'freshtv906)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv907 * _menhir_state * 'tv_option_pointer_) * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 14727 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv908)) : 'freshtv910)) : 'freshtv912)

and _menhir_goto_pointer : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14735 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv843 * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14745 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv841 * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14751 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, tquals), _, ptr_decltor) = _menhir_stack in
        let _v : (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14757 "Parser.ml"
        ) = 
# 708 "Parser.mly"
    ( PDecl (option [] List.rev tquals, Some ptr_decltor) )
# 14761 "Parser.ml"
         in
        _menhir_goto_pointer _menhir_env _menhir_stack _menhir_s _v) : 'freshtv842)) : 'freshtv844)
    | MenhirState451 | MenhirState364 | MenhirState360 | MenhirState159 | MenhirState172 | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv845 * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14769 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (_menhir_reduce162 _menhir_env (Obj.magic _menhir_stack) : 'freshtv846)
    | MenhirState212 | MenhirState210 | MenhirState191 | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv853 * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14777 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv851 * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14785 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LBRACKET | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce162 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.COLON | Tokens.COMMA | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv847 * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14796 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, ptr_decltor) = _menhir_stack in
            let _v : (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 14802 "Parser.ml"
            ) = 
# 750 "Parser.mly"
    ( AbsDecl_pointer ptr_decltor )
# 14806 "Parser.ml"
             in
            _menhir_goto_abstract_declarator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv848)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv849 * _menhir_state * (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 14816 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv850)) : 'freshtv852)) : 'freshtv854)
    | _ ->
        _menhir_fail ()

and _menhir_reduce141 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_abstract_declarator_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 14828 "Parser.ml"
     in
    _menhir_goto_option_abstract_declarator_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce151 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_declarator_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 14837 "Parser.ml"
     in
    _menhir_goto_option_declarator_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce161 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_pointer_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 14846 "Parser.ml"
     in
    _menhir_goto_option_pointer_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_option_struct_declarator_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_struct_declarator_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv839 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 14857 "Parser.ml"
    )) * _menhir_state * 'tv_option_struct_declarator_list_) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv837 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 14865 "Parser.ml"
    )) * _menhir_state * 'tv_option_struct_declarator_list_) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv833 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 14874 "Parser.ml"
        )) * _menhir_state * 'tv_option_struct_declarator_list_) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv831 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 14881 "Parser.ml"
        )) * _menhir_state * 'tv_option_struct_declarator_list_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, tspecs_tquals), _, sdeclrs_opt) = _menhir_stack in
        let _v : (
# 105 "Parser.mly"
     (Cabs.struct_declaration)
# 14887 "Parser.ml"
        ) = 
# 594 "Parser.mly"
    ( let (tspecs, tquals) = tspecs_tquals in Struct_declaration (tspecs, tquals, option [] id sdeclrs_opt) )
# 14891 "Parser.ml"
         in
        _menhir_goto_struct_declaration _menhir_env _menhir_stack _menhir_s _v) : 'freshtv832)) : 'freshtv834)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv835 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 14901 "Parser.ml"
        )) * _menhir_state * 'tv_option_struct_declarator_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv836)) : 'freshtv838)) : 'freshtv840)

and _menhir_run160 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv829 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState160
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState160
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState160
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState160
    | Tokens.COLON | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.STAR | Tokens.VAR_NAME2 _ ->
        _menhir_reduce167 _menhir_env (Obj.magic _menhir_stack) MenhirState160
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160) : 'freshtv830)

and _menhir_goto_assignment_operator : _menhir_env -> 'ttv_tail -> (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 14932 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv827 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 14940 "Parser.ml"
    )) * (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 14944 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv825 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 14952 "Parser.ml"
    )) * (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 14956 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState68
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState68 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68) : 'freshtv826)) : 'freshtv828)

and _menhir_reduce30 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 14998 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
    let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15005 "Parser.ml"
    ) = 
# 326 "Parser.mly"
    ( expr )
# 15009 "Parser.ml"
     in
    _menhir_goto_cast_expression _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_enumerator : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 15016 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv819 * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 15025 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 15031 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv817 * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 15037 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (enum : (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 15043 "Parser.ml"
        )) = _v in
        ((let (_menhir_stack, _menhir_s, enums) = _menhir_stack in
        let _v : (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 15049 "Parser.ml"
        ) = 
# 636 "Parser.mly"
    ( enum::enums )
# 15053 "Parser.ml"
         in
        _menhir_goto_enumerator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv818)) : 'freshtv820)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv823) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 15063 "Parser.ml"
        )) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv821) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (enum : (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 15071 "Parser.ml"
        )) = _v in
        ((let _v : (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 15076 "Parser.ml"
        ) = 
# 634 "Parser.mly"
    ( [enum] )
# 15080 "Parser.ml"
         in
        _menhir_goto_enumerator_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv822)) : 'freshtv824)
    | _ ->
        _menhir_fail ()

and _menhir_goto_declaration_specifiers : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15089 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState192 | MenhirState193 | MenhirState194 | MenhirState201 | MenhirState196 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv803 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15099 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv801 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15105 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_declaration_specifiers_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 15111 "Parser.ml"
         in
        _menhir_goto_option_declaration_specifiers_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv802)) : 'freshtv804)
    | MenhirState176 | MenhirState191 | MenhirState238 | MenhirState212 | MenhirState207 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv807 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15119 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv805 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15127 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | Tokens.LBRACKET | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | Tokens.COMMA | Tokens.RPAREN ->
            _menhir_reduce141 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState210) : 'freshtv806)) : 'freshtv808)
    | MenhirState0 | MenhirState355 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv811 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15146 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv809 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15154 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState360
        | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState360
        | Tokens.SEMICOLON ->
            _menhir_reduce157 _menhir_env (Obj.magic _menhir_stack) MenhirState360
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState360) : 'freshtv810)) : 'freshtv812)
    | MenhirState501 | MenhirState371 | MenhirState408 | MenhirState417 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv815 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15173 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv813 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 15181 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState451
        | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState451
        | Tokens.SEMICOLON ->
            _menhir_reduce157 _menhir_env (Obj.magic _menhir_stack) MenhirState451
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState451) : 'freshtv814)) : 'freshtv816)
    | _ ->
        _menhir_fail ()

and _menhir_goto_abstract_declarator : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15201 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState191 | MenhirState212 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv795) * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15211 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv793) * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15219 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv789) * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15228 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv787) * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15235 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, abs_decltor) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 15241 "Parser.ml"
            ) = 
# 757 "Parser.mly"
    ( DAbs_abs_declarator abs_decltor )
# 15245 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv788)) : 'freshtv790)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv791) * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15255 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv792)) : 'freshtv794)) : 'freshtv796)
    | MenhirState188 | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv799 * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15264 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv797 * _menhir_state * (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 15270 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_abstract_declarator_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 15276 "Parser.ml"
         in
        _menhir_goto_option_abstract_declarator_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv798)) : 'freshtv800)
    | _ ->
        _menhir_fail ()

and _menhir_reduce159 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_parameter_type_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 15287 "Parser.ml"
     in
    _menhir_goto_option_parameter_type_list_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_option_type_qualifier_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_type_qualifier_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv765 * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv763 * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState164
        | Tokens.COLON | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.VAR_NAME2 _ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv761 * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, tquals) = _menhir_stack in
            let _v : (
# 144 "Parser.mly"
     (Cabs.pointer_declarator)
# 15313 "Parser.ml"
            ) = 
# 706 "Parser.mly"
    ( PDecl (option [] List.rev tquals, None) )
# 15317 "Parser.ml"
             in
            _menhir_goto_pointer _menhir_env _menhir_stack _menhir_s _v) : 'freshtv762)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164) : 'freshtv764)) : 'freshtv766)
    | MenhirState269 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv769 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15329 "Parser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv767 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15337 "Parser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState270
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState270 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState270) : 'freshtv768)) : 'freshtv770)
    | MenhirState268 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv785 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15380 "Parser.ml"
        )) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv783 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15388 "Parser.ml"
        )) * _menhir_state * 'tv_option_type_qualifier_list_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState277 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv779 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15419 "Parser.ml"
            )) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState277 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv777 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15428 "Parser.ml"
            )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RBRACKET ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv773 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15437 "Parser.ml"
                )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv771 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15444 "Parser.ml"
                )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (((_menhir_stack, ddecltor), _, tquals_opt), _) = _menhir_stack in
                let _v : (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15450 "Parser.ml"
                ) = 
# 696 "Parser.mly"
    ( DDecl_array (ddecltor, ADecl (option [] List.rev tquals_opt, false, Some ADeclSize_asterisk)) )
# 15454 "Parser.ml"
                 in
                _menhir_goto_direct_declarator _menhir_env _menhir_stack _v) : 'freshtv772)) : 'freshtv774)
            | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
                _menhir_reduce270 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv775 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 15466 "Parser.ml"
                )) * _menhir_state * 'tv_option_type_qualifier_list_) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv776)) : 'freshtv778)) : 'freshtv780)
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState277 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState277
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState277 _v
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv781) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState277 in
            ((let _v : 'tv_option_assignment_expression_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 15483 "Parser.ml"
             in
            _menhir_goto_option_assignment_expression_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv782)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState277) : 'freshtv784)) : 'freshtv786)
    | _ ->
        _menhir_fail ()

and _menhir_goto_specifier_qualifier_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15496 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState154 | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv751 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15506 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv749 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15514 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | Tokens.SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv747) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState159 in
            ((let _v : 'tv_option_struct_declarator_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 15527 "Parser.ml"
             in
            _menhir_goto_option_struct_declarator_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv748)
        | Tokens.LPAREN | Tokens.VAR_NAME2 _ ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | Tokens.COLON ->
            _menhir_reduce151 _menhir_env (Obj.magic _menhir_stack) MenhirState159
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState159) : 'freshtv750)) : 'freshtv752)
    | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState309 | MenhirState299 | MenhirState33 | MenhirState146 | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv755 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15543 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv753 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15551 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.STAR ->
            _menhir_run160 _menhir_env (Obj.magic _menhir_stack) MenhirState188
        | Tokens.LBRACKET | Tokens.LPAREN ->
            _menhir_reduce161 _menhir_env (Obj.magic _menhir_stack) MenhirState188
        | Tokens.COLON | Tokens.RPAREN ->
            _menhir_reduce141 _menhir_env (Obj.magic _menhir_stack) MenhirState188
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState188) : 'freshtv754)) : 'freshtv756)
    | MenhirState148 | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv759 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15570 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv757 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 15576 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, x) = _menhir_stack in
        let _v : 'tv_option_specifier_qualifier_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 15582 "Parser.ml"
         in
        _menhir_goto_option_specifier_qualifier_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv758)) : 'freshtv760)
    | _ ->
        _menhir_fail ()

and _menhir_goto_unary_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15591 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState466 | MenhirState429 | MenhirState10 | MenhirState312 | MenhirState314 | MenhirState284 | MenhirState185 | MenhirState46 | MenhirState123 | MenhirState120 | MenhirState111 | MenhirState108 | MenhirState106 | MenhirState104 | MenhirState102 | MenhirState100 | MenhirState95 | MenhirState93 | MenhirState91 | MenhirState88 | MenhirState85 | MenhirState83 | MenhirState81 | MenhirState77 | MenhirState75 | MenhirState72 | MenhirState70 | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv683 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15601 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (_menhir_reduce30 _menhir_env (Obj.magic _menhir_stack) : 'freshtv684)
    | MenhirState501 | MenhirState371 | MenhirState375 | MenhirState379 | MenhirState385 | MenhirState496 | MenhirState389 | MenhirState393 | MenhirState397 | MenhirState399 | MenhirState485 | MenhirState403 | MenhirState482 | MenhirState480 | MenhirState478 | MenhirState414 | MenhirState465 | MenhirState468 | MenhirState460 | MenhirState415 | MenhirState456 | MenhirState454 | MenhirState452 | MenhirState423 | MenhirState446 | MenhirState424 | MenhirState426 | MenhirState431 | MenhirState421 | MenhirState419 | MenhirState417 | MenhirState412 | MenhirState410 | MenhirState408 | MenhirState401 | MenhirState395 | MenhirState391 | MenhirState387 | MenhirState380 | MenhirState377 | MenhirState373 | MenhirState367 | MenhirState345 | MenhirState20 | MenhirState319 | MenhirState325 | MenhirState24 | MenhirState304 | MenhirState301 | MenhirState28 | MenhirState277 | MenhirState274 | MenhirState270 | MenhirState251 | MenhirState252 | MenhirState241 | MenhirState243 | MenhirState242 | MenhirState228 | MenhirState229 | MenhirState218 | MenhirState220 | MenhirState219 | MenhirState132 | MenhirState130 | MenhirState117 | MenhirState98 | MenhirState68 | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv733 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15609 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv731 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15617 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.AMPERSAND_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv687) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv685) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15630 "Parser.ml"
            ) = 
# 460 "Parser.mly"
    ( Assign_Band )
# 15634 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv686)) : 'freshtv688)
        | Tokens.CARET_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv691) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv689) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15646 "Parser.ml"
            ) = 
# 462 "Parser.mly"
    ( Assign_Bxor )
# 15650 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv690)) : 'freshtv692)
        | Tokens.EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv695) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv693) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15662 "Parser.ml"
            ) = 
# 444 "Parser.mly"
    ( Assign  )
# 15666 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv694)) : 'freshtv696)
        | Tokens.GT_GT_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv699) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv697) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15678 "Parser.ml"
            ) = 
# 458 "Parser.mly"
    ( Assign_Shr )
# 15682 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv698)) : 'freshtv700)
        | Tokens.LT_LT_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv703) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv701) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15694 "Parser.ml"
            ) = 
# 456 "Parser.mly"
    ( Assign_Shl )
# 15698 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv702)) : 'freshtv704)
        | Tokens.MINUS_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv707) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv705) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15710 "Parser.ml"
            ) = 
# 454 "Parser.mly"
    ( Assign_Sub )
# 15714 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv706)) : 'freshtv708)
        | Tokens.PERCENT_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv711) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv709) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15726 "Parser.ml"
            ) = 
# 450 "Parser.mly"
    ( Assign_Mod )
# 15730 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv710)) : 'freshtv712)
        | Tokens.PIPE_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv715) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv713) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15742 "Parser.ml"
            ) = 
# 464 "Parser.mly"
    ( Assign_Bor )
# 15746 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv714)) : 'freshtv716)
        | Tokens.PLUS_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv719) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv717) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15758 "Parser.ml"
            ) = 
# 452 "Parser.mly"
    ( Assign_Add )
# 15762 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv718)) : 'freshtv720)
        | Tokens.SLASH_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv723) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv721) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15774 "Parser.ml"
            ) = 
# 448 "Parser.mly"
    ( Assign_Div )
# 15778 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv722)) : 'freshtv724)
        | Tokens.STAR_EQ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv727) = Obj.magic _menhir_stack in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv725) = Obj.magic _menhir_stack in
            ((let _v : (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 15790 "Parser.ml"
            ) = 
# 446 "Parser.mly"
    ( Assign_Mul )
# 15794 "Parser.ml"
             in
            _menhir_goto_assignment_operator _menhir_env _menhir_stack _v) : 'freshtv726)) : 'freshtv728)
        | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.BANG_EQ | Tokens.CARET | Tokens.COLON | Tokens.COMMA | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.MINUS | Tokens.PERCENT | Tokens.PIPE | Tokens.PIPE_PIPE | Tokens.PLUS | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.SLASH | Tokens.STAR ->
            _menhir_reduce30 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv729 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15806 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv730)) : 'freshtv732)) : 'freshtv734)
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv737 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15815 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv735 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15821 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15827 "Parser.ml"
        ) = 
# 298 "Parser.mly"
    ( CabsEpredecr expr )
# 15831 "Parser.ml"
         in
        _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv736)) : 'freshtv738)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv741 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15839 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv739 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15845 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15851 "Parser.ml"
        ) = 
# 296 "Parser.mly"
    ( CabsEpreincr expr )
# 15855 "Parser.ml"
         in
        _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv740)) : 'freshtv742)
    | MenhirState15 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv745 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15863 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv743 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15869 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15875 "Parser.ml"
        ) = 
# 302 "Parser.mly"
    ( CabsEsizeof_expr expr )
# 15879 "Parser.ml"
         in
        _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv744)) : 'freshtv746)
    | _ ->
        _menhir_fail ()

and _menhir_goto_option_argument_expression_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_argument_expression_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv681 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15892 "Parser.ml"
    )) * _menhir_state * 'tv_option_argument_expression_list_) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv679 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15900 "Parser.ml"
    )) * _menhir_state * 'tv_option_argument_expression_list_) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv675 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15909 "Parser.ml"
        )) * _menhir_state * 'tv_option_argument_expression_list_) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv673 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15916 "Parser.ml"
        )) * _menhir_state * 'tv_option_argument_expression_list_) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, expr), _, exprs_opt) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15922 "Parser.ml"
        ) = 
# 271 "Parser.mly"
    ( CabsEcall (expr, option [] List.rev exprs_opt) )
# 15926 "Parser.ml"
         in
        _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv674)) : 'freshtv676)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv677 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 15936 "Parser.ml"
        )) * _menhir_state * 'tv_option_argument_expression_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv678)) : 'freshtv680)) : 'freshtv682)

and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 15944 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv671) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (cst : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 15954 "Parser.ml"
    )) = _v in
    ((let _v : (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 15959 "Parser.ml"
    ) = 
# 229 "Parser.mly"
    ( cst )
# 15963 "Parser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv669) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 15971 "Parser.ml"
    )) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv667 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 15978 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv665 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 15986 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv659 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 15995 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv657 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 16002 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState46
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState46 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState46) : 'freshtv658)) : 'freshtv660)
    | Tokens.COMMA | Tokens.RBRACE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv661 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 16045 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, enum_cst) = _menhir_stack in
        let _v : (
# 123 "Parser.mly"
     (Cabs.enumerator)
# 16051 "Parser.ml"
        ) = 
# 640 "Parser.mly"
    ( (enum_cst, None) )
# 16055 "Parser.ml"
         in
        _menhir_goto_enumerator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv662)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv663 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 16065 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv664)) : 'freshtv666)) : 'freshtv668)) : 'freshtv670)) : 'freshtv672)

and _menhir_goto_option_declaration_specifiers_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_declaration_specifiers_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState194 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv639 * _menhir_state * (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 16078 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv637 * _menhir_state * (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 16086 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (specs_opt : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_stack, _menhir_s, sc) = _menhir_stack in
        let _v : (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 16094 "Parser.ml"
        ) = 
# 490 "Parser.mly"
    ( let specs = option empty_specs id specs_opt in
      { specs with storage_classes= sc :: specs.storage_classes }
    )
# 16100 "Parser.ml"
         in
        _menhir_goto_declaration_specifiers _menhir_env _menhir_stack _menhir_s _v) : 'freshtv638)) : 'freshtv640)
    | MenhirState196 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv643 * _menhir_state * (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 16108 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv641 * _menhir_state * (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 16116 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (specs_opt : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_stack, _menhir_s, fspec) = _menhir_stack in
        let _v : (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 16124 "Parser.ml"
        ) = 
# 502 "Parser.mly"
    ( let specs = option empty_specs id specs_opt in
      { specs with function_specifiers= fspec :: specs.function_specifiers }
    )
# 16130 "Parser.ml"
         in
        _menhir_goto_declaration_specifiers _menhir_env _menhir_stack _menhir_s _v) : 'freshtv642)) : 'freshtv644)
    | MenhirState201 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv647 * _menhir_state * (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 16138 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv645 * _menhir_state * (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 16146 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (specs_opt : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_stack, _menhir_s, aspec) = _menhir_stack in
        let _v : (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 16154 "Parser.ml"
        ) = 
# 506 "Parser.mly"
    ( let specs = option empty_specs id specs_opt in
      { specs with alignment_specifiers= aspec :: specs.alignment_specifiers }
    )
# 16160 "Parser.ml"
         in
        _menhir_goto_declaration_specifiers _menhir_env _menhir_stack _menhir_s _v) : 'freshtv646)) : 'freshtv648)
    | MenhirState193 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv651 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 16168 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv649 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 16176 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (specs_opt : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_stack, _menhir_s, tqual) = _menhir_stack in
        let _v : (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 16184 "Parser.ml"
        ) = 
# 498 "Parser.mly"
    ( let specs = option empty_specs id specs_opt in
      { specs with type_qualifiers= tqual :: specs.type_qualifiers }
    )
# 16190 "Parser.ml"
         in
        _menhir_goto_declaration_specifiers _menhir_env _menhir_stack _menhir_s _v) : 'freshtv650)) : 'freshtv652)
    | MenhirState192 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv655 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16198 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv653 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16206 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (specs_opt : 'tv_option_declaration_specifiers_) = _v in
        ((let (_menhir_stack, _menhir_s, tspec) = _menhir_stack in
        let _v : (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 16214 "Parser.ml"
        ) = 
# 494 "Parser.mly"
    ( let specs = option empty_specs id specs_opt in
      { specs with type_specifiers= tspec :: specs.type_specifiers }
    )
# 16220 "Parser.ml"
         in
        _menhir_goto_declaration_specifiers _menhir_env _menhir_stack _menhir_s _v) : 'freshtv654)) : 'freshtv656)
    | _ ->
        _menhir_fail ()

and _menhir_goto_direct_abstract_declarator : _menhir_env -> 'ttv_tail -> (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16229 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv635 * _menhir_state * 'tv_option_pointer_) * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16237 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv633 * _menhir_state * 'tv_option_pointer_) * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16245 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LBRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv623 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16254 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv621 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16261 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv605 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16294 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState241 in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv603 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16302 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_ : _menhir_state) = _menhir_s in
            ((let (_menhir_stack, dabs_decltor) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16309 "Parser.ml"
            ) = 
# 766 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl ([], false, None)) )
# 16313 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv604)) : 'freshtv606)
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv615 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16325 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState241 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv613 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16334 "Parser.ml"
            )) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.RBRACKET ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv609 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16343 "Parser.ml"
                )) * _menhir_state) = Obj.magic _menhir_stack in
                ((let _ = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv607 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16350 "Parser.ml"
                )) * _menhir_state) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, dabs_decltor), _) = _menhir_stack in
                let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16356 "Parser.ml"
                ) = 
# 791 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl ([], false, Some ADeclSize_asterisk)) )
# 16360 "Parser.ml"
                 in
                _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv608)) : 'freshtv610)
            | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
                _menhir_reduce270 _menhir_env (Obj.magic _menhir_stack)
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv611 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16372 "Parser.ml"
                )) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv612)) : 'freshtv614)) : 'freshtv616)
        | Tokens.STATIC ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv619 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16381 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState241 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv617 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16390 "Parser.ml"
            )) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.ATOMIC ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.CONST ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState242 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.RESTRICT ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState242 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState242 _v
            | Tokens.VOLATILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState242) : 'freshtv618)) : 'freshtv620)
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState241
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState241) : 'freshtv622)) : 'freshtv624)
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv627 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16453 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv625 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16460 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState238 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | Tokens.RPAREN ->
            _menhir_reduce159 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState238) : 'freshtv626)) : 'freshtv628)
    | Tokens.COLON | Tokens.COMMA | Tokens.RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv629 * _menhir_state * 'tv_option_pointer_) * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16533 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, ptr_decltor_opt), dabs_decltor) = _menhir_stack in
        let _v : (
# 162 "Parser.mly"
     (Cabs.abstract_declarator)
# 16539 "Parser.ml"
        ) = 
# 752 "Parser.mly"
    ( AbsDecl_direct (ptr_decltor_opt, dabs_decltor) )
# 16543 "Parser.ml"
         in
        _menhir_goto_abstract_declarator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv630)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv631 * _menhir_state * 'tv_option_pointer_) * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 16553 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv632)) : 'freshtv634)) : 'freshtv636)

and _menhir_reduce168 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 16561 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x) = _menhir_stack in
    let _v : 'tv_option_type_qualifier_list_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 16568 "Parser.ml"
     in
    _menhir_goto_option_type_qualifier_list_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_option_specifier_qualifier_list_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_specifier_qualifier_list_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv597 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 16580 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_specifier_qualifier_list_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv595 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 16588 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (tspecs_tquals_opt : 'tv_option_specifier_qualifier_list_) = _v in
        ((let (_menhir_stack, _menhir_s, tqual) = _menhir_stack in
        let _v : (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 16596 "Parser.ml"
        ) = 
# 605 "Parser.mly"
    (
      let (tspecs, tquals) = option ([],[]) id tspecs_tquals_opt in
      (tspecs, tqual::tquals)
    )
# 16603 "Parser.ml"
         in
        _menhir_goto_specifier_qualifier_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv596)) : 'freshtv598)
    | MenhirState148 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv601 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16611 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_option_specifier_qualifier_list_) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv599 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16619 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let (tspecs_tquals_opt : 'tv_option_specifier_qualifier_list_) = _v in
        ((let (_menhir_stack, _menhir_s, tspec) = _menhir_stack in
        let _v : (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 16627 "Parser.ml"
        ) = 
# 600 "Parser.mly"
    (
      let (tspecs, tquals) = option ([],[]) id tspecs_tquals_opt in
      (tspec::tspecs, tquals)
    )
# 16634 "Parser.ml"
         in
        _menhir_goto_specifier_qualifier_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv600)) : 'freshtv602)
    | _ ->
        _menhir_fail ()

and _menhir_goto_postfix_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16643 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv593 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16651 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv591 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16659 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.DOT ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv557 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16668 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv555 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16675 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.OTHER_NAME _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv551 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16684 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_v : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 16689 "Parser.ml"
            )) = _v in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv549 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16696 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (id : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 16701 "Parser.ml"
            )) = _v in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16707 "Parser.ml"
            ) = 
# 273 "Parser.mly"
    ( CabsEmemberof (expr, id) )
# 16711 "Parser.ml"
             in
            _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv550)) : 'freshtv552)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv553 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16721 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv554)) : 'freshtv556)) : 'freshtv558)
    | Tokens.LBRACKET ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv561 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16730 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv559 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16737 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState132
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState132 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState132) : 'freshtv560)) : 'freshtv562)
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv567 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16780 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv565 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16787 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState55
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState55 _v
        | Tokens.RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv563) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState55 in
            ((let _v : 'tv_option_argument_expression_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 16828 "Parser.ml"
             in
            _menhir_goto_option_argument_expression_list_ _menhir_env _menhir_stack _menhir_s _v) : 'freshtv564)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState55) : 'freshtv566)) : 'freshtv568)
    | Tokens.MINUS_GT ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv577 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16840 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv575 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16847 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.OTHER_NAME _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv571 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16856 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_v : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 16861 "Parser.ml"
            )) = _v in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv569 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16868 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (id : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 16873 "Parser.ml"
            )) = _v in
            ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
            let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16879 "Parser.ml"
            ) = 
# 275 "Parser.mly"
    ( CabsEmemberofptr (expr, id) )
# 16883 "Parser.ml"
             in
            _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv570)) : 'freshtv572)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv573 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16893 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv574)) : 'freshtv576)) : 'freshtv578)
    | Tokens.MINUS_MINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv581 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16902 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv579 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16909 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16915 "Parser.ml"
        ) = 
# 279 "Parser.mly"
    ( CabsEpostdecr expr )
# 16919 "Parser.ml"
         in
        _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv580)) : 'freshtv582)
    | Tokens.PLUS_PLUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv585 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16927 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _ = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv583 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16934 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16940 "Parser.ml"
        ) = 
# 277 "Parser.mly"
    ( CabsEpostincr expr )
# 16944 "Parser.ml"
         in
        _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv584)) : 'freshtv586)
    | Tokens.AMPERSAND | Tokens.AMPERSAND_AMPERSAND | Tokens.AMPERSAND_EQ | Tokens.BANG_EQ | Tokens.CARET | Tokens.CARET_EQ | Tokens.COLON | Tokens.COMMA | Tokens.EQ | Tokens.EQ_EQ | Tokens.GT | Tokens.GT_EQ | Tokens.GT_GT | Tokens.GT_GT_EQ | Tokens.LT | Tokens.LT_EQ | Tokens.LT_LT | Tokens.LT_LT_EQ | Tokens.MINUS | Tokens.MINUS_EQ | Tokens.PERCENT | Tokens.PERCENT_EQ | Tokens.PIPE | Tokens.PIPE_EQ | Tokens.PIPE_PIPE | Tokens.PLUS | Tokens.PLUS_EQ | Tokens.QUESTION | Tokens.RBRACE | Tokens.RBRACKET | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.SLASH | Tokens.SLASH_EQ | Tokens.STAR | Tokens.STAR_EQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv587 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16952 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, expr) = _menhir_stack in
        let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16958 "Parser.ml"
        ) = 
# 294 "Parser.mly"
    ( expr )
# 16962 "Parser.ml"
         in
        _menhir_goto_unary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv588)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv589 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 16972 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv590)) : 'freshtv592)) : 'freshtv594)

and _menhir_goto_struct_or_union_specifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 96 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16980 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv547) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 96 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16989 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv545) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (spec : (
# 96 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 16997 "Parser.ml"
    )) = _v in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 17002 "Parser.ml"
    ) = 
# 566 "Parser.mly"
    ( spec )
# 17006 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv546)) : 'freshtv548)

and _menhir_goto_option_OTHER_NAME_ : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_option_OTHER_NAME_ -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv533 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv531 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv527 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv525 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.VAR_NAME2 _v ->
                _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38 _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38) : 'freshtv526)) : 'freshtv528)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv529 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv530)) : 'freshtv532)) : 'freshtv534)
    | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv543 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17049 "Parser.ml"
        )) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv541 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17057 "Parser.ml"
        )) * _menhir_state * 'tv_option_OTHER_NAME_) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv537 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17066 "Parser.ml"
            )) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
            ((let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv535 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17073 "Parser.ml"
            )) * _menhir_state * 'tv_option_OTHER_NAME_) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ATOMIC ->
                _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.ATOMIC_LPAREN ->
                _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.BOOL ->
                _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.CHAR ->
                _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.COMPLEX ->
                _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.CONST ->
                _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.DOUBLE ->
                _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.ENUM ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.FLOAT ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.INT ->
                _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.LONG ->
                _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.RESTRICT ->
                _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.SHORT ->
                _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.SIGNED ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.STATIC_ASSERT ->
                _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.STRUCT ->
                _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.TYPEDEF_NAME2 _v ->
                _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v
            | Tokens.UNION ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.UNSIGNED ->
                _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.VOID ->
                _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | Tokens.VOLATILE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState154
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154) : 'freshtv536)) : 'freshtv538)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv539 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17130 "Parser.ml"
            )) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv540)) : 'freshtv542)) : 'freshtv544)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_reduce149 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_declaration_specifiers_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 17147 "Parser.ml"
     in
    _menhir_goto_option_declaration_specifiers_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_type_qualifier_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17154 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState269 | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv483 * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17164 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv481 * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17172 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState161
        | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.COLON | Tokens.COMMA | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LBRACKET | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RPAREN | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
            _menhir_reduce168 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState161) : 'freshtv482)) : 'freshtv484)
    | MenhirState219 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv487) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17195 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv485) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17203 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState220 _v
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState220
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState220) : 'freshtv486)) : 'freshtv488)
    | MenhirState218 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv499) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17254 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv497) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17262 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv491) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17295 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState228 in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv489) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17303 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_ : _menhir_state) = _menhir_s in
            ((let (_menhir_stack, _, tquals) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17310 "Parser.ml"
            ) = 
# 772 "Parser.mly"
    ( DAbs_array (None, ADecl (tquals, false, None)) )
# 17314 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv490)) : 'freshtv492)
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.STATIC ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv495) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17328 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState228 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv493) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17337 "Parser.ml"
            )) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState229
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229) : 'freshtv494)) : 'freshtv496)
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState228 _v
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState228
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState228) : 'freshtv498)) : 'freshtv500)
    | MenhirState242 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv503 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17392 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17396 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv501 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17404 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17408 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState243 _v
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState243
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState243) : 'freshtv502)) : 'freshtv504)
    | MenhirState241 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv515 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17459 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17463 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv513 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17471 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17475 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.RBRACKET ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv507 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17508 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17512 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState251 in
            ((let _ = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv505 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17520 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17524 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_ : _menhir_state) = _menhir_s in
            ((let ((_menhir_stack, dabs_decltor), _, tquals) = _menhir_stack in
            let _v : (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17531 "Parser.ml"
            ) = 
# 762 "Parser.mly"
    ( DAbs_array (Some dabs_decltor, ADecl (tquals, false, None)) )
# 17535 "Parser.ml"
             in
            _menhir_goto_direct_abstract_declarator _menhir_env _menhir_stack _v) : 'freshtv506)) : 'freshtv508)
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.STATIC ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv511 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17549 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17553 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState251 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv509 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 17562 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17566 "Parser.ml"
            )) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState252 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState252 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState252 _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState252) : 'freshtv510)) : 'freshtv512)
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState251 _v
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState251
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState251) : 'freshtv514)) : 'freshtv516)
    | MenhirState268 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv523 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 17621 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17625 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv521 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 17633 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17637 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState273
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState273
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState273
        | Tokens.STATIC ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv519 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 17652 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17656 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState273 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _tok = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv517 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 17665 "Parser.ml"
            )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 17669 "Parser.ml"
            )) * _menhir_state) = _menhir_stack in
            let (_tok : Tokens.token) = _tok in
            ((match _tok with
            | Tokens.ALIGNOF ->
                _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.AMPERSAND ->
                _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.BANG ->
                _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.CONSTANT _v ->
                _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState274 _v
            | Tokens.GENERIC ->
                _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.LPAREN ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.MINUS ->
                _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.MINUS_MINUS ->
                _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.PLUS ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.PLUS_PLUS ->
                _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.SIZEOF ->
                _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.STAR ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.STRING_LITERAL _v ->
                _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState274 _v
            | Tokens.TILDE ->
                _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState274
            | Tokens.VAR_NAME2 _v ->
                _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState274 _v
            | _ ->
                assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                _menhir_env._menhir_shifted <- (-1);
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState274) : 'freshtv518)) : 'freshtv520)
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState273
        | Tokens.ALIGNOF | Tokens.AMPERSAND | Tokens.BANG | Tokens.CONSTANT _ | Tokens.GENERIC | Tokens.LPAREN | Tokens.MINUS | Tokens.MINUS_MINUS | Tokens.PLUS | Tokens.PLUS_PLUS | Tokens.RBRACKET | Tokens.SIZEOF | Tokens.STAR | Tokens.STRING_LITERAL _ | Tokens.TILDE | Tokens.VAR_NAME2 _ ->
            _menhir_reduce168 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState273) : 'freshtv522)) : 'freshtv524)
    | _ ->
        _menhir_fail ()

and _menhir_reduce163 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_specifier_qualifier_list_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 17723 "Parser.ml"
     in
    _menhir_goto_option_specifier_qualifier_list_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce270 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let _v : (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 17733 "Parser.ml"
    ) = 
# 312 "Parser.mly"
    ( CabsIndirection )
# 17737 "Parser.ml"
     in
    _menhir_goto_unary_operator _menhir_env _menhir_stack _menhir_s _v

and _menhir_run20 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv479 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState20
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv480)

and _menhir_goto_primary_expression : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 17827 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv477) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 17836 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv475) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (expr : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 17844 "Parser.ml"
    )) = _v in
    ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 17849 "Parser.ml"
    ) = 
# 267 "Parser.mly"
    ( expr )
# 17853 "Parser.ml"
     in
    _menhir_goto_postfix_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv476)) : 'freshtv478)

and _menhir_goto_unary_operator : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 17860 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv473 * _menhir_state * (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 17868 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv471 * _menhir_state * (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 17876 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState47
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47) : 'freshtv472)) : 'freshtv474)

and _menhir_goto_struct_or_union : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17918 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv469 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17926 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv467 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17934 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.OTHER_NAME _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv465 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17943 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState151 in
        let (_v : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 17949 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv463 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17957 "Parser.ml"
        )) * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 17961 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS | Tokens.ATOMIC | Tokens.ATOMIC_LPAREN | Tokens.AUTO | Tokens.BOOL | Tokens.CHAR | Tokens.COLON | Tokens.COMMA | Tokens.COMPLEX | Tokens.CONST | Tokens.DOUBLE | Tokens.ENUM | Tokens.EXTERN | Tokens.FLOAT | Tokens.INLINE | Tokens.INT | Tokens.LBRACKET | Tokens.LONG | Tokens.LPAREN | Tokens.NORETURN | Tokens.REGISTER | Tokens.RESTRICT | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.SHORT | Tokens.SIGNED | Tokens.STAR | Tokens.STATIC | Tokens.STRUCT | Tokens.THREAD_LOCAL | Tokens.TYPEDEF | Tokens.TYPEDEF_NAME2 _ | Tokens.UNION | Tokens.UNSIGNED | Tokens.VAR_NAME2 _ | Tokens.VOID | Tokens.VOLATILE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv459 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17970 "Parser.ml"
            )) * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 17974 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, ctor), _, id) = _menhir_stack in
            let _v : (
# 96 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 17980 "Parser.ml"
            ) = 
# 578 "Parser.mly"
    ( ctor (Some id) None )
# 17984 "Parser.ml"
             in
            _menhir_goto_struct_or_union_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv460)
        | Tokens.LBRACE ->
            _menhir_reduce140 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv461 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 17996 "Parser.ml"
            )) * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 18000 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv462)) : 'freshtv464)) : 'freshtv466)
    | Tokens.LBRACE ->
        _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack) MenhirState151
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState151) : 'freshtv468)) : 'freshtv470)

and _menhir_goto_function_specifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 18014 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv457 * _menhir_state * (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 18022 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv455 * _menhir_state * (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 18030 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState196 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
        _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack) MenhirState196
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState196) : 'freshtv456)) : 'freshtv458)

and _menhir_reduce139 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_option_OTHER_NAME_ = 
# 29 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( None )
# 18104 "Parser.ml"
     in
    _menhir_goto_option_OTHER_NAME_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_enum_specifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 117 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18111 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv453) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 117 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18120 "Parser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv451) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (spec : (
# 117 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18128 "Parser.ml"
    )) = _v in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18133 "Parser.ml"
    ) = 
# 568 "Parser.mly"
    ( spec )
# 18137 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv452)) : 'freshtv454)

and _menhir_reduce140 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 18144 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, x) = _menhir_stack in
    let _v : 'tv_option_OTHER_NAME_ = 
# 31 "/Users/catzilla/.opam/4.01.0/lib/menhir/standard.mly"
    ( Some x )
# 18151 "Parser.ml"
     in
    _menhir_goto_option_OTHER_NAME_ _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_type_specifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18158 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState309 | MenhirState299 | MenhirState33 | MenhirState185 | MenhirState155 | MenhirState154 | MenhirState149 | MenhirState148 | MenhirState146 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv445 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18168 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv443 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18176 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState148 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | Tokens.COLON | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
            _menhir_reduce163 _menhir_env (Obj.magic _menhir_stack) MenhirState148
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState148) : 'freshtv444)) : 'freshtv446)
    | MenhirState501 | MenhirState371 | MenhirState417 | MenhirState408 | MenhirState355 | MenhirState0 | MenhirState176 | MenhirState238 | MenhirState212 | MenhirState207 | MenhirState201 | MenhirState196 | MenhirState194 | MenhirState193 | MenhirState192 | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv449 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18231 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv447 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 18239 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState192 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
            _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack) MenhirState192
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState192) : 'freshtv448)) : 'freshtv450)
    | _ ->
        _menhir_fail ()

and _menhir_goto_storage_class_specifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 18313 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv441 * _menhir_state * (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 18321 "Parser.ml"
    )) = Obj.magic _menhir_stack in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv439 * _menhir_state * (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 18329 "Parser.ml"
    )) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState194 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
        _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack) MenhirState194
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState194) : 'freshtv440)) : 'freshtv442)

and _menhir_goto_type_qualifier : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18401 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState345 | MenhirState20 | MenhirState24 | MenhirState309 | MenhirState299 | MenhirState33 | MenhirState146 | MenhirState185 | MenhirState155 | MenhirState154 | MenhirState149 | MenhirState148 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv425 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18411 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv423 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18419 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | Tokens.COLON | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
            _menhir_reduce163 _menhir_env (Obj.magic _menhir_stack) MenhirState149
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149) : 'freshtv424)) : 'freshtv426)
    | MenhirState273 | MenhirState251 | MenhirState243 | MenhirState228 | MenhirState220 | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv429 * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 18474 "Parser.ml"
        )) * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18478 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv427 * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 18484 "Parser.ml"
        )) * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18488 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, tquals), _, tqual) = _menhir_stack in
        let _v : (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 18494 "Parser.ml"
        ) = 
# 714 "Parser.mly"
    ( tqual::tquals )
# 18498 "Parser.ml"
         in
        _menhir_goto_type_qualifier_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv428)) : 'freshtv430)
    | MenhirState268 | MenhirState269 | MenhirState241 | MenhirState242 | MenhirState218 | MenhirState219 | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv433 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18506 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv431 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18512 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, tqual) = _menhir_stack in
        let _v : (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 18518 "Parser.ml"
        ) = 
# 712 "Parser.mly"
    ( [tqual] )
# 18522 "Parser.ml"
         in
        _menhir_goto_type_qualifier_list _menhir_env _menhir_stack _menhir_s _v) : 'freshtv432)) : 'freshtv434)
    | MenhirState501 | MenhirState371 | MenhirState417 | MenhirState408 | MenhirState355 | MenhirState0 | MenhirState176 | MenhirState238 | MenhirState212 | MenhirState207 | MenhirState191 | MenhirState201 | MenhirState196 | MenhirState194 | MenhirState193 | MenhirState192 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv437 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18530 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        let _tok = _menhir_env._menhir_token in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv435 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 18538 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNAS ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.AUTO ->
            _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.EXTERN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.INLINE ->
            _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.NORETURN ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.REGISTER ->
            _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.STATIC ->
            _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.THREAD_LOCAL ->
            _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.TYPEDEF ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | Tokens.COMMA | Tokens.LBRACKET | Tokens.LPAREN | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.STAR | Tokens.VAR_NAME2 _ ->
            _menhir_reduce149 _menhir_env (Obj.magic _menhir_stack) MenhirState193
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193) : 'freshtv436)) : 'freshtv438)
    | _ ->
        _menhir_fail ()

and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 18612 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv421) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (id : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 18622 "Parser.ml"
    )) = _v in
    ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 18627 "Parser.ml"
    ) = 
# 235 "Parser.mly"
    ( CabsEident id )
# 18631 "Parser.ml"
     in
    _menhir_goto_primary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv422)

and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv419) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 18644 "Parser.ml"
    ) = 
# 318 "Parser.mly"
    ( CabsBnot )
# 18648 "Parser.ml"
     in
    _menhir_goto_unary_operator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv420)

and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 18655 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv417) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (lit : (
# 39 "Parser.mly"
      (Cabs.cabs_string_literal)
# 18665 "Parser.ml"
    )) = _v in
    ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 18670 "Parser.ml"
    ) = 
# 239 "Parser.mly"
    ( CabsEstring lit )
# 18674 "Parser.ml"
     in
    _menhir_goto_primary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv418)

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _ = _menhir_discard _menhir_env in
    _menhir_reduce270 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv415 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv413 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState15 in
        ((let _menhir_stack = (_menhir_stack, _menhir_s) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv411 * _menhir_state) * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState345 _v
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState345 _v
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState345 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState345 _v
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState345
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState345) : 'freshtv412)) : 'freshtv414)
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState15
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState15 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState15) : 'freshtv416)

and _menhir_run16 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv409 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState16
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16) : 'freshtv410)

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv407) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 18861 "Parser.ml"
    ) = 
# 314 "Parser.mly"
    ( CabsPlus )
# 18865 "Parser.ml"
     in
    _menhir_goto_unary_operator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv408)

and _menhir_run18 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv405 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.LPAREN ->
        _menhir_run20 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState18
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState18 _v
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState18) : 'freshtv406)

and _menhir_run19 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv403) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 18921 "Parser.ml"
    ) = 
# 316 "Parser.mly"
    ( CabsMinus )
# 18925 "Parser.ml"
     in
    _menhir_goto_unary_operator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv404)

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv401 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNOF ->
        _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.AMPERSAND ->
        _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.BANG ->
        _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.CONSTANT _v ->
        _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.GENERIC ->
        _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.LPAREN ->
        _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.MINUS ->
        _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.MINUS_MINUS ->
        _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.PLUS ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.PLUS_PLUS ->
        _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.SIZEOF ->
        _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.STAR ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.STRING_LITERAL _v ->
        _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.TILDE ->
        _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.VAR_NAME2 _v ->
        _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState24 _v
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState24
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState24) : 'freshtv402)

and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv399 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv395 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv393 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState28
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState28 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28) : 'freshtv394)) : 'freshtv396)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv397 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv398)) : 'freshtv400)

and _menhir_run29 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 36 "Parser.mly"
      (Cabs.cabs_constant)
# 19073 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv391) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (cst : (
# 36 "Parser.mly"
      (Cabs.cabs_constant)
# 19083 "Parser.ml"
    )) = _v in
    ((let _v : (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19088 "Parser.ml"
    ) = 
# 237 "Parser.mly"
    ( CabsEconst cst )
# 19092 "Parser.ml"
     in
    _menhir_goto_primary_expression _menhir_env _menhir_stack _menhir_s _v) : 'freshtv392)

and _menhir_run30 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv389) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 19105 "Parser.ml"
    ) = 
# 320 "Parser.mly"
    ( CabsNot )
# 19109 "Parser.ml"
     in
    _menhir_goto_unary_operator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv390)

and _menhir_run31 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv387) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 19122 "Parser.ml"
    ) = 
# 310 "Parser.mly"
    ( CabsAddress )
# 19126 "Parser.ml"
     in
    _menhir_goto_unary_operator _menhir_env _menhir_stack _menhir_s _v) : 'freshtv388)

and _menhir_run32 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv385 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv381 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv379 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState33
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33) : 'freshtv380)) : 'freshtv382)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv383 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv384)) : 'freshtv386)

and _menhir_discard : _menhir_env -> Tokens.token =
  fun _menhir_env ->
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = _menhir_env._menhir_lexer lexbuf in
    _menhir_env._menhir_token <- _tok;
    _menhir_env._menhir_startp <- lexbuf.Lexing.lex_start_p;
    _menhir_env._menhir_endp <- lexbuf.Lexing.lex_curr_p;
    let shifted = Pervasives.(+) _menhir_env._menhir_shifted 1 in
    if Pervasives.(>=) shifted 0 then
      _menhir_env._menhir_shifted <- shifted;
    _tok

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState501 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv85 * _menhir_state * (
# 193 "Parser.mly"
     (Cabs.cabs_statement list)
# 19218 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState496 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv87 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19227 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 19231 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState485 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv89 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19240 "Parser.ml"
        )) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 19244 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState482 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv91 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 19253 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState480 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv93 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 19262 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState478 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv95 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 19271 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState468 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19280 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState466 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv99 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState465 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv101 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState460 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv103 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 19299 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState456 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv105 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 19308 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState454 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv107 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 19317 "Parser.ml"
        )) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState452 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * _menhir_state) * _menhir_state * (
# 78 "Parser.mly"
     (Cabs.declaration)
# 19326 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState451 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 19335 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState446 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv113 * _menhir_state) * _menhir_state * (
# 186 "Parser.mly"
     (Cabs.cabs_statement)
# 19344 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState431 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv115 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19353 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState429 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv117 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState426 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv119 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState424 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv121 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState423 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv123 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv124)
    | MenhirState421 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv125 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)
    | MenhirState419 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv127 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv128)
    | MenhirState417 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv129 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv130)
    | MenhirState415 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv131 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv132)
    | MenhirState414 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv133 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)
    | MenhirState412 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv135 * _menhir_state) * _menhir_state * 'tv_option_expression_) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)
    | MenhirState410 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv137 * _menhir_state) * _menhir_state * 'tv_option_expression_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)
    | MenhirState408 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)
    | MenhirState403 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv141 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19422 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)
    | MenhirState401 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv143 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)
    | MenhirState399 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv145 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 19436 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv146)
    | MenhirState397 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv147 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19445 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv148)
    | MenhirState395 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv149 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)
    | MenhirState393 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv151 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19459 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)
    | MenhirState391 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv153 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)
    | MenhirState389 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv155 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19473 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)
    | MenhirState387 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv157 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)
    | MenhirState385 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv159 * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 19487 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)
    | MenhirState380 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv161 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)
    | MenhirState379 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv163 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19501 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)
    | MenhirState377 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv165 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)
    | MenhirState375 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv167 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19515 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv168)
    | MenhirState373 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv169 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv170)
    | MenhirState371 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv171 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv172)
    | MenhirState370 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv173 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 19534 "Parser.ml"
        )) * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 19538 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv174)
    | MenhirState367 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv175 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 19547 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv176)
    | MenhirState366 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv177 * _menhir_state * (
# 138 "Parser.mly"
     (Cabs.declarator)
# 19556 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)
    | MenhirState364 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv179 * _menhir_state * (
# 84 "Parser.mly"
     (Cabs.init_declarator list)
# 19565 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv180)
    | MenhirState360 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv181 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 19574 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)
    | MenhirState355 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv183 * _menhir_state * (
# 199 "Parser.mly"
     (Cabs.external_declaration list)
# 19583 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)
    | MenhirState347 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv185 * _menhir_state) * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 19592 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)
    | MenhirState345 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv187 * _menhir_state) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv188)
    | MenhirState342 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv189 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 19606 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv190)
    | MenhirState336 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv191 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 19615 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 19619 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv192)
    | MenhirState328 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv193 * _menhir_state * (
# 177 "Parser.mly"
     (Cabs.designator list)
# 19628 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv194)
    | MenhirState325 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv195 * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 19637 "Parser.ml"
        )) * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv196)
    | MenhirState323 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv197 * _menhir_state) * _menhir_state * (
# 171 "Parser.mly"
     (((Cabs.designator list) option * Cabs.initializer_) list)
# 19646 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv198)
    | MenhirState320 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv199 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv200)
    | MenhirState319 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv201 * _menhir_state * 'tv_option_designation_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)
    | MenhirState314 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv203 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv204)
    | MenhirState313 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv205 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 19670 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)
    | MenhirState312 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv207 * _menhir_state) * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 19679 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv208)
    | MenhirState309 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv209 * _menhir_state * (
# 65 "Parser.mly"
     (Cabs.cabs_generic_association list)
# 19688 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv210)
    | MenhirState304 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv211 * _menhir_state * (
# 159 "Parser.mly"
     (Cabs.type_name)
# 19697 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv212)
    | MenhirState301 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv213 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv214)
    | MenhirState299 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv215 * _menhir_state) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 19711 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv216)
    | MenhirState284 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv217 * _menhir_state * 'tv_option_declarator_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv218)
    | MenhirState277 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv219 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19725 "Parser.ml"
        )) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv220)
    | MenhirState274 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv221 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19734 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19738 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv222)
    | MenhirState273 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv223 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19747 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19751 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv224)
    | MenhirState270 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv225 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19760 "Parser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv226)
    | MenhirState269 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv227 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19769 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv228)
    | MenhirState268 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv229 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19778 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv230)
    | MenhirState252 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv231 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 19786 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19790 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv232)
    | MenhirState251 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv233 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 19799 "Parser.ml"
        )) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19803 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv234)
    | MenhirState243 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv235 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 19812 "Parser.ml"
        )) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19816 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv236)
    | MenhirState242 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv237 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 19825 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv238)
    | MenhirState241 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv239 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 19834 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv240)
    | MenhirState238 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv241 * (
# 165 "Parser.mly"
     (Cabs.direct_abstract_declarator)
# 19842 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv242)
    | MenhirState229 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv243) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19850 "Parser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv244)
    | MenhirState228 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv245) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19859 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv246)
    | MenhirState220 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv247) * _menhir_state) * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19868 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv248)
    | MenhirState219 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv249) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv250)
    | MenhirState218 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv251) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv252)
    | MenhirState212 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv253) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv254)
    | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv255 * _menhir_state * (
# 81 "Parser.mly"
     (Cabs.specifiers)
# 19890 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv256)
    | MenhirState207 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv257 * _menhir_state * (
# 153 "Parser.mly"
     (Cabs.parameter_declaration list)
# 19899 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv258)
    | MenhirState201 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv259 * _menhir_state * (
# 135 "Parser.mly"
     (Cabs.alignment_specifier)
# 19908 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv260)
    | MenhirState196 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv261 * _menhir_state * (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 19917 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv262)
    | MenhirState194 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv263 * _menhir_state * (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 19926 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv264)
    | MenhirState193 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv265 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 19935 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv266)
    | MenhirState192 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv267 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 19944 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv268)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv269) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv270)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv271 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 19957 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv272)
    | MenhirState185 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv273 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv274)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv275 * (
# 141 "Parser.mly"
     (Cabs.direct_declarator)
# 19971 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv276)
    | MenhirState172 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv277) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv278)
    | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv279 * _menhir_state * (
# 111 "Parser.mly"
     (Cabs.struct_declarator list)
# 19983 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv280)
    | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv281 * _menhir_state) * _menhir_state * 'tv_option_type_qualifier_list_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv282)
    | MenhirState161 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv283 * _menhir_state * (
# 147 "Parser.mly"
     (Cabs.cabs_type_qualifier list)
# 19997 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv284)
    | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv285 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv286)
    | MenhirState159 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv287 * _menhir_state * (
# 108 "Parser.mly"
     (Cabs.cabs_type_specifier list * Cabs.cabs_type_qualifier list)
# 20011 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv288)
    | MenhirState155 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv289 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 20020 "Parser.ml"
        )) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 102 "Parser.mly"
     (Cabs.struct_declaration list)
# 20024 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv290)
    | MenhirState154 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv291 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 20033 "Parser.ml"
        )) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv292)
    | MenhirState151 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv293 * _menhir_state * (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 20042 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv294)
    | MenhirState149 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv295 * _menhir_state * (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 20051 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv296)
    | MenhirState148 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv297 * _menhir_state * (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20060 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv298)
    | MenhirState146 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv299 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv300)
    | MenhirState132 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv301 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20074 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv302)
    | MenhirState130 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv303 * _menhir_state * (
# 70 "Parser.mly"
     (Cabs.cabs_expression list)
# 20083 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv304)
    | MenhirState123 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv305 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20092 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv306)
    | MenhirState120 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv307 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20101 "Parser.ml"
        )) * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20105 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv308)
    | MenhirState117 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv309 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20114 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv310)
    | MenhirState111 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv311 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20123 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv312)
    | MenhirState108 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv313 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20132 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv314)
    | MenhirState106 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv315 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20141 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv316)
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv317 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20150 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv318)
    | MenhirState102 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv319 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20159 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv320)
    | MenhirState100 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv321 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20168 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv322)
    | MenhirState98 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv323 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20177 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv324)
    | MenhirState95 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv325 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20186 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv326)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv327 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20195 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv328)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv329 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20204 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv330)
    | MenhirState88 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv331 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20213 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv332)
    | MenhirState85 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv333 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20222 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv334)
    | MenhirState83 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv335 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20231 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv336)
    | MenhirState81 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv337 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20240 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv338)
    | MenhirState77 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv339 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20249 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)
    | MenhirState75 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv341 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20258 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv342)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv343 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20267 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)
    | MenhirState70 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv345 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20276 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv346)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv347 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20285 "Parser.ml"
        )) * (
# 75 "Parser.mly"
     (Cabs.cabs_assignment_operator)
# 20289 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv348)
    | MenhirState55 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv349 * _menhir_state * (
# 57 "Parser.mly"
     (Cabs.cabs_expression)
# 20298 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv350)
    | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv351 * _menhir_state * (
# 73 "Parser.mly"
     (Cabs.cabs_unary_operator)
# 20307 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv352)
    | MenhirState46 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv353 * _menhir_state * (
# 54 "Parser.mly"
     (Cabs.cabs_identifier)
# 20316 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv354)
    | MenhirState42 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv355 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) * _menhir_state * (
# 120 "Parser.mly"
     (Cabs.enumerator list)
# 20325 "Parser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv356)
    | MenhirState38 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv357 * _menhir_state) * _menhir_state * 'tv_option_OTHER_NAME_) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv358)
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv359 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv360)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv361 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv362)
    | MenhirState28 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv363 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv364)
    | MenhirState24 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv365 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv366)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv367 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv368)
    | MenhirState18 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv369 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv370)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv371 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv372)
    | MenhirState15 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv373 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv374)
    | MenhirState10 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv375 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv376)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv377) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv378)

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv83) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 20393 "Parser.ml"
    ) = 
# 658 "Parser.mly"
    ( Q_volatile )
# 20397 "Parser.ml"
     in
    _menhir_goto_type_qualifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv84)

and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv81) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20410 "Parser.ml"
    ) = 
# 542 "Parser.mly"
    ( TSpec_void )
# 20414 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv82)

and _menhir_run3 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv79) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20427 "Parser.ml"
    ) = 
# 558 "Parser.mly"
    ( TSpec_unsigned )
# 20431 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv80)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv77) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 20444 "Parser.ml"
    ) = 
# 584 "Parser.mly"
    ( fun x y -> TSpec_union (x, y) )
# 20448 "Parser.ml"
     in
    _menhir_goto_struct_or_union _menhir_env _menhir_stack _menhir_s _v) : 'freshtv78)

and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 20455 "Parser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv75) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (id : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 20465 "Parser.ml"
    )) = _v in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20470 "Parser.ml"
    ) = 
# 570 "Parser.mly"
    ( TSpec_name id )
# 20474 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv76)

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv73) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 20487 "Parser.ml"
    ) = 
# 526 "Parser.mly"
    ( SC_typedef )
# 20491 "Parser.ml"
     in
    _menhir_goto_storage_class_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv74)

and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv71) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 20504 "Parser.ml"
    ) = 
# 532 "Parser.mly"
    ( SC_Thread_local )
# 20508 "Parser.ml"
     in
    _menhir_goto_storage_class_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv72)

and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv69) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 99 "Parser.mly"
     (Cabs.cabs_identifier option -> (Cabs.struct_declaration list) option -> Cabs.cabs_type_specifier)
# 20521 "Parser.ml"
    ) = 
# 582 "Parser.mly"
    ( fun x y -> TSpec_struct (x, y) )
# 20525 "Parser.ml"
     in
    _menhir_goto_struct_or_union _menhir_env _menhir_stack _menhir_s _v) : 'freshtv70)

and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv67 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv63 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv61 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState10
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState10 _v
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState10) : 'freshtv62)) : 'freshtv64)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv65 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)) : 'freshtv68)

and _menhir_run177 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv59) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 20596 "Parser.ml"
    ) = 
# 530 "Parser.mly"
    ( SC_static )
# 20600 "Parser.ml"
     in
    _menhir_goto_storage_class_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv60)

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv57) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20613 "Parser.ml"
    ) = 
# 556 "Parser.mly"
    ( TSpec_signed )
# 20617 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv58)

and _menhir_run22 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv55) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20630 "Parser.ml"
    ) = 
# 546 "Parser.mly"
    ( TSpec_short )
# 20634 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv56)

and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv53) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 20647 "Parser.ml"
    ) = 
# 656 "Parser.mly"
    ( Q_restrict )
# 20651 "Parser.ml"
     in
    _menhir_goto_type_qualifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv54)

and _menhir_run179 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv51) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 20664 "Parser.ml"
    ) = 
# 536 "Parser.mly"
    ( SC_register )
# 20668 "Parser.ml"
     in
    _menhir_goto_storage_class_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv52)

and _menhir_run180 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv49) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 20681 "Parser.ml"
    ) = 
# 668 "Parser.mly"
    ( FS_Noreturn )
# 20685 "Parser.ml"
     in
    _menhir_goto_function_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv50)

and _menhir_run25 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv47) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20698 "Parser.ml"
    ) = 
# 550 "Parser.mly"
    ( TSpec_long )
# 20702 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv48)

and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv45) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20715 "Parser.ml"
    ) = 
# 548 "Parser.mly"
    ( TSpec_int )
# 20719 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv46)

and _menhir_run181 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv43) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 132 "Parser.mly"
     (Cabs.function_specifier)
# 20732 "Parser.ml"
    ) = 
# 666 "Parser.mly"
    ( FS_inline )
# 20736 "Parser.ml"
     in
    _menhir_goto_function_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv44)

and _menhir_run34 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv41) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20749 "Parser.ml"
    ) = 
# 552 "Parser.mly"
    ( TSpec_float )
# 20753 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv42)

and _menhir_run182 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv39) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 20766 "Parser.ml"
    ) = 
# 528 "Parser.mly"
    ( SC_extern )
# 20770 "Parser.ml"
     in
    _menhir_goto_storage_class_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv40)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv37 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.OTHER_NAME _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv35 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState35 in
        let (_v : (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 20789 "Parser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv33 * _menhir_state) * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 20797 "Parser.ml"
        )) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.LBRACE ->
            _menhir_reduce140 _menhir_env (Obj.magic _menhir_stack)
        | Tokens.ALIGNAS | Tokens.ATOMIC | Tokens.ATOMIC_LPAREN | Tokens.AUTO | Tokens.BOOL | Tokens.CHAR | Tokens.COLON | Tokens.COMMA | Tokens.COMPLEX | Tokens.CONST | Tokens.DOUBLE | Tokens.ENUM | Tokens.EXTERN | Tokens.FLOAT | Tokens.INLINE | Tokens.INT | Tokens.LBRACKET | Tokens.LONG | Tokens.LPAREN | Tokens.NORETURN | Tokens.REGISTER | Tokens.RESTRICT | Tokens.RPAREN | Tokens.SEMICOLON | Tokens.SHORT | Tokens.SIGNED | Tokens.STAR | Tokens.STATIC | Tokens.STRUCT | Tokens.THREAD_LOCAL | Tokens.TYPEDEF | Tokens.TYPEDEF_NAME2 _ | Tokens.UNION | Tokens.UNSIGNED | Tokens.VAR_NAME2 _ | Tokens.VOID | Tokens.VOLATILE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv29 * _menhir_state) * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 20808 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, id) = _menhir_stack in
            let _v : (
# 117 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20814 "Parser.ml"
            ) = 
# 630 "Parser.mly"
    ( TSpec_enum (Some id, None)  )
# 20818 "Parser.ml"
             in
            _menhir_goto_enum_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv30)
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv31 * _menhir_state) * _menhir_state * (
# 33 "Parser.mly"
      (Cabs.cabs_identifier)
# 20828 "Parser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv32)) : 'freshtv34)) : 'freshtv36)
    | Tokens.LBRACE ->
        _menhir_reduce139 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35) : 'freshtv38)

and _menhir_run141 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv27) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20848 "Parser.ml"
    ) = 
# 554 "Parser.mly"
    ( TSpec_double )
# 20852 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv28)

and _menhir_run142 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv25) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 20865 "Parser.ml"
    ) = 
# 654 "Parser.mly"
    ( Q_const )
# 20869 "Parser.ml"
     in
    _menhir_goto_type_qualifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv26)

and _menhir_run143 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv23) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20882 "Parser.ml"
    ) = 
# 562 "Parser.mly"
    ( TSpec_Complex )
# 20886 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv24)

and _menhir_run144 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv21) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20899 "Parser.ml"
    ) = 
# 544 "Parser.mly"
    ( TSpec_char )
# 20903 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv22)

and _menhir_run145 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv19) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 93 "Parser.mly"
     (Cabs.cabs_type_specifier)
# 20916 "Parser.ml"
    ) = 
# 560 "Parser.mly"
    ( TSpec_Bool )
# 20920 "Parser.ml"
     in
    _menhir_goto_type_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv20)

and _menhir_run183 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 90 "Parser.mly"
     (Cabs.storage_class_specifier)
# 20933 "Parser.ml"
    ) = 
# 534 "Parser.mly"
    ( SC_auto )
# 20937 "Parser.ml"
     in
    _menhir_goto_storage_class_specifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv18)

and _menhir_run146 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv15 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState146 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState146
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState146) : 'freshtv16)

and _menhir_run147 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _ = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv13) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let _v : (
# 129 "Parser.mly"
     (Cabs.cabs_type_qualifier)
# 21003 "Parser.ml"
    ) = 
# 660 "Parser.mly"
    ( Q_Atomic )
# 21007 "Parser.ml"
     in
    _menhir_goto_type_qualifier _menhir_env _menhir_stack _menhir_s _v) : 'freshtv14)

and _menhir_run184 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _tok = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv11 * _menhir_state) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv7 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _tok = _menhir_discard _menhir_env in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv5 * _menhir_state) = _menhir_stack in
        let (_tok : Tokens.token) = _tok in
        ((match _tok with
        | Tokens.ALIGNOF ->
            _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.AMPERSAND ->
            _menhir_run31 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.ATOMIC ->
            _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.ATOMIC_LPAREN ->
            _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.BANG ->
            _menhir_run30 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.BOOL ->
            _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.CHAR ->
            _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.COMPLEX ->
            _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.CONST ->
            _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.CONSTANT _v ->
            _menhir_run29 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
        | Tokens.DOUBLE ->
            _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.ENUM ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.FLOAT ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.GENERIC ->
            _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.INT ->
            _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.LONG ->
            _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.LPAREN ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.MINUS ->
            _menhir_run19 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.MINUS_MINUS ->
            _menhir_run18 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.PLUS ->
            _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.PLUS_PLUS ->
            _menhir_run16 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.RESTRICT ->
            _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.SHORT ->
            _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.SIGNED ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.SIZEOF ->
            _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.STAR ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.STRING_LITERAL _v ->
            _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
        | Tokens.STRUCT ->
            _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.TILDE ->
            _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.TYPEDEF_NAME2 _v ->
            _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
        | Tokens.UNION ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.UNSIGNED ->
            _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.VAR_NAME2 _v ->
            _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState185 _v
        | Tokens.VOID ->
            _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | Tokens.VOLATILE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState185
        | _ ->
            assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
            _menhir_env._menhir_shifted <- (-1);
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState185) : 'freshtv6)) : 'freshtv8)
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv9 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)) : 'freshtv12)

and translation_unit_file : (Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> (
# 212 "Parser.mly"
      (Cabs.translation_unit)
# 21112 "Parser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> Tokens.token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = lexer lexbuf in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_startp = lexbuf.Lexing.lex_start_p;
        _menhir_endp = lexbuf.Lexing.lex_curr_p;
        _menhir_shifted = max_int;
        }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv3) = () in
    ((assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
    let _tok = _menhir_env._menhir_token in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv1) = _menhir_stack in
    let (_tok : Tokens.token) = _tok in
    ((match _tok with
    | Tokens.ALIGNAS ->
        _menhir_run184 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.ATOMIC ->
        _menhir_run147 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.ATOMIC_LPAREN ->
        _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.AUTO ->
        _menhir_run183 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.BOOL ->
        _menhir_run145 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.CHAR ->
        _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.COMPLEX ->
        _menhir_run143 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.CONST ->
        _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.DOUBLE ->
        _menhir_run141 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.ENUM ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.EXTERN ->
        _menhir_run182 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.FLOAT ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.INLINE ->
        _menhir_run181 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.INT ->
        _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.LONG ->
        _menhir_run25 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.NORETURN ->
        _menhir_run180 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.REGISTER ->
        _menhir_run179 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.RESTRICT ->
        _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.SHORT ->
        _menhir_run22 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.SIGNED ->
        _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.STATIC ->
        _menhir_run177 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.STATIC_ASSERT ->
        _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.STRUCT ->
        _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.THREAD_LOCAL ->
        _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.TYPEDEF ->
        _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.TYPEDEF_NAME2 _v ->
        _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | Tokens.UNION ->
        _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.UNSIGNED ->
        _menhir_run3 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.VOID ->
        _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | Tokens.VOLATILE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
        _menhir_env._menhir_shifted <- (-1);
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv2)) : 'freshtv4))



