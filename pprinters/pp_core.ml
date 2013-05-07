open Global
open Core

open Colour

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let precedence = function
  | Etuple _          -> Some 0
  | Enull             -> Some 0
  | Econst _          -> Some 0
  | Eaddr _           -> Some 0
  | Esym _            -> Some 0
  | Etrue             -> Some 0
  | Efalse            -> Some 0
  | Ectype _          -> Some 0
  | Eundef            -> Some 0
  | Eerror            -> Some 0
  | Eskip             -> Some 0
  | Erun _            -> Some 0
  | Enot _            -> Some 1
  | Esave _           -> Some 1
  | Eret _            -> Some 1
  | Eindet _          -> Some 1
  | Eaction _         -> Some 2
  | Esame _           -> Some 2
  | Eproc _           -> Some 2
  | Ecall _           -> Some 2
  | Eop (OpMul, _, _) -> Some 3
  | Eop (OpDiv, _, _) -> Some 3
  | Eop (OpMod, _, _) -> Some 3
  | Eop (OpAdd, _, _) -> Some 4
  | Eop (OpSub, _, _) -> Some 4
  | Eop (OpLt,  _, _) -> Some 5
  | Eop (OpEq,  _, _) -> Some 6
  | Eop (OpAnd, _, _) -> Some 7
  | Eop (OpOr,  _, _) -> Some 8
  | Eif _             -> Some 9
  | Elet _            -> Some 10
  | Easeq _           -> Some 11
  | Ewseq _           -> Some 12
  | Esseq _           -> Some 13
  | Eunseq _          -> Some 14
  | Etuple _          -> None (* shouldn't be needed *)
  | Ebound _          -> None (* shouldn't be needed *)
  | COMMENT _         -> None
  | DEBUG _           -> None
(* TODO: hack *)
  | End _             -> None


let lt_precedence p1 p2 =
  match (p1, p2) with
    | (Some n1, Some n2) -> n1 <= n2
    | (Some _ , None   ) -> true
    | (None   , _      ) -> false


let pp_keyword  w = !^ (ansi_format [Bold; Magenta] w)
let pp_constant c = !^ (ansi_format [Magenta] c)
let pp_control  w = !^ (ansi_format [Bold; Blue] w)
let pp_symbol   a = !^ (ansi_format [Blue] $ Symbol.to_string_pretty a)
let pp_number   n = !^ (ansi_format [Yellow] n)


let rec pp_core_base_type = function
  | Integer       -> !^ "integer"
  | Boolean       -> !^ "boolean"
  | Address       -> !^ "address"
  | Ctype         -> !^ "ctype"
  | Unit          -> !^ "unit"
  | Wildcard      -> !^ "wildcard"
  | Tuple baseTys -> P.parens (P.separate_map P.comma pp_core_base_type baseTys)


let pp_core_type = function
  | TyBase   baseTy -> pp_core_base_type baseTy
  | TyEffect baseTy -> P.brackets (pp_core_base_type baseTy)


let pp_binop = function
  | OpAdd -> P.plus
  | OpSub -> P.minus
  | OpMul -> P.star
  | OpDiv -> P.slash
  | OpMod -> P.percent
  | OpEq  -> P.equals
  | OpLt  -> P.langle
  | OpAnd -> !^ "/\\"
  | OpOr  -> !^ "\\/"


(* Qualification prefix for memory addresses *)
let rec pp_prefix = function
  | []    -> P.empty
  | x::xs -> pp_symbol x ^^ P.dot ^^ pp_prefix xs


let pp_polarity = function
  | Pos -> P.empty
  | Neg -> P.tilde


let rec pp_expr e =
  let rec pp p e =
    let p' = precedence e in
    let pp = P.group -| pp p' in
    let wseq = !^ ">>" in
    let pp_wseq (_a, e) =
      match _a with
        | []       -> pp e
        | [Some a] -> pp_symbol a ^^^ !^ "<-" ^^ ((* P.align $ *) pp e)
        | [None]   -> pp e
        | _as      -> let g = function
                        | Some x -> pp_symbol x
                        | None   -> P.underscore
                      in (P.parens $ P.separate_map P.comma g _as) ^^^ !^ "<-" ^^ ((* P.align $ *) pp e)
    in
(*    (if lt_precedence p' p then fun x -> x else P.parens) $ *)
      P.parens $
      match e with
        | COMMENT (str, e) ->
            !^ (ansi_format [Bold; Red] $ "--" ^ str) ^^ P.break 1 ^^ pp e
        | DEBUG str ->
            !^ (ansi_format [Bold; Inverted; Red] $ "[DEBUG]{" ^ str ^ "}")
        | Etuple es ->
            P.parens (comma_list pp es)
        | Enull ->
            pp_constant "null"
        | Eskip ->
            pp_keyword "skip"
        | Econst n ->
            pp_number (string_of_int n)
        | Eaddr (pref, name) ->
            P.at ^^ P.braces (pp_prefix pref ^^ !^ (string_of_int name))
        | Esym a ->
            pp_symbol a
        | Eop (op, e1, e2) ->
            pp e1 ^^^ pp_binop op ^^^ pp e2
        | Etrue ->
            pp_constant "true"
        | Efalse ->
            pp_constant "false"
        | Enot e ->
            pp_keyword "not" ^^^ pp e
        | Ectype ty ->
            Pp_ail.pp_ctype ty
        | Elet (a, e1, e2) ->
            pp_control "let" ^^^ pp_symbol a ^^^ P.equals ^^^
            ((* P.align $ *) pp e1) ^^^ pp_control "in" ^^ P.break 1 ^^ pp e2
        | Eif (b, e1, e2) ->
            pp_control "if" ^^^ pp b ^^^ pp_control "then" ^^
            P.nest 2 (P.break 1 ^^ pp e1) ^^ P.break 1 ^^
            pp_control "else" ^^ P.nest 2 (P.break 1 ^^ pp e2) ^^ P.break 1
        | Eproc (_, fname, es) ->
            pp_symbol fname ^^ P.braces (comma_list pp es)
        | Ecall (fname, es) ->
            pp_symbol fname ^^ P.parens (comma_list pp es)
        | Esame (e1, e2) ->
            pp_keyword "same" ^^ P.parens (pp e1 ^^ P.comma ^^^ pp e2)
        | Eundef ->
            pp_keyword "undef"
        | Eerror ->
            pp_keyword "error"
        | Eaction (p, (bs, a)) ->
          (* (if Set.is_empty bs then P.empty else P.langle ^^ (P.sepmap P.space pp_trace_action (Set.to_list bs)) ^^
             P.rangle ^^ P.space) ^^ *)
          pp_polarity p ^^ pp_action a
        | Eunseq [] ->
            !^ "BUG: UNSEQ must have at least two arguments (seen 0)"
        | Eunseq [e] ->
            !^ "BUG: UNSEQ must have at least two arguments (seen 1)" ^^ (pp_control "[-[-[") ^^ pp e ^^ (pp_control "]-]-]")
        | Eunseq es ->
            P.brackets $ P.separate_map (P.space ^^ (pp_control "||") ^^ P.space) pp es
(*      | Ewseq es ret -> (P.sepmap (wseq ^^ P.break1) pp_wseq es) ^^^ wseq ^^ P.break1 ^^ f ret *)
        | Ewseq ([], e1, e2) ->
            pp e1 ^^^ wseq ^^ P.break 1 ^^ pp e2
        | Ewseq ([Some a], e1, e2) ->
            pp_symbol a ^^^ !^ "<-" ^^^ ((* P.align $ *) pp e1) ^^^ wseq ^^ P.break 1 ^^ pp e2
        | Ewseq ([None], e1, e2) ->
            pp e1 ^^^ (!^ ">>") ^^ P.break 1 ^^ pp e2
        | Ewseq (_as, e1, e2) ->
            let g = function
              | Some x -> pp_symbol x
              | None   -> P.underscore
            in (P.parens (comma_list g _as)) ^^^ !^ "<-" ^^^ ((* P.align $ *) pp e1) ^^^ wseq ^^ P.break 1 ^^ pp e2
        | Esseq ([], e1, e2) ->
            pp e1 ^^^ P.semi ^^ P.break 1 ^^ pp e2
        | Esseq ([Some a], e1, e2) ->
            pp_symbol a ^^^ !^ "<-" ^^^ ((* P.align $ *) pp e1) ^^^ P.semi ^^ P.break 1 ^^ pp e2
        | Esseq ([None], e1, e2) ->
            pp e1 ^^^ P.semi ^^ P.break 1 ^^ pp e2
        | Esseq (_as, e1, e2) ->
            let g = function
              | Some x -> pp_symbol x
              | None   -> P.underscore
            in (P.parens (comma_list g _as)) ^^^ !^ "<-" ^^^ ((* P.align $ *) pp e1) ^^^ P.semi ^^ P.break 1 ^^ pp e2
        | Easeq (None, act, y) ->
            pp (Eaction (Pos, act)) ^^^ !^ "|>" ^^^ pp (Eaction y)
        | Easeq (Some a, act, y) ->
            pp_symbol a ^^^ !^ "<-" ^^^ pp (Eaction (Pos, act)) ^^^ !^ "|>" ^^^ pp (Eaction y)
        | Eindet e ->
            P.brackets (pp e)
        | Esave (l, _, _, e) ->
            pp_keyword "save" ^^^ pp_symbol l ^^ P.dot ^^^ pp e
        | Erun (l, _, _) ->
            pp_keyword "run" ^^^ pp_symbol l
        | Eret e ->
            pp_keyword "ret" ^^^ pp e
        | End es ->
            P.brackets $ P.separate_map (P.space ^^ (pp_control ";") ^^ P.space) pp es
  in pp None e

and pp_action = function
  | Create (ty, _)     -> pp_keyword "create" ^^ P.parens (pp_expr ty)
  | Alloc (a, _)       -> pp_keyword "alloc"  ^^ P.parens (pp_expr a)
  | Kill e             -> pp_keyword "kill"   ^^ P.parens (pp_expr e)
  | Store (ty, e1, e2) -> pp_keyword "store"  ^^ P.parens (pp_expr ty ^^ P.comma ^^^ pp_expr e1 ^^ P.comma ^^^ pp_expr e2)
  | Load (ty, e)       -> pp_keyword "load"   ^^ P.parens (pp_expr ty ^^ P.comma  ^^^ pp_expr e)



let pp_file file =
  let pp_argument (aname, atype) = pp_symbol aname ^^ P.colon ^^^ pp_core_base_type atype in
  let f acc (fname, (ftype, args, body)) =
    acc ^^
      pp_keyword "fun" ^^^ pp_symbol fname ^^^ P.parens (comma_list pp_argument args) ^^ P.colon ^^^ pp_core_type ftype ^^^
      P.colon ^^ P.equals ^^
      P.nest 2 (P.break 1 ^^ pp_expr body) ^^ P.break 1 ^^ P.break 1 in
  List.fold_left f P.empty (Pmap.bindings file.fun_map) ^^ P.break 1
