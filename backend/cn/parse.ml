open Cerb_frontend.Annot
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Pp
module Cn = Cerb_frontend.Cn

(* NOTE: There are four types of CN parsing constructs, each with
   a different entry point from which a parser can be started:
     - cn_statement: for proof guidance, debugging
     - cn_function_spec: pre and post conditions
     - cn_loop_spec: loop invariants
     - cn_toplevel: for declarations

   1. C program is parsed into a C abstract sytnax tree (Cabs)
   2. Toplevel magic comments are turned into CN toplevel declarations.
   3. Magic statements, function specifications and loop specifications are
      inserted as string annotations (attributes).
   4. Cabs is desugared, then elaborated into Core (including the CN toplevel declarations).
   5. Core is turned into mucore, during which process the remaining magic
      comments are parsed and desugared into mucore as well. *)

(* the character @ is not a separator in C, so supporting @start as a
   legacy syntax requires special hacks *)
let fiddle_at_hack string =
  let ss = String.split_on_char '@' string in
  let rec fix = function
    | [] -> ""
    | [s] -> s
    | (s1 :: s2 :: ss) -> if Tools.starts_with "start" s2
        then fix ((s1 ^ "%" ^ s2) :: ss)
        else fix ((s1 ^ "@" ^ s2) :: ss)
  in
  fix ss

let debug_tokens loc string =
  let (toks, pos) = C_parser_driver.diagnostic_get_tokens ~inside_cn:true loc string in
  let pp_int_pair (x, y) = Pp.(parens (int x ^^ comma ^^^ int y)) in
  Pp.item "failed to parse tokens" (Pp.braces (Pp.list Pp.string toks))
    ^/^ Pp.item "(line, col)" (Pp.braces (Pp.list pp_int_pair pos))

let parse parser_start (loc, string) =
  let string = fiddle_at_hack string in
  let module Exn = Cerb_frontend.Exception in
  match C_parser_driver.parse_loc_string parser_start (loc, string) with
  | Exn.Result spec ->
    return spec
  | Exn.Exception (loc, Cerb_frontend.Errors.CPARSER err) ->
    Pp.debug 6 (lazy (debug_tokens loc string));
    fail {loc; msg = Parser err}
  | Exn.Exception _ ->
    assert false

let cn_statements annots =
  annots
  |> get_cerb_magic_attr
  |> ListM.concat_mapM (parse C_parser.cn_statements)

let function_spec (Attrs attributes) =
  let@ conditions =
    [Aattrs (Attrs (List.Old.rev attributes))]
    |> get_cerb_magic_attr
    |> ListM.concat_mapM (parse C_parser.function_spec) in
  ListM.fold_leftM (fun acc cond ->
    match cond, acc with
    | (Cn.CN_trusted loc), (_, [], [], [], []) ->
       return (Mucore.Trusted loc, [], [], [], [])
    | (Cn.CN_trusted loc), _ ->
       fail {loc; msg= Generic !^"Please specify 'trusted' before other conditions"}
    | (CN_accesses (loc, ids)), (trusted, accs, [], [], ex) ->
       return (trusted, accs @ List.map ~f:(fun id -> (loc, id)) ids, [], [], ex)
    | (CN_accesses (loc, _)), _ ->
       fail { loc; msg= Generic !^"Please specify 'accesses' before any 'requires' and 'ensures'" }
    | (CN_requires (loc, cond)), (trusted, accs, reqs, [], ex) ->
       return (trusted, accs, reqs @ List.map ~f:(fun c -> (loc, c)) cond, [], ex)
    | (CN_requires (loc, _)), _ ->
       fail {loc; msg = Generic !^"Please specify 'requires' before any 'ensures'"}
    | (CN_ensures (loc, cond)), (trusted, accs, reqs, enss, ex) ->
       return (trusted, accs, reqs, enss @ List.map ~f:(fun c -> (loc, c)) cond, ex)
    | (CN_mk_function (loc, nm)), (trusted, accs, reqs, enss, ex) ->
       return (trusted, accs, reqs, enss, ex @ [(loc, Mucore.Make_Logical_Function nm)])
    )
    (Mucore.Checked, [], [], [], []) conditions

let loop_spec attrs =
  [Aattrs attrs]
  |> get_cerb_magic_attr
  |> ListM.concat_mapM (fun (loc, arg) ->
      let@ (Cn.CN_inv (_loc, conds)) = parse C_parser.loop_spec (loc, arg) in
      return conds)


