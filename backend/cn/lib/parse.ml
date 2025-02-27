open Cerb_frontend.Annot
open Or_TypeError

open Effectful.Make (Or_TypeError)

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
    | [ s ] -> s
    | s1 :: s2 :: ss ->
      if Tools.starts_with "start" s2 then
        fix ((s1 ^ "%" ^ s2) :: ss)
      else
        fix ((s1 ^ "@" ^ s2) :: ss)
  in
  fix ss


let debug_tokens loc string =
  let toks, pos = C_parser_driver.diagnostic_get_tokens ~inside_cn:true loc string in
  let pp_int_pair (x, y) = Pp.(parens (int x ^^ comma ^^^ int y)) in
  Pp.item "failed to parse tokens" (Pp.braces (Pp.list Pp.string toks))
  ^/^ Pp.item "(line, col)" (Pp.braces (Pp.list pp_int_pair pos))


let parse parser_start (loc, string) =
  let string = fiddle_at_hack string in
  let module Exn = Cerb_frontend.Exception in
  match C_parser_driver.parse_loc_string parser_start (loc, string) with
  | Exn.Result spec -> return spec
  | Exn.Exception (loc, Cerb_frontend.Errors.CPARSER err) ->
    Pp.debug 6 (lazy (debug_tokens loc string));
    fail { loc; msg = Parser err }
  | Exn.Exception _ -> assert false


let cn_statements annots =
  annots |> get_cerb_magic_attr |> ListM.concat_mapM (parse C_parser.cn_statements)


let function_spec warning_loc (Attrs attributes) =
  let@ conditions =
    [ Aattrs (Attrs (List.rev attributes)) ]
    |> get_cerb_magic_attr
    |> ListM.mapM (parse C_parser.fundef_spec)
  in
  let process
    Cn.{ cn_fundef_trusted; cn_fundef_acc_func; cn_fundef_requires; cn_fundef_ensures }
    =
    let cross_fst x =
      match x with None -> [] | Some (a, bs) -> List.map (fun b -> (a, b)) bs
    in
    let trust =
      match cn_fundef_trusted with
      | None -> Mucore.Checked
      | Some loc -> Mucore.Trusted loc
    in
    let accs, exs =
      match cn_fundef_acc_func with
      | None -> ([], [])
      | Some (loc, Cn.CN_mk_function nm) -> ([], [ (loc, `Make_Logical_Function nm) ])
      | Some (loc, Cn.CN_accesses ids) -> (cross_fst (Some (loc, ids)), [])
    in
    let reqs = cross_fst cn_fundef_requires in
    let enss = cross_fst cn_fundef_ensures in
    (trust, accs, reqs, enss, exs)
  in
  let conditions = List.map process conditions in
  let base = (Mucore.Checked, [], [], [], []) in
  match conditions with
  | [] -> return base
  | [ condition ] -> return condition
  | _ :: _ :: _ ->
    (* TODO remove this "feature" *)
    Pp.warn
      warning_loc
      !^"Deprecated: function specs should not be split across multiple magic comments.";
    let comb left right =
      match (left, right) with
      | Mucore.Trusted loc, _ -> Mucore.Trusted loc
      | _, Mucore.Trusted loc -> Mucore.Trusted loc
      | _, _ -> Mucore.Checked
    in
    let combine left right =
      match (left, right) with
      | (trust, accs, reqs, enss, ex), (trust', accs', reqs', enss', ex') ->
        return (comb trust trust', accs @ accs', reqs @ reqs', enss @ enss', ex @ ex')
    in
    ListM.fold_leftM combine base conditions


let loop_spec attrs =
  [ Aattrs attrs ]
  |> get_cerb_magic_attr
  |> ListM.concat_mapM (fun (loc, arg) ->
    let@ (Cn.CN_inv (_loc, conds)) = parse C_parser.loop_spec (loc, arg) in
    return conds)
