(* open Cerb_frontend *)
open Cerb_frontend.Annot
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Pp
module Cn = Cerb_frontend.Cn


module Loc = Locations

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

let parse_function_spec (Attrs attributes) =
  let attributes = List.rev attributes in
  let@ conditions =
    ListM.concat_mapM (fun attr ->
        let k = (Option.value ~default:"<>" (Option.map Id.s attr.attr_ns), Id.s attr.attr_id) in
        (* FIXME (TS): I'm not sure if the check against cerb::magic was strange,
            or if it was checking the wrong thing the whole time *)
        let use = List.exists (fun (x, y) -> String.equal x (fst k) && String.equal y (snd k))
            [("cerb", "magic"); ("cn", "requires"); ("cn", "ensures");
                ("cn", "accesses"); ("cn", "trusted")] in
        if use then
          ListM.concat_mapM (fun (loc, arg, _) ->
              parse C_parser.function_spec (loc, arg)
            ) attr.attr_args
        else return []
      ) attributes
  in
  ListM.fold_leftM (fun acc cond ->
    match cond, acc with
    | (Cn.CN_trusted loc), (_, [], [], [], []) ->
       return (Mucore.Trusted loc, [], [], [], [])
    | (Cn.CN_trusted loc), _ ->
       fail {loc; msg= Generic !^"Please specify 'trusted' before other conditions"}
    | (CN_accesses (loc, ids)), (trusted, accs, [], [], ex) ->
       return (trusted, accs @ List.map (fun id -> (loc, id)) ids, [], [], ex)
    | (CN_accesses (loc, _)), _ ->
       fail { loc; msg= Generic !^"Please specify 'accesses' before any 'requires' and 'ensures'" }
    | (CN_requires (loc, cond)), (trusted, accs, reqs, [], ex) ->
       return (trusted, accs, reqs @ List.map (fun c -> (loc, c)) cond, [], ex)
    | (CN_requires (loc, _)), _ ->
       fail {loc; msg = Generic !^"Please specify 'requires' before any 'ensures'"}
    | (CN_ensures (loc, cond)), (trusted, accs, reqs, enss, ex) ->
       return (trusted, accs, reqs, enss @ List.map (fun c -> (loc, c)) cond, ex)
    | (CN_mk_function (loc, nm)), (trusted, accs, reqs, enss, ex) ->
       return (trusted, accs, reqs, enss, ex @ [(loc, Mucore.Make_Logical_Function nm)])
    )
    (Mucore.Checked, [], [], [], []) conditions

let parse_inv_spec (Attrs attributes) =
  ListM.concat_mapM (fun attr ->
      match Option.map Id.s (attr.attr_ns), Id.s (attr.attr_id) with
      | Some "cerb", "magic" ->
         ListM.concat_mapM (fun (loc, arg, _) ->
             let@ (Cn.CN_inv (_loc, conds)) = parse C_parser.loop_spec (loc, arg) in
             return conds
           ) attr.attr_args
      | _ ->
         return []
    ) attributes


