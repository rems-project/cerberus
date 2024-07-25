module CF = Cerb_frontend
open CF.AilSyntax

module LocCompare = struct
  type t = Locations.t

  type pre_cmp = int * (int * int * int * string) list * string list [@@deriving eq, ord]

  let lex_to_cmp l =
    let open Lexing in
    (l.pos_lnum, l.pos_bol, l.pos_cnum, l.pos_fname)


  let to_pre_cmp = function
    | Cerb_location.Loc_unknown -> (0, [], [])
    | Cerb_location.Loc_other nm -> (1, [], [ nm ])
    | Cerb_location.Loc_point p -> (2, [ lex_to_cmp p ], [])
    | Cerb_location.Loc_region (x, y, _) -> (3, [ lex_to_cmp x; lex_to_cmp y ], [])
    | Cerb_location.Loc_regions (xs, _) ->
      (4, List.map lex_to_cmp (List.concat (List.map (fun (x, y) -> [ x; y ]) xs)), [])


  let mk_cmp (x : t) = to_pre_cmp x

  let compare x y = compare_pre_cmp (mk_cmp x) (mk_cmp y)

  let equal x y = equal_pre_cmp (mk_cmp x) (mk_cmp y)
end

module LocMap = Map.Make (LocCompare)

let stmt_loc = function AnnotatedStatement (loc, _, _) -> loc

let expr_loc = function AnnotatedExpression (_, _, loc, _) -> loc

(* build a map from expression locations to statement locations *)
let expr_locs (expr : 'a expression) =
  let gen_expr = function AilGAtype (_, x) -> x | AilGAdefault x -> x in
  let rec f ls exprs =
    match exprs with
    | [] -> ls
    | AnnotatedExpression (_, _, loc, ex) :: exprs ->
      let ls = loc :: ls in
      (match ex with
       | AilEunary (_, x) -> f ls (x :: exprs)
       | AilEbinary (x, _, y) -> f ls (x :: y :: exprs)
       | AilEassign (x, y) -> f ls (x :: y :: exprs)
       | AilEcompoundAssign (x, _, y) -> f ls (x :: y :: exprs)
       | AilEcond (x, Some y, z) -> f ls (x :: y :: z :: exprs)
       | AilEcond (x, None, z) -> f ls (x :: z :: exprs)
       | AilEcast (_, _, x) -> f ls (x :: exprs)
       | AilEcall (f_x, xs) -> f ls ((f_x :: xs) @ exprs)
       | AilEassert x -> f ls (x :: exprs)
       | AilEgeneric (x, xs) -> f ls ((x :: List.map gen_expr xs) @ exprs)
       | AilEarray (_, _, xs) -> f ls (List.filter_map (fun x -> x) xs @ exprs)
       | AilEstruct (_, xs) -> f ls (List.filter_map snd xs @ exprs)
       | AilEunion (_, _, opt_x) -> f ls (Option.to_list opt_x @ exprs)
       | AilEcompound (_, _, x) -> f ls (x :: exprs)
       | AilEmemberof (x, _) -> f ls (x :: exprs)
       | AilEmemberofptr (x, _) -> f ls (x :: exprs)
       | AilEsizeof_expr x -> f ls (x :: exprs)
       | AilEannot (_, x) -> f ls (x :: exprs)
       | AilEva_start (x, _) -> f ls (x :: exprs)
       | AilEva_arg (x, _) -> f ls (x :: exprs)
       | AilEva_copy (x, y) -> f ls (x :: y :: exprs)
       | AilEva_end x -> f ls (x :: exprs)
       | AilEprint_type x -> f ls (x :: exprs)
       | AilEbmc_assume x -> f ls (x :: exprs)
       | AilErvalue x -> f ls (x :: exprs)
       | AilEarray_decay x -> f ls (x :: exprs)
       | AilEfunction_decay x -> f ls (x :: exprs)
       | _ -> f ls exprs)
  in
  f [] [ expr ]


let add_map_stmt (stmt : 'a statement) m =
  let map stmt_loc m expr_loc =
    if LocMap.mem expr_loc m then
      m
    else
      LocMap.add expr_loc stmt_loc m
  in
  let do_x stmt_loc m expr = List.fold_left (map stmt_loc) m (expr_locs expr) in
  let do_xs stmt_loc m exprs = List.fold_left (do_x stmt_loc) m exprs in
  let rec f stmts m =
    match stmts with
    | [] -> m
    | AnnotatedStatement (l, _, x) :: ss ->
      let m = map l m l in
      (match x with
       | AilSblock (_, ss2) -> f (ss2 @ ss) m
       | AilSif (e, s1, s2) -> f (s1 :: s2 :: ss) (do_x (expr_loc e) m e)
       | AilSwhile (e, s, _) -> f (s :: ss) (do_x (expr_loc e) m e)
       | AilSdo (s, e, _) -> f (s :: ss) (do_x (expr_loc e) m e)
       | AilSswitch (e, s) -> f (s :: ss) (do_x (expr_loc e) m e)
       | AilScase (_, s) -> f (s :: ss) m
       | AilSdefault s -> f (s :: ss) m
       | AilSlabel (_, s, _) -> f (s :: ss) m
       | AilSpar ss2 -> f (ss2 @ ss) m
       | AilSexpr e -> f ss (do_x l m e)
       | AilSreturn e -> f ss (do_x l m e)
       | AilSdeclaration xs -> f ss (do_xs l m (List.filter_map snd xs))
       | AilSreg_store (_, x) -> f ss (do_x l m x)
       | _ -> f ss m)
  in
  f [ stmt ] m


let search (sigma : 'a sigma) =
  List.fold_right
    (fun (_, (_, _, _, _, stmt)) m -> add_map_stmt stmt m)
    sigma.function_definitions
    LocMap.empty
