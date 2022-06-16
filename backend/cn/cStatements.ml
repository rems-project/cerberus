module CF=Cerb_frontend

open CF.AilSyntax


let stmt_loc = function
  | AnnotatedStatement (loc, _, _) -> loc

let expr_loc = function
  | AnnotatedExpression (_, _, loc, _) -> loc

let search_stmt (stmt : 'a statement) =
  let rec f ls stmts = match stmts with
    | [] -> ls
    | (AnnotatedStatement (l, _, x) :: ss) ->
    let l = stmt_loc (List.hd stmts) in
    begin match x with
    | AilSblock (_, ss2) -> f ls (ss2 @ ss)
    | AilSif (e, s1, s2) -> f (expr_loc e :: ls) (s1 :: s2 :: ss)
    | AilSwhile (e, s, _) -> f (expr_loc e :: ls) (s :: ss)
    | AilSdo (s, e, _) -> f (expr_loc e :: ls) (s :: ss)
    | AilSswitch (e, s) -> f (expr_loc e :: ls) (s :: ss)
    | AilScase (_, s) -> f ls (s :: ss)
    | AilSdefault s -> f ls (s :: ss)
    | AilSlabel (_, s, _) -> f ls (s :: ss)
    | AilSpar ss2 -> f ls (ss2 @ ss)
    | _ -> f (l :: ls) ss
    end
  in
  f [] [stmt]

let search (sigma : 'a sigma) =
  List.concat (List.map (fun (_, (_, _, _, stmt)) -> search_stmt stmt)
    sigma.function_definitions)


