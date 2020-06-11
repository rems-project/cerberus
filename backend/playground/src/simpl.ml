open Cerb_frontend
open Core_rewriter
open Core


module Identity = struct
  type 'a t = 'a
  let return = fun z -> z
  let bind m f = f m
  let (>>=) = bind
  let mapM = List.map
  let foldlM f xs init =
    List.fold_left (fun acc x ->
      f x acc
    ) init xs
  
  let unwrap (x: 'a t) : 'a = x
end

module RW = Rewriter(Identity)


let subst_pexpr pat cval pe =
  match Core_aux.match_pattern pat cval with
    | None ->
        pe
    | Some xs ->
        List.fold_left (fun acc (sym, cval) ->
          Core_aux.subst_sym_pexpr sym cval acc
        ) pe xs

let subst_expr pat cval e =
  match Core_aux.match_pattern pat cval with
    | None ->
        e
    | Some xs ->
        List.fold_left (fun acc (sym, cval) ->
          Core_aux.subst_sym_expr sym cval acc
        ) e xs


let test file expr : unit expr =
  let eval_pexpr pexpr =
    let emp = Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method in
    Core_eval.eval_pexpr Location_ocaml.unknown emp [] None file pexpr in
  
  let rec simpl =
    let open RW in {
      rw_pexpr=
        RW.RW begin fun (Pexpr (annots, bty, pexpr_) as pexpr) ->
          match pexpr_ with
            | PEcfunction pe ->
                begin match eval_pexpr pexpr with
                  | Right (Defined cval) ->
                      ChangeDoChildrenPost
                        ( Identity.return (Pexpr (annots, bty, PEval cval))
                        , fun z -> Identity.return z )
                  | Right (Undef (_, ubs)) ->
                      failwith (String.concat ", " (List.map Undefined.stringFromUndefined_behaviour ubs))
                  | Right (Error (_, str)) ->
                      print_endline str;
                      exit 1
                  | Left err ->
                      print_endline ("PEcfunction => " ^ Pp_errors.to_string err);
                      exit 1
                end
            | PElet (pat, Pexpr (_, _, PEval cval), pe2) ->
                ChangeDoChildrenPost
                  ( Identity.return (subst_pexpr pat cval pe2)
                  , Identity.return )
            | _ ->
                Traverse
        end;
      
      rw_action=
        RW.RW begin fun act ->
          Unchanged
        end;
      
      rw_expr=
    RW.RW begin fun (Expr (annots, expr_) as expr) ->
      match expr_ with
        | Ebound e ->
            ChangeDoChildrenPost
              ( Identity.return e, Identity.return )
(*
        | Esseq (pat, e1, e2) ->
            begin match Core_aux.to_pure e1 with
              | Some pe ->
                  begin match eval_pexpr pe with
                    | Right (Defined cval) ->
                        ChangeDoChildrenPost
                          ( Identity.return (subst_expr pat cval e2)
                          , Identity.return )
                    | _ ->
                        assert false
                  end
              | None ->
                  Traverse
            end
*)
        | Ewseq (pat, e1, e2) ->
            ChangeDoChildrenPost
              ( begin
                  rewriteExpr simpl e1 >>= fun e1' ->
                  begin match Core_aux.to_pure e1' with
                    | Some pe ->
                        begin match eval_pexpr pe with
                          | Right (Defined cval) ->
                              rewriteExpr simpl (subst_expr pat cval e2)
                          | _ ->
                              rewriteExpr simpl e2 >>= fun e2' ->
                              Identity.return (Expr (annots, Ewseq (pat, e1', e2')))(*expr*)
                        end
                    | None ->
                        rewriteExpr simpl e2 >>= fun e2' ->
                        Identity.return (Expr (annots, Ewseq (pat, e1', e2')))(*expr*)
                  end
                end
              , Identity.return )
        | Esseq (pat, e1, e2) ->
            ChangeDoChildrenPost
              ( begin
                  rewriteExpr simpl e1 >>= fun e1' ->
                  begin match Core_aux.to_pure e1' with
                    | Some pe ->
                        begin match eval_pexpr pe with
                          | Right (Defined cval) ->
                              rewriteExpr simpl (subst_expr pat cval e2)
                          | _ ->
                              rewriteExpr simpl e2 >>= fun e2' ->
                              Identity.return (Expr (annots, Esseq (pat, e1', e2')))(*expr*)
                        end
                    | None ->
                        rewriteExpr simpl e2 >>= fun e2' ->
                        Identity.return (Expr (annots, Esseq (pat, e1', e2')))(*expr*)
                  end
                end
              , Identity.return )
(*
        | Ewseq (pat, e1, e2) ->
            print_string "Ewseq ==> ";
            begin match Core_aux.to_pure e1 with
              | Some pe ->
                  begin match eval_pexpr pe with
                    | Right (Defined cval) ->
                        print_endline "ChangeDoChildrenPost";
                        FOO(*ChangeDoChildrenPost*)
                          ( Identity.return (subst_expr pat cval e2)
                          , Identity.return )
                    | _ ->
                        assert false
                  end
              | None ->
                  print_endline "Traverse";
                  Traverse
            end
*)
        | Eunseq _ ->
            ChangeDoChildrenPost
              ( Identity.return expr
              , function
                  | Expr (_, Eunseq es) as expr' ->
                      Identity.return begin match Core_aux.to_pures es with
                        | Some pes ->
                            Core_aux.(mk_pure_e (mk_tuple_pe pes))
                        | None ->
                            expr'
                      end
                  | _ ->
                      assert false )
(*
        | Esseq _ ->
            FOO(*ChangeDoChildrenPost*)
              ( Identity.return expr
              , function
                  | Expr (_, Esseq (pat, e1, e2)) as expr' ->
                      begin match Core_aux.to_pure e1 with
                        | Some pe ->
                            begin match eval_pexpr pe with
                              | Right (Defined cval) ->
                                  Identity.return (subst_expr pat cval e2)
                              | _ ->
                                  assert false
                            end
                        | None ->
                            Identity.return expr'
                      end )
        | Ewseq _ ->
            FOO(*ChangeDoChildrenPost*)
              ( Identity.return expr
              , function
                  | Expr (_, Ewseq (pat, e1, e2)) as expr' ->
                      begin match Core_aux.to_pure e1 with
                        | Some pe ->
                            begin match eval_pexpr pe with
                              | Right (Defined cval) ->
                                  Identity.return (subst_expr pat cval e2)
                              | _ ->
                                  assert false
                            end
                        | None ->
                            Identity.return expr'
                      end )
*)
        | _ ->
          Traverse

    end
    } in

  
  Identity.unwrap RW.(rewriteExpr simpl expr)



(*
  

let fetch_tag (tag: string) (prog: 'a ail_program) : A.ail_identifier option =
  let tagDefs = (snd prog).tag_definitions in
  let rec aux = function
    | [] ->
        None
    | (Symbol.Symbol (_, _, Some str) as sym, _) :: xs ->
        if tag = str then
          Some sym
        else
          aux xs
    | _ :: xs ->
        aux xs
  in aux tagDefs


let startup prog =
  let str= "my_Struct" in
  match fetch_tag str prog with
    | None ->
        prerr_endline ("Couldn't fined tag definition for '" ^ str ^ "'");
        exit 1
    | Some sym ->
        Printf.printf "SUCCESS, for symbol %s for tag name '%s'\n"
          (Pp_utils.to_plain_string (Pp_ail.pp_id sym))
          str
*)
