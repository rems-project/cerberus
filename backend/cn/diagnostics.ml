
open Typing
module LC = LogicalConstraints
module LCSet = Set.Make(LC)
module IT = IndexTerms
open Effectful.Make(Typing)
module BT = BaseTypes

type cfg = {
  model : Solver.model_with_q;
  arc : string;
  arc_index : int}

type opt = {
  doc : Pp.doc;
  continue : cfg -> (unit, TypeErrors.type_error) m
}

let opt_key = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

let continue_with (opts : opt list) cfg =
  assert (List.length opts <= String.length opt_key);
  let xs = List.mapi (fun i opt ->
    let c = String.get opt_key i in
    let s = String.make 1 c in
    Pp.print stdout (Pp.string (s ^ " to continue with:"));
    Pp.print stdout opt.doc;
    (c, opt.continue)) opts in
  let next = if cfg.arc_index >= String.length cfg.arc
    then None
    else List.find_opt (fun (c, _) -> Char.equal c (String.get cfg.arc cfg.arc_index)) xs
  in
  match next with
  | None -> return ()
  | Some (c, cont) ->
    Pp.print stdout (Pp.string ("picking " ^ String.make 1 c));
    Pp.print stdout (Pp.string ("-- continuing --"));
    cont {cfg with arc_index = cfg.arc_index + 1}

let term_with_model_name nm cfg x =
  let@ g = get_global () in
  match Solver.eval g (fst cfg.model) x with
  | None ->
    let open Pp in
    return (bold nm ^^ colon ^^^ parens (string "cannot eval") ^^ colon ^^^ IT.pp x)
  | Some r ->
    let open Pp in
    return (bold nm ^^ colon ^^^ parens (IT.pp r ^^^ string "in model") ^^ colon ^^^ IT.pp x)

let bool_subterms_of t =
  let rec f t =
    let xs = match IT.term t with
    | IT.Bool_op (IT.And xs) -> xs
    | IT.Bool_op (IT.Or xs) -> xs
    | IT.Bool_op (IT.Impl (x, y)) -> [x; y]
    | IT.Bool_op (IT.Not x) -> [x]
    | IT.Bool_op (IT.EQ (x, y)) -> if BT.equal (IT.bt x) BT.Bool
        then [x; y] else []
    | _ -> []
    in
    t :: List.concat (List.map f xs)
  in f t

let same_pred nm t = match IT.term t with
  | IT.Pred (nm2, _) -> Sym.equal nm nm2
  | _ -> false

let pred_args t = match IT.term t with
  | IT.Pred (_, args) -> args
  | _ -> []

(* investigate the provability of a term *)
let rec investigate_term cfg t =
  let rec_opt nm t =
    let@ doc = term_with_model_name nm cfg t in
    return {doc; continue = fun cfg -> investigate_term cfg t}
  in
  let sub_ts = match IT.term t with
    | IT.Bool_op (IT.And xs) -> xs
    | IT.Bool_op (IT.Or xs) -> xs
    | IT.Bool_op (IT.Impl (x, y)) -> [IT.disperse_not_ x; y]
    | IT.Bool_op (IT.Not x) -> [x]
    | IT.Bool_op (IT.ITE (x, y, z)) -> [x]
    | _ -> []
  in
  let@ sub_t_opts = ListM.mapM (rec_opt "sub-term") sub_ts in
  let@ sc = Typing.simp_ctxt () in
  let s_t = Simplify.IndexTerms.simp sc t in
  let s_ts = if IT.equal s_t t then [] else [s_t] in
  let@ simp_opts = ListM.mapM (rec_opt "simplified term") s_ts in
  let@ pred_opts = match IT.term t with
    | IT.Pred (nm, xs) -> investigate_pred cfg nm xs
    | _ -> return []
  in
  let opts = sub_t_opts @ simp_opts @ pred_opts in
  if List.length opts == 0
  then Pp.print stdout (Pp.item "out of diagnostic options at" (IT.pp t))
  else ();
  continue_with opts cfg

and investigate_pred cfg nm xs =
  let@ cs_set = all_constraints () in
  let cs = LCSet.elements cs_set in
  let cs_subts = List.map (function
    | LC.Forall _ -> []
    | LC.T t -> List.map (fun t2 -> (t2, t)) (bool_subterms_of t)
  ) cs
    |> List.concat
    |> List.filter (fun (t, ctxt_t) -> same_pred nm t) in
  let pred_opt p = 
    let@ doc = term_with_model_name "matching pred from constraint" cfg p in
    return {doc; continue = fun cfg -> investigate_pred_pred cfg xs (pred_args p)}
  in
  let pred_ctxt_opt t =
    let@ doc = term_with_model_name "constraint containing pred" cfg t in
    return {doc; continue = fun cfg -> investigate_term cfg t}
  in
  let@ opts = ListM.mapM (fun (p, ctxt_t) ->
    let@ p_opt = pred_opt p in
    let cs = if IT.equal p ctxt_t then [] else [ctxt_t] in
    let@ c_opts = ListM.mapM pred_ctxt_opt cs in
    return (p_opt :: c_opts)
  ) cs_subts in
  return (List.concat opts)

and investigate_pred_pred cfg goal_args hyp_args =
  Pp.print stdout (Pp.bold "considering equalities of predicate args");
  let eqs = List.map2 (fun x y -> IT.eq_ (x, y)) goal_args hyp_args in
  let eq_opt eq =
    let@ doc = term_with_model_name "pred argument equality" cfg eq in
    return {doc; continue = fun cfg -> investigate_term cfg eq}
  in
  let@ opts = ListM.mapM eq_opt eqs in
  continue_with opts cfg
  
  

let investigate_lc cfg lc = match lc with
  | LC.T t -> investigate_term cfg t
  | LC.Forall (q, t) -> investigate_term cfg t

let diag_string = ref (None : string option)

let get_arc () = (! diag_string)

let investigate model lc =
  match get_arc () with
  | None ->
    Pp.debug 3 (lazy (Pp.bold "branching diagnostics may be available with --diag"));
    return ()
  | Some arc ->
    let cfg = {arc; model; arc_index = 0} in
    Pp.print stdout (Pp.item "investigating unproven constraint" (LC.pp lc));
    investigate_lc cfg lc




