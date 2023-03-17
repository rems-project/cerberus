
open Typing
module LC = LogicalConstraints
module LCSet = Set.Make(LC)
module IT = IndexTerms
open Effectful.Make(Typing)
module BT = BaseTypes
module ITSet = Set.Make(IT)

type cfg = {
  model : Solver.model_with_q;
  arc : string;
  arc_index : int}

type opt = {
  doc : Pp.doc;
  continue : cfg -> (unit) m
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
    if IT.is_true r
    then begin
      let@ p = provable Locations.unknown in
      let info = match p (LC.T x) with
        | `True -> "provably true"
        | `False -> "true in this model"
      in
      let open Pp in
      return (bold nm ^^ colon ^^^ parens (string info) ^^ colon ^^^ IT.pp x)
    end else
    let open Pp in
    return (bold nm ^^ colon ^^^ parens (IT.pp r ^^^ string "in model") ^^ colon ^^^ IT.pp x)

let bool_subterms1 t = match IT.term t with
  | IT.Bool_op (IT.And xs) -> xs
  | IT.Bool_op (IT.Or xs) -> xs
  | IT.Bool_op (IT.Impl (x, y)) -> [x; y]
  | IT.Bool_op (IT.Not x) -> [x]
  | IT.Bool_op (IT.EQ (x, y)) -> if BT.equal (IT.bt x) BT.Bool
      then [x; y] else []
  | _ -> []

let rec bool_subterms_of t =
  t :: List.concat (List.map bool_subterms_of (bool_subterms1 t))

let constraint_ts () =
  let@ cs = all_constraints () in
  let ts = List.filter_map (function
    | LC.T t -> Some t
    | _ -> None) (LCSet.elements cs)
  in
  return ts

let same_pred nm t = match IT.term t with
  | IT.Pred (nm2, _) -> Sym.equal nm nm2
  | _ -> false

let pred_args t = match IT.term t with
  | IT.Pred (_, args) -> args
  | _ -> []

let split_eq x y = match (IT.term x, IT.term y) with
  | (IT.Map_op (IT.Get (m1, x1)), IT.Map_op (IT.Get (m2, x2))) -> Some [(m1, m2); (x1, x2)]
  | (IT.Pred (nm, xs), IT.Pred (nm2, ys)) when Sym.equal nm nm2 ->
    Some (List.map2 (fun x y -> (x, y)) xs ys)
  | _ -> None

(* investigate the provability of a term *)
let rec investigate_term cfg t =
  let rec_opt nm t =
    let@ doc = term_with_model_name nm cfg t in
    return {doc; continue = fun cfg -> investigate_term cfg t}
  in
  let sub_ts = bool_subterms1 t in
  let@ sub_t_opts = ListM.mapM (rec_opt "sub-term") sub_ts in
  let@ sc = Typing.simp_ctxt () in
  let s_t = Simplify.IndexTerms.simp sc t in
  let s_ts = if IT.equal s_t t then [] else [s_t] in
  let@ simp_opts = ListM.mapM (rec_opt "simplified term") s_ts in
  let@ eq_opts = match IT.is_eq t with
    | None -> return []
    | Some (x, y) ->
      let@ trans_opts = ListM.mapM (investigate_eq_side cfg) [("lhs", x, y); ("rhs", y, x)] in
      let get_eq_opt = {doc = Pp.string "check for further eqs at this type";
        continue = fun cfg -> get_eqs_then_investigate cfg x y} in
      let@ split_opts = match split_eq x y with
        | None -> return []
        | Some bits -> ListM.mapM (fun (x, y) -> rec_opt "parametric eq" (IT.eq_ (x, y))) bits
      in
      return (List.concat trans_opts @ [get_eq_opt] @ split_opts)
  in
  let@ pred_opts = match IT.term t with
    | IT.Pred (nm, xs) -> investigate_pred cfg nm t
    | _ -> return []
  in
  let@ ite_opts = investigate_ite cfg t in
  let opts = sub_t_opts @ simp_opts @ eq_opts @ pred_opts @ ite_opts in
  if List.length opts == 0
  then Pp.print stdout (Pp.item "out of diagnostic options at" (IT.pp t))
  else ();
  continue_with opts cfg

and investigate_eq_side cfg (side_nm, t, t2) =
  let@ eq_group = value_eq_group None t in
  let xs = ITSet.elements eq_group |> List.filter (fun x -> not (IT.equal t x)) in
  let open Pp in
  let clique_opts = match xs with
    | [] ->
    print stdout (string side_nm ^^^ string "is not known equal to any other terms");
    []
    | _ ->
    print stdout (string side_nm ^^^ string "is in an equality group of size"
      ^^^ int (List.length xs + 1) ^^^ string "with:" ^^^ brackets (list IT.pp xs));
    [{doc = string "switch with another from" ^^^ string side_nm ^^^ string "eq-group";
      continue = continue_with (List.map (fun t ->
          {doc = IT.pp t; continue = fun cfg ->
              let eq = IT.eq_ (t, t2) in
              print stdout (bold "investigating eq:" ^^^ IT.pp eq);
              investigate_term cfg eq}) xs)}]
  in
  let t_opt = {doc = string "transitivity of" ^^^ string side_nm;
    continue = investigate_trans_eq t} in
  return ([t_opt] @ clique_opts)

and investigate_trans_eq t cfg =
  let@ cs = constraint_ts () in
  let eq_xs = IT.fold_list (fun _ acc t -> match IT.is_eq t with
    | None -> acc
    | Some (x, y) -> if BT.equal (IT.bt x) (IT.bt t) then [x; y] @ acc else acc
  ) [] [] cs in
  let opt_xs = eq_xs
    |> List.filter (fun x -> Option.is_some (split_eq t x))
    |> ITSet.of_list |> ITSet.elements in
  let opt_of x =
    let eq = (IT.eq_ (t, x)) in
    let@ doc = term_with_model_name "eq to constraint elem" cfg eq in
    return {doc; continue = fun cfg -> investigate_term cfg eq}
  in
  let@ opts = ListM.mapM opt_of opt_xs in
  if List.length opts == 0
  then Pp.print stdout (Pp.item "no interesting transitive options for" (IT.pp t))
  else ();
  continue_with opts cfg

and get_eqs_then_investigate cfg x y =
  let@ cs = constraint_ts () in
  let x_set = IT.fold_list (fun _ acc t -> if BT.equal (IT.bt t) (IT.bt x)
    then ITSet.add t acc else acc) [] ITSet.empty cs in
  let opt_xs = ITSet.elements x_set in
  let@ () = test_value_eqs Locations.unknown None x opt_xs in
  let@ () = test_value_eqs Locations.unknown None y opt_xs in
  investigate_term cfg (IT.eq_ (x, y))

and investigate_pred cfg nm t =
  let@ cs = constraint_ts () in
  let ps = IT.fold_list (fun _ acc t -> if same_pred nm t
    then t :: acc else acc) [] [] cs in
  let pred_opt p =
    let@ doc = term_with_model_name "eq to pred in constraint" cfg p in
    return {doc; continue = fun cfg -> investigate_term cfg (IT.eq_ (t, p))}
  in
  ListM.mapM pred_opt ps

and investigate_ite cfg t =
  let ites = IT.fold (fun _ acc t -> match IT.term t with
    | IT.Bool_op (ITE (x, y, z)) -> x :: acc
    | _ -> acc) [] [] t in
  let@ g = get_global () in
  let sc1 = Simplify.default g in
  let sc f = Simplify.{sc1 with lcs = LCSet.of_list [LC.T f]} in
  let simp f t = Simplify.IndexTerms.simp (sc f) t in
  let opt x b =
    let nm = if b then "true" else "false" in
    let f = if b then x else IT.not_ x in
    let@ doc = term_with_model_name ("rewrite ite cond to " ^ nm) cfg x in
    return {doc; continue = fun cfg ->
          let open Pp in
          print stdout (bold "rewrote to:" ^^^ IT.pp (simp f t));
          investigate_term cfg (simp f t)}
  in
  let opts x = ListM.mapM (opt x) [true; false] in
  let@ xs = ListM.mapM opts ites in
  return (List.concat xs)

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




