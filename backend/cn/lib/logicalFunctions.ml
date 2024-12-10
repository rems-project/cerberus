module Loc = Locations
module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
open IndexTerms

type def_or_uninterp =
  | Def of IT.t
  | Rec_Def of IT.t
  | Uninterp

let subst_def_or_uninterp subst = function
  | Def it -> Def (IT.subst subst it)
  | Rec_Def it -> Rec_Def (IT.subst subst it)
  | Uninterp -> Uninterp


type definition =
  { loc : Locations.t;
    args : (Sym.t * LogicalSorts.t) list;
    (* If the predicate is supposed to get used in a quantified form, one of the arguments
       has to be the index/quantified variable. For now at least. *)
    return_bt : BT.t;
    emit_coq : bool;
    definition : def_or_uninterp
  }

let is_recursive def =
  match def.definition with Rec_Def _ -> true | Def _ -> false | Uninterp -> false


let given_to_solver def =
  match def.definition with Rec_Def _ -> false | Def _ -> true | Uninterp -> false


let pp_args xs =
  Pp.flow_map
    (Pp.break 1)
    (fun (sym, typ) -> Pp.parens (Pp.typ (Sym.pp sym) (BT.pp typ)))
    xs


let pp_def nm def =
  let open Pp in
  nm
  ^^ colon
  ^^^ pp_args def.args
  ^^ colon
  ^/^
  match def.definition with
  | Uninterp -> !^"uninterpreted"
  | Def t -> IT.pp t
  | Rec_Def t -> !^"rec:" ^^^ IT.pp t


let open_fun def_args def_body args =
  let su = make_subst (List.map2 (fun (s, _) arg -> (s, arg)) def_args args) in
  IT.subst su def_body


let unroll_once def args =
  match def.definition with
  | Def body | Rec_Def body -> Some (open_fun def.args body args)
  | Uninterp -> None


let try_open_fun def args =
  match def.definition with
  | Def body -> Some (open_fun def.args body args)
  | Rec_Def _ -> None
  | Uninterp -> None


(* let try_open_fun_to_term def name args = Option.map (fun body -> Body.to_term
   def.return_bt body ) (try_open_fun def name args) *)

(* let add_unfolds_to_terms preds terms = let rec f acc t = match IT.term t with |
   IT.Apply (name, ts) -> let def = Sym.Map.find name preds in begin match
   try_open_fun_to_term def name ts with | None -> acc | Some t2 -> f (t2 :: acc) t2 end |
   _ -> acc in IT.fold_list (fun _ acc t -> f acc t) [] terms terms *)

(* (\* Check for cycles in the logical predicate graph, which would cause *)
(*    the system to loop trying to unfold them. Predicates whose definition *)
(*    are marked with Rec_Def aren't checked, as cycles there are expected. *\) *)
(* let cycle_check (defs : definition Sym.Map.t) = *)
(*   let def_preds nm =  *)
(*     let def =  Sym.Map.find nm defs in *)
(*     begin match def.definition with *)
(*     | Def t -> Sym.Set.elements (IT.preds_of (Body.to_term def.return_bt t)) *)
(*     | _ -> [] *)
(*     end *)
(*   in *)
(*   let rec search known_ok = function *)
(*     | [] -> None *)
(*     | (nm, Some path) :: q -> if Sym.Set.mem nm known_ok *)
(*       then search known_ok q *)
(*       else if List.exists (Sym.equal nm) path *)
(*       then Some (List.rev path @ [nm]) *)
(*       else *)
(*         let deps = List.map (fun p -> (p, Some (nm :: path))) (def_preds nm) in *)
(*         search known_ok (deps @ [(nm, None)] @ q) *)
(*     | (nm, None) :: q -> search (Sym.Set.add nm known_ok) q *)
(* in search Sym.Set.empty (List.map (fun (p, _) -> (p, Some [])) (Sym.Map.bindings
   defs)) *)

(*Extensibility hook. For now, all functions are displayed as "interesting" in error reporting*)
let is_interesting : definition -> bool = fun _ -> true
