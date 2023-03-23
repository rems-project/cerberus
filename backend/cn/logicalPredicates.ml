module Loc = Locations
module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes

open IndexTerms
open Subst
open Pp


module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)


module Body = struct

  type t = 
    | Case of IT.t * (Sym.t * t) list
    | Let of (Sym.t * IT.t) * t
    | Term of IT.t

  let rec subst su = function
    | Case (it, cases) ->
       let it = IT.subst su it in
       let cases = List.map_snd (subst su) cases in
       Case (it, cases)
    | Let ((s, it), t) -> 
       let it = IT.subst su it in
       let s, t = suitably_alpha_rename su.relevant (s, IT.bt it) t in
       Let ((s, it), subst su t)
    | Term t ->
       Term (IT.subst su t)

  and alpha_rename (s, ls) t = 
    let s' = Sym.fresh_same s in
    (s', subst (IT.make_subst [(s, IT.sym_ (s', ls))]) t)

  and suitably_alpha_rename syms (s, ls) t = 
    if SymSet.mem s syms 
    then alpha_rename (s, ls) t
    else (s, t)

  let rec pp ?(atomic=false) = function
    | Case (it, cases) ->
       !^"switch" ^^ parens (IT.pp it) ^^ hardline 
       ^^ nest 2
            ((separate_map hardline (fun (ctor, body) ->
                  Sym.pp ctor ^^^ lbrace ^^ hardline
                  ^^ nest 2 (pp body) ^^ hardline
                  ^^ rbrace
             )) cases)
    | Let ((s, it), t) ->
       let pped = 
         !^"let" ^^^ Sym.pp s ^^^ !^"equal" ^^^ IT.pp it ^^ semi 
         ^/^ pp t
       in
       if atomic then parens pped else pped
    | Term t ->
       IT.pp ~atomic t


  let rec to_term bt = function
    (* adapting earlier compilePredicates.ml code for this *)
    | Case (it, cases) ->
       (* TODO: there's a potential blowup due to `it` being repeated. *)
       List.fold_right (fun (ctor, case_body) acc ->
           ite_ (IT.datatype_is_cons_ ctor it, 
                 to_term bt case_body, 
                 acc)
         ) cases (default_ bt)
    | Let ((s, it), t) -> 
       to_term bt (subst (IT.make_subst [(s, it)]) t)
    | Term t -> 
       t

end



type def_or_uninterp = 
  | Def of Body.t
  | Rec_Def of Body.t
  | Uninterp





let subst_def_or_uninterp subst = function
  | Def it -> Def (Body.subst subst it)
  | Rec_Def it -> Rec_Def (Body.subst subst it)
  | Uninterp -> Uninterp

type definition = {
    loc : Locations.t;
    args : (Sym.t * LogicalSorts.t) list;
    (* If the predicate is supposed to get used in a quantified form,
       one of the arguments has to be the index/quantified
       variable. For now at least. *)
    return_bt: BT.t;
    definition : def_or_uninterp;
  }


let is_recursive def = 
  match def.definition with
  | Rec_Def _ -> true
  | Def _ -> false
  | Uninterp -> false


let alpha_rename_definition def = 
  let args, subst = 
    List.fold_right (fun (s, ls) (args, subst) ->
        let s' = Sym.fresh_same s in
        ((s', ls) :: args, (s, sym_ (s', ls)) :: subst)
      ) def.args ([],[])
  in
  let definition = subst_def_or_uninterp (IT.make_subst subst) def.definition in
  { loc = def.loc; args; return_bt = def.return_bt; definition }


let pp_def nm def =
  let open Pp in
  nm ^^ colon ^^^ flow (break 1)
    (List.map (fun (sym, t) -> parens (typ (Sym.pp sym) (LogicalSorts.pp t))) def.args) ^^
    colon ^/^
    begin match def.definition with
    | Uninterp -> !^ "uninterpreted"
    | Def t -> Body.pp t
    | Rec_Def t -> !^ "rec:" ^^^ Body.pp t
    end


let open_pred def_args def_body args =
  let su = make_subst (List.map2 (fun (s, _) arg -> (s, arg)) def_args args) in
  Body.subst su def_body



let single_unfold_to_term def name args =
  match def.definition with
  | Def body -> 
     Some (Body.to_term def.return_bt (open_pred def.args body args))
  | Rec_Def body -> 
     Some (Body.to_term def.return_bt (open_pred def.args body args))
  | _ -> 
     None


let try_open_pred def name args =
  match def.definition with
  | Def body -> Some (open_pred def.args body args)
  | _ -> None

let try_open_pred_to_term def name args = 
  Option.map (fun body ->
      Body.to_term def.return_bt body
    ) (try_open_pred def name args)



let add_unfolds_to_terms preds terms =
  let rec f acc t = match IT.term t with
    | IT.Pred (name, ts) ->
      let def = SymMap.find name preds in
      begin match try_open_pred_to_term def name ts with
        | None -> acc
        | Some t2 -> f (t2 :: acc) t2
      end
    | _ -> acc
  in
  IT.fold_list (fun _ acc t -> f acc t) [] terms terms




(* (\* Check for cycles in the logical predicate graph, which would cause *)
(*    the system to loop trying to unfold them. Predicates whose definition *)
(*    are marked with Rec_Def aren't checked, as cycles there are expected. *\) *)
(* let cycle_check (defs : definition SymMap.t) = *)
(*   let def_preds nm =  *)
(*     let def =  SymMap.find nm defs in *)
(*     begin match def.definition with *)
(*     | Def t -> SymSet.elements (IT.preds_of (Body.to_term def.return_bt t)) *)
(*     | _ -> [] *)
(*     end *)
(*   in *)
(*   let rec search known_ok = function *)
(*     | [] -> None *)
(*     | (nm, Some path) :: q -> if SymSet.mem nm known_ok *)
(*       then search known_ok q *)
(*       else if List.exists (Sym.equal nm) path *)
(*       then Some (List.rev path @ [nm]) *)
(*       else *)
(*         let deps = List.map (fun p -> (p, Some (nm :: path))) (def_preds nm) in *)
(*         search known_ok (deps @ [(nm, None)] @ q) *)
(*     | (nm, None) :: q -> search (SymSet.add nm known_ok) q *)
(*   in search SymSet.empty (List.map (fun (p, _) -> (p, Some [])) (SymMap.bindings defs)) *)



