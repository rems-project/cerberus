module Loc = Locations
module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes

open IndexTerms


module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)


type def_or_uninterp = 
  | Def of IndexTerms.t
  | Rec_Def of IndexTerms.t
  | Uninterp

type definition = {
    loc : Locations.t;
    args : (Sym.t * LogicalSorts.t) list;
    (* If the predicate is supposed to get used in a quantified form,
       one of the arguments has to be the index/quantified
       variable. For now at least. *)
    return_bt: BT.t;
    definition : def_or_uninterp;
  }


let pp_def nm def =
  let open Pp in
  nm ^^ colon ^^^ flow (break 1)
    (List.map (fun (sym, t) -> parens (typ (Sym.pp sym) (LogicalSorts.pp t))) def.args) ^^
    colon ^^^
    begin match def.definition with
    | Uninterp -> !^ "uninterpreted"
    | Def t -> IT.pp t
    | Rec_Def t -> !^ "rec:" ^^^ IT.pp t
    end


let open_pred def_args def_body args =
  let su = make_subst (List.map2 (fun (s, _) arg -> (s, arg)) def_args args) in
  IT.subst su def_body

let try_open_pred def name args =
  match def.definition with
  | Def body -> Some (open_pred def.args body args)
  | _ -> None




exception Unknown of Sym.t

(* Compute if a predicate is sufficiently defined, i.e. not uninterpreted
   nor can it call a predicate that is uninterpreted. recursive functions
   count as uninterpreted as the SMT solver will not necessarily be given
   full definitions of them. *)
let is_fully_defined (defs : definition SymMap.t) nm =
  let rec scan seen = function
    | [] -> true
    | nm :: nms -> if SymSet.mem nm seen
      then scan seen nms
      else begin match SymMap.find_opt nm defs with
        | None -> raise (Unknown nm)
        | Some def -> begin match def.definition with
            | Def t -> scan (SymSet.add nm seen) (SymSet.elements (IT.preds_of t) @ nms)
            | _ -> false
        end
    end
  in
  scan SymSet.empty [nm]


(* Check for cycles in the logical predicate graph, which would cause
   the system to loop trying to unfold them. Predicates whose definition
   are marked with Rec_Def aren't checked, as cycles there are expected. *)
let cycle_check (defs : definition SymMap.t) =
  let def_preds nm = match SymMap.find_opt nm defs with
    | None -> raise (Unknown nm)
    | Some def -> begin match def.definition with
        | Def t -> SymSet.elements (IT.preds_of t)
        | _ -> []
    end
  in
  let rec search known_ok = function
    | [] -> None
    | (nm, Some path) :: q -> if SymSet.mem nm known_ok
      then search known_ok q
      else if List.exists (Sym.equal nm) path
      then Some (List.rev path @ [nm])
      else
        let deps = List.map (fun p -> (p, Some (nm :: path))) (def_preds nm) in
        search known_ok (deps @ [(nm, None)] @ q)
    | (nm, None) :: q -> search (SymSet.add nm known_ok) q
  in search SymSet.empty (List.map (fun (p, _) -> (p, Some [])) (SymMap.bindings defs))



