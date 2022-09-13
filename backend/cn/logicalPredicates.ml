module Loc = Locations
module IT = IndexTerms
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes

open IndexTerms
open Sctypes
open BaseTypes

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
  | Def body -> open_pred def.args body args
  | _ -> IT.pred_ name args def.return_bt

let open_if_pred defs t = match IT.term t with
  | IT.Pred (name, args) -> begin match SymMap.find_opt name defs with
    | Some def -> try_open_pred def name args
    | None -> t
  end
  | _ -> t


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



exception Struct_not_found




module PageAlloc = struct

  module Aux(SD : sig val struct_decls : Memory.struct_decls end) = struct
    open SD

    let pPAGE_SHIFT = 12
    let pPAGE_SIZE = 4096
    let mMAX_ORDER = 11
    let hHYP_NO_ORDER = 4294967295

    let list_head_tag, _ = 
      try Memory.find_tag struct_decls "list_head" with
      | Not_found -> raise Struct_not_found
    let hyp_pool_tag, _ = 
      try Memory.find_tag struct_decls "hyp_pool" with
      | Not_found -> raise Struct_not_found
    let hyp_page_tag, _ = 
      try Memory.find_tag struct_decls "hyp_page" with
      | Not_found -> raise Struct_not_found

    let (%.) t member = IT.(%.) struct_decls t (Id.id member)

    let hyp_page_size = int_ (Memory.size_of_struct hyp_page_tag)

    let vmemmap_offset_of_pointer ~vmemmap_pointer pointer = 
      IT.array_offset_of_pointer ~base:vmemmap_pointer ~pointer

    let vmemmap_index_of_pointer ~vmemmap_pointer pointer = 
      array_pointer_to_index ~base:vmemmap_pointer ~item_size:hyp_page_size
        ~pointer

    let vmemmap_good_pointer ~vmemmap_pointer pointer range_start range_end = 
      cellPointer_ ~base:vmemmap_pointer ~step:hyp_page_size
        ~starti:(range_start %/ int_ pPAGE_SIZE)
        ~endi:(range_end %/ int_ pPAGE_SIZE)
        ~p:pointer


    let vmemmap_resource ~vmemmap_pointer ~range_start ~range_end =
      let range_start_i = range_start %/ (int_ pPAGE_SIZE) in
      let range_end_i = range_end %/ (int_ pPAGE_SIZE) in
      let q_s, q = IT.fresh_named Integer "q" in
      let permission = and_ [range_start_i %<= q; q %<= (sub_ (range_end_i, int_ 1))] in
      let resource =
        ResourceTypes.Q {
            name = Owned (Struct hyp_page_tag);
            q = q_s;
            pointer = vmemmap_pointer;
            iargs = [];
            step = IT.int_ (Memory.size_of_ctype (Struct hyp_page_tag));
            permission = permission;
           }
      in
      let oargs_spec = Resources.q_owned_oargs (Struct hyp_page_tag) in
      ((resource, oargs_spec), ((q_s, q), permission))


  end


end



