module IT = IndexTerms
module RET = ResourceTypes
module RE = Resources

open IT

exception Failure of Pp.doc
exception NoResult

let note_failure f x =
  begin try Some (f x)
  with
  | Failure pp ->
    Pp.debug 5 (lazy (Pp.item "failed in span computations" pp));
    None
  | NoResult -> None
  end

type action = Pack of RET.predicate_type | Unpack of RET.predicate_type
[@@deriving eq, ord]

let pp_action act =
  let open Pp in
  match act with
  | Pack pt -> !^ "Pack:" ^^^ (RET.pp_predicate_type pt)
  | Unpack pt -> !^ "Unpack:" ^^^ (RET.pp_predicate_type pt)

let lb_str = function
  | None -> "-inf"
  | Some i -> Z.to_string i

let ub_str = function
  | None -> "inf"
  | Some i -> Z.to_string i

let pp_pair (i, j) = Pp.string (Z.to_string i ^ " - " ^ Z.to_string j)
let pp_ipair (i, j) = Pp.string (lb_str i ^ " - " ^ ub_str j)

let pp ss =
  let open Pp in
  !^"[" ^^ list pp_pair ss ^^ !^"]"

let pp_open ss =
  let open Pp in
  !^"[" ^^ list pp_ipair ss ^^ !^"]"

let pp_res_span (r, span) =
  let open Pp in
  RET.pp r ^^ colon ^^^ pp_pair span

let eval_extract msg m_g f x =
  let (m, global) = m_g in
  match Solver.eval global m x with
  | None -> raise (Failure (Pp.item ("cannot eval: " ^ msg) (IT.pp x)))
  | Some v -> begin match f v with
      | Some y -> y
      | None -> raise (Failure (Pp.item ("cannot eval and interpret: " ^ msg)
          (Pp.list IT.pp [x; v])))
  end

let inc_b = Option.map (Z.add (Z.of_int 1))
let dec_b = Option.map (fun i -> Z.sub i (Z.of_int 1))

let norm_spans ss =
  let cmp (x, _) (y, _) = Option.compare Z.compare x y in
  let ok = function
    | (Some x, Some y) -> Z.leq x y
    | _ -> true
  in
  let ss = List.sort cmp (List.filter ok ss) in
  let rec f = function
    | [] -> []
    | [x] -> [x]
    | (x_lb, None) :: _ -> [(x_lb, None)]
    | (x_lb, x_ub) :: (y_lb, y_ub) :: zs ->
      if Option.compare Z.compare y_lb (inc_b x_ub) > 0
      then (x_lb, x_ub) :: f ((y_lb, y_ub) :: zs)
      else if Option.is_none y_ub || Option.compare Z.compare y_ub x_ub > 0
      then f ((x_lb, y_ub) :: zs)
      else f ((x_lb, x_ub) :: zs)
  in f ss

let not_flip_spans ss =
  let ss = norm_spans ss in
  let rec f = function
    | (None, []) -> []
    | (Some x, []) -> [(inc_b (Some x), None)]
    | (l, (lb, ub) :: xs) -> (inc_b l, dec_b lb) :: f (ub, xs)
  in
  match ss with
    | [] -> [(None, None)]
    | (None, ub) :: xs -> f (ub, xs)
    | (lb, ub) :: xs -> (None, dec_b lb) :: f (ub, xs)

let subtract_closed_spans ss1 ss2 =
  let mk_open (lb, ub) = (Some lb, Some ub) in
  let mk_closed = function
    | (Some lb, Some ub) -> (lb, ub)
    | _ -> assert false
  in
  let inv_opts = not_flip_spans (List.map mk_open ss1) @ List.map mk_open ss2 in
  let ss = norm_spans (not_flip_spans inv_opts) in
  List.map mk_closed ss

let rec perm_spans m_g q perm =
  let is_q = IT.equal (sym_ (q, BT.Integer)) in
  match term perm with
  | Bool_op (And xs) -> perm_spans m_g q (not_ (or_ (List.map not_ xs)))
  | Bool_op (Or xs) ->
        let ss = List.map (perm_spans m_g q) xs in
        norm_spans (List.concat ss)
  | Bool_op (Impl (lhs, rhs)) -> perm_spans m_g q (or_ [not_ lhs; rhs])
  | Bool_op (Not x) ->
        let s = perm_spans m_g q x in
        not_flip_spans s
  | Bool_op (ITE (x,y,z)) -> perm_spans m_g q (or_ [and_ [x; y]; and_ [not_ x; z]])
  | Bool_op (EQ (lhs, rhs)) when is_q lhs ->
        let x = eval_extract "idx eq rhs" m_g is_z rhs in
        [(Some x, Some x)]
  | Bool_op (EQ (lhs, rhs)) when is_q rhs ->
        let x = eval_extract "idx eq lhs" m_g is_z lhs in
        [(Some x, Some x)]
  | Arith_op (LE (lhs, rhs)) when is_q lhs ->
        let x = eval_extract "idx less-eq rhs" m_g is_z rhs in
        [(None, Some x)]
  | Arith_op (LE (lhs, rhs)) when is_q rhs ->
        let x = eval_extract "idx less-eq lhs" m_g is_z lhs in
        [(Some x, None)]
  | Arith_op (LT (lhs, rhs)) when is_q lhs ->
        let x = eval_extract "idx less-than rhs" m_g is_z rhs in
        [(None, dec_b (Some x))]
  | Arith_op (LT (lhs, rhs)) when is_q rhs ->
        let x = eval_extract "idx less-than lhs" m_g is_z lhs in
        [(inc_b (Some x), None)]
  | _ ->
        let fv = IT.free_vars perm in
        if SymSet.mem q fv
        then raise (Failure (Pp.item "unsupported quantified permission" (IT.pp perm)))
        else let x = eval_extract "idx non-ineq guard term" m_g is_bool perm in
        if x then [(None, None)] else []

let model_res_spans m_g (res : ResourceTypes.t) =
  match res with
  | (RET.P ({name = Owned ct; _} as pt)) ->
      let perm = eval_extract "resource permission" m_g is_bool pt.permission in
      begin match perm with
      | false -> []
      | true ->
          let ptr = eval_extract "resource pointer" m_g is_pointer pt.pointer in
          let sz = Memory.size_of_ctype ct in
          [(ptr, Z.add ptr (Z.of_int sz))]
      end
  | (RET.Q ({name = Owned ct; _} as qpt)) ->
      assert (IT.equal qpt.step (IT.int_ (Memory.size_of_ctype ct)));
      let ispans = perm_spans m_g qpt.q qpt.permission in
      if List.compare_length_with ispans 0 == 0
      then []
      else
      if List.exists (fun (lb, rb) -> Option.is_none lb || Option.is_none rb) ispans
      then raise (Failure (Pp.item "unbounded resource interval" (IT.pp qpt.permission)))
      else
      let spans = List.map (fun (i, j) -> (Option.get i, Option.get j)) ispans in
      let ptr = eval_extract "q-resource pointer" m_g is_pointer qpt.pointer in
      let sz = Z.of_int (Memory.size_of_ctype ct) in
      let offs i = Z.add ptr (Z.mul i sz) in
      (List.map (fun (i, j) -> (offs i, offs (Z.add j (Z.of_int 1)))) spans)
  | _ -> []

let inter (i_lb, i_ub) (j_lb, j_ub) =
  Z.lt j_lb i_ub && Z.lt i_lb j_ub

let spans_compare_for_pp m g res =
  try
    let ss = model_res_spans (m, g) res in
    Some (fun ss2 -> List.exists (fun s -> List.exists (inter s) ss2) ss)
  with
    Failure _ -> None

let pp_model_spans m g cmp res =
  try
    let open Pp in
    let s = model_res_spans (m, g) res in
    let doc = pp s in
    match cmp with
    | None -> doc
    | Some f -> if f s then doc ^^ !^" - (spans overlap)" else doc
  with
    Failure s -> s

let pp_pt_ct pt ct =
  let open Pp in
  IT.pp pt ^^ !^": (" ^^ Sctypes.pp ct ^^ !^") ptr"

let pp_fold pt ct =
  let open Pp in
  !^"fold(" ^^ pp_pt_ct pt ct ^^ !^")"

let rec enclosing_count g = function
  | Sctypes.Struct nm ->
    let open Global in
    let ds = g.struct_decls in
    let fs = SymMap.find nm ds in
    let enc_counts = List.map (fun (_, ct) -> enclosing_count g ct + 1)
        (Memory.member_types fs) in
    List.fold_left Int.add 0 enc_counts
  | Sctypes.Array (ct, _) ->
    enclosing_count g ct + 1
  | _ -> 0

let compare_enclosing g ct1 ct2 =
  let sz_compare = Int.compare (Memory.size_of_ctype ct1) (Memory.size_of_ctype ct2) in
  if sz_compare != 0
  then sz_compare
  else Int.compare (enclosing_count g ct1) (enclosing_count g ct2)

let req_pt_ct = function
  | RET.P ({name = Owned ct; _} as pt) -> (pt.pointer, ct, false)
  | RET.Q ({name = Owned ct; _} as qpt) -> (qpt.pointer, ct, true)
  | _ -> assert false

let scan_subterms f t = fold_subterms (fun _ xs t -> match f t with
  | None -> xs
  | Some r -> r :: xs) [] t

(* get concrete objects that (probably) exist in this resource/request *)
let get_witnesses = function
  | RET.P ({name = Owned _; _} as pt) -> [(pt.pointer, pt.permission)]
  | RET.Q ({name = Owned ct; _} as qpt) ->
     assert (IT.equal qpt.step (IT.int_ (Memory.size_of_ctype ct)));
     let i = sym_ (qpt.q, BT.Integer) in
     let lbs = scan_subterms is_le qpt.permission
       |> List.filter (fun (lhs, rhs) -> IT.equal i rhs)
       |> List.map fst in
     if List.length lbs <> 0
     then Pp.debug 8 (lazy (Pp.item "unexpected number of lower bounds"
       (Pp.list IT.pp lbs)))
     else ();
     let eqs = scan_subterms is_eq qpt.permission
       |> List.filter (fun (lhs, rhs) -> IT.equal i lhs || IT.equal i rhs)
     in
     begin match lbs with
         | [] -> []
         | (lb :: _) ->
     List.init (List.length eqs + 1)
       (fun i -> (arrayShift_ (qpt.pointer, ct, add_ (lb, z_ (Z.of_int i))),
           subst (make_subst [(qpt.q, z_ (Z.of_int i))]) qpt.permission))
     end
  | _ -> []

let outer_object m g inner_ptr = function
  | RET.P ({name = Owned ct; _} as pt) -> Some (pt.pointer, ct, pt.permission)
  | RET.Q ({name = Owned ct; _} as qpt) ->
  (* need to invent an index at which to fold/unfold *)
  begin try
    let qptr = eval_extract "q-resource pointer" (m, g) is_pointer qpt.pointer in
    let iptr = eval_extract "inner object pointer" (m, g) is_pointer inner_ptr in
    let sz = Z.of_int (Memory.size_of_ctype ct) in
    let m_diff = Z.sub iptr qptr in
    let m_ix = Z.div m_diff sz in
    let m_offs = Z.sub m_diff (Z.mul m_ix sz) in
    let ptr = integerToPointerCast_
        (sub_ (pointerToIntegerCast_ inner_ptr, z_ m_offs)) in
    let offset = array_offset_of_pointer ~base:qpt.pointer ~pointer:ptr in
    let index = array_pointer_to_index ~base:qpt.pointer ~item_size:(z_ sz)
        ~pointer:ptr in
    let ok = and_ [divisible_ (offset, z_ sz);
        subst (make_subst [(qpt.q, index)]) qpt.permission] in
    Some (ptr, ct, ok)
  with
    Failure pp -> begin
      Pp.debug 5 (lazy (Pp.item "failed to compute object offsets" pp));
      None
    end
  end
  | _ -> None

let intersection_action m g (req, req_span) (res, res_span) =
  let (req_pt, req_ct, req_qpt) = req_pt_ct req in
  let (res_pt, res_ct, res_qpt) = req_pt_ct (RE.request res) in
  let cmp = compare_enclosing g req_ct res_ct in
  if cmp = 0 then begin
      Pp.debug 5 (lazy (Pp.item "unexpected overlap of diff same-rank types"
        (Pp.list RET.pp [req; RE.request res])));
      None
  end
  else
  (* the "inner witnesses" are concrete objects of interior type *)
  let witnesses = if cmp < 0
    then get_witnesses req
    else get_witnesses (RE.request res)
  in
  Pp.debug 8 (lazy (Pp.item "witnesses"
    (Pp.list IT.pp (List.map fst witnesses))));
  let obj = outer_object m g (if cmp < 0 then req_pt else res_pt)
            (if cmp < 0 then RE.request res else req) in
  match (witnesses, obj) with
  | ([], _) -> None
  | (_, None) -> None
  | (_, Some (ptr, ct, permission)) ->
  let sz = Memory.size_of_ctype ct in
  let upper = integerToPointerCast_ (add_ (pointerToIntegerCast_ ptr,
      z_ (Z.of_int (sz - 1)))) in
  let ok = and_ [permission;
    or_ (List.map (fun (w_ptr, perm) -> and_ [perm; lePointer_ (ptr, w_ptr);
        lePointer_ (w_ptr, upper)]) witnesses)] in
  let pred_t = RET.{name = RET.Owned ct; pointer = ptr;
        permission = bool_ true; iargs = []} in
  let action = if cmp < 0 then Unpack pred_t else Pack pred_t in
  Some (action, ok)

let model_res_spans_or_empty m g req =
  try
    model_res_spans (m, g) req
  with
    Failure pp ->
      Pp.debug 5 (lazy (Pp.item "failed to extract resource span" pp));
      []

let rec gather_same_actions opts = match opts with
  | [] -> []
  | (action, _) :: _ ->
    let same (a2, _) = equal_action action a2
    in
    let oks = List.filter same opts |> List.map (fun (_, ok) -> ok) in
    let others = List.filter (fun opt -> not (same opt)) opts in
    (action, or_ oks) :: gather_same_actions others

let is_unknown_array_size = function
  | RET.P ({name = Owned ct; _}) -> begin match ct with
      | Sctypes.Array (_, None) -> true
      | _ -> false
  end
  | _ -> false

let get_active_clause m g clauses =
  let rec seek not_prev = function
    | [] -> raise NoResult
    | (c :: clauses) ->
      let gd = c.ResourcePredicates.guard in
      let this = eval_extract "resource predicate clause guard" (m, g) is_bool gd in
      Pp.debug 11 (lazy (Pp.item "this clause guard" (Pp.list IT.pp [gd; IT.bool_ this])));
      if this then (IT.and_ (List.rev (gd :: not_prev)), c)
      else seek (IT.not_ gd :: not_prev) clauses
  in
  seek [] clauses

let do_null_resource_check m g req =
  Pp.debug 11 (lazy (Pp.item "doing null resource check" (RET.pp req)));
  let (nm, pt) = match req with
    | RET.P ({name = PName nm; _} as pt) -> (nm, pt)
    | _ -> raise NoResult
  in
  let def = match SymMap.find_opt nm g.Global.resource_predicates with
    | None -> raise NoResult
    | Some def -> def
  in
  let clauses = match ResourcePredicates.instantiate_clauses def pt.pointer pt.iargs with
    | None -> raise NoResult
    | Some clauses -> clauses
  in
  let (cond, active_clause) = get_active_clause m g clauses in
  if LogicalArgumentTypes.has_resource (fun _ -> false) active_clause.packing_ft
  then raise NoResult else ();
  (pt, cond)

let null_resource_check m g req = note_failure (do_null_resource_check m g) req

let res_pointer m g = function
  | RET.P pt -> eval_extract "resource pointer" (m, g) is_pointer pt.pointer
  | RET.Q qpt -> eval_extract "resource pointer" (m, g) is_pointer qpt.pointer


(* The standard span logic for a model, request and resource context is:
   (1) Compute spans for all existing and requested resources.
   (2) Subtract from the request spans the spans of existing resources of
       the same type. Such resources can already be handled by the resource
       inference and are preferred. This avoids a silly case where overlapping
       resources in the context create a problem.
   (3) If the remaining request spans intersect with a different-typed resource,
       something needs to be decomposed. If the context resource is larger,
       unpack it. If the request is larger, attempt to pack the requested
       thing. That pack operation recurses into requests for the components
       (i.e. splitting up the request). The request will be reattempted with
       the packed/unpacked resource in the context. In the packing case, this
       will be a same-typed resource shrinking the request span according to (2).
       - structs/arrays with one element, and resource predicates, count as
         larger than their contents, even if they're the same size.
       - if neither object is larger, but they're different, we need to split
         at both ends. start with the context resource. this happens e.g. if a
         resource needs to be unpacked out of one predicate type and packed
         again in another.
       - for an outer iterated array, operate on the element that intersects
         with the relevant inner object.
       - for an inner iterated array, require a witness that the array is nonempty
         and proceed based on it. multiple potential witnesses may be needed to deal
         with a tricky case involving missing elements of variable index.
   (4) If the request, in this model, is a resource predicate where the
       relevant clause claims no resources, then pack it. Only do this if
       there is no pointer-matching resource in the context.
*)

let do_guess_span_actions ress req m g =
  (* the inference logic supports requests for arrays of non-specific
     size as a special case which the span logic can ignore *)
  if is_unknown_array_size req
  then raise NoResult else ();
  let same_name res = RET.same_predicate_name req (RE.request res) in
  match null_resource_check m g req with
  | Some (pt, ok) ->
    (* null resources will also have no span, so skip the rest *)
    let req_ptr = res_pointer m g req in
    if List.exists (fun res -> same_name res &&
      (res_pointer m g (RE.request res) == req_ptr)) ress
    then [] else [(Pack pt, ok)]
  | None ->
  let res_spans = ress
    |> List.map (fun r -> List.map (fun s -> (r, s))
        (model_res_spans_or_empty m g (RE.request r)))
    |> List.concat in
  let (same, diff) = List.partition (fun (r, _) -> same_name r) res_spans in
  let req_spans1 = model_res_spans_or_empty m g req in
  let req_spans = subtract_closed_spans req_spans1 (List.map snd same) in
  let interesting = List.filter_map (fun (r, s) -> List.find_opt (inter s) req_spans
        |> Option.map (fun s2 -> (r, s, s2)))
    diff
    |> List.sort (fun (_, (lb, _), _) (_, (lb2, _), _) -> Z.compare lb lb2) in
  if List.length interesting == 0
  then
  Pp.debug 7 (lazy (Pp.bold "no span intersections"))
  else ();
  let opts = List.filter_map (fun (r, s, s2) ->
    Pp.debug 7 (lazy (Pp.item "resource (partial?) overlap"
      (Pp.list pp_res_span [(req, s2); (RE.request r, s)])));
    intersection_action m g (req, s2) (r, s)
  ) interesting in
  gather_same_actions opts

let guess_span_actions ress req m g =
  note_failure (do_guess_span_actions ress req m) g
  |> Option.to_list |> List.concat

let diag_req ress req m g =
  let act = guess_span_actions ress req m g in
  Pp.debug 5 (lazy (match act with
    | [] -> Pp.item "guess span action: none" (Pp.string "")
    | (action, ok) :: oth -> Pp.item "guessed span action" (pp_action action)
  ))


