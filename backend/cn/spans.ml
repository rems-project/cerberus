module IT = IndexTerms
module RET = ResourceTypes
module RE = Resources
module LAT = LogicalArgumentTypes

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

let some_result x =
  match x with
  | Some y -> y
  | None -> raise NoResult

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
  !^"[" ^^ list pp_pair (List.map fst ss) ^^ !^"]"

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

let subtract_closed_spans_from_tagged closed_ss tagged_ss =
  List.map (fun (span, tag) -> subtract_closed_spans [span] closed_ss
    |> List.map (fun span -> (span, tag))) tagged_ss
  |> List.concat

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

let get_active_clause m_g clauses =
  let rec seek not_prev = function
    | [] -> raise NoResult
    | (c :: clauses) ->
      let gd = c.ResourcePredicates.guard in
      let this = eval_extract "resource predicate clause guard" m_g is_bool gd in
      if this then (IT.and_ (List.rev (gd :: not_prev)), c)
      else seek (IT.not_ gd :: not_prev) clauses
  in
  seek [] clauses

let rec get_packing_ft_owned_resources = function
  | LAT.I _ -> []
  | LAT.Constraint (_, _, ftyp) -> get_packing_ft_owned_resources ftyp
  | LAT.Define ((s, it), _, ftyp) ->
    let ftyp = LAT.subst OutputDef.subst (IT.make_subst [(s, it)]) ftyp in
    get_packing_ft_owned_resources ftyp
  | LAT.Resource ((s, (resource, bt)), _, ftyp) ->
    resource :: get_packing_ft_owned_resources ftyp

let rec model_res_spans m_g (res : ResourceTypes.t) =
  match res with
  | (RET.P ({name = Owned ct; _} as pt)) ->
      let perm = eval_extract "resource permission" m_g is_bool pt.permission in
      let _ = perm || raise NoResult in
      let ptr = eval_extract "resource pointer" m_g is_pointer pt.pointer in
      let sz = Memory.size_of_ctype ct in
      [((ptr, Z.add ptr (Z.of_int sz)), (res, res))]
  | (RET.P ({name = PName pname; _} as r_pt)) ->
      let perm = eval_extract "resource permission" m_g is_bool r_pt.permission in
      let _ = perm || raise NoResult in
      let rpreds = (snd m_g).Global.resource_predicates in
      let def = SymMap.find_opt pname rpreds |> some_result in
      let clauses = ResourcePredicates.instantiate_clauses def r_pt.pointer r_pt.iargs
        |> some_result in
      let (cond, active_clause) = get_active_clause m_g clauses in
      let ress = get_packing_ft_owned_resources active_clause.ResourcePredicates.packing_ft in
      ress |> List.map (note_failure (model_res_spans m_g))
        |> List.map Option.to_list
        |> List.concat |> List.concat
        |> List.map (fun (span, (orig, res2)) -> (span, (res, res2)))
  | (RET.Q ({name = Owned ct; _} as qpt)) ->
      assert (IT.equal qpt.step (IT.int_ (Memory.size_of_ctype ct)));
      let ispans = perm_spans m_g qpt.q qpt.permission in
      let _ = List.length ispans > 0 || raise NoResult in
      if List.exists (fun (lb, rb) -> Option.is_none lb || Option.is_none rb) ispans
      then raise (Failure (Pp.item "unbounded resource interval" (IT.pp qpt.permission)))
      else ();
      let spans = List.map (fun (i, j) -> (Option.get i, Option.get j)) ispans in
      let ptr = eval_extract "q-resource pointer" m_g is_pointer qpt.pointer in
      let sz = Z.of_int (Memory.size_of_ctype ct) in
      let offs i = Z.add ptr (Z.mul i sz) in
      List.map (fun (i, j) -> ((offs i, offs (Z.add j (Z.of_int 1))), (res, res))) spans
  | _ -> []

let inter ((i_lb, i_ub), _) ((j_lb, j_ub), _) =
  Z.lt j_lb i_ub && Z.lt i_lb j_ub

let spans_compare_for_pp m g res =
  note_failure (model_res_spans (m, g)) res
  |> Option.map (fun ss ss2 -> List.exists (fun s -> List.exists (inter s) ss2) ss)

let pp_model_spans m g cmp res =
  try
    let open Pp in
    let s = model_res_spans (m, g) res in
    let doc = pp s in
    match cmp with
    | None -> doc
    | Some f -> if f s then doc ^^ !^" - (spans overlap)" else doc
  with
    | Failure s -> s
    | NoResult -> Pp.string "[]"

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

let compare_enclosing_ct g ct1 ct2 =
  let sz_compare = Int.compare (Memory.size_of_ctype ct1) (Memory.size_of_ctype ct2) in
  if sz_compare != 0
  then sz_compare
  else Int.compare (enclosing_count g ct1) (enclosing_count g ct2)

let req_ctype = function
  | RET.P ({name = Owned ct; _}) -> ct
  | RET.Q ({name = Owned ct; _}) -> ct
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
     if List.length lbs <> 1
     then Pp.debug 8 (lazy (Pp.item "unexpected number of lower bounds"
       (Pp.list IT.pp lbs)))
     else ();
     let eqs = scan_subterms is_eq qpt.permission
       |> List.filter (fun (lhs, rhs) -> IT.equal i lhs || IT.equal i rhs)
     in
     let lb = match lbs with
         | [] -> IT.int_ 0
         | (lb :: _) -> lb
     in
     List.init (List.length eqs + 1)
       (fun i -> (arrayShift_ (qpt.pointer, ct, add_ (lb, z_ (Z.of_int i))),
           subst (make_subst [(qpt.q, z_ (Z.of_int i))]) qpt.permission))
  | _ -> []

let narrow_quantified_to_witness ptr (q_pt : RET.qpredicate_type) =
  let ct = match q_pt.name with
    | Owned ct -> ct
    | _ -> assert false
  in
  assert (IT.equal q_pt.step (IT.int_ (Memory.size_of_ctype ct)));
  let index = IT.array_pointer_to_index ~base:q_pt.pointer ~item_size:q_pt.step ~pointer:ptr in
  let item_ptr = IT.array_index_to_pointer ~base:q_pt.pointer ~item_ct:ct ~index in
  let sub = make_subst [(q_pt.q, index)] in
  RET.{
    name = q_pt.name;
    pointer = item_ptr;
    permission = IT.subst sub q_pt.permission;
    iargs = List.map (IT.subst sub) q_pt.iargs;
  }

let intersection_action m g ((orig_req, req), req_span) ((orig_res, res), res_span) =
  let res_outer = match orig_res, orig_req with
    | RET.P ({name = PName _; _}), _ -> true
    | _, RET.P ({name = PName _; _}) -> false
    | _, _ ->
      let cmp = compare_enclosing_ct g (req_ctype req) (req_ctype res) in
      if cmp = 0 then begin
        Pp.debug 5 (lazy (Pp.item "unexpected overlap of diff same-rank types"
          (Pp.list RET.pp [req; res])));
        raise NoResult
      end else cmp < 0
  in
  let witnesses = get_witnesses (if res_outer then req else res) in
  let first_witness_ptr = match witnesses with
    | (ptr, _) :: _ -> ptr
    | _ -> assert false
  in
  Pp.debug 8 (lazy (Pp.item "witnesses"
    (Pp.list IT.pp (List.map fst witnesses))));
  let target_res = if res_outer then (orig_res, res) else (orig_req, req) in
  let target_pt = match target_res with
    | (RET.Q ({name = Owned _; _} as q_pt), _) ->
      narrow_quantified_to_witness first_witness_ptr q_pt
    | (RET.P pt, _) -> pt
    | _ -> assert false
  in
  let (target_lb, target_ub_inclusive, target_perm) = match target_pt with
    | {name = Owned ctype; _} ->
      let sz = Memory.size_of_ctype ctype in
      let ptr = target_pt.pointer in
      (ptr, IT.pointer_offset_ (ptr, IT.z_ (Z.of_int (sz - 1))), target_pt.permission)
    | _ -> assert false
  in
  let ok = and_ [target_perm;
    or_ (List.map (fun (w_ptr, perm) -> and_ [perm; lePointer_ (target_lb, w_ptr);
        lePointer_ (w_ptr, target_ub_inclusive)]) witnesses)] in
  let action = if res_outer then Unpack target_pt else Pack target_pt in
  Some (action, ok)

let model_res_spans_or_empty m g req =
  note_failure (model_res_spans (m, g)) req
  |> Option.to_list |> List.concat

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
  let (cond, active_clause) = get_active_clause (m, g) clauses in
  if LogicalArgumentTypes.has_resource (fun _ -> false) active_clause.packing_ft
  then raise NoResult else ();
  (pt, cond)

let null_resource_check m g req = note_failure (do_null_resource_check m g) req

let res_pointer m g = function
  | RET.P pt -> eval_extract "resource pointer" (m, g) is_pointer pt.pointer
  | RET.Q qpt -> eval_extract "resource pointer" (m, g) is_pointer qpt.pointer

let res_pt_present m g = function
  | RET.P pt -> eval_extract "resource permission" (m, g) is_bool pt.permission
  | RET.Q _ -> assert false


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
  let same_name res = RET.same_predicate_name req res in
  match null_resource_check m g req with
  | Some (pt, ok) ->
    (* null resources will also have no span, so skip the rest *)
    let req_ptr = res_pointer m g req in
    if List.exists (fun res -> same_name (RE.request res) &&
      (res_pointer m g (RE.request res) == req_ptr) &&
      res_pt_present m g (RE.request res)) ress
    then [] else [(Pack pt, ok)]
  | None ->
  let res_spans = ress
    |> List.map (fun r -> model_res_spans_or_empty m g (RE.request r))
    |> List.concat in
  let (same, diff) = List.partition (fun (_, (r, _)) -> same_name r) res_spans in
  let req_spans = model_res_spans_or_empty m g req
    |> subtract_closed_spans_from_tagged (List.map fst same)
  in
  let interesting = List.filter_map (fun res_span -> List.find_opt (inter res_span) req_spans
        |> Option.map (fun req_span -> (res_span, req_span)))
    diff
  in
  if List.length interesting == 0
  then
  Pp.debug 7 (lazy (Pp.bold "no span intersections"))
  else ();
  let opts = List.filter_map (fun ((s, res), (s2, req)) ->
    Pp.debug 7 (lazy (Pp.item "resource (partial?) overlap"
      (Pp.list pp_res_span [(fst req, s2); (fst res, s)])));
    intersection_action m g (req, s2) (res, s)
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


