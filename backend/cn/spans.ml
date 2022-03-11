module IT = IndexTerms
module RER = Resources.Requests
module RE = Resources.RE

open IT

exception Failure of Pp.doc

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

let eval_extract msg m_g f x =
  let (m, global) = m_g in
  let open Global in
  match Solver.eval global.struct_decls m x with
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

let model_res_spans m_g res =
  match res with
  | (RER.Point pt) ->
      let perm = eval_extract "resource permission" m_g is_bool pt.permission in
      begin match perm with
      | false -> []
      | true ->
          let ptr = eval_extract "resource pointer" m_g is_pointer pt.pointer in
          let sz = Memory.size_of_ctype pt.ct in
          [(ptr, Z.add ptr (Z.of_int sz))]
      end
  | (RER.QPoint qpt) ->
      let ispans = perm_spans m_g qpt.q qpt.permission in
      if List.compare_length_with ispans 0 == 0
      then []
      else
      if List.exists (fun (lb, rb) -> Option.is_none lb || Option.is_none rb) ispans
      then raise (Failure (Pp.item "unbounded resource interval" (IT.pp qpt.permission)))
      else
      let spans = List.map (fun (i, j) -> (Option.get i, Option.get j)) ispans in
      let ptr = eval_extract "q-resource pointer" m_g is_pointer qpt.pointer in
      let sz = Z.of_int (Memory.size_of_ctype qpt.ct) in
      let offs i = Z.add ptr (Z.mul i sz) in
      (List.map (fun (i, j) -> (offs i, offs (Z.add j (Z.of_int 1)))) spans)
  | _ -> []

let pp_model_spans m g res =
  try
    let s = model_res_spans (m, g) res in
    pp s
  with
    Failure s -> s

let pp_pt_ct pt ct =
  let open Pp in
  IT.pp pt ^^ !^": (" ^^ Sctypes.pp ct ^^ !^") ptr"

let pp_fold pt ct =
  let open Pp in
  !^"fold(" ^^ pp_pt_ct pt ct ^^ !^")"

let inter (i_lb, i_ub) (j_lb, j_ub) =
  Z.lt j_lb i_ub && Z.lt i_lb j_ub

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
  | RER.Point pt -> (pt.pointer, pt.ct, false)
  | RER.QPoint qpt -> (qpt.pointer, qpt.ct, true)
  | _ -> raise (Invalid_argument "foo")

let scan_subterms f t = fold_subterms (fun _ xs t -> match f t with
  | None -> xs
  | Some r -> r :: xs) [] t

(* get concrete objects that (probably) exist in this resource/request *)
let get_witnesses = function
  | RER.Point pt -> [(pt.pointer, pt.permission)]
  | RER.QPoint qpt ->
  let i = sym_ (qpt.q, BT.Integer) in
  let lbs = scan_subterms is_le qpt.permission
    |> List.filter (fun (lhs, rhs) -> IT.equal i rhs)
    |> List.map fst in
  if List.length lbs <> 0
  then Pp.debug 3 (lazy (Pp.item "unexpected number of lower bounds"
    (Pp.list IT.pp lbs)))
  else ();
  let eqs = scan_subterms is_eq qpt.permission
    |> List.filter (fun (lhs, rhs) -> IT.equal i lhs || IT.equal i rhs)
  in
  begin match lbs with
      | [] -> []
      | (lb :: _) ->
  List.init (List.length eqs + 1)
    (fun i -> (arrayShift_ (qpt.pointer, qpt.ct, add_ (lb, z_ (Z.of_int i))),
        subst (make_subst [(qpt.q, z_ (Z.of_int i))]) qpt.permission))
  end
  | _ -> []

let outer_object m g inner_ptr = function
  | RER.Point pt -> Some (pt.pointer, pt.ct, pt.permission)
  | RER.QPoint qpt ->
  (* need to invent an index at which to fold/unfold *)
  begin try
    let qptr = eval_extract "q-resource pointer" (m, g) is_pointer qpt.pointer in
    let iptr = eval_extract "inner object pointer" (m, g) is_pointer inner_ptr in
    let sz = Z.of_int (Memory.size_of_ctype qpt.ct) in
    let m_diff = Z.sub iptr qptr in
    let m_ix = Z.div m_diff sz in
    let m_offs = Z.sub m_diff (Z.mul m_ix sz) in
    let ptr = integerToPointerCast_
        (sub_ (pointerToIntegerCast_ inner_ptr, z_ m_offs)) in
    let offset = array_offset_of_pointer ~base:qpt.pointer ~pointer:ptr in
    let index = array_pointer_to_index ~base:qpt.pointer ~item_size:(z_ sz)
        ~pointer:ptr in
    let ok = and_ [eq_ (rem_ (offset, z_ sz), int_ 0);
        subst (make_subst [(qpt.q, index)]) qpt.permission] in
    Some (ptr, qpt.ct, ok)
  with
    Failure pp -> begin
      Pp.debug 3 (lazy (Pp.item "failed to compute object offsets" pp));
      None
    end
  end
  | _ -> None

let intersection_action m g (req, req_span) (res, res_span) =
  let (req_pt, req_ct, req_qpt) = req_pt_ct req in
  let (res_pt, res_ct, res_qpt) = req_pt_ct (RE.request res) in
  let cmp = compare_enclosing g req_ct res_ct in
  if cmp = 0 then begin
      Pp.debug 3 (lazy (Pp.item "unexpected overlap of diff same-rank types"
        (Pp.list RER.pp [req; RE.request res])));
      None
  end
  else
  let action = if cmp < 0 then "unpack" else "pack" in
  (* the "inner witnesses" are objects of interior type *)
  let witnesses = if cmp < 0
    then get_witnesses req
    else get_witnesses (RE.request res)
  in
  Pp.debug 3 (lazy (Pp.item "witnesses"
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
  Some (action, ptr, ct, ok)

let model_res_spans_or_empty m g req =
  try
    model_res_spans (m, g) req
  with
    Failure pp ->
      Pp.debug 3 (lazy (Pp.item "failed to extract resource span" pp));
      []

let guess_span_intersection_action ress req m g =
  let diff res = not (Resources.same_type_resource req res) in
  let res_ss = List.filter diff ress
    |> List.map (fun r -> List.map (fun s -> (r, s))
        (model_res_spans_or_empty m g (Resources.RE.request r)))
    |> List.concat in
  let req_ss = model_res_spans_or_empty m g req in
  let interesting = List.filter (fun (_, s) -> List.exists (inter s) req_ss) res_ss
    |> List.sort (fun (_, (lb, _)) (_, (lb2, _)) -> Z.compare lb lb2) in
  match interesting with
  | [] ->
  Pp.debug 3 (lazy (Pp.item "spans as expected for inference" (Pp.string "")));
  None
  | _ ->
  List.find_map (fun (r, s) ->
  Pp.debug 3 (lazy (Pp.item "resource partial overlap"
    (Pp.list RER.pp [req; RE.request r])));
  let req_s = List.find (inter s) req_ss in
  intersection_action m g (req, req_s) (r, s)
  ) interesting


let diag_req ress req m g =
  let act = guess_span_intersection_action ress req m g in
  Pp.debug 1 (lazy (match act with
    | None -> Pp.item "guess intersection action: None" (Pp.string "")
    | Some (nm, pt, ct, ok) -> Pp.item ("guessed: do " ^ nm) (pp_pt_ct pt ct)
  ))


