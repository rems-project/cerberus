module IT = IndexTerms
module BT = BaseTypes
module LC = LogicalConstraints

module ITMap = Map.Make(IT)
module ITSet = Set.Make(IT)

open IT

let make_mappings_info (mappings : (string * IT.t) list) =
    info_ "mappings" (List.map (fun (nm, t) -> info_ "name" [info_ nm []; t]) mappings)

let make_naming pos mappings = info_ "Naming" [info_ pos []; mappings]

let is_info t = match IT.term t with
  | IT.Info (nm, ts) -> Some (nm, ts)
  | _ -> None

let is_named_info nm t = Option.bind (is_info t)
    (fun (t_nm, ts) -> if String.equal t_nm nm then Some ts else None)

let is_str_info t = Option.bind (is_info t) (function
    | (nm, []) -> Some nm
    | _ -> None)

let is_naming_constraint = function
  | LC.T t -> is_named_info "Naming" t
  | _ -> None

let is_str_info_assert ct t = match is_str_info t with
  | Some s -> s
  | None -> (Pp.print stdout (Pp.item "not str info in"
        (Pp.list IT.pp [ct; t])); assert false)

let is_name_tuple t = match is_named_info "name" t with
  | Some [x; y] -> (is_str_info_assert t x, y)
  | _ -> (Pp.print stdout (Pp.item "not name tuple" (IT.pp t)); assert false)

let get_naming_mappings c = match is_naming_constraint c with
  | Some [position_t; mappings_t] ->
    begin match is_named_info "mappings" mappings_t with
      | None -> None
      | Some ms ->
        let ct = info_ "Naming" [position_t; mappings_t] in
        let position = is_str_info_assert ct position_t in
        Some (position, List.map is_name_tuple ms)
    end
  | _ -> None

let find_xs m x = match ITMap.find_opt x m with
  | None -> []
  | Some xs -> xs

let add_eq x y eqs = ITMap.add x (y :: find_xs eqs x) eqs

let rec add_known_eqs c_tm eqs = match is_eq c_tm with
  | Some (lhs, rhs) -> add_eq lhs rhs (add_eq rhs lhs eqs)
  | None -> begin match is_and c_tm with
      | Some ts -> List.fold_right add_known_eqs ts eqs
      | None -> eqs
  end

let add_c_eqs c eqs = match c with
  | LC.T ct -> add_known_eqs ct eqs
  | _ -> eqs

let member_eq_steps t_eqs t = match term t with
    | Struct_op (StructMember (t2, nm)) ->
        t_eqs t @ List.map (fun t -> member_simp_ (bt t) t nm) (t_eqs t2)
    | _ -> t_eqs t

let search_eqs (ms : (string * IT.t) list) (start_ms : (string * IT.t) list) constraints =
  let eqs = List.fold_right add_c_eqs constraints ITMap.empty in
  let start = List.fold_right (fun (nm, t) t_nms -> ITMap.add t (nm :: find_xs t_nms t) t_nms)
    start_ms ITMap.empty in
  let rec seek seen found = function
    | [] -> found
    | (t :: ts) when ITSet.mem t seen -> seek seen found ts
    | (t :: ts) ->
      let eq_ts = member_eq_steps (find_xs eqs) t in
      seek (ITSet.add t seen) (find_xs start t @ found) (eq_ts @ ts)
  in
  let seek2 t = seek ITSet.empty [] [t] in
  List.concat (List.map (fun (end_nm, t) ->
    List.map (fun nm -> (end_nm, nm)) (seek2 t)) ms)

let naming_constraint_eqs constraints c = match get_naming_mappings c with
  | Some (kind, ms) when String.equal kind "end" ->
    begin match List.filter_map get_naming_mappings constraints
        |> List.filter (fun (kind2, _) -> String.equal kind2 "start") with
      | [(_, start_ms)] -> Some (search_eqs ms start_ms constraints)
      | _ -> None
    end
  | _ -> None

(* sigh, apparently standard from OCaml 4.13, which we probably shouldn't assume *)
let starts_with pfx s =
  String.length s >= String.length pfx &&
  String.equal (String.sub s 0 (String.length pfx)) pfx

module SPair = struct
  type s_pair = string * string
  [@@deriving eq, ord]
  type t = s_pair
  let equal = equal_s_pair
  let compare = compare_s_pair
end

module SPairSet = Set.Make(SPair)
module SSet = Set.Make(String)

type constraint_analysis = CA of (SPairSet.t * SSet.t * string list)

let eqs_from_constraints arg_cs ret_cs =
  let starts = List.filter_map get_naming_mappings arg_cs
    |> List.filter (fun (kind, _) -> String.equal kind "start") in
  let ends = List.filter_map get_naming_mappings ret_cs
    |> List.filter (fun (kind, _) -> String.equal kind "end") in
  begin match starts, ends with
    | [(_, start_ms)], [(_, end_ms)] ->
      let end_not_addr = List.filter (fun (nm, _) -> not (starts_with "&" nm)) end_ms in
(*
      Pp.debug 3 (lazy (Pp.item "eqs_from_constraints start terms"
          (Pp.list (fun (_, t) -> IT.pp t) start_ms)));
      Pp.debug 3 (lazy (Pp.item "eqs_from_constraints end (not addr) terms"
          (Pp.list (fun (_, t) -> IT.pp t) end_not_addr)));
*)
      let eqs = search_eqs end_not_addr start_ms arg_cs in
      let ret_explicit_eqs = List.fold_right add_c_eqs ret_cs ITMap.empty in
      let end_eqs = List.filter (fun (_, tm) -> ITMap.mem tm ret_explicit_eqs) end_ms
        |> List.map fst in
      Some (CA (SPairSet.of_list eqs, SSet.of_list end_eqs, List.map fst start_ms))
    | _ -> None
  end

let pp_pair (s1, s2) =
  let open Pp in
  !^ (wrap s1) ^^ !^ " <-> " ^^ !^ (wrap s2)

let dot_split s = match String.split_on_char '.' s with
  | [v; x; fld] when String.equal x "" -> Some (v, fld)
  | _ -> None

module Eq_Kinds = struct
  type eq_kinds =
    | Eq
    | PredRet of (string * string)
    | Other
    [@@deriving eq, ord]
  type t = eq_kinds
  let equal = equal_eq_kinds
  let compare = compare_eq_kinds
end
open Eq_Kinds
module EKSet = Set.Make(Eq_Kinds)

let v_group x y = match dot_split x, dot_split y, String.equal x y with
  | (Some (xr, xf), Some (yr, yf), _) when String.equal xf yf -> PredRet (xr, yr)
  | (Some _, _, _) -> Other
  | (_, _, true) -> Eq
  | _ -> Other

let s_delim = Pp.format [] "\""

let ensures elts =
  let open Pp in
  !^"[[cn::ensures(" ^^ flow comma (List.map (fun e -> s_delim ^^ e ^^ s_delim) elts) ^^ !^ ")]]"

let unchanged x =
  let open Pp in
  !^"{" ^^ !^ x ^^ !^ "} unchanged"

let warn_other (_, x, y) =
  let open Pp in
  [ensures [!^ x ^^^ !^ "== {" ^^ !^ y ^^ !^ "}@start"]]

let warn_group names gp = match gp with
  | (Eq, _, _) :: _ -> [ensures (List.map (fun (_, _, x) -> unchanged x) gp)]
  | [(PredRet _, _, _)] -> warn_other (List.hd gp)
  | (PredRet (x, y), _, _) :: _ ->
    let flds = List.map (fun (_, x, _) -> snd (Option.get (dot_split x))) gp
        |> SSet.of_list in
    let orig_flds = List.filter_map dot_split names
        |> List.filter (fun (pred, _) -> String.equal pred y) |> List.map snd |> SSet.of_list in
    assert (SSet.subset flds orig_flds);
    let excludes = SSet.diff orig_flds flds in
    let open Pp in
    let exc = if SSet.cardinal excludes == 0 then !^"{}"
      else !^"{/" ^^^ flow comma (List.map (format []) (SSet.elements excludes)) ^^ !^ "}" in
    [ensures [!^ x ^^^ !^"==" ^^^ exc ^^^ !^ y]]
  | _ -> assert false

let debug_pp_pair (x, y) =
  let open Pp in
  !^ x ^^ !^ "<==" ^^^ !^ y

let warn_missing_spec_eqs = function
  | [] -> ()
  | per_path_eqs ->
  let data = List.map (function | CA x -> x) per_path_eqs in
  let eq_sets = List.map (fun (eqs, _, _) -> eqs) data in
(*
  Pp.debug 3 (lazy (Pp.item "spec eqs eq_sets" (Pp.list (fun xs ->
        Pp.brackets (Pp.list debug_pp_pair (SPairSet.elements xs))) eq_sets)));
*)
  let inter = List.fold_right SPairSet.inter (List.tl eq_sets) (List.hd eq_sets) in
  let has_ret_eq_sets = List.map (fun (_, rets, _) -> rets) data in
  let start_names = List.hd (List.map (fun (_, _, names) -> names) data) in
  let ret_inter = List.fold_right SSet.inter (List.tl has_ret_eq_sets) (List.hd has_ret_eq_sets) in
  let eqs_w_group = List.map (fun (x, y) -> (v_group x y, x, y)) (SPairSet.elements inter) in
  let novel = List.filter (fun (_, x, _) -> not (SSet.mem x ret_inter)) eqs_w_group in
  let act_groups = novel |> List.map (fun (g, _, _) -> g)
    |> List.filter (fun g -> not (Eq_Kinds.equal Other g)) |> EKSet.of_list |> EKSet.elements in
  let group_eqs = act_groups
    |> List.map (fun g -> List.filter (fun (g2, _, _) -> equal_eq_kinds g g2) eqs_w_group) in
  let other_eqs = List.filter (fun (g, _, _) -> Eq_Kinds.equal Other g) eqs_w_group in
  let warns = List.map (warn_group start_names) group_eqs @ List.map warn_other other_eqs in
  begin match List.concat warns with
  | [] -> ()
  | xs ->
    let open Pp in
    print stdout (format [Yellow] ("### weak specification, also true:"));
    List.iter (fun w -> print stdout (format [Yellow] "###" ^^^ w)) xs
  end


