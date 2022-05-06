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

let search_eqs (ms : (string * IT.t) list) (start_ms : (string * IT.t) list) constraints =
  let eqs = List.fold_right add_c_eqs constraints ITMap.empty in
  let start = List.fold_right (fun (nm, t) t_nms -> ITMap.add t (nm :: find_xs t_nms t) t_nms)
    start_ms ITMap.empty in
  let rec seek seen found = function
    | [] -> found
    | (t :: ts) when ITSet.mem t seen -> seek seen found ts
    | (t :: ts) -> seek (ITSet.add t seen) (find_xs start t @ found) (find_xs eqs t @ ts)
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

type constraint_analysis = CA of (SPairSet.t * SSet.t)

let eqs_from_constraints arg_cs ret_cs =
  let starts = List.filter_map get_naming_mappings arg_cs
    |> List.filter (fun (kind, _) -> String.equal kind "start") in
  let ends = List.filter_map get_naming_mappings ret_cs
    |> List.filter (fun (kind, _) -> String.equal kind "end") in
  begin match starts, ends with
    | [(_, start_ms)], [(_, end_ms)] ->
      let end_not_addr = List.filter (fun (nm, _) -> not (starts_with "&" nm)) end_ms in
      let eqs = search_eqs end_not_addr start_ms arg_cs in
      let ret_explicit_eqs = List.fold_right add_c_eqs ret_cs ITMap.empty in
      let end_eqs = List.filter (fun (_, tm) -> ITMap.mem tm ret_explicit_eqs) end_ms
        |> List.map fst in
      Some (CA (SPairSet.of_list eqs, SSet.of_list end_eqs))
    | _ -> None
  end

let pp_pair (s1, s2) =
  let open Pp in
  !^ (wrap s1) ^^ !^ " <-> " ^^ !^ (wrap s2)

let dot_split s = match String.split_on_char '.' s with
  | [v; x; fld] when String.equal x "" -> Some (v, fld)
  | _ -> None

let v_group x y = match dot_split x, dot_split y, String.equal x y with
  | (Some (xr, _), Some (yr, _), _) -> xr ^ "-" ^ yr
  | (Some _, _, _) -> "other"
  | (_, _, true) -> "eq"
  | _ -> "other"

let ensures str = "[[cn::ensures(\"" ^ str ^ "\")]]"

let warn_group nm eqs = if String.equal nm "eq"
  then [ensures ("{" ^ String.concat ", " (List.map (fun (_, _, x) -> x) eqs) ^ "} unchanged")]
  else if String.equal nm "other"
  then List.map (fun (g, x, y) -> ensures (x ^ " == {" ^ y ^ "}@start")) eqs
  else List.map (fun (g, x, y) -> ensures (x ^ " == {" ^ y ^ "}@start")) eqs

let warn_missing_spec_eqs = function
  | [] -> ()
  | per_path_eqs ->
  let data = List.map (function | CA x -> x) per_path_eqs in
  let eq_sets = List.map fst data in
  let inter = List.fold_right SPairSet.inter (List.tl eq_sets) (List.hd eq_sets) in
  let has_ret_eq_sets = List.map snd data in
  let ret_inter = List.fold_right SSet.inter (List.tl has_ret_eq_sets) (List.hd has_ret_eq_sets) in
  let inter_groups = List.map (fun (x, y) -> (v_group x y, x, y)) (SPairSet.elements inter) in
  let act_on = List.filter (fun (_, x, _) -> not (SSet.mem x ret_inter)) inter_groups in
  let act_groups = List.map (fun (g, _, _) -> g) act_on |> SSet.of_list |> SSet.elements in
  let warns = List.map (fun nm -> warn_group nm
        (List.filter (fun (g, _, _) -> String.equal g nm) inter_groups)) act_groups
    |> List.concat in
  let print_warn w = Pp.print stdout (Pp.format [Colour.Yellow] ("### " ^ w)) in
  begin match warns with
  | [] -> ()
  | _ ->
    print_warn "weak specification, also true:";
    List.iter print_warn warns
  end
    


