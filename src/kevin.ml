(* kevin.ml - a C11 candidate execution layout tool *)
(* (C) J Pichon 2019 *)
(* call "neato" on the output *)
(* this assumes 'asw' is pretty simple *)

let option_map f xs =
  let rec g l = function
  | [] -> List.rev l
  | x :: xs ->
    let l' = (match f x with None -> l | Some y -> y :: l) in
    g l' xs in
  g [] xs

module Ord_pair (X : Set.OrderedType) (Y : Set.OrderedType) : Set.OrderedType with type t = X.t * Y.t = struct
  type t = X.t * Y.t
  let compare ((x1, x2) : t) (y1, y2) =
    match X.compare x1 y1 with
    | 0 -> Y.compare x2 y2
    | v -> v
end

module Ord_triple (X : Set.OrderedType) (Y : Set.OrderedType) (Z : Set.OrderedType) : Set.OrderedType with type t = X.t * Y.t * Z.t = struct
  type t = X.t * Y.t * Z.t
  let compare ((x1, x2, x3) : t) (y1, y2, y3) =
    match X.compare x1 y1 with
    | 0 ->
      (match Y.compare x2 y2 with
      | 0 -> Z.compare x3 y3
      | v -> v)
    | v -> v
end

let rec list_compare f xs ys =
  match (xs, ys) with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | x :: xs', y :: ys' ->
    (match f x y with
    | 0 -> list_compare f xs' ys'
    | v -> v)

module Ord_list (X : Set.OrderedType) : Set.OrderedType with type t = X.t list = struct
  type t = X.t list
  let rec compare (xs : t) (ys) =
    list_compare X.compare xs ys
end


module Real_map (X : Set.S) (Y : Set.S) = struct
  let map (f : X.elt -> Y.elt) (s : X.t) =
    X.fold (fun x s' -> Y.add (f x) s') s Y.empty
end

module Set_union (X : Set.S) = struct
  let union (xs : X.t list) =
    List.fold_left X.union X.empty xs
end

module Union (Y : Set.S) = struct
  let union (xs : Y.t list) =
    List.fold_left Y.union Y.empty xs
end

module Powerset_bind (X : Set.S) (Y : Set.S) : sig val bind : (X.elt -> Y.t) -> X.t -> Y.t end = struct
  module U = Union(Y)

  let bind (f : X.elt -> Y.t) (s : X.t) =
    U.union (List.map f (X.elements s))
end

module Option_set_bind (X : Set.S) (Y : Set.S) = struct

  let bind (f : X.elt -> Y.elt option) (s : X.t) =
    Y.of_list (option_map f (X.elements s))
end

module Map_of_list (X : Map.S) = struct
  let of_list (l : 'a) =
    List.fold_left
      (fun mo (x, v) ->
        match mo with
        | None -> None
        | Some m ->
          (match X.find_opt x m with
          | None -> Some (X.add x v m)
          | Some _ -> None))
      (Some X.empty)
      l
end

module Collect_in_map (X : Map.S) (Y : Set.S) = struct
  let collect index_of set =
    Y.fold
      (fun a m ->
        let ix = index_of a in
        match X.find_opt ix m with
        | None -> X.add ix (Y.singleton a) m
        | Some s -> X.add ix (Y.add a s) m)
      set
      X.empty
end

module Collect_in_map_fun (X : Map.S) (Y : Set.S) (Z : Set.S) = struct
  let set_map_of f s =
    Y.fold
      (fun x map ->
        let (k, v) = f x in
        match X.find_opt k map with
        | None -> X.add k (Z.singleton v) map
        | Some acts -> X.add k (Z.add v acts) map)
      s
      X.empty
end

type rational = int * int

let rec gcd a b = if b = 0 then a else gcd b (a mod b)

module Rational = struct
  type t = rational

  let simplify (n, d) =
    let n = n * (d / abs d) in
    let d = abs d in
    let g = abs (gcd n d) in
    (n / g, d / g)

  let compare (x : t) y =
    let (n1, d1) = simplify x in
    let (n2, d2) = simplify y in
    Pervasives.compare (n1 * d2) (n2 * d1)

  let max (n1, d1) (n2, d2) =
    if n1 * d2 < d1 * n2 then (n2, d2) else (n1, d1)

  let min (n1, d1) (n2, d2) =
     if n1 * d2 < d1 * n2 then (n1, d1) else (n2, d2)

  let add (n1, d1) (n2, d2) =
    simplify (n1 * d2 + d1 * n2, d1 * d2)

  let addn rs =
    List.fold_left
      add
      (0, 1)
      rs

  let sub x (n2, d2) =
    add x (- n2, d2)

  let mult (n1, d1) (n2, d2) =
    simplify (n1 * n2, d1 * d2)

  let div (n1, d1) (n2, d2) =
    simplify (n1 * d2, d1 * n2)

  let div_int (n, d) k = simplify (n, d * k)

  let string_of_rational (n, d) =
    string_of_int n ^ "/" ^ string_of_int d

  let float_of_rat (n, d) =
    float_of_int n /. float_of_int d
end

module Dot = struct

type node_attr =
  | NColor of string
  | NLabel of string
  | NShape of string
  | NHtmlLabel of string
  | NMargin of string
  | NPos of float * float

type node_info = {
  nname : string;
  nattrs: node_attr list;
}

(* start of stolen from Batteries *)
let explode s =
  let rec loop i l =
    if i < 0 then
      l
    else
      (* i >= 0 && i < length s *)
      loop (i - 1) (String.get s i :: l)
  in
  loop (String.length s - 1) []

let implode l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
    | [] -> ()
    | c :: l -> Bytes.set res i c; imp (i + 1) l in
  imp 0 l;
  Bytes.unsafe_to_string res
(* end of Batteries *)

(* TODO: should escape value *)
let escape s : string =
  implode
    (List.concat
      (List.map
        (function
        | '"' -> ['\\'; '"']
        | '\\' -> ['\\'; '\\']
        | c -> [c])
        (explode s)))

let string_of_str_attr name value =
  name ^ "=\"" ^ escape value ^ "\""

let string_of_nattr = function
  | NColor c -> string_of_str_attr "color" c
  | NLabel l -> string_of_str_attr "label" l
  | NShape s -> string_of_str_attr "shape" s
  | NHtmlLabel l -> "label=<" ^ l ^ ">"
  | NMargin s -> string_of_str_attr "margin" s
  | NPos (x, y) -> string_of_str_attr "pos" (string_of_float x ^ "," ^ string_of_float y ^ "!")

let string_of_node (n : node_info) =
  n.nname
  ^ match n.nattrs with
    | [] -> ";"
    | _ ->
      " ["
      ^ String.concat "," (List.map string_of_nattr n.nattrs)
      ^ "];"

type edge_attr =
  | ELabel of string
  | EColor of string
  | Lhead of string
  | Ltail of string
  | EStyle of string

type edge_info = {
  src : string;
  tgt: string;
  eattrs: edge_attr list;
}

let string_of_eattr coloro = function
  | EColor _ ->
    begin match coloro with
      | Some c -> string_of_str_attr "color" c
      | None -> assert false
    end
  | ELabel l -> "label=<" ^ l ^ ">"
  | Lhead n -> string_of_str_attr "lhead" n
  | Ltail n -> string_of_str_attr "ltail" n
  | EStyle s -> string_of_str_attr "style" s

let string_of_edge e =
  let coloro =
    match option_map (function EColor s -> Some s | _ -> None) e.eattrs with
      | [] -> None
      | [c] -> Some c
      | cs ->
        prerr_string "multiple colours for edge; took last\n";
        Some (List.hd (List.rev cs)) in
  e.src ^ " -> " ^ e.tgt
  ^ (match e.eattrs with
    | [] -> ""
    | _ ->
      " ["
      ^ String.concat ","
        (List.map
           (string_of_eattr coloro)
           e.eattrs)
      ^ "];")

type rankdir =
  | TB
  | LR

type graph_attr =
  | Compound
  | GLabel of string
  | Rankdir of rankdir
  | Splines of bool
  | Overlap of bool

let string_of_bool b =
  if b then "true" else "false"

let string_of_graph_attr = function
  | Compound -> string_of_str_attr "compound" "true" ^ ";"
  | GLabel s ->
    string_of_str_attr "label" s ^ ";\n"
    ^ "labelloc=top;\n"
    ^ "labeljust=left;"
  | Rankdir TB -> "rankdir=TB;";
  | Rankdir LR -> "rankdir=LR;"
  | Splines b -> "splines=" ^ string_of_bool b ^ ";"
  | Overlap b -> "overlap=" ^ string_of_bool b ^ ";"

type graph_element =
  | Node of node_info
  | Edge of edge_info
  | Graph_attr of graph_attr
  | Subgraph of string * graph_element list

type graph = graph_element list

let indent indentlvl s =
  String.make (2 * indentlvl) ' ' ^ s

let rec string_of_cluster_element indentlvl = function
  | Node ni -> indent indentlvl (string_of_node ni)
  | Edge ei -> indent indentlvl (string_of_edge ei)
  | Graph_attr ca -> indent indentlvl (string_of_graph_attr ca)
  | Subgraph (name, ces) ->
    indent indentlvl ("subgraph " ^ name ^ " {\n")
    ^ String.concat "" (List.map (fun x -> string_of_cluster_element (indentlvl + 1) x ^ "\n") ces)
    ^ indent indentlvl ("}\n")

let string_of_digraph s =
  "digraph G {\n"
  ^ String.concat "" (List.map (fun x -> string_of_cluster_element 1 x ^ "\n") s)
  ^ "}\n"

end


module Int = struct
  type t = int
  let compare (x : t) y = Pervasives.compare x y
end

module Int_map = Map.Make(Int)

let pair_compare f1 f2 (a1, b1) (a2, b2) =
  match f1 a1 a2 with
  | 0 -> f2 b1 b2
  | v -> v

module Aid = struct
  type t = Bmc_types.aid
  let compare (x : t) y =
    Pervasives.compare x y
end

module Tid = struct
  type t = Bmc_types.tid
  let compare (x : t) y =
    Pervasives.compare x y
end

module Memory_order2 = struct
  type t = Bmc_types.memory_order
  let compare (x : t) y =
    Pervasives.compare x y
end

module Z3_location = struct
  type t = Bmc_types.z3_location
  let compare (x : t) y =
    Pervasives.compare x y
end

module Z3_value = struct
  type t = Bmc_types.z3_value
  let compare (x : t) y =
    Pervasives.compare x y
end

module Action = struct
  let action_rank = function
  | Bmc_types.Load _ -> 0
  | Bmc_types.Store _ -> 1
  | Bmc_types.RMW _ -> 2
  | Bmc_types.Fence _ -> 3

  type t = Bmc_types.action
  (* TODO: do we care about types at this point? *)
  let compare (x : t) y =
    match x, y with
    | Bmc_types.Load (a1, t1, m1, l1, v1, ty1), Bmc_types.Load (a2, t2, m2, l2, v2, ty2) ->
      pair_compare Aid.compare (pair_compare Tid.compare (pair_compare Memory_order2.compare (pair_compare Z3_location.compare Z3_value.compare)))  (a1, (t1, (m1, (l1, v1)))) (a2, (t2, (m2, (l2, v2))))
    | Bmc_types.Store (a1, t1, m1, l1, v1, ty1), Bmc_types.Store (a2, t2, m2, l2, v2, ty2) ->
      pair_compare Aid.compare (pair_compare Aid.compare (pair_compare Memory_order2.compare (pair_compare Z3_location.compare Z3_value.compare)))  (a1, (t1, (m1, (l1, v1)))) (a2, (t2, (m2, (l2, v2))))
    | Bmc_types.RMW (a1, t1, m1, l1, v11, v21, ty1), Bmc_types.RMW (a2, t2, m2, l2, v12, v22, ty2) ->
      pair_compare Aid.compare (pair_compare Tid.compare (pair_compare Memory_order2.compare (pair_compare Z3_location.compare (pair_compare Z3_value.compare Z3_value.compare))))  (a1, (t1, (m1, (l1, (v11, v21))))) (a2, (t2, (m2, (l2, (v12, v22)))))
    | Bmc_types.Fence (a1, t1, m1), Bmc_types.Fence (a2, t2, m2) ->
      pair_compare Aid.compare (pair_compare Tid.compare Memory_order2.compare)  (a1, (t1, m1)) (a2, (t2, m2))
    | _, _ -> Pervasives.compare (action_rank x) (action_rank y)
end

module Action_set = Set.Make(Action)

module Aid_set = Set.Make(Aid)
module String_map = Map.Make(String)

module Aid_times_aid = Ord_pair(Aid)(Aid)
module Aid_times_aid_set = Set.Make(Aid_times_aid)
module Aid_times_aid_map = Map.Make(Aid_times_aid)

module Pos = struct
  type t = rational * int
  let compare (x : t) y =
    Pervasives.compare x y
end

module Action_times_pos = Ord_pair(Action)(Pos)

module Action_times_pos_set = Set.Make(Action_times_pos)

let tid_of_action = function
| Bmc_types.Load (_, t, _, _, _, _) -> t
| Bmc_types.Store (_, t, _, _, _, _) -> t
| Bmc_types.RMW (_, t, _, _, _, _, _) -> t
| Bmc_types.Fence (_, t, _) -> t

let aid_of_action = function
| Bmc_types.Load (a, _, _, _, _, _) -> a
| Bmc_types.Store (a, _, _, _, _, _) -> a
| Bmc_types.RMW (a, _, _, _, _, _, _) -> a
| Bmc_types.Fence (a, _, _) -> a

let string_of_c_memory_order = function
| Cmm_csem.NA -> "na"
| Cmm_csem.Seq_cst -> "sc"
| Cmm_csem.Relaxed -> "rlx"
| Cmm_csem.Release -> "rel"
| Cmm_csem.Acquire -> "acq"
| Cmm_csem.Consume -> "con"
| Cmm_csem.Acq_rel -> "acqrel"

let string_of_linux_memory_order = function
| Linux.Once -> "once"
| Linux.Acquire0 -> "acq"
| Linux.Release0 -> "rel"
| Linux.Rmb -> "rmb"
| Linux.Wmb -> "wmb"
| Linux.Mb -> "mb"
| Linux.RbDep -> "rbdep"
| Linux.RcuLock -> "rculock"
| Linux.RcuUnlock -> "rcuunlock"
| Linux.SyncRcu -> "syncrcu"

let string_of_memory_order = function
| Bmc_types.C_mem_order mo -> string_of_c_memory_order mo
| Bmc_types.Linux_mem_order mo -> string_of_linux_memory_order mo

(* TODO: change? *)
let string_of_location loc_map loc =
  let default =
    begin match Z3.Expr.get_args loc with
    | [a] ->
        Printf.sprintf "(%s)" (Z3.Expr.to_string a)
    | [a1;a2] -> Printf.sprintf "(%s.%s)" (Z3.Expr.to_string a1) (Z3.Expr.to_string a2)
    | _ -> Z3.Expr.to_string loc
    end in
  match Pmap.lookup loc loc_map with
  | Some s -> s (*^ default*)
  | None -> default

(* TODO: change? *)
let string_of_value expr =
  let open Z3 in
  let open Bmc_sorts in
  assert (Expr.get_num_args expr = 1);
  let arg = List.hd (Expr.get_args expr) in
  if (Sort.equal (Expr.get_sort arg) (LoadedInteger.mk_sort)) then
    begin
      if (Boolean.is_true
        (Expr.simplify (LoadedInteger.is_unspecified arg) None)) then
        "?"
      else
      Expr.to_string (List.hd (Expr.get_args arg))
    end
  else if (Sort.equal (Expr.get_sort arg) (LoadedPointer.mk_sort)) then
    begin
      if (Boolean.is_true
        (Expr.simplify (LoadedPointer.is_unspecified arg) None)) then
        "?"
      else begin
        PointerSort.pp (List.hd (Expr.get_args arg))
      end
    end
  else
    Expr.to_string arg

let string_of_aid a =
  String.make 1 (Char.chr ((Char.code 'a') + a))

let string_of_action loc_map = function
| Bmc_types.Load (a, t, mo, x, v, ty) -> string_of_aid a ^ ":R" ^ string_of_memory_order mo ^ " " ^ string_of_location loc_map x ^ "=" ^ string_of_value v
| Bmc_types.Store (a, t, mo, x, v, ty) -> string_of_aid a ^ ":W" ^ string_of_memory_order mo ^ " " ^ string_of_location loc_map x ^ "=" ^ string_of_value v
| Bmc_types.RMW (a, t, mo, x, v1, v2, ty) -> string_of_aid a ^ ":RMW" ^ string_of_memory_order mo ^ " " ^ string_of_location loc_map x ^ " " ^ string_of_value v1 ^ "->" ^ string_of_value v2
| Bmc_types.Fence (a, t, mo) -> string_of_aid a ^ ":F" ^ string_of_memory_order mo

let aid_times_aid_set_of_rel rel =
  Aid_times_aid_set.of_list (List.map (fun (a, a') -> (aid_of_action a, aid_of_action a')) rel)

module Layout = struct

let make_line sb laid_out_aids to_lay_out =
  let line =
    Action_set.filter
      (fun a ->
        Aid_times_aid_set.for_all (fun (aid, aid') -> not (aid' = aid_of_action a) || Aid_set.mem aid laid_out_aids ) sb)
      to_lay_out in
  let line_aids =
    Aid_set.of_list (List.map aid_of_action (Action_set.elements line)) in
  (line, line_aids, Action_set.diff to_lay_out line)

let vertical_layout sb acts =
  let rec f (laid_out, laid_out_aids, to_lay_out) =
    if Action_set.is_empty to_lay_out then laid_out
    else let (line, line_aids, rest) = make_line sb laid_out_aids to_lay_out in
      f (laid_out @ [line], Aid_set.union laid_out_aids line_aids, rest) in
  f ([], Aid_set.empty, acts)

module Aid_map = Map.Make(Aid)

module Aid_list = Ord_list(Aid)

module Aid_list_set = Set.Make(Aid_list)

module Real_map_action_set_aid_list_set = Real_map(Action_set)(Aid_list_set)

module Aid_times_aid_list = Ord_pair(Aid)(Aid_list)

module Aid_times_aid_list_set = Set.Make(Aid_times_aid_list)

module Option_bind_aid_list_set_aid_times_aid_list_set = Option_set_bind(Aid_list_set)(Aid_times_aid_list_set)

type reduction_mode =
| RM_no_reduction
| RM_transitive_reduction
| RM_transitive_reduction_over_sb

type colour = string

type edge_display_mode =
| ED_hide
| ED_show of reduction_mode * colour

type layout =
| L_naive
| L_frac

type display_info = {
  repulsion_factor : rational;
  mask : edge_display_mode String_map.t;
  layout : layout;
  step_div : int;
  iterations : int;
  margin : rational;
  x_factor : rational;
  y_factor : rational;
}

let rec last = function
| [] -> assert false
| [x] -> x
| _ :: xs -> last xs

let columns_of sb acts =
  let next columns =
    Aid_list_set.map
      (fun column ->
        let bot = List.hd column in
        let top = last column in
        let preds = Aid_times_aid_set.filter (fun (aid, aid') -> aid' = bot && Aid_times_aid_set.cardinal (Aid_times_aid_set.filter (fun (aid'', _) -> aid'' = aid) sb) = 1) sb in
        let succs = Aid_times_aid_set.filter (fun (aid, aid') -> aid = top && Aid_times_aid_set.cardinal (Aid_times_aid_set.filter (fun (_, aid'') -> aid'' = aid') sb) = 1) sb in
        (if Aid_times_aid_set.cardinal preds = 1 then match Aid_times_aid_set.choose_opt preds with None -> assert false | Some (aid, _) -> [aid] else [])
        @ column
        @ (if Aid_times_aid_set.cardinal succs = 1 then match Aid_times_aid_set.choose_opt succs with None -> assert false| Some (_, aid) -> [aid] else []))
      columns in
  let rec f columns =
    let columns' = next columns in
    if Aid_list_set.equal columns columns' then columns
    else f columns' in
  let columns = f (Real_map_action_set_aid_list_set.map (fun a -> [aid_of_action a]) acts) in
  let non_singleton_columns =
    Option_bind_aid_list_set_aid_times_aid_list_set.bind
      (function
      | [] -> assert false
      | [_] -> None
      | hd :: tail -> Some (hd, tail)) columns in
  let columns_map =
    List.fold_left
      (fun columns_map column ->
        let bot = List.hd column in
        let top = last column in
        List.fold_left (fun m x -> Aid_map.add x (bot, top) m) columns_map column)
      Aid_map.empty
      (Aid_list_set.elements columns) in
  (non_singleton_columns, columns_map)

type formula =
  | F_var of Bmc_types.aid
  | F_const of rational
  | F_plus of formula list
  | F_minus of formula * formula
  | F_times of formula * formula
  | F_div of formula * formula

module Formula = struct
  type t = formula
  let compare (x : t) y = Pervasives.compare x y

  let rec string_of_formula_aux = function
  | F_var aid -> (string_of_aid aid, true)
  | F_const r -> (Rational.string_of_rational r, true)
  | F_plus fs ->
    (match fs with
    | [] -> ("0", true)
    | [f] -> string_of_formula_aux f
    | _ -> (String.concat " + " (List.map string_of_formula_protected fs), false))
  | F_minus (f1, f2) ->
     (string_of_formula_protected f1 ^ " - " ^ string_of_formula_protected f2 , false)
  | F_times (f1, f2) ->
    (string_of_formula_protected f1 ^ " * " ^ string_of_formula_protected f2 , false)
  | F_div (f1, f2) ->
    (string_of_formula_protected f1 ^ " / " ^ string_of_formula_protected f2 , false)
  and string_of_formula_protected f =
    let (s, str) = string_of_formula_aux f in
    if str then s else "(" ^ s ^ ")"
  let string_of_formula f =
    let (s, _) = string_of_formula_aux f in s
end

module Formula_set = Set.Make(Formula)

let rec simplify_formula = function
| F_var x -> F_var x
| F_const (n, d) -> if n = 0 then F_const (0, 1) else F_const (n, d)
| F_plus fs ->
  let fs = List.map simplify_formula fs in
  let const_part = Rational.addn (option_map (function F_const (n, d) -> Some (n, d) | _ -> None) fs) in
  let non_consts = option_map (function F_const _ -> None | f -> Some f) fs in
  (match const_part with
  | (0, _) -> (match non_consts with [] -> F_const (0, 1) | [f] -> f | _ -> F_plus non_consts)
  | _ ->
    let f = F_const const_part in
    (match non_consts with [] -> f | _ -> F_plus (non_consts @ [f])))
| F_minus (f1, f2) ->
  let f1 = simplify_formula f1 in
  let f2 = simplify_formula f2 in
  if Formula.compare f1 f2 = 0 then F_const (0, 1)
  else
    (match f1, f2 with
    | _, F_const (0, _) -> f1
    | F_const r1, F_const r2 -> F_const (Rational.sub r1 r2)
    | _ -> F_minus (f1, f2))
| F_times (f1, f2) ->
  let f1 = simplify_formula f1 in
  let f2 = simplify_formula f2 in
  (match f1, f2 with
  | F_const (0, _), _ -> F_const (0, 1)
  | _, F_const (0, _) -> F_const (0, 1)
  | F_const (1, _), _ -> f2
  | _, F_const (1, _) -> f1
  | _, _ -> F_times (f1, f2))
| F_div (f1, f2) ->
  let f1 = simplify_formula f1 in
  let f2 = simplify_formula f2 in
  (match f1, f2 with
  | F_const (0, _), _ -> F_const (0, 1)
  | _, F_const (1, _) -> f1
  | _, _ -> F_div (f1, f2))

let rec derivative x = function
| F_var y -> if x = y then F_const (1, 1) else F_const (0, 1)
| F_const _ -> F_const (0, 1)
| F_plus fs -> F_plus (List.map (derivative x) fs)
| F_minus (f1, f2) -> F_minus (derivative x f1, derivative x f2)
| F_times (f1, f2) -> F_plus [F_times (derivative x f1, f2); F_times (f1, derivative x f2)]
| F_div (f1, f2) -> F_div (F_minus (F_times (derivative x f1, f2), F_times (f1, derivative x f2)), F_times (f2, f2))

let f_square f = F_times (f, f)

let width_of_action loc_map act =
  String.length (string_of_action loc_map act)

let repulse repulsion_factor a_rep a'_rep width =
  F_times (F_div (F_const repulsion_factor, f_square (F_minus (F_var a_rep, F_var a'_rep))), F_const (width, 7))

let attract a a' =
  f_square (F_minus (F_var a, F_var a'))

module Real_map_aid_times_aid_to_formula_set = Option_set_bind(Aid_times_aid_set)(Formula_set)

let equation_of_act display_info loc_map sb columns_map line act =
  (* TODO: should take label size into account *)
  let trans a =
    match Aid_map.find_opt a columns_map with
    | None -> assert false
    | Some v -> v in
  let a = aid_of_action act in
  let (a_top, a_bot) = trans a in
  let a_w = width_of_action loc_map act in
  assert (a = a_top);
  let repulsion =
    option_map
      (fun act' ->
        let a' = aid_of_action act' in
        let a'_w = width_of_action loc_map act' in
        if a' = a then None
        else
          let a'_rep = fst (trans a') in
          Some (repulse display_info.repulsion_factor a_top a'_rep (a_w + a'_w)))
      (Action_set.elements line) in
  let attraction_up =
    Real_map_aid_times_aid_to_formula_set.bind
      (fun (a1, a2) -> if a2 = a_top then let (a1', _) = trans a1 in Some (attract a1' a_top) else None)
      sb in
  let attraction_down =
    Real_map_aid_times_aid_to_formula_set.bind
      (fun (a1, a2) -> if a1 = a_bot then Some (attract a_bot a2) else None)
      sb in
  let attraction = (Formula_set.elements attraction_up) @ (Formula_set.elements attraction_down) in
  (* prerr_string ("|attractions " ^ string_of_aid a ^ "| = " ^ string_of_int (List.length attraction) ^ "\n"); *)
  let f = F_plus (repulsion @ attraction) in
  let f' = simplify_formula (derivative a_top f) in
  (*prerr_string ("f(" ^ string_of_aid a ^ ") = " ^ Formula.string_of_formula f ^ "\n"); flush stderr;
  prerr_string ("f'(" ^ string_of_aid a ^ ") = " ^ Formula.string_of_formula f' ^ "\n"); flush stderr;*)
  simplify_formula (F_minus (F_const (0, 1), f'))

let rec evaluate map x = function
| F_var x -> Aid_map.find x map
| F_const c -> c
| F_plus fs -> Rational.addn (List.map (evaluate map x) fs)
| F_minus (f1, f2) -> Rational.sub (evaluate map x f1) (evaluate map x f2)
| F_times (f1, f2) -> Rational.mult (evaluate map x f1) (evaluate map x f2)
| F_div (f1, f2) -> Rational.div (evaluate map x f1) (evaluate map x f2)

module Aid_map_of_list = Map_of_list(Aid_map)

let equations_map_of display_info loc_map sb columns_map lines =
  let x =
    Aid_map_of_list.of_list
      (List.concat
        (List.map
          (fun line ->
            option_map
              (fun act ->
                let aid = aid_of_action act in
                let (aid', _) = Aid_map.find aid columns_map in
                if Aid.compare aid aid' <> 0 then None
                else
                  let eqn = equation_of_act display_info loc_map sb columns_map line act in
                  Some (aid, eqn))
                (Action_set.elements line))
          lines)) in
  match x with
  | None -> assert false
  | Some map -> map

module Aid_times_pos = Ord_pair(Aid)(Pos)

module Aid_times_pos_set = Set.Make(Aid_times_pos)

module Real_map_action_times_pos_set_to_aid_times_pos_set = Real_map(Action_times_pos_set)(Aid_times_pos_set)

let obstruction_set_of actposs columns =
  let aidposs0 = Real_map_action_times_pos_set_to_aid_times_pos_set.map (fun (act, pos) -> (aid_of_action act, pos)) actposs in
  match Aid_map_of_list.of_list (Aid_times_pos_set.elements aidposs0) with
  | None -> assert false
  | Some aid_map ->
    Aid_times_aid_list_set.fold
      (fun (e, xs) aidposs ->
        match Aid_map.find_opt e aid_map with
        | None -> aidposs
        | Some (x, y) ->
          let (aidposs', _) =
            List.fold_left
              (fun (aidposs, y) aid -> (Aid_times_pos_set.add (aid, (x, y)) aidposs, y + 1) )
              (aidposs, y + 1)
              xs in
          aidposs')
      columns
      aidposs0

let obstruction obstruction_set pos =
  match Aid_times_pos_set.choose_opt (Aid_times_pos_set.filter (fun (_, pos') -> Pos.compare pos pos' = 0) obstruction_set) with
  | None -> None
  | Some (aid, _) -> Some aid

module Rational_map = Map.Make(Rational)

module Action_times_int = Ord_pair(Action)(Int)

module Action_times_int_set = Set.Make(Action_times_int)

module Real_map_action_times_int_set_to_action_times_pos = Real_map(Action_times_int_set)(Action_times_pos_set)

module Action_times_pos_set_union = Union(Action_times_pos_set)

module Collect_actions = Collect_in_map_fun(Rational_map)(Action_times_pos_set)(Action_times_int_set)

let make_unit_spacing actposs =
  let act_map = Collect_actions.set_map_of (fun (act, (x, y)) -> (x, (act, y))) actposs in
  let actss =
    List.mapi
      (fun x (_, acts) ->
        Real_map_action_times_int_set_to_action_times_pos.map (fun (act, y) -> (act, ((x, 1), y))) acts)
      (Rational_map.bindings act_map) in
  Action_times_pos_set_union.union actss

let init_var_map_frac sb (columns, columns_map) lines =
  let add_line actposs y line =
    let obstruction_set = obstruction_set_of actposs columns in
    let (actposs', _) =
      List.fold_left
        (fun (actposs, x) act ->
          let aid = aid_of_action act in
          let x' = Rational.add (1, 1) x in
          match obstruction obstruction_set (x', y) with
          | None ->
            (match Aid_map.find_opt aid columns_map with
            | None -> (Action_times_pos_set.add (act, (x', y)) actposs, x')
            | Some (bot_aid, _) ->
              if aid = bot_aid then (Action_times_pos_set.add (act, (x', y)) actposs, x')
              else
                let (x'', _) = snd (Action_times_pos_set.choose (Action_times_pos_set.filter (fun (act, _) -> aid_of_action act = bot_aid) actposs)) in
                (Action_times_pos_set.add (act, (x'', y)) actposs, x''))
          | Some aid ->
            if (aid = aid_of_action act) then (Action_times_pos_set.add (act, (x', y)) actposs, x')
            else
              let x'' = Rational.div_int (Rational.add x x') 2 in
              (Action_times_pos_set.add (act, (x'', y)) actposs, x''))
          (actposs, (0, 1))
          (Action_set.elements line) in
    actposs' in
  let (actposs, _) =
    List.fold_left
      (fun (actposs, y) line -> (add_line actposs y line, y + 1))
      (Action_times_pos_set.empty, 0)
      lines in
  make_unit_spacing actposs

let init_var_map_naive sb columns lines =
  let rec add_line actposs columns y (n, d) = function
  | [] -> actposs
  | act :: line ->
    let actposs' = Action_times_pos_set.add (act, ((n, d), y)) actposs in
    add_line actposs' columns y (n + 1, d) line in
  let (actposs, _) =
    List.fold_left
      (fun (actposs, y) line ->
        (add_line actposs columns y (0, 1) (Action_set.elements line), y + 1))
      (Action_times_pos_set.empty, 0)
      lines in
  actposs

let step_aux display_info map eqn x =
  let deltax = Rational.div_int (evaluate map x eqn) display_info.step_div in
  (*prerr_string (Rat.string_of_rat deltax ^ "\n"); flush stderr;*)
  Rational.add x deltax

let step display_info columns_map eqns var_map =
  let map =
    Action_times_pos_set.fold
      (fun (act, (x, _)) m -> Aid_map.add (aid_of_action act) x m)
      var_map
      Aid_map.empty in
  Action_times_pos_set.map
    (fun (act, (x, y)) ->
      let (var, _) = Aid_map.find (aid_of_action act) columns_map in
      let x' = step_aux display_info map (Aid_map.find var eqns) x in
      (act, (x', y)))
    var_map

let iterate display_info columns_map eqns init_var_map =
  let rec f var_map n =
    if n <= 0 then var_map
    else f (step display_info columns_map eqns init_var_map) (n - 1) in
  f init_var_map display_info.iterations

module String_map_of_list = Map_of_list(String_map)

let default_display_info = {
  repulsion_factor = (1, 1);
  mask =
    (let l = [
      ("rf", ED_show (RM_no_reduction, "red"));
      ("sb", ED_show (RM_no_reduction, "black"));
      ("asw", ED_show (RM_transitive_reduction_over_sb, "deeppink4"));
      ("mo", ED_show (RM_no_reduction, "blue"));
      ("sc", ED_show (RM_no_reduction, "orange"));
      ("sw", ED_show (RM_no_reduction, "deeppink4"));
      ("hb", ED_show (RM_transitive_reduction, "forestgreen"));
      ("ithb", ED_show (RM_transitive_reduction, "forestgreen"))
      ] in
    match String_map_of_list.of_list l with | None -> assert false | Some m -> m);
  layout = L_frac;
  step_div = 10;
  iterations = 1000;
  margin = (2, 1);
  x_factor = (3, 2);
  y_factor = (1, 1);
}

let layout_thread display_info loc_map sb acts =
  let lines = vertical_layout sb acts in
  let (columns, columns_map) = columns_of sb acts in
  match display_info.layout with
  | L_naive -> init_var_map_naive sb columns lines
  | L_frac ->
     let eqns = equations_map_of display_info loc_map sb columns_map lines in
    iterate display_info columns_map eqns (init_var_map_frac sb (columns, columns_map) lines)

(* TODO: take label size into account *)
let bounds_of acts =
  match Action_times_pos_set.elements acts with
  | [] -> ((0, 1), (0, 1))
  | (_, (xpos, _)) :: acts' ->
    List.fold_left
      (fun (min, max) (_, (xpos, _)) -> (Rational.min min xpos, Rational.max max xpos))
      (xpos, xpos)
      acts'

let shift offset acts =
  Action_times_pos_set.map
    (fun (act, (x, y)) -> (act, (Rational.add x offset, y)))
    acts

module Powerset_bind_aid_set_aid_set = Powerset_bind(Aid_set)(Aid_set)

module Aid_times_aid_set_to_aid_set_map = Real_map(Aid_times_aid_set)(Aid_set)

let down_closure rel n =
  let next s =
    let nx =
      Powerset_bind_aid_set_aid_set.bind
        (fun aid ->
          let outgoing = Aid_times_aid_set.filter (fun (src, _) -> src = aid) rel in
          Aid_times_aid_set_to_aid_set_map.map (fun (_, tgt) -> tgt) outgoing)
        s in
    Aid_set.union s nx in
  let rec f s =
    let s' = next s in
    if Aid_set.equal s s' then s
    else f s' in
  f (Aid_set.singleton n)

(* this assumes asw is pretty simple *)
let asw_surgery sb asw actposs =
  let level_map_of actposs =
    List.fold_left
      (fun m (act, (_, y)) -> Int_map.add (aid_of_action act) y m)
      Int_map.empty
      (Action_times_pos_set.elements actposs) in
  let min_asw excluded level_map =
    match
    List.fold_left
      (fun int_times_asws_opt (src, tgt) ->
        if Aid_times_aid_set.mem (src, tgt) excluded then int_times_asws_opt
        else
        match Int_map.find_opt src level_map with
        | None -> assert false
        | Some lvl ->
          (match int_times_asws_opt with
           | None -> Some (lvl, [(src, tgt)])
           | Some (lvl', edges) ->
             if lvl < lvl' then Some (lvl', [(src, tgt)])
             else if lvl > lvl' then Some (lvl', edges)
             else Some (lvl, edges @ [(src, tgt)])))
      None
      (Aid_times_aid_set.elements asw) with
      | None -> assert false
      | Some (_, edges) -> List.hd edges in
  let vertical_move_sb_down_closure y_offset tgt actposs =
    let aids = down_closure sb tgt in
    Action_times_pos_set.map
      (fun (act, (x, y)) -> if Aid_set.mem (aid_of_action act) aids then (act, (x, y + y_offset)) else (act, (x, y)))
      actposs in
  let step (excluded, actposs) =
    let level_map = level_map_of actposs in
    let (src, tgt) = min_asw excluded level_map in
    let lvl_tgt = Int_map.find tgt level_map in
    let lvl_src = Int_map.find src level_map in
    if lvl_tgt > lvl_src then (Aid_times_aid_set.add (src, tgt) excluded, actposs)
    else
      let offset = max (lvl_tgt - lvl_src) 1 in
      let actposs' = vertical_move_sb_down_closure offset tgt actposs in
      (Aid_times_aid_set.add (src, tgt) excluded, actposs') in
  let rec f (excluded, actposs) =
    if Aid_times_aid_set.equal excluded asw then actposs
    else f (step (excluded, actposs)) in
  f (Aid_times_aid_set.empty, actposs)

let juxtapose_threads display_info ths =
  let (actposs, _) =
    List.fold_left
      (fun (actposs, offset) th ->
        let (min, max) = bounds_of th in
        (Action_times_pos_set.union actposs (shift (Rational.sub offset min) th), Rational.add offset (Rational.add (Rational.sub max min) display_info.margin) ))
      (Action_times_pos_set.empty, (0, 1))
      ths in
  actposs

module Collect_tid = Collect_in_map(Int_map)(Action_set)

let collect_threads ex =
  Collect_tid.collect (tid_of_action) (Action_set.of_list ex.Bmc_types.actions)

(* TODO: space threads out depending on width *)
let layout_threads display_info loc_map ex =
  let thread_map = collect_threads ex in
  let sb' = aid_times_aid_set_of_rel ex.Bmc_types.sb in
  let ths =
    List.map
      (fun (tid, acts) -> layout_thread display_info loc_map sb' acts)
      (Int_map.bindings thread_map) in
  let actposs = juxtapose_threads display_info ths in
  asw_surgery sb' (aid_times_aid_set_of_rel ex.Bmc_types.asw) actposs

end

module Display = struct

let transitive_reduction s =
  Aid_times_aid_set.filter
    (fun (n, n'') ->
      not (Aid_times_aid_set.exists (fun (n1, n2) ->
        n = n1 &&
        Aid_times_aid_set.exists (fun (n3, n4) -> n2 = n3 && n4 = n'') s) s))
    s

let transitive_reduction_over_right s link =
  Aid_times_aid_set.filter
    (fun (s_src, s_tgt) ->
      not (Aid_times_aid_set.exists (fun (s'_src, s'_tgt) ->
        s_src = s'_src &&
        Aid_times_aid_set.exists (fun (l_src, l_tgt) -> s'_tgt = l_src && l_tgt = s_tgt) link) s))
    s

let transitive_reduction_over_left s link =
  Aid_times_aid_set.filter
    (fun (s_src, s_tgt) ->
      not (Aid_times_aid_set.exists (fun (s'_src, s'_tgt) ->
        s_tgt = s'_tgt &&
        Aid_times_aid_set.exists (fun (l_src, l_tgt) -> s'_src = l_tgt && l_src = s_src) link) s))
    s

let transitive_reduction_over s link =
  transitive_reduction_over_left (transitive_reduction_over_right s link) link

let repr n = "n" ^ string_of_int n

let make_edges display_info ex ew d =
  let add_edges name col rel edges =
    List.fold_left
      (fun edges (src, tgt) ->
        match Aid_times_aid_map.find_opt (src, tgt) edges with
        | None -> Aid_times_aid_map.add (src, tgt) [(name, col)] edges
        | Some l -> Aid_times_aid_map.add (src, tgt) (l @ [(name, col)]) edges)
      edges
      (Aid_times_aid_set.elements rel) in
  let sb' = transitive_reduction @@ aid_times_aid_set_of_rel ex.Bmc_types.sb in
  let asw' = aid_times_aid_set_of_rel ex.Bmc_types.asw in
  let rf' = aid_times_aid_set_of_rel ew.Bmc_types.rf in
  let mo' = transitive_reduction (aid_times_aid_set_of_rel ew.Bmc_types.mo) in
  let sc = aid_times_aid_set_of_rel ew.Bmc_types.sc in
  let transform rm edges =
    match rm with
    | Layout.RM_no_reduction -> edges
    | Layout.RM_transitive_reduction -> transitive_reduction edges
    | Layout.RM_transitive_reduction_over_sb -> transitive_reduction_over edges sb' in
  let add_edges_mask mask name rel edges =
    match String_map.find_opt name mask with
    | None -> edges
    | Some Layout.ED_hide -> edges
    | Some (Layout.ED_show (rm, col)) -> add_edges name col (transform rm rel) edges in
  let add_edges_mask2 mask name rel edges = add_edges_mask mask name (aid_times_aid_set_of_rel rel) edges in
  let base_edges =
    Aid_times_aid_map.empty |>
    add_edges_mask display_info.Layout.mask "sb" sb' |>
    add_edges_mask display_info.Layout.mask "asw" asw' |>
    add_edges_mask display_info.Layout.mask "rf" rf' |>
    add_edges_mask display_info.Layout.mask "mo" mo' |>
    add_edges_mask display_info.Layout.mask "sc" sc in
  let edges_with_derived = List.fold_left (fun edges (name, rel) -> add_edges_mask2 display_info.Layout.mask name rel edges) base_edges d.Bmc_types.derived_relations in
  let all_edges =
    List.fold_left
      (fun edges (name, fault) ->
        match fault with
        | Bmc_types.One x -> edges
        | Bmc_types.Two rel -> add_edges "undef" "darkorange" (aid_times_aid_set_of_rel rel) edges)
      edges_with_derived
      d.Bmc_types.undefined_behaviour in
  all_edges

let dot_of_edge attrs (n1, n2) =
  Dot.Edge { Dot.src = repr n1; Dot.tgt = repr n2; Dot.eattrs = attrs }

let display_nodes loc_map display_info d g =
  List.map
    (fun (act, (x, y)) ->
      let aid = aid_of_action act in
      (* TODO: is this the best way to display undef? *)
      let undefs =
        if List.exists
          (fun (name, fault) ->
            match fault with
              Bmc_types.One set -> List.mem act set
            | Bmc_types.Two _ -> false)
          d.Bmc_types.undefined_behaviour then [Dot.NColor "orange"]
        else [] in
      Dot.Node { Dot.nname = repr aid; Dot.nattrs = [Dot.NLabel (string_of_action loc_map act); Dot.NPos (Rational.float_of_rat (Rational.mult display_info.Layout.x_factor x), -. Rational.float_of_rat (Rational.mult (y, 1) display_info.Layout.y_factor)); Dot.NShape "none";] @ undefs })
    (Action_times_pos_set.elements g)

let display_edges display_info ex ew d =
  List.map
    (fun ((src, tgt), info) ->
      dot_of_edge
        [Dot.EColor (String.concat ":" (List.map snd info));
          Dot.ELabel (String.concat "," (List.map (fun (name, col) -> "<font color=\"" ^ col ^ "\">" ^ name ^ "</font>") info))] (src, tgt))
    (Aid_times_aid_map.bindings (make_edges display_info ex ew d))

let digraph_of_execution_aux loc_map display_info (ex, ew, d) g =
  [Dot.Graph_attr (Dot.Overlap false); Dot.Graph_attr (Dot.Splines true)] @ display_nodes loc_map display_info d g @ display_edges display_info ex ew d

let digraph_of_execution loc_map display_info (ex, ew, d) =
  let ths = Layout.layout_threads display_info loc_map ex in
  digraph_of_execution_aux loc_map display_info (ex, ew, d) ths

end

let pp_dot loc_map exec =
  Dot.string_of_digraph (Display.digraph_of_execution loc_map Layout.default_display_info exec)
