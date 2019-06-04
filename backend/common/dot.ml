
(* dot.ml  - DSL for Graphviz '.dot' format *)
(* (C) J Pichon 2019 *)

let option_map f xs =
  let rec g l = function
  | [] -> List.rev l
  | x :: xs ->
    let l' = (match f x with None -> l | Some y -> y :: l) in
    g l' xs in
  g [] xs

type node_attr =
  | NColor of string
  | NLabel of string
  | NShape of string
  | NHtmlLabel of string
  | NMargin of string
  | NPos of float * float
  | NFontname of string
  | NFontsize of int

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
  | NFontname s -> string_of_str_attr "fontname" s
  | NFontsize sz -> string_of_str_attr "fontsize" (string_of_int sz)

let string_of_node_attrs nattrs =
  String.concat "," (List.map string_of_nattr nattrs)

let string_of_node (n : node_info) =
  n.nname
  ^ match n.nattrs with
    | [] -> ";"
    | _ ->
      " ["
      ^ string_of_node_attrs n.nattrs
      ^ "];"

type edge_attr =
  | ELabel of string
  | EColor of string
  | Lhead of string
  | Ltail of string
  | EStyle of string
  | EFontname of string
  | EFontsize of int

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
  | EFontname s -> string_of_str_attr "fontname" s
  | EFontsize sz -> string_of_str_attr "fontsize" (string_of_int sz)

let string_of_edge_attrs coloro eattrs =
  String.concat "," (List.map (string_of_eattr coloro) eattrs)

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
    | _ -> " [" ^ string_of_edge_attrs coloro e.eattrs ^ "];")

type rankdir =
  | TB
  | LR

type graph_attr =
  | Compound
  | GLabel of string
  | Rankdir of rankdir
  | Splines of bool
  | Overlap of bool
  | Scale of float * float
  | All_nodes of node_attr list
  | All_edges of edge_attr list

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
  | Scale (x, y) -> "scale=\"" ^ string_of_float x ^ "," ^ string_of_float y ^ "\";"
  | All_nodes ns -> "node [" ^ string_of_node_attrs ns ^ "];"
  | All_edges es -> "edge [" ^ string_of_edge_attrs None es ^ "];"


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