(*********************************************************************************)
(*                Odot                                                           *)
(*                                                                               *)
(*    Copyright (C) 2005 Institut National de Recherche en Informatique et       *)
(*    en Automatique. All rights reserved.                                       *)
(*                                                                               *)
(*    This program is free software; you can redistribute it and/or modify       *)
(*    it under the terms of the GNU General Public License as published          *)
(*    by the Free Software Foundation; either version 2.1 of the License, or     *)
(*    any later version.                                                         *)
(*                                                                               *)
(*    This program is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(*    GNU Lesser General Public License for more details.                        *)
(*                                                                               *)
(*    You should have received a copy of the GNU General Public License          *)
(*    along with this program; if not, write to the Free Software                *)
(*    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA                   *)
(*    02111-1307  USA                                                            *)
(*                                                                               *)
(*    Contact: Maxence.Guesdon@inria.fr                                          *)
(*********************************************************************************)

(* $Id: odot.ml 134 2005-12-16 10:15:20Z zoggy $ *)

open Odot_types

type graph_kind =
    Graph | Digraph

type id =
    Simple_id of string
  | Html_id of string
  | Double_quoted_id of string

type attr = id * id option

type compass_pt =
    N | NE | E | SE | S | SW | W | NW

type port = id * compass_pt option

type node_id = id * port option

type edge_stmt_point =
    Edge_node_id of node_id
  | Edge_subgraph of subgraph

and edge_stmt = edge_stmt_point * edge_stmt_point list * attr list

and attr_stmt =
    Attr_graph of attr list
  | Attr_node of attr list
  | Attr_edge of attr list

and stmt =
  | Stmt_node of node_id * attr list
  | Stmt_equals of id * id
  | Stmt_edge of edge_stmt
  | Stmt_attr of attr_stmt
  | Stmt_subgraph of subgraph

and subgraph =
    { mutable sub_id : id option ;
      mutable sub_stmt_list : stmt list ;
    }

and graph =
    {
      mutable strict : bool ;
      mutable kind : graph_kind ;
      mutable id : id option;
      mutable stmt_list : stmt list ;
    }

let parse_string s = parse (Lexing.from_string s)

let string_of_graph_kind = function
    Graph -> "graph"
  | Digraph -> "digraph"

let string_of_id = function
    Simple_id s -> s
  | Html_id s -> Printf.sprintf "<%s>" s
  | Double_quoted_id s ->
      let len = String.length s in
      let b = Buffer.create len in
      for i = 0 to len - 1 do
	match s.[i] with
	  '"' -> Buffer.add_string b "\\\""
	| c -> Buffer.add_char b c
      done;
      Printf.sprintf "\"%s\"" (Buffer.contents b)

let string_of_attr = function
    (id,None) -> string_of_id id
  | (id,Some v) ->
      Printf.sprintf "%s=%s"
	(string_of_id id)
	(string_of_id v)

let string_of_attr_list = function
    [] -> ""
  | l ->
      Printf.sprintf "[%s]"
	(String.concat ", " (List.map string_of_attr l))

let string_of_compass_pt = function
    N -> "n"
  | NE -> "ne"
  | E -> "e"
  | SE -> "se"
  | S -> "s"
  | SW -> "sw"
  | W -> "w"
  | NW -> "nw"

let string_of_node_id = function
    (id, None) -> string_of_id id
  | (id, Some (id2, None)) ->
      Printf.sprintf "%s:%s"
	(string_of_id id)
	(string_of_id id2)
  | (id, Some (id2, Some c)) ->
      Printf.sprintf "%s:%s:%s"
	(string_of_id id)
	(string_of_id id2)
	(string_of_compass_pt c)

let rec string_of_edge_stmt_point kind = function
    Edge_node_id nid -> string_of_node_id nid
  | Edge_subgraph s -> string_of_subgraph kind s

and string_of_edge_stmt kind =
  let sep =
    match kind with
      Graph -> "--"
    | Digraph -> "->"
  in
  function (p1, lp, attr) ->
    Printf.sprintf "%s%s%s"
      (string_of_edge_stmt_point kind p1)
      (String.concat ""
	 (List.map
	    (fun p -> Printf.sprintf " %s %s" sep
		(string_of_edge_stmt_point kind p))
	    lp
	 )
      )
      (string_of_attr_list attr)

and string_of_attr_stmt stmt =
  let (s,attr) =
    match stmt with
      Attr_graph l -> ("graph", l)
    | Attr_node l -> ("node", l)
    | Attr_edge l -> ("edge", l)
  in
  Printf.sprintf "%s %s" s
    (string_of_attr_list attr)

and string_of_stmt kind = function
    Stmt_node (nid, attr) ->
      Printf.sprintf "%s %s"
	(string_of_node_id nid)
	(string_of_attr_list attr)
  | Stmt_equals (id1, id2) ->
      Printf.sprintf "%s=%s"
	(string_of_id id1)
	(string_of_id id2)
  | Stmt_edge s ->
      string_of_edge_stmt kind s
  | Stmt_attr s ->
      string_of_attr_stmt s
  | Stmt_subgraph g ->
      string_of_subgraph kind g

and string_of_stmt_list kind l =
  String.concat "\n"
    (List.map
       (fun s -> Printf.sprintf "%s;" (string_of_stmt kind s)) l)

and string_of_subgraph kind g =
  Printf.sprintf "subgraph %s{\n%s\n  }"
    (match g.sub_id with
      None -> ""
    | Some id -> Printf.sprintf "%s " (string_of_id id)
    )
    (string_of_stmt_list kind g.sub_stmt_list)

let string_of_graph g =
  Printf.sprintf "%s%s %s {\n%s\n}"
    (if g.strict then "strict " else "")
    (string_of_graph_kind g.kind)
    (match g.id with
      None -> ""
    | Some id -> Printf.sprintf "%s " (string_of_id id)
    )
    (string_of_stmt_list g.kind g.stmt_list)

let print oc p =
  output_string oc (string_of_graph p)

let print_file f p =
  let oc = open_out f in
  print oc p;
  close_out oc


let attr_value id l =
  try List.assoc id l
  with Not_found -> None

let node_id ?port ?comp id =
  match port with
    None -> (id, None)
  | Some p ->
      match comp with
	None -> (id, Some (p,None))
      | Some c -> (id, Some (p, Some c))

let simple_node_id s = node_id (Simple_id s)
let dblq_node_id s = node_id (Double_quoted_id s)
let html_node_id s = node_id (Html_id s)
