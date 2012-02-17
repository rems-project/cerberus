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

(* $Id: odot.mli 134 2005-12-16 10:15:20Z zoggy $ *)

(** Parsing and printing graphviz dot files. *)

(** {2 Version} *)

(** {2 Representation of dot graphs} *)

type graph_kind = Graph | Digraph
type id =
    Simple_id of string
  | Html_id of string
  | Double_quoted_id of string

type attr = id * id option

type compass_pt = N | NE | E | SE | S | SW | W | NW

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

(** {2 Printing} *)

val string_of_graph_kind : graph_kind -> string
val string_of_id : id -> string
val string_of_attr : id * id option -> string
val string_of_attr_list : (id * id option) list -> string
val string_of_compass_pt : compass_pt -> string
val string_of_node_id : id * (id * compass_pt option) option -> string
val string_of_edge_stmt_point : graph_kind -> edge_stmt_point -> string
val string_of_edge_stmt : graph_kind -> edge_stmt -> string
val string_of_attr_stmt : attr_stmt -> string
val string_of_stmt : graph_kind -> stmt -> string
val string_of_stmt_list : graph_kind -> stmt list -> string
val string_of_subgraph : graph_kind -> subgraph -> string

val string_of_graph : graph -> string
val print : out_channel -> graph -> unit

(** @raise Sys_error if the file cannot be open for writing. *)
val print_file : string -> graph -> unit

(** {2 Useful functions} *)

val attr_value : id -> attr list -> id option

val node_id : ?port: id -> ?comp: compass_pt -> id -> node_id
val simple_node_id : string -> node_id
val dblq_node_id : string -> node_id
val html_node_id : string -> node_id
