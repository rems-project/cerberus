(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2011-2020                                                         *)
(*    Kayvan Memarian                                                               *)
(*    Victor Gomes                                                                  *)
(*    Justus Matthiesen                                                             *)
(*    Peter Sewell                                                                  *)
(*    Kyndylan Nienhuis                                                             *)
(*    Stella Lau                                                                    *)
(*    Jean Pichon-Pharabod                                                          *)
(*    Christopher Pulte                                                             *)
(*    Rodolphe Lepigre                                                              *)
(*    James Lingard                                                                 *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(************************************************************************************)

open Pp_prelude
open Pp_utils
open Colour

module P = PPrint

type doc_tree =
  | Dleaf of P.document
  | Dleaf_attrs of P.document * Annot.attributes
  | Dnode of P.document * doc_tree list
  | Dnode_attrs of P.document * Annot.attributes * doc_tree list


let add_dtree_of_attributes (Annot.Attrs xs) dtrees =
  let open Annot in
  match xs with
    | [] ->
        dtrees
    | _ ->
        let string_of_ident (Symbol.Identifier (_, str)) = str in
        Dnode ( !^ (ansi_format [Bold; Red] "Attributes")
              , List.map (fun attr ->
                  let str =
                    begin match attr.attr_ns with
                  | Some z ->
                          string_of_ident z ^ "::"
                      | None ->
                          ""
                    end ^ string_of_ident attr.attr_id ^
                    "(" ^ String.concat ", " (List.map (fun (_, z) -> "\"" ^ String.escaped z ^ "\"") attr.attr_args) ^  ")" in
                  Dleaf (!^ str)
                ) xs )
        :: dtrees

let pp_doc_tree dtree =
  let to_space = function
    | '|'
      -> "|"
    | _
      -> " " in
  let pp_prefix pref =
    !^ (ansi_format [Blue] pref) in
  let rec aux (pref, (current : char)) = function
    | Dleaf doc ->
        pp_prefix (pref ^ String.make 1 current ^ "-") ^^ doc
    | Dnode (doc, []) ->
        pp_prefix (pref ^ String.make 1 current ^ "-") ^^ doc ^^^ !^ "EMPTY"
        (* TODO: do a failwith ? *)
    | Dnode (doc, dtrees) ->
        P.separate P.hardline begin
          (pp_prefix (pref ^ String.make 1 current ^ "-") ^^ doc) ::
          map_with_last
            (aux (pref ^ to_space current ^ " ", '|'))
            (aux (pref ^ to_space current ^ " ", '`'))
            dtrees
        end
    | Dleaf_attrs (doc, attrs) ->
        aux (pref, current) (Dnode (doc, add_dtree_of_attributes attrs []))
    | Dnode_attrs (doc, attrs, dtrees) ->
        aux (pref, current) (Dnode (doc, add_dtree_of_attributes attrs dtrees))
  in
  begin match dtree with
    | Dleaf doc ->
        doc
    | Dnode (doc, dtrees) ->
        doc ^^ P.hardline ^^
        P.separate P.hardline begin
          map_with_last
            (aux ("", '|'))
            (aux ("", '`'))
            dtrees
        end
  end

let pp_keyword w      = !^ (ansi_format [Bold; Cyan] w)
let pp_const c        = !^ (ansi_format [Magenta] c)

let pp_ctor k =
  !^ (ansi_format [Bold; Cyan] k)

let pp_type_keyword w = !^ (ansi_format [Green] w)

let pp_stmt_ctor k =
  !^ (ansi_format [Bold; Magenta] k)

let pp_decl_ctor w = !^ (ansi_format [Bold; Green] w)
let pp_id_type id = !^ (ansi_format [Green] (Pp_symbol.to_string_pretty id))

let pp_cond switch doc =
  if switch then
    (^^^) doc
  else
    (^^) P.empty

let filter_opt_list xs =
  List.fold_left (fun acc opt -> match opt with None -> acc | Some x -> x::acc) [] (List.rev xs)
let opt_list f = function
  | [] -> None
  | xs -> Some (f xs)

let leaf_opt_list ctor pp =
  opt_list (fun xs -> (Dleaf (pp_ctor ctor ^^^ P.brackets (comma_list pp xs))))

let node_opt_list ctor pp =
  opt_list (fun xs -> (Dnode (pp_ctor ctor, List.map pp xs)))

let guarded_opt b x =
  if b then Some x else None

let option z f = function
  | Some x -> Some (f x)
  | None   -> z

let with_attributes (Annot.Attrs xs as attrs) = function
  | Dleaf doc ->
      Dleaf_attrs (doc, attrs)
  | Dleaf_attrs (doc, Annot.Attrs xs') ->
      Dleaf_attrs (doc, Annot.Attrs (xs @ xs'))
  | Dnode (doc, dtrees) ->
      Dnode_attrs (doc, attrs, dtrees)
  | Dnode_attrs (doc, Annot.Attrs xs', dtrees) ->
      Dnode_attrs (doc, Annot.Attrs (xs @ xs'), dtrees)
