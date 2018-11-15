(****************************************************************************)
(*  Copyright (c) 2013, 2014, 2015, Tom Ridge, David Sheets, Thomas Tuerk,  *)
(*  Andrea Giugliano (as part of the SibylFS project)                       *)
(*                                                                          *)
(*  Permission to use, copy, modify, and/or distribute this software for    *)
(*  any purpose with or without fee is hereby granted, provided that the    *)
(*  above copyright notice and this permission notice appear in all         *)
(*  copies.                                                                 *)
(*                                                                          *)
(*  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL           *)
(*  WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED           *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE        *)
(*  AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL    *)
(*  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR   *)
(*  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER          *)
(*  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR        *)
(*  PERFORMANCE OF THIS SOFTWARE.                                           *)
(*                                                                          *)
(*  Meta:                                                                   *)
(*    - Headers maintained using headache.                                  *)
(*    - License source: http://opensource.org/licenses/ISC                  *)
(****************************************************************************)

(* wrappers around LEM generated OCaml code that instantiates dictionaries *)
open Fs_prelude

module FmapFunctor = functor (D : sig 
  val map_dict : unit -> 'a Lem_map.mapKeyType_class 
  val set_dict : unit -> 'a Lem_basic_classes.setType_class
end) -> struct 
(*  open Fmap *)

  let fmap_remove m a = fmap_remove (D.map_dict ()) m a;;
  let fmap_update m (a,b) = fmap_update (D.map_dict ()) m (a,b);;
  let fmap_update_option m (k,vopt) = fmap_update_option (D.map_dict ()) m (k,vopt);;
  let fmap_from_list l = fmap_from_list (D.map_dict ()) l;;
  let fmap_lookup m a = fmap_lookup (D.map_dict ()) m a;;
  let fmap_empty () = fmap_empty (D.map_dict ()) ();;

  let fmap_dom m = fmap_dom (D.map_dict ()) (D.set_dict ()) m;;
end

module Fmap_default = FmapFunctor (struct 
  let map_dict () = Lem_map.instance_Map_MapKeyType_var_dict Lem_basic_classes.instance_Basic_classes_SetType_var_dict 
  let set_dict () = Lem_basic_classes.instance_Basic_classes_SetType_var_dict 
end);;
