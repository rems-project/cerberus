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

module Fmap_default :
  sig
    val fmap_remove :
      ('a, 'b) Fs_prelude.fmap -> 'a -> ('a, 'b) Fs_prelude.fmap
    val fmap_update :
      ('a, 'b) Fs_prelude.fmap -> 'a * 'b -> ('a, 'b) Fs_prelude.fmap
    val fmap_update_option :
      ('a, 'b) Fs_prelude.fmap -> 'a * 'b option -> ('a, 'b) Fs_prelude.fmap
    val fmap_from_list : ('a * 'b) list -> ('a, 'b) Fs_prelude.fmap
    val fmap_lookup : ('a, 'b) Fs_prelude.fmap -> 'a -> 'b option
    val fmap_empty : unit -> ('a, 'b) Fs_prelude.fmap
    val fmap_dom : ('a, 'b) Fs_prelude.fmap -> 'a Lem_support.finset
  end
