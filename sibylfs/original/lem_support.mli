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

type 'a finset (* = Finset of 'a list *)
val list_from_finset : 'a finset -> 'a list
val finset_from_list : 'a list -> 'a finset
module Int32 :
  sig
(*
    val zero : int32
    val one : int32
    val minus_one : int32
    external neg : int32 -> int32 = "%int32_neg"
    external add : int32 -> int32 -> int32 = "%int32_add"
    external sub : int32 -> int32 -> int32 = "%int32_sub"
    external mul : int32 -> int32 -> int32 = "%int32_mul"
    external div : int32 -> int32 -> int32 = "%int32_div"
    external logor : int32 -> int32 -> int32 = "%int32_or"
    external logxor : int32 -> int32 -> int32 = "%int32_xor"
    val lognot : int32 -> int32
    external shift_left : int32 -> int -> int32 = "%int32_lsl"
    external shift_right : int32 -> int -> int32 = "%int32_asr"
    external shift_right_logical : int32 -> int -> int32 = "%int32_lsr"
*)
    val of_int : int -> int32
    val logand: int32 -> int32 -> int32
    val logor : int32 -> int32 -> int32
    val lognot : int32 -> int32
    val to_int : int32 -> int
(*
    external of_float : float -> int32 = "caml_int32_of_float"
    external to_float : int32 -> float = "caml_int32_to_float"
    external of_string : string -> int32 = "caml_int32_of_string"
    external bits_of_float : float -> int32 = "caml_int32_bits_of_float"
    external float_of_bits : int32 -> float = "caml_int32_float_of_bits"
*)
    val to_string : int32 -> string
    type t = int32
(*
    val compare : t -> t -> int
    external format : string -> int32 -> string = "caml_int32_format"
*)
    val t_of_sexp : Sexplib.Sexp.t -> int32
    val sexp_of_t : int32 -> Sexplib.Sexp.t
  end
module Int64 :
  sig
(*
    val zero : int64
    val one : int64
    val minus_one : int64
    external neg : int64 -> int64 = "%int64_neg"
    external add : int64 -> int64 -> int64 = "%int64_add"
    external sub : int64 -> int64 -> int64 = "%int64_sub"
    external mul : int64 -> int64 -> int64 = "%int64_mul"
    external div : int64 -> int64 -> int64 = "%int64_div"
    external rem : int64 -> int64 -> int64 = "%int64_mod"
    val succ : int64 -> int64
    val pred : int64 -> int64
    val abs : int64 -> int64
    val max_int : int64
    val min_int : int64
    external logand : int64 -> int64 -> int64 = "%int64_and"
    external logor : int64 -> int64 -> int64 = "%int64_or"
    external logxor : int64 -> int64 -> int64 = "%int64_xor"
    val lognot : int64 -> int64
    external shift_left : int64 -> int -> int64 = "%int64_lsl"
    external shift_right : int64 -> int -> int64 = "%int64_asr"
    external shift_right_logical : int64 -> int -> int64 = "%int64_lsr"
*)
    val of_int : int -> int64
    val to_int : int64 -> int
(*
    external of_float : float -> int64 = "caml_int64_of_float"
    external to_float : int64 -> float = "caml_int64_to_float"
    external of_int32 : int32 -> int64 = "%int64_of_int32"
    external to_int32 : int64 -> int32 = "%int64_to_int32"
    external of_nativeint : nativeint -> int64 = "%int64_of_nativeint"
    external to_nativeint : int64 -> nativeint = "%int64_to_nativeint"
    external of_string : string -> int64 = "caml_int64_of_string"
    external bits_of_float : float -> int64 = "caml_int64_bits_of_float"
    external float_of_bits : int64 -> float = "caml_int64_float_of_bits"
*)
    val to_string : int64 -> string
    type t = int64
(*
    val compare : t -> t -> int
    external format : string -> int64 -> string = "caml_int64_format"
*)
    val t_of_sexp : Sexplib.Sexp.t -> int64
    val sexp_of_t : int64 -> Sexplib.Sexp.t
  end
