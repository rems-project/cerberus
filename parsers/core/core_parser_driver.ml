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

open Cerb_frontend
open Core_parser_util

let genparse mode std filename =
  let read f input =
    let channel = open_in input in
    let result  = f channel in
    let ()      = close_in channel in
    result
  in
  let module Parser = Core_parser.Make (struct
    let mode = mode
    let std = std
  end) in
  let parse_channel ic =
    let lexbuf = Lexing.from_channel ic in
    (* TODO: I don't know why Lexing is losing the filename information!! *)
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p  with pos_fname= filename };
    try
      Exception.except_return @@ Parser.start Core_lexer.main lexbuf
    with
    | Core_lexer.Error ->
      let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
      Exception.fail (loc, Errors.CORE_PARSER Errors.Core_parser_invalid_symbol)
    | Parser.Error ->
      let loc = Location_ocaml.region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) None in
      Exception.fail (loc, Errors.CORE_PARSER (Errors.Core_parser_unexpected_token (Lexing.lexeme lexbuf)))
    | Core_parser_util.Core_error (loc, err) ->
      Exception.fail (loc, Errors.CORE_PARSER err)
    | Failure msg ->
      prerr_endline "CORE_PARSER_DRIVER (Failure)";
      failwith msg
    | _ ->
      failwith "CORE_PARSER_DRIVER"
  in
  read parse_channel filename

let parse_stdlib =
  genparse StdMode (Pmap.empty _sym_compare)

let parse stdlib =
  genparse ImplORFileMode
    begin List.fold_left (fun acc (fsym, _) ->
        match fsym with
        | Symbol.Symbol (_, _, Some str) ->
          let std_pos = {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"} in
          Pmap.add (str, (std_pos, std_pos)) fsym acc
        | Symbol.Symbol (_, _, None) ->
          acc
      ) (Pmap.empty Core_parser_util._sym_compare) (Pmap.bindings_list (snd stdlib))
    end
