(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)


module E = Errormsg

(* TODO This really is in the wrong place! *)
(* Output management *)
let out : out_channel option ref = ref None
let close_me = ref false

(* whether to print a file of prototypes after parsing *)
let doPrintProtos : bool ref = ref false

let close_output _ =
  match !out with
    | None -> ()
    | Some o ->
      flush o;
      if !close_me then close_out o else ();
      close_me := false


let set_output filename =
  close_output ();
  let out_chan = 
    try
      open_out filename 
    with Sys_error msg -> 
      (output_string stderr ("Error while opening output: " ^ msg); exit 1) in
  out := Some out_chan;
  Whitetrack.setOutput out_chan;
  close_me := true

exception ParseError of string

let clexer lexbuf =
  Clexer.clear_white ();
  Clexer.clear_lexeme ();
  let token = Clexer.initial lexbuf in
  let white = Clexer.get_white () in
  let cabsloc = Clexer.currentLoc () in
  let lexeme = Clexer.get_extra_lexeme () ^ Lexing.lexeme lexbuf in
  (white, lexeme, token, cabsloc)

let parse_to_cabs name lexbuf =
  try
    let lexbuf = Clexer.init name lexbuf in
    let cabs = Cparser.start (Whitetrack.wraplexer clexer) lexbuf in
    Whitetrack.setFinalWhite (Clexer.get_white ());
    Clexer.finish ();
    (name, cabs)
  with
  | Sys_error msg ->
      begin
        ignore (E.log "Cannot open %s : %s\n" name msg);
        Clexer.finish ();
        close_output ();
        raise (ParseError("Cannot open " ^ name ^ ": " ^ msg ^ "\n"))
      end
    | Parsing.Parse_error ->
        begin
          ignore (E.log "Parsing error");
          Clexer.finish ();
          close_output ();
          raise (ParseError("Parse error"))
        end
    | Cparser.Error ->
        begin
          ignore (E.log "Unexpected token: %s.\n" (Lexing.lexeme lexbuf));
          Clexer.finish ();
          raise (ParseError("Parse error"))
        end
(*    | e ->
        begin
          ignore (E.log "Caught %s while parsing\n" (Printexc.to_string e));
          Clexer.finish ();
          raise e
        end
*)
            
let rec parse_exn name lexbuf =
  let cabs = parse_to_cabs name lexbuf in
  if !E.hadErrors then
    E.s (E.error "There were parsing errors in %s" name);
  cabs
