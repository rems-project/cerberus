(** Support for annotations in special comments. *)

type comment_annots =
  { ca_inlined       : string list
  ; ca_imports       : (string * string) list
  ; ca_proof_imports : (string * string) list
  ; ca_code_imports  : (string * string) list
  ; ca_context       : string list
  ; ca_typedefs      : Rc_annot.typedef list }

type annot_line =
  | AL_annot of string * string option
  | AL_comm  of string
  | AL_none

let read_line : string -> annot_line = fun s ->
  (* First try to read an annotation comment. *)
  let k_annot name n =
    let payload = String.trim (String.sub s n (String.length s - n)) in
    let payload = if payload = "" then None else Some(payload) in
    AL_annot(name, payload)
  in
  try Scanf.sscanf s "//@rc::%s%n" k_annot
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Then try to read a comment. *)
  let k_comm n = AL_comm(String.sub s n (String.length s - n)) in
  try Scanf.sscanf s "//@%n" k_comm
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Line has no special meaning. *)
  AL_none

type where = Default | CodeOnly | ProofsOnly

let read_import : string -> (string * string * where) option = fun s ->
  let k proof_only mod_name from = Some(from, mod_name, proof_only) in
  (* First try to read an import that is only for proofs. *)
  try Scanf.sscanf s "%s from %s (for proofs only) %!" (k ProofsOnly)
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Then try to read an import that is only for the code. *)
  try Scanf.sscanf s "%s from %s (for code only) %!" (k CodeOnly)
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Then try to read a general import. *)
  try Scanf.sscanf s "%s from %s %!" (k Default)
  with End_of_file | Scanf.Scan_failure(_) -> None

let read_typedef : string -> Rc_annot.typedef option = fun s ->
  let open Earley_core in
  let parse_string = Earley.parse_string Rc_annot.typedef Blanks.default in
  try Some(parse_string s) with Earley.Parse_error(_,_) -> None

let parse_annots : string list -> comment_annots = fun ls ->
  let error msg =
    Panic.panic_no_pos "Comment annotation error: %s." msg
  in
  let imports = ref [] in
  let inlined = ref [] in
  let typedefs = ref [] in
  let context = ref [] in
  let rec loop inline ls =
    match ls with
    | []      -> if inline then error "unclosed [rc::inlined] annotation"
    | l :: ls ->
    match read_line l with
    | AL_annot(n,p) ->
        begin
          let get_payload () =
            match p with Some(s) -> s | None ->
            error ("annotation [rc::" ^ n ^ "] expects a payload")
          in
          let no_payload () =
            match p with None -> () | Some(_) ->
            error ("annotation [rc::" ^ n ^ "] does not expects a payload")
          in
          let check_inline b =
            if inline <> b then
              error ("unexpected [rc::" ^ n ^ "] annotation")
          in
          match n with
          | "inlined" ->
              begin
                check_inline false;
                match p with
                | Some(s) -> inlined := s :: !inlined; loop inline ls
                | None    -> loop true ls
              end
          | "end"     ->
              check_inline true; no_payload (); loop false ls
          | "import"  ->
              begin
                check_inline false;
                match (read_import (get_payload ())) with
                | Some(i) -> imports := i :: !imports; loop inline ls
                | None    ->
                    error ("invalid [rc::import] annotation")
              end
          | "typedef" ->
              begin
                check_inline false;
                match (read_typedef (get_payload ())) with
                | Some(t) -> typedefs := t :: !typedefs; loop inline ls
                | None    ->
                    error ("invalid [rc::typedef] annotation")
              end
          | "context" ->
              check_inline false;
              context := get_payload () :: !context;
              loop inline ls
          | _         ->
              error ("unknown annotation [rc::" ^ n ^ "]")
        end
    | AL_comm(s)    ->
        if not inline then error "ill-placed inlined line";
        inlined := s :: !inlined;
        loop inline ls
    | AL_none       ->
        if inline then error "invalid line after a [rc::inlined] annotation";
        loop inline ls
  in
  loop false ls;
  let imports = List.rev !imports in
  let proof_imports = List.filter (fun (_,_,w) -> w = ProofsOnly) imports in
  let code_imports  = List.filter (fun (_,_,w) -> w = CodeOnly  ) imports in
  let imports       = List.filter (fun (_,_,w) -> w = Default   ) imports in
  { ca_inlined        = List.rev !inlined
  ; ca_proof_imports  = List.map (fun (f,m,_) -> (f,m)) proof_imports
  ; ca_code_imports   = List.map (fun (f,m,_) -> (f,m)) code_imports
  ; ca_imports        = List.map (fun (f,m,_) -> (f,m)) imports
  ; ca_context        = List.rev !context
  ; ca_typedefs       = List.rev !typedefs }
