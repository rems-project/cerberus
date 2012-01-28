open Printf
open Syntax
open ListSet
open MetatheoryAtom
open Maps
open Lattice
open Dtree

let print_reachablity (rd:LLVMsyntax.l list) : bool =
  if !Globalstates.debug then 
    (eprintf "RD: %s\n\n" (String.concat ", " rd); flush_all (););
  true

let print_dominators (bd:LLVMsyntax.l list) (dt:LLVMsyntax.l set AMap.t): bool =
  if !Globalstates.debug then 
    (eprintf "DOM:\n";
     List.iter (fun l0 -> 
                eprintf "%s: %s\n" l0 (String.concat "," (AMap.get l0 dt))) bd;
     eprintf "\n";
     flush_all (););
  true

let string_of_intent (n:int) : String.t = String.make n (Char.chr 95)

let rec string_of_dtree (dt:coq_DTree) (n:int) : String.t = 
  match dt with
    | DT_node (l0, dts) -> 
        string_of_intent n ^ l0 ^ "\n" ^ string_of_dtrees dts (n+1) 
and string_of_dtrees (dts:coq_DTrees) (n:int) : String.t =
  match dts with
    | DT_nil -> ""
    | DT_cons (dt, dts') -> string_of_dtree dt n ^ string_of_dtrees dts' n

let print_dtree (dt:coq_DTree) : bool = 
  if !Globalstates.debug then 
    (eprintf "DT:\n%s\n" (string_of_dtree dt 0);
     flush_all ();); 
  true

let init_expected_name (u:unit) : int = 0

let check_vname (oldn:LLVMsyntax.id) (expected:int)
  : (LLVMsyntax.id * int) option = 
  try 
    let oldi = int_of_string (Coq_pretty_printer.getRealName oldn) in
    if expected = oldi then 
      Some (oldn, expected+1)
    else
      if oldi > expected then
        Some ("%" ^ string_of_int expected, expected+1)
      else None
  with 
    | _ -> Some (oldn, expected)

let check_bname (lname:LLVMsyntax.l) (expected:int) 
  : (LLVMsyntax.l * int) option = 
  try 
    let li = int_of_string lname in
    if expected = li then 
      Some (lname, expected+1)
    else
      if li > expected then
        Some (string_of_int expected, expected+1)
      else None
  with 
    | _ -> Some (lname, expected)

let does_pre (t:unit) : bool = !Globalstates.does_pre

let does_load_elim (t:unit) : bool = !Globalstates.does_load_elim

let does_phi_elim (t:unit) : bool = !Globalstates.does_phi_elim

let does_macro_m2r (t:unit) : bool = !Globalstates.does_macro_m2r

let does_stld_elim (t:unit) : bool = !Globalstates.does_stld_elim

let aa_db = ref stdin

let open_aa_db () : bool = 
  try
    aa_db := open_in "aa.db"; true
  with 
    | Sys_error _ -> false

let close_aa_db () : unit = 
  try
    close_in !aa_db
  with 
    | Sys_error _ -> ()

let no_htl : (String.t, unit) Hashtbl.t ref = ref (Hashtbl.create 4000)
let must_htl : (String.t, unit) Hashtbl.t ref = ref (Hashtbl.create 1000)

let read_aa_from_fun (name: String.t) : bool =
  try 
    Hashtbl.clear !no_htl;
    Hashtbl.clear !must_htl;
    Scanf.fscanf !aa_db "%s #" 
      (fun fname -> 
         if "@" ^ fname <> name then 
           failwith (fname ^ " in aa db does not match " ^ name)
         else ()
      );
    try 
      while true do
        Scanf.fscanf !aa_db "%u%s@ %s@;" 
          (fun flag p1 p2 -> 
            if flag = 0 then Hashtbl.add !no_htl (p1 ^ p2) () 
            else if flag = 2 then Hashtbl.add !must_htl (p1 ^ p2) () 
            else failwith "Wrong alias result"
          );
      done; true
    with
      | Scanf.Scan_failure err -> Scanf.fscanf !aa_db "\n" (); true
  with
    | End_of_file ->
        close_aa_db (); false

let is_no_alias p1 p2 : bool = 
  let key = if p1 < p2 then p1 ^ p2 else p2 ^ p1 in
  Hashtbl.mem !no_htl key

let is_must_alias p1 p2 : bool =
  let key = if p1 < p2 then p1 ^ p2 else p2 ^ p1 in
  Hashtbl.mem !must_htl key




