module C = Cabs

let nextident = ref 0
let getident () =
    nextident := !nextident + 1;
    !nextident

let currentLoc () =
  let l, f, c = Errormsg.getPosition () in
  { C.lineno   = l; 
    C.filename = f; 
    C.byteno   = c;
    C.ident    = getident ();}

let cabslu = {C.lineno = -10; 
	      C.filename = "cabs loc unknown"; 
	      C.byteno = -10;
              C.ident = 0}

(* clexer puts comments here *)
let commentsGA = GrowArray.make 100 (GrowArray.Elem(cabslu,"",false))


(*********** HELPER FUNCTIONS **********)

(*
let missingFieldDecl = ("___missing_field_name", C.JUSTBASE, [], cabslu)
*)

let rec isStatic storage =
  BatSet.mem C.STATIC storage

let rec isExtern storage =
  BatSet.mem C.STATIC storage

(*
let rec isInline = function
    [] -> false
  | C.SpecInline :: _ -> true
  | _ :: rest -> isInline rest

let rec isTypedef = function
    [] -> false
  | C.SpecTypedef :: _ -> true
  | _ :: rest -> isTypedef rest
*)


let get_definitionloc (_, l) = l

let get_statementloc (_, l) = l

let explodeStringToInts (s: string) : int64 list =  
  let rec allChars i acc = 
    if i < 0 then acc
    else allChars (i - 1) (Int64.of_int (Char.code (String.get s i)) :: acc)
  in
  allChars (-1 + String.length s) []

let valueOfDigit chr =
  let int_value = 
    match chr with
      '0'..'9' -> (Char.code chr) - (Char.code '0')
    | 'a'..'z' -> (Char.code chr) - (Char.code 'a') + 10
    | 'A'..'Z' -> (Char.code chr) - (Char.code 'A') + 10
    | _ -> Errormsg.s (Errormsg.bug "not a digit") in
  Int64.of_int int_value
  
    
open Pretty
let d_cabsloc () (cl : C.cabsloc) =
  text cl.C.filename ++ text ":" ++ num cl.C.lineno
