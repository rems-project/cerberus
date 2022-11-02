From Cerberus Require CheriMemory.

From Coq Require Extraction.

Require ExtrOcamlBasic.
Require ExtrOcamlChar.
Require ExtrOcamlNativeString.
Require ExtrOCamlFloats.
Require ExtrOCamlInt63.

Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.

Extraction Language OCaml.
Unset Extraction Optimize. (* trying to make print_msg work *)

Extraction Blacklist String List Char Core Monad Bool Format Nat Int.

(* Debugging print *)
Extraction NoInline CheriMemory.print_msg.
Extract Constant CheriMemory.print_msg => "print_endline".

(* Set Extraction AccessOpaque. *)

Extraction Library Vector.
Recursive Extraction Library CheriMemory.
