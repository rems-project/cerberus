From Cerberus Require CheriMemory.
From Cerberus Require Morello.

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

Extraction Blacklist String List Char Core Monad Bool Vector Format Nat Int FMapAVL.

(* Debugging print *)
Extraction NoInline Cerberus.Utils.print_msg.
Extract Constant Cerberus.Utils.print_msg => "print_endline".
Extract Inlined Constant Morello.MorelloCapability.strfcap => "strfcap".

(* Set Extraction AccessOpaque. *)

Extraction Library Vector.
Recursive Extraction Library CheriMemory.
