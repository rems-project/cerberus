
From CheriMemory Require CheriMemory.
From Morello Require Morello.

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

Extraction Blacklist String List Char Core Monad Bool Vector Format Nat Int Option Base Numbers FMapAVL OrderedType Map.

(* Debugging print *)
Extraction NoInline Common.Utils.print_msg.
Extract Constant Common.Utils.print_msg => "print_endline".
Extract Inlined Constant Morello.Capability.strfcap => "strfcap".

(* Used by Coq's Real library *)
Extract Constant ClassicalDedekindReals.sig_forall_dec => "fun _ -> assert false".
Extract Constant ClassicalDedekindReals.sig_not_dec => false.  (* Ugh *)

(* Set Extraction AccessOpaque. *)

Extraction Library Vector.
Recursive Extraction Library CheriMemory.

