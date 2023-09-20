
From CheriMemory Require CheriMorelloMemory.
From Morello Require MorelloCapsGS.

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

Require Import Coq.Vectors.Vector.
From stdpp Require Import vector.

Extraction Blacklist vector Vector String List Char Core Monad Bool Format Nat Int Option Base Numbers FMapAVL OrderedType Map.

(* Debugging print *)
Extraction NoInline Common.Utils.print_msg.
Extraction NoInline Common.Utils.sprint_msg.
Extract Constant Common.Utils.print_msg => "Stdlib.prerr_endline".
Extract Constant Sail.Values.prerr_endline => "Stdlib.prerr_endline".
Extract Inlined Constant MorelloCapsGS.Capability_GS.strfcap => "strfcap".

(* Used by Coq's Real library *)
Extract Constant ClassicalDedekindReals.sig_forall_dec => "fun _ -> assert false".
Extract Constant ClassicalDedekindReals.sig_not_dec => false.  (* Ugh *)

(* Set Extraction AccessOpaque. *)

Extraction Library vector.
Recursive Extraction Library MorelloCapsGS.
Recursive Extraction Library CheriMorelloMemory.
