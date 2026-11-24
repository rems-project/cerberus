
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

Extraction Blacklist vector Vector String List Char Core Monad Bool Format Nat Int Option Base Numbers FMapAVL FMapFacts OrderedType Map.

(* Debugging print *)
Extraction NoInline Common.Utils.print_msg.
Extraction NoInline Common.Utils.sprint_msg.
Extract Constant Common.Utils.print_msg => "Stdlib.prerr_endline".
Extract Constant SailStdpp.Values.prerr_endline => "Stdlib.prerr_endline".
Extract Inlined Constant MorelloCapsGS.Capability_GS.strfcap => "strfcap".

(* Floating stuff *)
(* The IEEE 754 binary64 representation of floating values, as a signed 64 bit integer
   (CheriMorelloMemory converts it from/to bytes with [bytes_of_Z true]/[Z_of_bytes true]).
   NOTE: in the extracted code [Z] is Coq's module, hence the use of Big_int_Z *)
Extract Constant Common.Utils.bits_of_float =>
  "fun f -> Big_int_Z.big_int_of_int64 (Stdlib.Int64.bits_of_float (Float64.to_float f))".
Extract Constant Common.Utils.float_of_bits =>
  "fun z -> Float64.of_float (Stdlib.Int64.float_of_bits (Big_int_Z.int64_of_big_int z))".

(* Used by Coq's Real library *)
Extract Constant ClassicalDedekindReals.sig_forall_dec => "fun _ -> assert false".
Extract Constant ClassicalDedekindReals.sig_not_dec => false.  (* Ugh *)

(* Set Extraction AccessOpaque. *)

Extraction Library vector.
Recursive Extraction Library MorelloCapsGS.
Recursive Extraction Library CheriMorelloMemory.
