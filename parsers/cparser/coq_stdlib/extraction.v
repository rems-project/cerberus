Extract Inductive unit    => "unit" [ "()" ].
Extract Inductive bool    => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option  => "option" [ "Some" "None" ].
Extract Inductive list    => "list" [ "[]" "(::)" ].
Extract Inductive prod    => "(*)" [ "(,)" ].

Extraction Blacklist List String Int.

(* TODO: reduce the list to the toplevel modules, or alternatively
         I could even learn how to do it properly (...) *)
Require Init Program.
Require Arith NArith ZArith.
Require Bool Streams MSets FSets.
Require FMapAVL.

Extraction Library Basics.
Extraction Library BinInt.
Extraction Library BinNat.
Extraction Library BinPos.
Extraction Library Compare_dec.
Extraction Library Datatypes.
Extraction Library Equalities.
Extraction Library FMapAVL.
Extraction Library FMapList.
Extraction Library FSetAVL.
Extraction Library GenericMinMax.
Extraction Library Int.
Extraction Library List.
Extraction Library MSetAVL.
Extraction Library MSetInterface.
Extraction Library OrderedType.
Extraction Library Orders.
Extraction Library OrdersAlt.
Extraction Library OrdersFacts.
Extraction Library OrdersTac.
Extraction Library Peano.
Extraction Library Specif.
Extraction Library Streams.
Extraction Library Sumbool.
Extraction Library ZArith_dec.
Extraction Library ZOrderedType.
Extraction Library Zbool.
Extraction Library Zeven.
Extraction Library Zminmax. (* why isn't this extracting? *)
