header{*Generated by Lem from maybe_extra.lem.*}

theory "Lem_maybe_extra" 

imports 
 	 Main
	 "Lem_basic_classes" 
	 "Lem_maybe" 
	 "Lem_assert_extra" 

begin 

 

(*open import Basic_classes Maybe Assert_extra*)

(* ----------------------- *)
(* fromJust                *)
(* ----------------------- *)

(*val fromJust : forall 'a. maybe 'a -> 'a*)
(*let fromJust op = match op with | Just v -> v | Nothing -> failwith fromJust of Nothing end*)

end
