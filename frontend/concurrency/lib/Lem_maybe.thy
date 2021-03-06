header{*Generated by Lem from maybe.lem.*}

theory "Lem_maybe" 

imports 
 	 Main
	 "Lem_bool" 
	 "Lem_basic_classes" 
	 "Lem_function" 

begin 

 

(*open import Bool Basic_classes Function*)

(* ========================================================================== *)
(* Basic stuff                                                                *)
(* ========================================================================== *)

(*type maybe 'a = 
  | Nothing
  | Just of 'a*)


(*val maybeEqual : forall 'a. Eq 'a => maybe 'a -> maybe 'a -> bool*)
(*val maybeEqualBy : forall 'a. ('a -> 'a -> bool) -> maybe 'a -> maybe 'a -> bool*)

fun maybeEqualBy  :: "('a \<Rightarrow> 'a \<Rightarrow> bool)\<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool "  where 
     " maybeEqualBy eq None None = ( True )"
|" maybeEqualBy eq None (Some _) = ( False )"
|" maybeEqualBy eq (Some _) None = ( False )"
|" maybeEqualBy eq (Some x') (Some y') = ( (eq x' y'))" 
declare maybeEqualBy.simps [simp del]
  


fun maybeCompare  :: "('b \<Rightarrow> 'a \<Rightarrow> ordering)\<Rightarrow> 'b option \<Rightarrow> 'a option \<Rightarrow> ordering "  where 
     " maybeCompare cmp None None = ( EQ )"
|" maybeCompare cmp None (Some _) = ( LT )"
|" maybeCompare cmp (Some _) None = ( GT )"
|" maybeCompare cmp (Some x') (Some y') = ( cmp x' y' )" 
declare maybeCompare.simps [simp del]



(* ----------------------- *)
(* maybe                   *)
(* ----------------------- *)

(*val maybe : forall 'a 'b. 'b -> ('a -> 'b) -> maybe 'a -> 'b*)
(*let maybe d f mb = match mb with 
  | Just a -> f a
  | Nothing -> d
end*)

(* ----------------------- *)
(* isJust / isNothing      *)
(* ----------------------- *)

(*val isJust : forall 'a. maybe 'a -> bool*)
(*let isJust mb = match mb with 
  | Just _ -> true
  | Nothing -> false
end*)

(*val isNothing : forall 'a. maybe 'a -> bool*)
(*let isNothing mb = match mb with 
  | Just _ -> false
  | Nothing -> true
end*)

(* ----------------------- *)
(* fromMaybe               *)
(* ----------------------- *)

(*val fromMaybe : forall 'a. 'a -> maybe 'a -> 'a*)
(*let fromMaybe d mb = match mb with
   | Just v  -> v
   | Nothing -> d
end*)

(* ----------------------- *)
(* map                     *)
(* ----------------------- *)

(*val map : forall 'a 'b. ('a -> 'b) -> maybe 'a -> maybe 'b*) 
(*let map f = maybe Nothing (fun v -> Just (f v))*)


(* ----------------------- *)
(* bind                    *)
(* ----------------------- *)

(*val bind : forall 'a 'b. maybe 'a -> ('a -> maybe 'b) -> maybe 'b*) 
(*let bind mb f = maybe Nothing f mb*)
end
