theory Nondeterminism_lemmas

imports
Main
"lib/Nondeterminism"
begin

abbreviation mem (infixl "[\<in>]" 50) where "mem \<equiv> Nondeterminism.mem"
abbreviation nmem (infixl "[\<notin>]" 50) where "nmem x l \<equiv> \<not>(mem x l)"

lemma forget_mzero [simp]:
  shows "forget mzero = []"
unfolding forget.simps mzero_def
..

lemma member_mzero [simp]:
  shows "x [\<notin>] mzero"
unfolding mem_def
by simp

lemma forget_return [simp]:
  shows "forget (return x) = [x]"
unfolding forget.simps return_def
..

lemma member_return [simp]:
  shows "x [\<in>] return y = (x = y)"
unfolding mem_def
by simp

lemma forget_pick [simp]:
  shows "forget (pick m l) = l"
unfolding forget.simps pick_def
..

lemma member_pick [simp]:
  shows "x [\<in>] pick m l = (x \<in> set l)"
unfolding mem_def
by simp

lemma forget_kill [simp]:
  shows "forget (kill0 r) = []"
unfolding forget.simps kill0_def
by simp

lemma member_kill [simp]:
  shows "x [\<notin>] kill0 r"
unfolding mem_def
by simp

lemma forget_guard [simp]:
  shows "forget (guard b r) = (if b then [()] else [])"
unfolding forget.simps guard_def
by simp

lemma member_guard [simp]:
  shows "x [\<in>] guard b r = b"
unfolding mem_def
by simp

lemma forget_mplus [simp]:
  shows "forget (mplus l1 l2) = (forget l1 @ forget l2)"
apply (cases l1, cases l2, simp)
unfolding forget.simps mplus.simps
..

lemma member_mplus [simp]:
  shows "x [\<in>] mplus l1 l2 = (x [\<in>] l1 \<or> x [\<in>] l2)"
unfolding mem_def
by simp

lemma forget_msum_empty [simp]:
  shows "forget (msum []) = []"
unfolding msum_def
by simp

lemma member_msum_empty [simp]:
  shows "x [\<notin>] msum []"
unfolding mem_def
by simp

lemma forget_msum [simp]:
  shows "forget (msum l) = foldr append (map forget l) []"
proof (induct l)
  case Cons
  thus ?case
    unfolding forget.simps msum_def
    by simp
qed simp

(* Not that great as a simp, so not added to the simp set. *)
lemma set_foldr_append:
  shows "set (foldr append l []) = \<Union> set (map set l)"
by (induct l) auto

lemma member_msum [simp]:
  shows "x [\<in>] msum l = (\<exists>m\<in>set l. x [\<in>] m)"
unfolding mem_def
by (auto simp add: set_foldr_append)

(* Not that great as a simp, so not added to the simp set. *)
lemma forget_bindExhaustive:
  shows "forget (bindExhaustive m f) = foldr op @ (map (forget \<circ> f) (forget m)) []"
unfolding bindExhaustive_def
by simp

lemma member_bindExhaustive [simp]:
  shows "x [\<in>] bindExhaustive m f = (\<exists>y. y [\<in>] m \<and> x [\<in>] f y) "
unfolding mem_def 
by (auto simp add: forget_bindExhaustive set_foldr_append)

(* The following simps are not determined by the monad itself, but useful in proofs. *)

lemma member_if [simp]:
  shows "x [\<in>] (if b then m1 else m2) = (if b then x [\<in>] m1 else x [\<in>] m2)"
by auto

(* I don't know how to treat all the "case of" at once. The following only proves what I want in
   case of the option type. *)
lemma member_cases_maybe [simp]:
  shows "  x [\<in>] (case w of None \<Rightarrow> m1 | Some v \<Rightarrow> m2 v) 
         = (case w of None \<Rightarrow> x [\<in>] m1 | Some v \<Rightarrow> x [\<in>] m2 v)"
by (cases w) auto

end
