(* 

  Proving equivalence of the operational semantics and the axiomatic model
  Kyndylan Nienhuis 

Contents

Section 1 - Termination proofs, simplifications and auxilary lemmas
Section 2 - Soundness
Section 3 - The execution order of the operational semantics
Section 4 - Properties of happens-before
Section 5 - Invariance of consistency predicates under prefixes
Section 6 - Completeness

*)

theory "EquivalenceMinimalOpsem"

imports
Main
"_bin/Cmm_master"
"_bin/MinimalOpsem"
begin

(* Section 1 - Termination proofs, simplifications and auxilary lemmas-------------------------- *)

termination apply_tree by lexicographic_order

(* Simplifications of Lem-library functions *)

lemma isIrreflexive_empty [simp]:
  shows "isIrreflexive {}"
unfolding isIrreflexive_def
by simp

lemma isTransitive_empty [simp]:
  shows "isTransitive {}"
unfolding isTransitive_def
by simp

lemma isTransitive_trancl [simp]:
  shows "isTransitive (x\<^sup>+)"
unfolding isTransitive_def relApply_def
by auto

lemma isTransitive_cross [simp]:
  shows "isTransitive (x \<times> x)"
unfolding isTransitive_def relApply_def
by simp

lemma isStrictPartialOrder_empty [simp]:
  shows "isStrictPartialOrder {}"
unfolding isStrictPartialOrder_def
by simp

lemma relDomain_empty [simp]:
  shows "relDomain {} = {}"
unfolding relDomain_def
by simp

lemma relDomain_member [simp]:
  shows   "a \<in> relDomain x = (\<exists>b. (a, b) \<in> x)"
unfolding relDomain_def
by force

lemma relRange_empty [simp]:
  shows "relRange {} = {}"
unfolding relRange_def
by simp

lemma relRange_union [simp]:
  shows "relRange (x \<union> y) = relRange x \<union> relRange y"
unfolding relRange_def
by auto

lemma relRange_member [simp]:
  shows   "b \<in> relRange x = (\<exists>a. (a, b) \<in> x)"
unfolding relRange_def
by force

lemma relRange_cross_id [simp]:
  shows "relRange (x \<times> x) = x"
unfolding relRange_def
by simp

lemma relOver_empty [simp]:
  shows "relOver {} x"
unfolding relOver_def
by simp

lemma relOver_empty2 [simp]:
  shows "relOver x {} = (x = {})"
using assms 
unfolding relOver_def relDomain_def relRange_def 
by simp

lemma relOver_union [simp]:
  shows "relOver (x \<union> y) z = (relOver x z \<and> relOver y z)"
unfolding relOver_def relDomain_def relRange_def
by auto

lemma relOver_trancl [simp]:
  shows "relOver (x\<^sup>+) z = relOver x z"
unfolding relOver_def relDomain_def relRange_def
proof auto
  fix p q
  assume "fst ` x \<subseteq> z" "(p, q) \<in> x\<^sup>+"
  hence "\<exists>q'. (p, q') \<in> x" using tranclD by metis
  thus "p \<in> z" using `image fst x \<subseteq> z` by auto
next
  fix p q
  assume "snd ` x \<subseteq> z" "(p, q) \<in> x\<^sup>+"
  hence "\<exists>p'. (p', q) \<in> x" using tranclD2 by metis
  thus "q \<in> z" using `image snd x \<subseteq> z` by auto
qed

(* Other Cmm simpliations *)

lemma compose_simp [simp]:
  shows "compose0 a b = relComp a b"
unfolding compose0_def relComp_def
by auto

lemma finite_prefixes_empty [simp]:
  shows "finite_prefixes {} x"
unfolding finite_prefixes_def
by simp

lemma finite_prefixes_union [simp]:
  shows "finite_prefixes (r \<union> r') s = (finite_prefixes r s \<and> finite_prefixes r' s)"
unfolding finite_prefixes_def
by auto

lemma finite_prefixes_composition [simp]:
  assumes "finite_prefixes r s"
          "finite_prefixes r' s"
          "relOver r' s"
  shows "finite_prefixes (relComp r r') s"
unfolding finite_prefixes_def 
proof (intro ballI)
  fix c
  assume "c \<in> s"
  let ?S = "\<Union>b\<in>{b. (b, c) \<in> r'}. {a. (a, b) \<in> r}"
  have subset: "{a. (a, c) \<in> relComp r r'} \<subseteq> ?S"
    unfolding relComp_def by auto
  have "finite {b. (b, c) \<in> r'}" 
    using assms `c \<in> s` unfolding finite_prefixes_def by auto
  hence "finite ?S"
    proof (rule finite_UN_I, clarify)
      fix b
      assume "(b, c) \<in> r'"
      hence "b \<in> s" using `relOver r' s` unfolding relOver_def relDomain_def by auto
      thus "finite {a. (a, b) \<in> r}" using assms unfolding finite_prefixes_def by simp
    qed
  thus "finite {a. (a, c) \<in> relComp r r'}"
    using subset by (metis rev_finite_subset)
qed

lemma downclosed_empty [simp]:
  shows "downclosed {} x"
unfolding downclosed_def
by simp

lemma downclosed_union [simp]:
  shows "downclosed a (x \<union> y) = (downclosed a x \<and> downclosed a y)"
unfolding downclosed_def
by auto

lemma downclosed_trancl [simp]:
  shows "downclosed a (x\<^sup>+) = downclosed a x"
unfolding downclosed_def
proof auto
  fix p q
  assume IH: "\<forall>p. (\<exists>q. q \<in> a \<and> (p, q) \<in> x) \<longrightarrow> p \<in> a"
     and     "q \<in> a" "(p, q) \<in> x\<^sup>+"
  show "p \<in> a"
    using `(p, q) \<in> x\<^sup>+` `q \<in> a` 
    proof induct
      fix y
      assume "(p, y) \<in> x" "y \<in> a"
      thus "p \<in> a" using IH by auto
    next
      fix y z
      assume "(y, z) \<in> x" "y \<in> a \<Longrightarrow> p \<in> a" "z \<in> a"
      thus "p \<in> a" using IH by auto
    qed
qed

lemma selective_downclosed_empty [simp]:
  shows "selective_downclosed f {} x"
unfolding selective_downclosed_def
by simp

lemma selective_downclosed_setcomprehension [simp]:
  shows "downclosed a {p \<in> x. case p of (p1, p2) \<Rightarrow> f p2} = selective_downclosed f a x"
unfolding downclosed_def selective_downclosed_def
by auto

lemma selective_prefixes_are_final_empty [simp]:
  shows "selective_prefixes_are_final f {} x y"
unfolding selective_prefixes_are_final_def
by simp

(* Simplification for definedness *)

lemma exIsDefined_simp [simp]:
  shows "exIsDefined ex =
         (each_empty (undefined0 memory_model) ex \<and> sublanguage {ex})"
unfolding memory_model_def
          sc_fenced_memory_model_def
          locks_only_undefined_behaviour_def
          each_empty_def
          exIsDefined_def 
          getDefinedness_def 
          Let_def
by simp

(* Simplifications for restrictions *)

lemma relRestrict_empty1 [simp]:
  shows "relRestrict x {} = {}"
unfolding relRestrict_def
by simp

lemma relRestrict_empty2 [simp]:
  shows "relRestrict {} x = {}"
unfolding relRestrict_def
by simp

lemma relRestrict2_empty1 [simp]:
  shows "relRestrict2 x {} = {}"
unfolding relRestrict2_def
by simp

lemma relRestrict2_empty2 [simp]:
  shows "relRestrict2 {} x = {}"
unfolding relRestrict2_def
by simp

lemma relRestrict_member [simp]:
  shows "x \<in> relRestrict rel s = (x \<in> rel \<and> (fst x) \<in> s \<and> (snd x) \<in> s)"
unfolding relRestrict_def
by (cases x) force

lemma relRestrict2_member [simp]:
  shows "x \<in> relRestrict2 rel s = (x \<in> rel \<and> (fst x) \<in> s)"
unfolding relRestrict2_def
by auto

lemma relRestrict_isTransitive [simp]:
  assumes "isTransitive x"
  shows   "isTransitive (relRestrict x s)"
using assms
unfolding isTransitive_def relApply_def
by auto (metis (lifting) split_conv)

lemma relRestrict2_isTransitive [simp]:
  assumes "isTransitive x"
  shows   "isTransitive (relRestrict2 x s)"
using assms
unfolding isTransitive_def relApply_def
by auto (metis (lifting) split_conv)

lemma relRestrict_isIrreflexive [simp]:
  assumes "isIrreflexive x"
  shows   "isIrreflexive (relRestrict x s)"
using assms
unfolding isIrreflexive_def 
by auto 

lemma relRestrict2_isIrreflexive [simp]:
  assumes "isIrreflexive x"
  shows   "isIrreflexive (relRestrict2 x s)"
using assms
unfolding isIrreflexive_def 
by auto 

lemma relOver_relRestrict [simp]:
  assumes "relOver x z"
  shows   "relOver (relRestrict x s) z"
using assms
unfolding relOver_def 
(* TODO: remove apply style *)
apply auto 
apply (metis relDomain_member set_rev_mp)
apply (metis relRange_member set_rev_mp)
done

lemma relOver_relRestrict2 [simp]:
  assumes "relOver x z"
  shows   "relOver (relRestrict2 x s) z"
using assms
unfolding relOver_def 
by auto (metis relRange_member set_rev_mp)

lemma witnessRestrict_multiple [simp]:
  shows "witnessRestrict (witnessRestrict x y) z = witnessRestrict x (y \<inter> z)"
unfolding witnessRestrict_def 
by auto

lemma witnessRestrict_empty1 [simp]:
  shows "witnessRestrict wit {} = initialWitness"
unfolding witnessRestrict_def initialWitness_def 
by simp

lemma witnessRestrict_empty2 [simp]:
  shows "witnessRestrict initialWitness x = initialWitness"
unfolding witnessRestrict_def initialWitness_def 
by simp

lemma witnessRestrict_simps [simp]:
  shows "rf (witnessRestrict wit actions) = relRestrict (rf wit) actions"
        "mo (witnessRestrict wit actions) = relRestrict2 (mo wit) actions"
        "sc (witnessRestrict wit actions) = relRestrict (sc wit) actions"
        "lo (witnessRestrict wit actions) = relRestrict (lo wit) actions"
        "tot (witnessRestrict wit actions) = relRestrict (tot wit) actions"
unfolding witnessRestrict_def
by simp_all

lemma initialWitness_simps [simp]:
  shows "rf initialWitness = {}"
        "mo initialWitness = {}"
        "sc initialWitness = {}"
        "lo initialWitness = {}"
        "tot initialWitness = {}"
unfolding initialWitness_def
by simp_all

(* Simplifications for memory-models *)

lemma release_acquire_fenced_simps [simp]:
  shows "consistent sc_fenced_memory_model = sc_fenced_consistent_execution"
        "relation_calculation sc_fenced_memory_model = release_acquire_fenced_relations"
        "undefined0 sc_fenced_memory_model = locks_only_undefined_behaviour"
unfolding sc_fenced_memory_model_def
by simp_all

(* Simplifications for states *)

lemma initialState_simps [simp]:
  shows "exWitness (initialState pre) = initialWitness"
        "committed (initialState pre) = {}"
        "stateIsDefined (initialState pre) = exIsDefined (pre, initialWitness, getRelations pre initialWitness)"
unfolding initialState_def
by simp_all

(* Simplifications for relation_list in consistency predicates *)

(* To avoid looping, the simps require rel \<noteq> []. In some cases rel will 
   be getOtherRel, so it's useful to prove that list to be non-empty. *)
lemma getOtherRel_nonempty [simp]:
  shows "getOtherRel pre wit \<noteq> []"
unfolding getOtherRel_def 
          memory_model_def
          sc_fenced_memory_model_def
by (simp add: release_acquire_fenced_relations_def Let_def)

lemma rel_list_assumptions [simp]:
  assumes "rel \<noteq> []"
  shows   "assumptions (pre, wit, rel) = assumptions (pre, wit,[])"
unfolding assumptions.simps ..

lemma rel_list_coherent_memory_use [simp]:
  assumes "rel \<noteq> []"
  shows   "coherent_memory_use (pre, wit, (''hb'', hb)#rel) = 
             coherent_memory_use (pre, wit, [(''hb'', hb)])"      
unfolding coherent_memory_use.simps ..

lemma rel_list_consistent_atomic_rf [simp]:
  assumes "rel \<noteq> []"
  shows   "consistent_atomic_rf (pre, wit, (''hb'', hb)#rel) = 
             consistent_atomic_rf (pre, wit, [(''hb'', hb)])"      
unfolding consistent_atomic_rf.simps ..

lemma rel_list_consistent_hb [simp]:
  assumes "rel \<noteq> []"
  shows    "consistent_hb (pre, wit, (''hb'', hb)#rel) = 
             consistent_hb (pre, wit, [(''hb'', hb)])"      
unfolding consistent_hb.simps ..

lemma rel_list_consistent_mo [simp]:
  assumes "rel \<noteq> []"
  shows   "consistent_mo (pre, wit, rel) = consistent_mo (pre, wit, [])"
unfolding consistent_mo.simps ..

lemma rel_list_consistent_mo_op [simp]:
  assumes "rel \<noteq> []"
  shows   "consistent_mo_op actions (pre, wit, rel) = consistent_mo_op actions (pre, wit, [])"
unfolding consistent_mo_op.simps ..

lemma rel_list_consistent_non_atomic_rf [simp]:
  assumes "rel \<noteq> []"
  shows    "consistent_non_atomic_rf (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             consistent_non_atomic_rf (pre, wit, [(''hb'', hb),(''vse'', vse)])"    
unfolding consistent_non_atomic_rf.simps ..

lemma rel_list_det_read [simp]:
  assumes "rel \<noteq> []"
  shows   "det_read (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])"          
unfolding det_read.simps ..

lemma rel_list_det_read_op [simp]:
  assumes "rel \<noteq> []"
  shows   "det_read_op actions (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             det_read_op actions (pre, wit, [(''hb'', hb),(''vse'', vse)])"          
unfolding det_read_op.simps ..

lemma rel_list_isInOpsemOrder [simp]:
  assumes "rel \<noteq> []"
  shows   "isInOpsemOrder actions (pre, wit, rel) = isInOpsemOrder actions (pre, wit, [])"
unfolding isInOpsemOrder.simps ..

lemma rel_list_locks_only_consistent_lo [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_lo (pre, wit, (''hb'', hb)#rel) = 
             locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
unfolding locks_only_consistent_lo.simps ..

lemma rel_list_locks_only_consistent_lo_op [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_lo_op actions (pre, wit, (''hb'', hb)#rel) = 
             locks_only_consistent_lo_op actions (pre, wit, [(''hb'', hb)])"
unfolding locks_only_consistent_lo_op.simps ..

lemma rel_list_locks_only_consistent_locks [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_locks (pre, wit, rel) = locks_only_consistent_locks (pre, wit, [])"
unfolding locks_only_consistent_locks.simps ..

lemma rel_list_locks_only_consistent_locks_op [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_locks_op actions (pre, wit, rel) = 
             locks_only_consistent_locks_op actions (pre, wit, [])"
unfolding locks_only_consistent_locks_op.simps ..

lemma rel_list_rmw_atomicity [simp]:
  assumes "rel \<noteq> []"
  shows   "rmw_atomicity (pre, wit, rel) = rmw_atomicity (pre, wit, [])"     
unfolding rmw_atomicity.simps ..

lemma rel_list_rmw_atomicity_op [simp]:
  assumes "rel \<noteq> []"
  shows   "rmw_atomicity_op actions (pre, wit, rel) = rmw_atomicity_op actions (pre, wit, [])"     
unfolding rmw_atomicity_op.simps ..

lemma rel_list_sc_accesses_consistent_sc [simp]:
  assumes "rel \<noteq> []"
  shows   "sc_accesses_consistent_sc (pre, wit, (''hb'', hb)#rel) = 
             sc_accesses_consistent_sc (pre, wit, [(''hb'', hb)])"
unfolding sc_accesses_consistent_sc.simps ..

lemma rel_list_sc_accesses_consistent_sc_op [simp]:
  assumes "rel \<noteq> []"
  shows   "sc_accesses_consistent_sc_op actions (pre, wit, (''hb'', hb)#rel) = 
             sc_accesses_consistent_sc_op actions (pre, wit, [(''hb'', hb)])"
unfolding sc_accesses_consistent_sc_op.simps ..

lemma rel_list_sc_fenced_sc_fences_heeded [simp]:
  assumes "rel \<noteq> []"
  shows   "sc_fenced_sc_fences_heeded (pre, wit, rel) = sc_fenced_sc_fences_heeded (pre, wit, [])"  
unfolding sc_fenced_sc_fences_heeded.simps ..

lemma rel_list_tot_empty [simp]:
  assumes "rel \<noteq> []"
  shows   "tot_empty (pre, wit, rel) = tot_empty (pre, wit,[])"
unfolding tot_empty.simps ..

lemma rel_list_well_formed_rf [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_rf (pre, wit, rel) = well_formed_rf (pre, wit, [])"
unfolding well_formed_rf.simps ..

lemma rel_list_well_formed_rf_op [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_rf_op actions (pre, wit, rel) = well_formed_rf_op actions (pre, wit, [])"
unfolding well_formed_rf_op.simps ..

lemma rel_list_well_formed_threads [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_threads (pre, wit, rel) = well_formed_threads (pre, wit, [])"
unfolding well_formed_threads.simps ..

lemma rel_list_sc_accesses_sc_reads_restricted [simp]:
  assumes "rel \<noteq> []"
  shows   "sc_accesses_sc_reads_restricted (pre, wit, (''hb'', hb)#rel) = 
             sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', hb)])"  
unfolding sc_accesses_sc_reads_restricted.simps ..

lemma rel_list_sc_fenced_consistent_execution [simp]:
  assumes "rel \<noteq> []"
  shows   "apply_tree sc_fenced_consistent_execution (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             apply_tree sc_fenced_consistent_execution (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
using assms     
unfolding sc_fenced_consistent_execution_def
by simp

lemma rel_list_exIsConsistent [simp]:
  assumes "rel \<noteq> []"
  shows   "exIsConsistent (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             exIsConsistent (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
using assms     
unfolding exIsConsistent_def memory_model_def 
by simp

lemma rel_list_exIsConsistent_op [simp]:
  assumes "rel \<noteq> []"
  shows   "exIsConsistent_op actions (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             exIsConsistent_op actions (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
using assms     
unfolding exIsConsistent_op_def memory_model_def 
by simp

lemma rel_list_unsequenced_races [simp]:
  assumes "rel \<noteq> []"
  shows   "unsequenced_races (pre, wit, rel) = 
             unsequenced_races (pre, wit, [])"  
unfolding unsequenced_races.simps ..

lemma rel_list_data_races [simp]:
  assumes "rel \<noteq> []"
  shows   "data_races (pre, wit, (''hb'', hb)#rel) = 
             data_races (pre, wit, [(''hb'', hb)])"  
unfolding data_races.simps ..

lemma rel_list_indeterminate_reads [simp]:
  assumes "rel \<noteq> []"
  shows   "indeterminate_reads (pre, wit, rel) = 
             indeterminate_reads (pre, wit, [])"  
unfolding indeterminate_reads.simps ..

lemma rel_list_locks_only_bad_mutexes [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_bad_mutexes (pre, wit, rel) = 
             locks_only_bad_mutexes (pre, wit, [])"  
unfolding locks_only_bad_mutexes.simps ..

lemma rel_list_locks_only_undefined_behaviour [simp]:
  assumes "rel \<noteq> []"
  shows   "each_empty locks_only_undefined_behaviour (pre, wit, (''hb'', hb)#rel) = 
             each_empty locks_only_undefined_behaviour (pre, wit, [(''hb'', hb)])"  
using assms
unfolding locks_only_undefined_behaviour_def each_empty_def
by simp

lemma rel_list_sublanguage [simp]:
  assumes "rel \<noteq> [] \<or> wit \<noteq> initialWitness"
  shows   "sublanguage {(pre, wit, rel)} = sublanguage {(pre, initialWitness, [])}"
unfolding sublanguage_def sc_fenced_condition_def
by simp

lemma rel_list_exIsDefined [simp]:
  assumes "rel \<noteq> []"
  shows   "exIsDefined (pre, wit, (''hb'', hb)#rel) = exIsDefined (pre, wit, [(''hb'', hb)])"
using assms
unfolding exIsDefined_simp memory_model_def
by simp

(* The following function wraps a Lem-library function, so we always simplify it. *)
declare relation_over_def [simp]
(* Simplifications for projection functions *)
declare aid_of.simps [simp]
declare tid_of.simps [simp]
declare loc_of.simps [simp]
declare value_read_by.simps [simp]
declare value_written_by.simps [simp]
declare is_lock.simps [simp]
declare is_successful_lock.simps [simp]
declare is_blocked_lock.simps [simp]
declare is_unlock.simps [simp]
declare is_atomic_load.simps [simp]
declare is_atomic_store.simps [simp]
declare is_RMW.simps [simp]
declare is_blocked_rmw.simps [simp]
declare is_NA_load.simps [simp]
declare is_NA_store.simps [simp]
declare is_load.simps [simp]
declare is_store.simps [simp]
declare is_fence.simps [simp]
declare is_atomic_action.simps [simp]
declare is_read.simps [simp]
declare is_write.simps [simp]
declare is_acquire.simps [simp]
declare is_release.simps [simp]
declare is_consume.simps [simp]
declare is_seq_cst.simps [simp]

(* Simplification of definitions that should have been funs *)

lemma is_alloc_simp1 [simp]:
  shows "is_alloc (Alloc aid tid loc)"
        "\<not> is_alloc (Load aid tid mem loc val)"
        "\<not> is_alloc (Store aid tid mem loc val)"
        "\<not> is_alloc (RMW aid tid mem loc val val2)"
        "\<not> is_alloc (Blocked_rmw aid tid loc)"
        "\<not> is_alloc (Lock aid tid loc outcome)"
        "\<not> is_alloc (Unlock aid tid loc)"
        "\<not> is_alloc (Fence aid tid mem)"
        "\<not> is_alloc (Dealloc aid tid loc)"
unfolding is_alloc_def by simp_all

lemma is_dealloc_simp1 [simp]:
  shows "is_dealloc (Dealloc aid tid loc)"
        "\<not> is_dealloc (Load aid tid mem loc val)"
        "\<not> is_dealloc (Store aid tid mem loc val)"
        "\<not> is_dealloc (RMW aid tid mem loc val val2)"
        "\<not> is_dealloc (Blocked_rmw aid tid loc)"
        "\<not> is_dealloc (Lock aid tid loc outcome)"
        "\<not> is_dealloc (Unlock aid tid loc)"
        "\<not> is_dealloc (Fence aid tid mem)"
        "\<not> is_dealloc (Alloc aid tid loc)"
unfolding is_dealloc_def by simp_all

(* Auxilary lemmas (not added to the simp-set) *)

(* We do not add this to the simp set, because then relOver would always be unfolded. *)
lemma relOver_simp:
  shows "relOver r s = (r \<subseteq> s \<times> s)"
unfolding relOver_def relDomain_def relRange_def
by auto

lemma relOver_relComp:
  assumes "relOver r z"
          "relOver s z"
  shows "relOver (relComp r s) z"
using assms
unfolding relComp_def relOver_def relDomain_def relRange_def
by auto

lemma transitive_simp:
  assumes "isTransitive r"
      and "(a, b) \<in> r"
      and "(b, c) \<in> r"
  shows   "(a, c) \<in> r"
using assms
unfolding isTransitive_def relApply_def
by auto

lemma na_implies_not_at:
  assumes "is_at_non_atomic_location p_lk a"
  shows   "\<not> is_at_atomic_location p_lk a"
using assms
unfolding is_at_non_atomic_location_def is_at_atomic_location_def
by (cases a) simp_all

lemma at_implies_not_na:
  assumes "is_at_atomic_location p_lk a"
  shows   "\<not> is_at_non_atomic_location p_lk a"
using assms
unfolding is_at_non_atomic_location_def is_at_atomic_location_def
by (cases a) simp_all

lemma finite_prefix_subset:
  assumes "finite_prefixes r s"
          "r' \<subseteq> r"
  shows   "finite_prefixes r' s"
unfolding finite_prefixes_def
proof
  fix b
  assume "b \<in> s"
  hence "finite {a. (a, b) \<in> r}"
    using assms unfolding finite_prefixes_def by simp
  have "{a. (a, b) \<in> r'} \<subseteq> {a. (a, b) \<in> r}"
    using `r' \<subseteq> r` by auto
  thus "finite {a. (a, b) \<in> r'}"
    using `finite {a. (a, b) \<in> r}` by (metis rev_finite_subset)
qed

lemma trancl_mono2:
  assumes "x \<subseteq> y"
  shows   "x\<^sup>+ \<subseteq> y\<^sup>+"
using assms
by (metis subsetI trancl_mono)

lemma trancl_mono3:
  assumes "isTransitive y"
  shows   "x\<^sup>+ \<subseteq> y = (x \<subseteq> y)"
proof -
  have "y = y\<^sup>+"
    (* TODO: can't get induct to work without verbose proof. *)
    proof auto
      fix a b
      assume "(a, b) \<in> y\<^sup>+"
      thus "(a, b) \<in> y"
        apply induct
        using assms
        unfolding isTransitive_def relApply_def
        by auto
    qed
  hence "x \<subseteq> y \<Longrightarrow> x\<^sup>+ \<subseteq> y"
    using trancl_mono2 by blast
  thus ?thesis by auto
qed

lemma relComp_mono:
  assumes "x \<subseteq> x2"
          "y \<subseteq> y2"
  shows   "relComp x y \<subseteq> relComp x2 y2"
using assms
unfolding relComp_def
by blast

lemma downclosed_subset:
  assumes "r \<subseteq> r'"
          "downclosed a r'"
  shows   "downclosed a r"
using assms
unfolding downclosed_def
by auto

lemma cons_assumptions:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "assumptions (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_tot_empty:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "tot_empty (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_well_formed_threads:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "well_formed_threads (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_well_formed_rf:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "well_formed_rf (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_locks_only_consistent_locks:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "locks_only_consistent_locks (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_locks_only_consistent_lo:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_consistent_mo:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_mo (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_sc_accesses_consistent_sc:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_sc_fenced_sc_fences_heeded:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "sc_fenced_sc_fences_heeded (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_consistent_hb:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_det_read:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "det_read (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_consistent_non_atomic_rf:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_consistent_atomic_rf:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_atomic_rf (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_coherent_memory_use:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "coherent_memory_use (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_rmw_atomicity:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "rmw_atomicity (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

lemma cons_sc_accesses_sc_reads_restricted:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def 
          sc_fenced_memory_model_def
          sc_fenced_consistent_execution_def
          getRelations_def
by simp

(* Section 2 - Soundness ---------------------------------------------------------------------- *)

lemma consistencySpecTrace: 
  assumes "minOpsemTrace pre r s"
          "r = initialState pre"
  shows   "exIsConsistent_op (committed s) (pre, (exWitness s), getRelations pre (exWitness s))"
using assms 
proof induct
  case minOpsemReflexive
  thus ?case by simp
next
  case minOpsemStep
  thus ?case unfolding minOpsemStep_def Let_def by auto
qed 

lemma isDefinedCorrespondence:
  assumes "minOpsemTrace pre r s"
          "r = initialState pre"
  shows   "stateIsDefined s = exIsDefined (pre, (exWitness s), getRelations pre (exWitness s))"
using assms
proof induct
  case minOpsemReflexive
  show ?case using minOpsemReflexive by simp
next
  case minOpsemStep
  thus ?case unfolding minOpsemStep_def Let_def by auto
qed 

(* The following predicate should be true independend of which memory_model is used, but its 
   proof does depend on the memory_model *)

lemma getRelationsIdentity: 
  shows "getRelations pre wit = relation_calculation memory_model pre wit"
unfolding memory_model_def 
          sc_fenced_memory_model_def 
          getRelations_def
          getHb_def
          getVse_def
          getOtherRel_def
          Let_def
by (auto simp add: release_acquire_fenced_relations_def Let_def)

(* The _opsem variants of the consistency predicates imply the corresponding consistency 
   predicates if all actions have been committed *)

lemma consistent_mo_resolution:
  assumes "consistent_mo_op (actions0 pre) (pre, wit, [])"
  shows   "consistent_mo (pre, wit, [])"
using assms
unfolding consistent_mo.simps consistent_mo_op.simps 
by simp

lemma det_read_resolution:
  assumes "det_read_op (actions0 pre) (pre, wit, [(''hb'', hb),(''vse'', vse)])"
  shows   "det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])"
using assms
unfolding det_read.simps det_read_op.simps 
by simp

lemma locks_only_consistent_lo_resolution:
  assumes "locks_only_consistent_lo_op (actions0 pre) (pre, wit, [(''hb'', hb)])"
  shows   "locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
using assms
unfolding locks_only_consistent_lo.simps locks_only_consistent_lo_op.simps
by simp

lemma locks_only_consistent_locks_resolution:
  assumes "locks_only_consistent_locks_op (actions0 pre) (pre, wit, [])"
          "relation_over (actions0 pre) (lo wit)"
  shows   "locks_only_consistent_locks (pre, wit, [])"
unfolding locks_only_consistent_locks.simps
proof auto
  fix a b
  assume assms2: "is_successful_lock a"
                 "is_successful_lock b"
                 "(a, b) \<in> lo wit"
  hence assms3: "b \<in> actions0 pre" using assms unfolding relation_over_def relOver_def by force
  obtain c where "c \<in> actions0 pre \<and> is_unlock c \<and> (a, c) \<in> lo wit \<and> (c, b) \<in> lo wit"
    using assms assms2 assms3 unfolding locks_only_consistent_locks_op.simps by blast
  thus "\<exists>c\<in>actions0 pre. is_unlock c \<and> (a, c) \<in> lo wit \<and> (c, b) \<in> lo wit"
    using assms3 by fast
qed

lemma rmw_atomicity_resolution:
  assumes "rmw_atomicity_op (actions0 pre) (pre, wit, [])"
  shows   "rmw_atomicity (pre, wit, [])"
using assms
unfolding rmw_atomicity.simps rmw_atomicity_op.simps
by simp

lemma sc_accesses_consistent_sc_resolution:
  assumes "sc_accesses_consistent_sc_op (actions0 pre) (pre, wit, [(''hb'', hb)])"
  shows   "sc_accesses_consistent_sc (pre, wit, [(''hb'', hb)])"
using assms
unfolding sc_accesses_consistent_sc.simps sc_accesses_consistent_sc_op.simps
by simp

lemma well_formed_rf_resolution:
  assumes "well_formed_rf_op (actions0 pre) (pre, wit, [])"
  shows   "well_formed_rf (pre, wit, [])"
using assms
unfolding well_formed_rf.simps well_formed_rf_op.simps 
by clarsimp auto

lemma execution_resolution:
  assumes "exIsConsistent_op (actions0 pre) (pre, wit, [(''hb'',hb),(''vse'',vse)])"
  shows   "exIsConsistent (pre, wit, [(''hb'',hb),(''vse'',vse)])"
proof -
  have "relation_over (actions0 pre) (lo wit)"
    using assms
    unfolding exIsConsistent_op_def
    by (simp add: locks_only_consistent_lo_op.simps)
  thus ?thesis
    using assms 
    unfolding exIsConsistent_def
              exIsConsistent_op_def
              memory_model_def
              sc_fenced_memory_model_def
              sc_fenced_consistent_execution_def
    by (auto simp add: well_formed_rf_resolution
              locks_only_consistent_locks_resolution
              locks_only_consistent_lo_resolution
              consistent_mo_resolution
              sc_accesses_consistent_sc_resolution
              det_read_resolution
              rmw_atomicity_resolution)
qed

lemma soundnessConsistency:
  assumes "minOpsemConsistent opsem_t p (pre, wit)"
  shows   "axiomConsistent opsem_t p (pre, wit, relation_calculation memory_model pre wit)"
using assms
proof -
  assume "minOpsemConsistent opsem_t p (pre, wit)"
  from this obtain s where as1: "minOpsemTrace pre (initialState pre) s"
                     and   as2: "exWitness s = wit"
                     and   as3: "opsem_t p pre"
                     and   as4: "committed s = actions0 pre"
    unfolding minOpsemConsistent_def by auto
  have "exIsConsistent_op (committed s) (pre, wit, getRelations pre wit)" 
    by (metis as1 as2 consistencySpecTrace)
  hence "exIsConsistent (pre, wit, getRelations pre wit)" 
    unfolding getRelations_def 
    using execution_resolution as4 
    by simp
  hence "exIsConsistent (pre, wit, relation_calculation memory_model pre wit)" 
    using getRelationsIdentity by auto
  thus "axiomConsistent opsem_t p (pre, wit, (relation_calculation memory_model) pre wit)"
    unfolding exIsConsistent_def axiomConsistent.simps
    using assms as3 by auto
qed

lemma soundnessUndefinedness:
  assumes "minOpsemUndefined opsem_t p (pre, wit)"
  shows   "\<exists>pre wit rl. axiomUndefined opsem_t p (pre, wit, rl)"
proof (intro exI[where x=pre] exI[where x=wit] exI[where x="relation_calculation memory_model pre wit"])
  from assms obtain s where as1: "minOpsemTrace pre (initialState pre) s"
                     and   as2: "exWitness s = wit"
                     and   as3: "opsem_t p pre"
                     and   as4: "committed s = actions0 pre"
                     and   as5: "\<not> stateIsDefined s"
    unfolding minOpsemUndefined_def by auto
  hence "minOpsemConsistent opsem_t p (pre, wit)"
    unfolding minOpsemConsistent_def by auto
  hence axiomConsistent: "axiomConsistent opsem_t p (pre, wit, relation_calculation memory_model pre wit)"
    using getRelationsIdentity by (metis soundnessConsistency)
  have "\<not> exIsDefined (pre, wit, getRelations pre wit)"
    using as1 as2 as5 by (metis isDefinedCorrespondence)
  hence "\<not> exIsDefined (pre, wit, relation_calculation memory_model pre wit)"
    using getRelationsIdentity unfolding getRelations_def by simp
  thus "axiomUndefined opsem_t p (pre, wit, relation_calculation memory_model pre wit)"
    using axiomConsistent unfolding axiomUndefined_def by simp
qed

(* Section 3 - The execution order of the operational semantics ------------------------------- *)

(* To show completeness with respect to the axiomatic model, we execute actions of a consistent
   execution in a particular order. In this section we prove that such an order exists *)

lemma opsemOrder_isStrictPartialOrder:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "isStrictPartialOrder (opsemOrder pre wit)"
proof -

  (* We need the following consistency predicates *)
  have cons_mo: "consistent_mo (pre, wit, [])"
    using assms cons_consistent_mo by simp
  have cons_hb: "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
    using assms  cons_consistent_hb by simp
  have cons_rf: "well_formed_rf (pre, wit, [])"
    using assms  cons_well_formed_rf by simp
  have cons_rmw: "rmw_atomicity (pre, wit, [])"
    using assms cons_rmw_atomicity by simp
  have cons_na_rf: "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
    using assms cons_consistent_non_atomic_rf by simp

  have mo_atomic_writes: "\<And>a b. ((a, b) \<in> mo wit \<or> (b, a) \<in> mo wit) \<Longrightarrow> \<not>is_na_or_non_write pre a"
    proof -
      fix a b
      assume in_mo: "(a, b) \<in> mo wit \<or> (b, a) \<in> mo wit"
      hence "a \<in> actions0 pre" "b \<in> actions0 pre"
        using cons_mo
        unfolding consistent_mo.simps 
                  relation_over_def 
                  relOver_def 
                  relDomain_def 
                  relRange_def
        by auto
      hence "is_write a" "is_at_atomic_location (lk pre) a" 
        using cons_mo in_mo
        unfolding consistent_mo.simps
        by auto
      thus "\<not> is_na_or_non_write pre a"
        unfolding is_na_or_non_write_def 
                  is_at_atomic_location_def
                  is_at_non_atomic_location_def
        by (cases "loc_of a") auto
    qed

  have rf_read_write: "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> 
                              is_write a \<and> is_read b \<and> loc_of a = loc_of b \<and> a \<in> actions0 pre \<and> b \<in> actions0 pre"
    proof -
      fix a b
      assume in_rf: "(a, b) \<in> rf wit"
      thus "is_write a \<and> is_read b \<and> loc_of a = loc_of b \<and> a \<in> actions0 pre \<and> b \<in> actions0 pre"
        using cons_rf
        unfolding well_formed_rf.simps
        by auto
    qed

  have non_atomic_rf_in_hb: "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> 
                                    is_na_or_non_write pre a \<Longrightarrow> 
                                    (a, b) \<in> hbMinus pre wit"
    proof -
      fix a b
      assume "(a, b) \<in> rf wit"
             "is_na_or_non_write pre a"
      have "is_write a" "is_read b" "loc_of a = loc_of b" using `(a, b) \<in> rf wit` rf_read_write by metis+
      hence "is_at_non_atomic_location (lk pre) a"
        using `is_na_or_non_write pre a` unfolding is_na_or_non_write_def by simp
      hence "is_at_non_atomic_location (lk pre) b"
        using `loc_of a = loc_of b`
        unfolding is_at_non_atomic_location_def by auto
      hence "is_na_or_non_write pre b"
        unfolding is_na_or_non_write_def by simp
      have "(a, b) \<in> getHb pre wit"
        using `is_at_non_atomic_location (lk pre) b` 
        using cons_na_rf `(a, b) \<in> rf wit` 
        unfolding consistent_non_atomic_rf.simps getVse_def visible_side_effect_set_def
        by auto
      thus "(a, b) \<in> hbMinus pre wit"
        using `is_na_or_non_write pre b` 
        unfolding hbMinus_def by simp
    qed

  have na_in_hbMinus: "\<And>a b. (a, b) \<in> hbMinus pre wit \<union> rf wit \<union> mo wit \<Longrightarrow>
                              is_na_or_non_write pre a \<Longrightarrow> 
                              (a, b) \<in> hbMinus pre wit"
    using mo_atomic_writes non_atomic_rf_in_hb
    by auto

  have a_in_mo: "\<And>a b. (a, b) \<in> hbMinus pre wit \<union> rf wit \<union> mo wit \<Longrightarrow>
                 \<not> is_na_or_non_write pre b \<Longrightarrow> 
                 (a, b) \<in> mo wit"
    proof -
      fix a b
      assume in_eb: "(a, b) \<in> hbMinus pre wit \<union> rf wit \<union> mo wit"
             "\<not> is_na_or_non_write pre b"
      show "(a, b) \<in> mo wit"
        proof (cases "is_read b")
          assume "\<not> is_read b"
          hence "(a, b) \<notin> rf wit" using rf_read_write by auto
          thus "(a, b) \<in> mo wit" using in_eb unfolding hbMinus_def by auto
        next
          assume "is_read b"
          hence "is_RMW b" 
            using `\<not> is_na_or_non_write pre b`
            unfolding is_na_or_non_write_def
            by (cases b) simp_all
          show "(a, b) \<in> mo wit" 
            proof (cases "(a, b) \<in> rf wit")
              assume "(a, b) \<notin> rf wit"
              thus "(a, b) \<in> mo wit" using in_eb unfolding hbMinus_def by auto
            next
              assume "(a, b) \<in> rf wit"
              thus "(a, b) \<in> mo wit" 
                using cons_rmw `is_RMW b` rf_read_write 
                unfolding rmw_atomicity.simps adjacent_less_than_def
                by auto
            qed
        qed
     qed

  have "trans (mo wit)"
    using cons_mo 
    unfolding consistent_mo.simps
    unfolding trans_def isTransitive_def relApply_def 
    by auto
  hence "(mo wit)\<^sup>+ = mo wit" by simp
  hence "isIrreflexive ((mo wit)\<^sup>+)"
    using cons_mo unfolding consistent_mo.simps by simp

  let ?hb_minus = "hbMinus pre wit"

  have "?hb_minus \<subseteq> getHb pre wit" unfolding hbMinus_def by auto
  hence "?hb_minus\<^sup>+ \<subseteq> (getHb pre wit)\<^sup>+" using trancl_mono2 by auto
  hence "isIrreflexive (?hb_minus\<^sup>+)"
    using cons_hb 
    unfolding consistent_hb.simps isIrreflexive_def
    by auto

  let ?eb = "opsemOrder pre wit"  

  have "\<And>a b. \<lbrakk>(a, b) \<in> ?eb; is_na_or_non_write pre a\<rbrakk> \<Longrightarrow> (a, b) \<in> ?hb_minus\<^sup>+"
    unfolding opsemOrder_def
    proof (erule trancl_induct)
      fix a y
      assume "is_na_or_non_write pre a" 
             "(a, y) \<in> hbMinus pre wit \<union> (rf wit \<union> mo wit)"
      hence "(a, y) \<in> ?hb_minus" using na_in_hbMinus by auto
      thus "(a, y) \<in> ?hb_minus\<^sup>+" by auto
    next
      fix a b y z
      assume "is_na_or_non_write pre a"
             "(a, y) \<in> (hbMinus pre wit \<union> (rf wit \<union> mo wit))\<^sup>+"
             "(y, z) \<in> hbMinus pre wit \<union> (rf wit \<union> mo wit)"
             "(a, y) \<in> ?hb_minus\<^sup>+"
      hence "\<exists>c. (c, y) \<in> ?hb_minus" 
        using tranclD2[where R="?hb_minus"] by auto
      hence "is_na_or_non_write pre y" unfolding hbMinus_def by simp   
      hence "(y, z) \<in> ?hb_minus"
        using `(y, z) \<in> hbMinus pre wit \<union> (rf wit \<union> mo wit)`
        using na_in_hbMinus by auto
      thus "(a, z) \<in> ?hb_minus\<^sup>+" 
        using `(a, y) \<in> ?hb_minus\<^sup>+` 
        by (auto simp add: trancl_into_trancl)
    qed
  hence irreflexive_na_non_write: "\<And>a b. \<lbrakk>(a, b) \<in> ?eb; is_na_or_non_write pre a\<rbrakk> \<Longrightarrow> a \<noteq> b"
    using `isIrreflexive (?hb_minus\<^sup>+)`
    unfolding isIrreflexive_def
    by blast

  have "\<And>a b. \<lbrakk>(a, b) \<in> ?eb; \<not> is_na_or_non_write pre b\<rbrakk> \<Longrightarrow> (a, b) \<in> (mo wit)\<^sup>+"
    unfolding opsemOrder_def
    proof (erule converse_trancl_induct) 
      fix b y
      assume "\<not> is_na_or_non_write pre b" 
             "(y, b) \<in> hbMinus pre wit \<union> (rf wit \<union> mo wit)"
      hence "(y, b) \<in> mo wit" using a_in_mo by auto
      thus "(y, b) \<in> (mo wit)\<^sup>+" by auto
    next
      fix b y z
      assume "\<not> is_na_or_non_write pre b"
             "(y, z) \<in> hbMinus pre wit \<union> (rf wit \<union> mo wit)"
             "(z, b) \<in> (hbMinus pre wit \<union> (rf wit \<union> mo wit))\<^sup>+"
             "(z, b) \<in> (mo wit)\<^sup>+"
      hence "\<exists>c. (z, c) \<in> mo wit" 
        using tranclD[where R="mo wit"] by auto
      hence "\<not> is_na_or_non_write pre z" 
        using mo_atomic_writes by auto
      hence "(y, z) \<in> mo wit"
        using `(y, z) \<in> hbMinus pre wit \<union> (rf wit \<union> mo wit)`
        using a_in_mo by auto
      thus "(y, b) \<in> (mo wit)\<^sup>+" 
        using `(z, b) \<in> (mo wit)\<^sup>+` 
        by (auto simp add: trancl_into_trancl)
    qed 
  hence irreflexive_a_and_write: "\<And>a b. \<lbrakk>(a, b) \<in> ?eb; \<not> is_na_or_non_write pre b\<rbrakk> \<Longrightarrow> a \<noteq> b"
    using `isIrreflexive ((mo wit)\<^sup>+)`
    unfolding isIrreflexive_def
    by blast

  have "isIrreflexive ?eb"
    using irreflexive_na_non_write irreflexive_a_and_write
    unfolding isIrreflexive_def
    by auto
  thus "isStrictPartialOrder ?eb" 
    unfolding isStrictPartialOrder_def opsemOrder_def by simp
qed

lemma supremum:
  assumes finite:    "finite A"
      and non_empty: "A \<noteq> {}"
      and order:     "isStrictPartialOrder R"
  shows   "\<exists>x. x \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> (x, y) \<notin> R)"
using finite non_empty
proof (induct rule: finite_ne_induct, clarsimp)
  fix x
  assume "(x, x) \<in> R"
  thus False 
    using order 
    unfolding isStrictPartialOrder_def isIrreflexive_def
    by auto
next
  fix a F
  assume "finite F"
     and "\<exists>x. x \<in> F \<and> (\<forall>y. y \<in> F \<longrightarrow> (x, y) \<notin> R)"
  from this obtain x where sup: "x \<in> F \<and> (\<forall>y. y \<in> F \<longrightarrow> (x, y) \<notin> R)" by blast
  show "\<exists>z. z \<in> insert a F \<and> (\<forall>y. y \<in> insert a F \<longrightarrow> (z, y) \<notin> R)"
    proof (cases "(x, a) \<in> R")
      assume "(x, a) \<in> R"
      show ?thesis 
        proof (rule exI[where x=a], auto)
          assume "(a, a) \<in> R"
          thus False 
            using order 
            unfolding isStrictPartialOrder_def isIrreflexive_def
            by auto
        next
          fix y
          assume "y \<in> F" "(a, y) \<in> R"
          hence "(x, y) \<in> R" 
            using `(x, a) \<in> R` order
            unfolding isStrictPartialOrder_def isTransitive_def relApply_def
            by auto
          thus False using sup `y \<in> F` by auto
        qed
    next
      assume "(x, a) \<notin> R"
      show ?thesis 
        apply (rule exI[where x=x])
        using `(x, a) \<notin> R` sup 
        by auto
    qed
qed

(* We define a specialised induction rule for downclosed finite sets. *)
lemma finite_downclosedsubset_induct:
  assumes fin:        "finite A"
      and universe:   "A \<subseteq> B"
      and downclosed: "downclosed A R"
      and order:      "isStrictPartialOrder R"
      and empty:      "P {}"
      and step:       "\<And>a F. finite F \<Longrightarrow> 
                          a \<in> B \<Longrightarrow> 
                          a \<notin> F \<Longrightarrow> 
                          (\<forall>b\<in>F. (a, b) \<notin> R) \<Longrightarrow> 
                          P F \<Longrightarrow> 
                          downclosed (insert a F) R \<Longrightarrow> 
                          P (insert a F)"
  shows           "P A"
using fin empty downclosed universe
proof (induct rule: finite_psubset_induct)
  fix A
  assume fin:        "finite A"
     and IH:         "\<And>C. C \<subset> A \<Longrightarrow> P {} \<Longrightarrow> downclosed C R \<Longrightarrow> C \<subseteq> B \<Longrightarrow> P C"
     and empty:      "P {}"
     and downclosed: "downclosed A R"
     and universe:   "A \<subseteq> B"
  show "P A"
    proof (cases "A = {}")
      assume "A = {}"
      thus "P A" using empty by metis
    next
      assume "A \<noteq> {}"
      obtain x where sup: "x \<in> A \<and> (\<forall>y. (x, y) \<in> R \<longrightarrow> y \<notin> A)"
        using fin `A \<noteq> {}` order by (metis supremum)
      have "x \<in> B" using universe sup by auto
      let ?F = "A - {x}"
      have insert: "x \<notin> ?F" "A = insert x ?F" "?F \<subset> A" using sup by auto
      have downclosed_f: "downclosed ?F R"
        using downclosed sup unfolding downclosed_def by auto
      have downclosed_insert_f: "downclosed (insert x ?F) R"
        using downclosed insert by auto
      have finite_f: "finite ?F" using fin insert by auto
      have universe_f: "?F \<subseteq> B" using universe by auto
      have "P ?F" using IH[OF `?F \<subset> A` empty downclosed_f universe_f] .
      have max: "\<forall>b\<in>?F. (x, b) \<notin> R" using sup by auto
      show "P A" 
        using step[OF finite_f `x \<in> B` `x \<notin> ?F` max `P ?F` downclosed_insert_f] 
        using `A = insert x ?F` 
        by simp
   qed
qed

(* Section 4 - Properties of happens-before --------------------------------------------------- *)

(* In this section we prove all properties of getHb that we need, so after this section we never
   need to unfold the definition of hb. This way, if hb changes, we only need to change this 
   section. *)

(* RelOver in the rel-acq-rlx fragment *)

lemma relOver_release_acquire_relaxed_sw:
  shows   "relOver (release_acquire_relaxed_synchronizes_with_set p_actions p_sb p_asw w_rf w_lo rs) p_actions "
unfolding release_acquire_relaxed_synchronizes_with_set_def 
unfolding relOver_def relDomain_def relRange_def
by auto

lemma relOver_no_consume_hb:
  assumes "relOver p_sb p_actions"
          "relOver sw p_actions"
  shows   "relOver (no_consume_hb p_sb sw) p_actions"
using assms
unfolding no_consume_hb_def
by simp
 
lemma relOver_release_acquire_relaxed_hb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (extractHb release_acquire_relaxed_relations pre wit) (actions0 pre)"
unfolding extractHb_def release_acquire_relaxed_relations_def Let_def
using relOver_no_consume_hb[OF assms relOver_release_acquire_relaxed_sw]
by simp

(* RelOver in the rel-acq-rlx-fence fragment *)

lemma relOver_release_acquire_fenced_sw:
  shows   "relOver (release_acquire_fenced_synchronizes_with_set p_actions p_sb p_asw w_rf w_lo rs hrs) p_actions "
unfolding release_acquire_fenced_synchronizes_with_set_def 
unfolding relOver_def relDomain_def relRange_def
by auto
 
lemma relOver_release_acquire_fenced_hb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (extractHb release_acquire_fenced_relations pre wit) (actions0 pre)"
unfolding extractHb_def release_acquire_fenced_relations_def Let_def 
using relOver_no_consume_hb[OF assms relOver_release_acquire_fenced_sw]
by simp

(* RelOver in the with_consume fragment *)

lemma relOver_dob:
  shows   "relOver (with_consume_dob_set p_actions w_rf rs cad) p_actions"
unfolding with_consume_dob_set_def 
unfolding relOver_def relDomain_def relRange_def
by auto

lemma relOver_ithb:
  assumes "relOver p_sb p_actions"
          "relOver sw p_actions"
          "relOver dob p_actions"
  shows   "relOver (inter_thread_happens_before p_actions p_sb sw dob) p_actions"
using assms
unfolding inter_thread_happens_before_def Let_def
by (simp add: relOver_relComp)

lemma relOver_happens_before:
  assumes "relOver p_sb p_actions"
          "relOver ithb p_actions"
  shows   "relOver (happens_before p_actions p_sb ithb) p_actions"
using assms
unfolding happens_before_def
by simp
 
lemma relOver_with_consume_hb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (extractHb with_consume_relations pre wit) (actions0 pre)"
unfolding extractHb_def with_consume_relations_def Let_def 
using relOver_happens_before[OF assms relOver_ithb[OF assms relOver_release_acquire_fenced_sw relOver_dob]]
by simp

(* Finite prefixes in the rel-acq-rlx fragment *)

lemma relComp_member [simp]:
  shows "(a, c) \<in> relComp r r' = (\<exists>b. (a, b) \<in> r \<and> (b, c) \<in> r')"
proof (intro iffI, auto)
  fix b
  assume "(a, b) \<in> r" "(b, c) \<in> r'"
  hence "((a, b), b, c) \<in> {x \<in> r \<times> r'. case x of (x, xa) \<Rightarrow> (case x of (e1, e2) \<Rightarrow> \<lambda>(e2', e3). e2 = e2') xa}"
    by auto
  thus "(a, c) \<in> relComp r r'" 
    unfolding relComp_def by (intro image_eqI) auto
qed (auto simp add: relComp_def)

(* TODO: prove finite.. rs *)

lemma finite_release_acquire_relaxed_sw:
  assumes "finite_prefixes p_asw p_actions"
          "finite_prefixes w_rf p_actions"
          "finite_prefixes w_lo p_actions"
          "finite_prefixes rs p_actions"
          "relOver w_rf p_actions"
  shows "finite_prefixes (release_acquire_relaxed_synchronizes_with_set p_actions p_sb p_asw w_rf w_lo rs) p_actions"
proof -
  have finite_union: "finite_prefixes (p_asw \<union> relComp rs w_rf \<union> w_lo) p_actions"
    using assms by auto
  have "release_acquire_relaxed_synchronizes_with_set p_actions p_sb p_asw w_rf w_lo rs \<subseteq> 
        p_asw \<union> relComp rs w_rf \<union> w_lo"
    unfolding release_acquire_relaxed_synchronizes_with_set_def
    by (auto simp add: release_acquire_relaxed_synchronizes_with_def)
  thus ?thesis using finite_union finite_prefix_subset by metis
qed

(* Sb in hb in the rel-acq-rlx fragment *)

lemma sbInHb_release_acquire_relaxed_hb:
  shows "sb pre \<subseteq> (extractHb release_acquire_relaxed_relations) pre wit"
unfolding extractHb_def release_acquire_relaxed_relations_def Let_def no_consume_hb_def
by auto

(* Sb in hb in the rel-acq-rlx-fence fragment *)

lemma sbInHb_release_acquire_fenced_hb:
  shows "sb pre \<subseteq> (extractHb release_acquire_fenced_relations) pre wit"
unfolding extractHb_def release_acquire_fenced_relations_def Let_def no_consume_hb_def
by auto

(* Sb in hb in the with_consume fragment *)

lemma sbInHb_with_consume_hb:
  shows "sb pre \<subseteq> (extractHb with_consume_relations) pre wit"
unfolding extractHb_def with_consume_relations_def Let_def happens_before_def
by auto

(* Syncing locks in hb in the rel-acq-rlx fragment *)

(* To enable reuse between fragments, we isolated the properties that depend on hb. *)

definition otherThreadLoInHb :: "hbCalculation \<Rightarrow> bool" where 
  "otherThreadLoInHb hbCalc \<equiv> \<forall>a b pre wit. tid_of a \<noteq> tid_of b \<longrightarrow> 
                                             is_unlock a \<longrightarrow> 
                                             is_lock b \<longrightarrow> 
                                             a \<in> actions0 pre \<longrightarrow> 
                                             b \<in> actions0 pre \<longrightarrow> 
                                             (a, b) \<in> lo wit \<longrightarrow> 
                                             (a, b) \<in> hbCalc pre wit"

lemma otherThreadLoInHb_release_acquire_relaxed_hb:
  shows   "otherThreadLoInHb (extractHb release_acquire_relaxed_relations)"
unfolding otherThreadLoInHb_def
          extractHb_def 
          release_acquire_relaxed_relations_def 
          Let_def 
          no_consume_hb_def
          release_acquire_relaxed_synchronizes_with_set_def
by (auto simp add: release_acquire_relaxed_synchronizes_with_def)

lemma loInHb_aux:
  assumes well_formed_threads:      "well_formed_threads (pre, wit, [])"
      and locks_only_consistent_lo: "locks_only_consistent_lo (pre, wit, [(''hb'', hbCalc pre wit)])"
      and otherThreadLoInHb:        "otherThreadLoInHb hbCalc"
      and sbInHb:                   "sb pre \<subseteq> hbCalc pre wit"
      and is_lo:                    "is_unlock a" "is_lock b" "(a, b) \<in> lo wit"
  shows                             "(a, b) \<in> hbCalc pre wit"
proof -

  have "relOver (lo wit) (actions0 pre)" using locks_only_consistent_lo
    unfolding locks_only_consistent_lo.simps by simp
  hence in_actions: "a \<in> actions0 pre" "b \<in> actions0 pre" 
    using is_lo
    unfolding relOver_def relRange_def relDomain_def by force+   

  show "(a, b) \<in> hbCalc pre wit" 
    proof (cases "tid_of a = tid_of b")
      assume "tid_of a \<noteq> tid_of b"
      thus "(a, b) \<in> hbCalc pre wit"
        using otherThreadLoInHb in_actions is_lo
        unfolding otherThreadLoInHb_def
        by simp
    next
      assume tid_eq: "tid_of a = tid_of b"

      have "(b, a) \<notin> hbCalc pre wit" using locks_only_consistent_lo is_lo in_actions
        unfolding locks_only_consistent_lo.simps by simp
      hence "(b, a) \<notin> sb pre" 
        using sbInHb
        by auto

      have "a \<noteq> b" using locks_only_consistent_lo is_lo in_actions
        unfolding locks_only_consistent_lo.simps 
                  isIrreflexive_def
        by auto

      have "is_at_mutex_location (lk pre) a" using assms is_lo in_actions
        unfolding locks_only_consistent_lo.simps 
        by force
      hence not_na_loc: "\<not> is_at_non_atomic_location (lk pre) a"
        unfolding is_at_mutex_location_def is_at_non_atomic_location_def
        by (cases "loc_of a") auto

      have "(a, b) \<in> sb pre"
        using well_formed_threads
        unfolding well_formed_threads.simps 
                  indeterminate_sequencing_def
        using in_actions tid_eq `a \<noteq> b` not_na_loc `(b, a) \<notin> sb pre`
        by auto

      thus "(a, b) \<in> hbCalc pre wit"
        using sbInHb
        by auto

    qed
qed

lemma loInHb_release_acquire_relaxed_hb:
  shows "hbCalcRespectsSyncingLocks (extractHb release_acquire_relaxed_relations)"
unfolding hbCalcRespectsSyncingLocks_def
using sbInHb_release_acquire_relaxed_hb 
      otherThreadLoInHb_release_acquire_relaxed_hb
      loInHb_aux
by metis

(* Syncing locks in hb in the rel-acq-rlx-fence fragment *)

lemma otherThreadLoInHb_release_acquire_fenced_hb:
  shows   "otherThreadLoInHb (extractHb release_acquire_fenced_relations)"
unfolding otherThreadLoInHb_def
          extractHb_def 
          release_acquire_fenced_relations_def 
          Let_def 
          no_consume_hb_def
          release_acquire_fenced_synchronizes_with_set_def
by (auto simp add: release_acquire_fenced_synchronizes_with_def)

lemma loInHb_release_acquire_fenced_hb:
  shows "hbCalcRespectsSyncingLocks (extractHb release_acquire_fenced_relations)"
unfolding hbCalcRespectsSyncingLocks_def
using sbInHb_release_acquire_fenced_hb 
      otherThreadLoInHb_release_acquire_fenced_hb
      loInHb_aux
by metis

(* Syncing locks in hb in the with_consume fragment *)

lemma otherThreadLoInHb_with_consume_hb:
  shows   "otherThreadLoInHb (extractHb with_consume_relations)"
unfolding otherThreadLoInHb_def
          extractHb_def 
          with_consume_relations_def 
          Let_def 
          happens_before_def
          inter_thread_happens_before_def
          release_acquire_fenced_synchronizes_with_set_def
by (auto simp add: release_acquire_fenced_synchronizes_with_def)

lemma loInHb_with_consume_hb:
  shows "hbCalcRespectsSyncingLocks (extractHb with_consume_relations)"
unfolding hbCalcRespectsSyncingLocks_def
using sbInHb_with_consume_hb 
      otherThreadLoInHb_with_consume_hb
      loInHb_aux
by metis

(* Monotonicity hb in the locks only fragment *)

lemma monotonicity_locks_only_sw:
  shows   "locks_only_sw_set p_actions p_asw (relRestrict w_lo actions) \<subseteq> 
           locks_only_sw_set p_actions p_asw w_lo "
unfolding locks_only_sw_set_def 
by (auto simp add: locks_only_sw_def)

lemma monotonicity_no_consume_hb:
  assumes "sw2 \<subseteq> sw"
  shows   "no_consume_hb p_sb sw2 \<subseteq> no_consume_hb p_sb sw"
using assms
unfolding no_consume_hb_def
by (metis Un_mono order_refl trancl_mono2)

lemma monotonicity_locks_only_hb:
  shows "hbCalcIsMonotonic (extractHb locks_only_relations)"
unfolding hbCalcIsMonotonic_def extractHb_def locks_only_relations_def Let_def
by simp (metis  monotonicity_no_consume_hb monotonicity_locks_only_sw)

(* Monotonicity hb in the rel-acq fragment *)

lemma monotonicity_release_acquire_sw:
  shows   "release_acquire_synchronizes_with_set p_actions p_sb p_asw 
                                                 (relRestrict w_rf actions) 
                                                 (relRestrict w_lo actions) \<subseteq> 
           release_acquire_synchronizes_with_set p_actions p_sb p_asw w_rf w_lo"
unfolding release_acquire_synchronizes_with_set_def 
by (auto simp add: release_acquire_synchronizes_with_def)

lemma monotonicity_release_acquire_hb:
  shows "hbCalcIsMonotonic (extractHb release_acquire_relations)"
unfolding hbCalcIsMonotonic_def extractHb_def release_acquire_relations_def Let_def
by simp (metis  monotonicity_no_consume_hb monotonicity_release_acquire_sw)

(* Monotonicity hb in the rel-acq-rlx fragment *)

lemma monotonicity_release_sequence:
  assumes "downclosed actions w_mo"
          "(a, b) \<in> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> release_sequence_set p_actions p_lk w_mo"
using assms
unfolding release_sequence_set_def downclosed_def
by auto

lemma release_acquire_relaxed_sw_elim [consumes 1, case_names asw lo rel_acq]:
  assumes "release_acquire_relaxed_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs a b"
          "\<lbrakk>tid_of a \<noteq> tid_of b; (a,b) \<in> p_asw\<rbrakk> \<Longrightarrow> P"
          "\<lbrakk>tid_of a \<noteq> tid_of b; is_unlock a; is_lock b; (a,b) \<in> w_lo\<rbrakk> \<Longrightarrow> P"
          "\<And>c. \<lbrakk>tid_of a \<noteq> tid_of b; is_release a; is_acquire b;
                 c \<in> p_actions; (a,c) \<in> rs; (c,b) \<in> w_rf\<rbrakk> \<Longrightarrow> P"
  shows   "P"
using assms
unfolding release_acquire_relaxed_synchronizes_with_def
by auto

lemma monotonicity_release_acquire_relaxed_sw:
  fixes   p_actions p_sb p_lk p_asw w_rf w_lo w_mo actions
  defines "w_rf2 \<equiv> relRestrict w_rf actions"
      and "w_lo2 \<equiv> relRestrict w_lo actions"
      and "rs  \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
  assumes "downclosed actions w_mo"
  shows   "release_acquire_relaxed_synchronizes_with_set p_actions p_sb p_asw w_rf2 w_lo2 rs2 \<subseteq> 
           release_acquire_relaxed_synchronizes_with_set p_actions p_sb p_asw w_rf  w_lo  rs"
unfolding release_acquire_relaxed_synchronizes_with_set_def
proof clarsimp
  fix a b
  assume sw1: "release_acquire_relaxed_synchronizes_with p_actions p_sb p_asw w_rf2 w_lo2 rs2 a b"
     and      "a \<in> p_actions" "b \<in> p_actions"
  show "release_acquire_relaxed_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs a b"
    using sw1 proof (cases rule: release_acquire_relaxed_sw_elim)
      fix c
      case (rel_acq c)
      hence "c \<in> actions" "b \<in> actions" unfolding w_rf2_def by auto
      hence "(a, c) \<in> rs" 
        using monotonicity_release_sequence assms rel_acq
        unfolding rs_def rs2_def
        by metis
      thus "release_acquire_relaxed_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs a b"
        using rel_acq
        unfolding release_acquire_relaxed_synchronizes_with_def w_rf2_def
        by auto
    qed (auto simp add: release_acquire_relaxed_synchronizes_with_def w_lo2_def)
qed

lemma monotonicity_release_acquire_relaxed_hb:
  shows "hbCalcIsMonotonic (extractHb release_acquire_relaxed_relations)"
unfolding hbCalcIsMonotonic_def extractHb_def release_acquire_relaxed_relations_def Let_def
by simp (metis  monotonicity_no_consume_hb monotonicity_release_acquire_relaxed_sw)

(* Monotonicity hb in the rel-acq-rlx-fenced fragment *)

lemma monotonicity_hypothetical_release_sequence:
  assumes "(a, b) \<in> hypothetical_release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
          "downclosed actions w_mo"
          "b \<in> actions"          
  shows   "(a, b) \<in> hypothetical_release_sequence_set p_actions p_lk w_mo"
using assms
unfolding hypothetical_release_sequence_set_def downclosed_def
by auto

lemma release_acquire_fenced_sw_elim [consumes 1, case_names asw lo rel_acq fence1 fence2 fence3]:
  assumes "release_acquire_fenced_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs hrs a b"
          "\<lbrakk>tid_of a \<noteq> tid_of b; (a,b) \<in> p_asw\<rbrakk> \<Longrightarrow> P"
          "\<lbrakk>tid_of a \<noteq> tid_of b; is_unlock a; is_lock b; (a,b) \<in> w_lo\<rbrakk> \<Longrightarrow> P"
          "\<And>c. \<lbrakk>tid_of a \<noteq> tid_of b; 
                 is_release a; 
                 is_acquire b;
                 c \<in> p_actions; 
                 (a,c) \<in> rs; 
                 (c,b) \<in> w_rf\<rbrakk> \<Longrightarrow> P"
          "\<And>x y z. \<lbrakk>tid_of a \<noteq> tid_of b;
                     is_fence a;
                     is_release a;
                     is_fence b;
                     is_acquire b;
                     x \<in> p_actions;
                     z \<in> p_actions;
                     y \<in> p_actions;
                     (a, x) \<in> p_sb;
                     (x, z) \<in> hrs;
                     (z, y) \<in> w_rf;
                     (y, b) \<in> p_sb\<rbrakk> \<Longrightarrow> P"
          "\<And>x y. \<lbrakk>tid_of a \<noteq> tid_of b;
                   is_fence a;
                   is_release a;
                   is_acquire b;
                   x \<in> p_actions;
                   y \<in> p_actions;
                   (a, x) \<in> p_sb;
                   (x, y) \<in> hrs;
                   (y, b) \<in> w_rf\<rbrakk> \<Longrightarrow> P"
          "\<And>x y. \<lbrakk>tid_of a \<noteq> tid_of b;
                   is_release a;
                   is_fence b;
                   is_acquire b;
                   x \<in> p_actions;
                   y \<in> p_actions;
                   (a, y) \<in> rs;
                   (y, x) \<in> w_rf;
                   (x, b) \<in> p_sb\<rbrakk> \<Longrightarrow> P"           
  shows   "P"
using assms
unfolding release_acquire_fenced_synchronizes_with_def
(* TODO: auto is a bit slow. By explicitely giving the case splits, 
         this can probably be improved. *)
by auto

lemma monotonicity_release_acquire_fenced_sw: 
  fixes   p_actions p_sb p_lk p_asw w_rf w_lo w_mo actions
  defines "w_rf2 \<equiv> relRestrict w_rf actions"
      and "w_lo2 \<equiv> relRestrict w_lo actions"
      and "rs  \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
      and "hrs  \<equiv> hypothetical_release_sequence_set p_actions p_lk w_mo"
      and "hrs2 \<equiv> hypothetical_release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
  assumes downclosed: "downclosed actions w_mo"
  shows   "release_acquire_fenced_synchronizes_with_set p_actions p_sb p_asw w_rf2 w_lo2 rs2 hrs2 \<subseteq> 
           release_acquire_fenced_synchronizes_with_set p_actions p_sb p_asw w_rf  w_lo  rs  hrs"
unfolding release_acquire_fenced_synchronizes_with_set_def
proof clarsimp
  fix a b
  assume sw1: "release_acquire_fenced_synchronizes_with p_actions p_sb p_asw w_rf2 w_lo2 rs2 hrs2 a b"
     and      "a \<in> p_actions" "b \<in> p_actions"
  show "release_acquire_fenced_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs hrs a b"
    using sw1 proof (cases rule: release_acquire_fenced_sw_elim)
      case asw
      thus ?thesis unfolding release_acquire_fenced_synchronizes_with_def by simp
    next
      case lo
      thus ?thesis unfolding w_lo2_def release_acquire_fenced_synchronizes_with_def by simp
    next
      case (rel_acq c)
      hence "c \<in> actions" unfolding w_rf2_def by auto
      hence "(a, c) \<in> rs"
        using monotonicity_release_sequence
        using downclosed rel_acq
        unfolding w_rf2_def rs_def rs2_def
        by auto
      hence "\<exists>c\<in>p_actions. (a, c) \<in> rs \<and> (c, b) \<in> w_rf"
        using rel_acq unfolding w_rf2_def by auto
      thus ?thesis
        using rel_acq unfolding release_acquire_fenced_synchronizes_with_def by auto        
    next
      case (fence1 x y z)
      hence "z \<in> actions" unfolding w_rf2_def by auto
      hence "(x, z) \<in> hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence1
        unfolding w_rf2_def hrs_def hrs2_def
        by auto
      hence "\<exists>x\<in>p_actions. \<exists>z\<in>p_actions. \<exists>y\<in>p_actions. (a, x) \<in> p_sb \<and> (x, z) \<in> hrs \<and> (z, y) \<in> w_rf \<and> (y, b) \<in> p_sb"
        using fence1 unfolding w_rf2_def by auto
      thus ?thesis 
        using fence1 unfolding release_acquire_fenced_synchronizes_with_def by auto
    next
      case (fence2 x y)
      hence "y \<in> actions" unfolding w_rf2_def by auto
      hence "(x, y) \<in> hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence2
        unfolding w_rf2_def hrs_def hrs2_def
        by auto
      hence "\<exists>x\<in>p_actions. \<exists>y\<in>p_actions. (a, x) \<in> p_sb \<and> (x, y) \<in> hrs \<and> (y, b) \<in> w_rf"
        using fence2 unfolding w_rf2_def by auto
      thus ?thesis 
        using fence2 unfolding release_acquire_fenced_synchronizes_with_def by auto
    next
      case (fence3 x y)
      hence "y \<in> actions" unfolding w_rf2_def by auto
      hence "(a, y) \<in> rs"
        using monotonicity_release_sequence
        using downclosed fence3
        unfolding w_rf2_def rs_def rs2_def
        by auto
      hence "\<exists>y\<in>p_actions. \<exists>x\<in>p_actions. (a, y) \<in> rs \<and> (y, x) \<in> w_rf \<and> (x, b) \<in> p_sb"
        using fence3 unfolding w_rf2_def by auto
      thus ?thesis 
        using fence3 unfolding release_acquire_fenced_synchronizes_with_def by auto
    qed
qed

lemma monotonicity_release_acquire_fenced_hb:
  shows "hbCalcIsMonotonic (extractHb release_acquire_fenced_relations)"
unfolding hbCalcIsMonotonic_def extractHb_def release_acquire_fenced_relations_def Let_def
by simp (metis monotonicity_no_consume_hb[OF monotonicity_release_acquire_fenced_sw])

(* Monotonicity hb in the with_consume fragment *)

lemma monotonicity_with_consume_cad:
  shows "with_consume_cad_set p_actions p_sb p_dd (relRestrict w_rf actions) \<subseteq> 
         with_consume_cad_set p_actions p_sb p_dd w_rf"
unfolding with_consume_cad_set_def
proof -
  have "relRestrict w_rf actions \<inter> p_sb \<union> p_dd \<subseteq> w_rf \<inter> p_sb \<union> p_dd" by auto
  thus "(relRestrict w_rf actions \<inter> p_sb \<union> p_dd)\<^sup>+ \<subseteq> (w_rf \<inter> p_sb \<union> p_dd)\<^sup>+"
    by (metis trancl_mono2)
qed

lemma monotonicity_dependency_ordered_before:
  fixes p_actions p_lk w_mo actions
  defines "rs \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
  assumes cad: "cad2 \<subseteq> cad"
      and downclosed: "downclosed actions w_mo"
      and dob: "dependency_ordered_before p_actions (relRestrict w_rf actions) rs2 cad2 a b"
  shows   "dependency_ordered_before p_actions w_rf rs cad a b"
proof -
  have ab: "a \<in> p_actions \<and> b \<in> p_actions \<and> is_release a"
    using dob unfolding dependency_ordered_before_def by auto
  obtain ba e where ba_e: "ba \<in> p_actions \<and> 
                           is_consume ba \<and> 
                           e \<in> p_actions \<and> 
                           (a, e) \<in> rs2 \<and> 
                           (e, ba) \<in> relRestrict w_rf actions \<and> 
                           ((ba, b) \<in> cad2 \<or> ba = b)"
    using dob unfolding dependency_ordered_before_def by auto
  hence "e \<in> actions" unfolding relRestrict_def by auto
  hence rs: "(a, e) \<in> rs"
    using ba_e monotonicity_release_sequence[OF downclosed]
    unfolding rs_def rs2_def
    by fast
  have cad2: "(ba, b) \<in> cad \<or> ba = b" using ba_e cad by auto
  show ?thesis
    using ab ba_e rs cad2 unfolding dependency_ordered_before_def by auto
qed

lemma monotonicity_with_consume_dob_set:
  fixes p_actions p_lk w_mo actions
  defines "rs \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
  assumes cad: "cad2 \<subseteq> cad"
      and downclosed: "downclosed actions w_mo"
  shows   "with_consume_dob_set p_actions (relRestrict w_rf actions) rs2 cad2 \<subseteq> 
           with_consume_dob_set p_actions w_rf rs cad"
unfolding  with_consume_dob_set_def Let_def rs_def rs2_def
using monotonicity_dependency_ordered_before[OF cad downclosed]
by fast

lemma monotonicity_ithb:
  assumes sw:  "sw2 \<subseteq> sw"
      and dob: "dob2 \<subseteq> dob"
  shows   "inter_thread_happens_before p_actions p_sb sw2 dob2 \<subseteq> 
           inter_thread_happens_before p_actions p_sb sw dob"
proof -
  have sw_sb: "relComp sw2 p_sb \<subseteq> relComp sw p_sb"
    using relComp_mono[OF sw] by auto
  hence  "relComp p_sb (sw2 \<union> dob2 \<union> relComp sw2 p_sb) \<subseteq>
          relComp p_sb (sw \<union> dob \<union> relComp sw p_sb)"
    using relComp_mono sw dob by (metis Un_mono order_refl)
  hence "sw2 \<union> dob2 \<union> relComp sw2 p_sb \<union> relComp p_sb (sw2 \<union> dob2 \<union> relComp sw2 p_sb) \<subseteq> 
         sw \<union> dob \<union> relComp sw p_sb \<union> relComp p_sb (sw \<union> dob \<union> relComp sw p_sb)"
    using sw dob sw_sb by auto
  thus ?thesis
    unfolding inter_thread_happens_before_def Let_def by (intro trancl_mono2) simp
qed

lemma monotonicity_happens_before:
  assumes "ithb2 \<subseteq> ithb"
  shows   "happens_before p_actions p_sb ithb2 \<subseteq> happens_before p_actions p_sb ithb"
using assms
unfolding happens_before_def
by auto

lemma monotonicity_with_consume_hb:
  shows "hbCalcIsMonotonic (extractHb with_consume_relations)"
unfolding hbCalcIsMonotonic_def
proof (intro allI impI)
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions :: "action set"
  let ?rs = "release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?rs2 = "release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?hrs = "hypothetical_release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?hrs2 = "hypothetical_release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?cad = "with_consume_cad_set (actions0 pre) (sb pre) (dd pre) (rf wit)"
  let ?cad2 = "with_consume_cad_set (actions0 pre) (sb pre) (dd pre) (relRestrict (rf wit) actions)"
  let ?dob = "with_consume_dob_set (actions0 pre) (rf wit) ?rs ?cad"
  let ?dob2 = "with_consume_dob_set (actions0 pre) (relRestrict (rf wit) actions) ?rs2 ?cad2"
  let ?sw = "release_acquire_fenced_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit) ?rs ?hrs" 
  let ?sw2 = "release_acquire_fenced_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (relRestrict (rf wit) actions) (relRestrict (lo wit) actions) ?rs2  ?hrs2"
  let ?ithb = "inter_thread_happens_before (actions0 pre) (sb pre) ?sw ?dob"
  let ?ithb2 = "inter_thread_happens_before (actions0 pre) (sb pre) ?sw2 ?dob2"
  let ?hb = "happens_before (actions0 pre) (sb pre) ?ithb"
  let ?hb2 = "happens_before (actions0 pre) (sb pre) ?ithb2"
  assume downclosed: "downclosed actions (mo wit)"
  have dob: "?dob2 \<subseteq> ?dob" 
    using monotonicity_with_consume_dob_set[OF monotonicity_with_consume_cad downclosed] by metis
  have sw: "?sw2 \<subseteq> ?sw"
    using monotonicity_release_acquire_fenced_sw[OF downclosed] by metis
  have ithb: "?ithb2 \<subseteq> ?ithb" using monotonicity_ithb[OF sw dob] by metis
  have hb: "?hb2 \<subseteq> ?hb" using monotonicity_happens_before[OF ithb] by metis
  thus "extractHb with_consume_relations pre (witnessRestrict wit actions) \<subseteq> 
        extractHb with_consume_relations pre wit"
    unfolding extractHb_def with_consume_relations_def Let_def
    by simp
qed

(* Prefixes are final in the rel-acq-rlx fragment *)

lemma final_release_sequence:
  assumes  "downclosed actions w_mo"
      and  "b \<in> actions"
      and  "(a, b) \<in> release_sequence_set p_actions p_lk w_mo"
  shows   "(a, b) \<in> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
using assms
unfolding release_sequence_set_def downclosed_def
by auto

lemma final_release_acquire_relaxed_sw:
  fixes   p_actions p_sb p_lk p_asw w_rf w_lo w_mo actions
  defines "w_rf2 \<equiv> relRestrict w_rf actions"
      and "w_lo2 \<equiv> relRestrict w_lo actions"
      and "rs  \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
  assumes downclosed_rf: "downclosed actions w_rf"
      and downclosed_mo: "downclosed actions w_mo"
      and "a \<in> actions" 
      and "b \<in> actions"
      and sw1: "release_acquire_relaxed_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs a b"
  shows   "release_acquire_relaxed_synchronizes_with p_actions p_sb p_asw w_rf2 w_lo2 rs2 a b"
using sw1
proof (cases rule: release_acquire_relaxed_sw_elim)
  case asw
  thus ?thesis
    unfolding release_acquire_relaxed_synchronizes_with_def
    by simp
next
  case lo
  thus ?thesis
    unfolding release_acquire_relaxed_synchronizes_with_def w_lo2_def
    using `a \<in> actions` `b \<in> actions`
    by simp
next
  case (rel_acq c)
  have "c \<in> actions" 
    using downclosed_rf `(c, b) \<in> w_rf` `b \<in> actions` unfolding downclosed_def by auto
  have "(a, c) \<in> rs2"
    using final_release_sequence[OF downclosed_mo `c \<in> actions`]  `(a, c) \<in> rs`
    unfolding rs_def rs2_def
    by metis
  thus ?thesis
    unfolding release_acquire_relaxed_synchronizes_with_def w_rf2_def rs2_def
    using rel_acq `b \<in> actions` `c \<in> actions`
    by auto
qed 

lemma final_no_consume_hb_aux:
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and                "b \<in> actions"
      and downclosed_hb: "\<And>c. (c, b) \<in> (no_consume_hb p_sb sw) \<Longrightarrow> c \<in> actions"
      and in_hb:         "(a, b) \<in> no_consume_hb p_sb sw"
      and final_sw:      "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> sw\<rbrakk> \<Longrightarrow> (x, y) \<in> sw'"
  shows   "(a, b) \<in> no_consume_hb p_sb sw'"
proof -
  let ?hb = "no_consume_hb p_sb sw"
  have "(a, b) \<in> (p_sb \<union> sw)\<^sup>+" using in_hb unfolding no_consume_hb_def .
  hence "(a, b) \<in> (p_sb \<union> sw')\<^sup>+"    
    proof (rule converse_trancl_induct)
      fix y
      assume inSbSw: "(y, b) \<in> p_sb \<union> sw"
      hence "(y, b) \<in> ?hb" unfolding no_consume_hb_def by auto
      hence "y \<in> actions" using downclosed_hb by simp
      hence "(y, b) \<in> p_sb \<union> sw'"
        using final_sw `b \<in> actions` inSbSw
        by auto
      thus "(y, b) \<in> (p_sb \<union> sw')\<^sup>+" by auto
    next
      fix y z
      assume inSbSw:        "(y, z) \<in> p_sb \<union> sw"
         and inSbSwTrancl:  "(z, b) \<in> (p_sb \<union> sw)\<^sup>+"
         and inSbSw2Trancl: "(z, b) \<in> (p_sb \<union> sw')\<^sup>+"
      hence "(z, b) \<in> ?hb" unfolding no_consume_hb_def by auto
      hence "z \<in> actions" using downclosed_hb by simp
      have "(y, b) \<in> ?hb"
        unfolding no_consume_hb_def
        using inSbSw inSbSwTrancl
        by (rule trancl_into_trancl2)
      hence "y \<in> actions" using downclosed_hb by simp
      hence "(y, z) \<in> p_sb \<union> sw'"
        using final_sw inSbSw `z \<in> actions`
        by auto     
      thus "(y, b) \<in> (p_sb \<union> sw')\<^sup>+" 
        using inSbSw2Trancl
        by (rule trancl_into_trancl2)
    qed
  thus "(a, b) \<in> no_consume_hb p_sb sw'" 
    unfolding no_consume_hb_def
    by simp
qed

lemma final_no_consume_hb:
  fixes pre wit sw sw'
  defines "hb  \<equiv> no_consume_hb (sb pre) sw"
      and "hb' \<equiv> no_consume_hb (sb pre) sw'"
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_hb:  "selective_downclosed f actions hb"
      and final_sw:      "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> sw\<rbrakk> \<Longrightarrow> (x, y) \<in> sw'"
  shows   "selective_prefixes_are_final f actions hb hb'"
unfolding selective_prefixes_are_final_def
proof auto
  fix a b c
  assume "c \<in> actions" 
         "f c" 
         "(a, b) \<in> hb" 
         "(b, c) \<in> hb"
  have "b \<in> actions"
    using downclosed_hb `(b, c) \<in> hb` `f c` `c \<in> actions`
    unfolding selective_downclosed_def
    by auto
  have downclosed_hb: "\<And>d. (d, b) \<in> hb \<Longrightarrow> d \<in> actions"
    proof -
      fix d
      assume "(d, b) \<in> hb"
      hence "(d, c) \<in> hb" using `(b, c) \<in> hb` 
        unfolding hb_def no_consume_hb_def by auto
      thus "d \<in> actions" 
        using downclosed_hb `f c` `c \<in> actions`
        unfolding selective_downclosed_def
        by auto
    qed
  show "(a, b) \<in> hb'" 
    using downclosed_hb `(a, b) \<in> hb`  final_sw
    unfolding hb_def hb'_def
    using final_no_consume_hb_aux[OF downclosed_rf downclosed_mo `b \<in> actions`]
    by metis
next
  fix a b
  assume "b \<in> actions" "f b" "(a, b) \<in> hb"
  hence "\<And>d. (d, b) \<in> hb \<Longrightarrow> d \<in> actions"
    using downclosed_hb unfolding selective_downclosed_def by auto
  thus "(a, b) \<in> hb'" 
    using `(a, b) \<in> hb` final_sw
    unfolding hb_def hb'_def
    using final_no_consume_hb_aux[OF downclosed_rf downclosed_mo  `b \<in> actions`]
    by metis
qed

lemma final_release_acquire_relaxed_hb:
  shows "hbCalcIsFinalForPrefixes (extractHb release_acquire_relaxed_relations)"
unfolding hbCalcIsFinalForPrefixes_def
          extractHb_def 
          release_acquire_relaxed_relations_def
          Let_def
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions
  let ?rs  = "release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?rs2 = "release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?sw  = "release_acquire_relaxed_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit) ?rs"
  let ?sw2 = "release_acquire_relaxed_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (relRestrict (rf wit) actions) (relRestrict (lo wit) actions) ?rs2"
  let ?f   = "is_na_or_non_write pre"
  assume downclosed: "downclosed actions (rf wit)" 
                     "downclosed actions (mo wit)"
                     "downclosed actions (sbMinus pre (sb pre))"
                     "selective_downclosed ?f actions (no_consume_hb (sb pre) ?sw)"
  have "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> ?sw\<rbrakk> \<Longrightarrow> (x, y) \<in> ?sw2"
    unfolding release_acquire_relaxed_synchronizes_with_set_def
    apply auto
    using final_release_acquire_relaxed_sw downclosed
    by metis 
  thus "selective_prefixes_are_final ?f actions (no_consume_hb (sb pre) ?sw) (no_consume_hb (sb pre) ?sw2)"
    using final_no_consume_hb downclosed by metis
qed

(* Prefixes are final in the rel-acq-rlx-fence fragment *)

lemma final_hypothetical_release_sequence:
  assumes "downclosed actions w_mo"
      and "b \<in> actions"
      and "(a, b) \<in> hypothetical_release_sequence_set p_actions p_lk w_mo"
  shows   "(a, b) \<in> hypothetical_release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
using assms
unfolding hypothetical_release_sequence_set_def downclosed_def
by auto

lemma final_release_acquire_fenced_sw:
  fixes   p_actions p_sb p_lk p_asw w_rf w_lo w_mo actions
  defines "w_rf2 \<equiv> relRestrict w_rf actions"
      and "w_lo2 \<equiv> relRestrict w_lo actions"
      and "rs  \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
      and "hrs  \<equiv> hypothetical_release_sequence_set p_actions p_lk w_mo"
      and "hrs2 \<equiv> hypothetical_release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
  assumes downclosed_rf: "downclosed actions w_rf"
      and downclosed_mo: "downclosed actions w_mo"
      and downclosed_sb: "downclosed actions (sbMinus pre p_sb)"
      and "a \<in> actions"
      and "b \<in> actions"
      and sw1: "release_acquire_fenced_synchronizes_with p_actions p_sb p_asw w_rf w_lo rs hrs a b"
  shows   "release_acquire_fenced_synchronizes_with p_actions p_sb p_asw w_rf2 w_lo2 rs2 hrs2 a b"
using sw1
proof (cases rule: release_acquire_fenced_sw_elim)
  case asw
  thus ?thesis
    unfolding release_acquire_fenced_synchronizes_with_def
    by simp
next
  case lo
  thus ?thesis
    unfolding release_acquire_fenced_synchronizes_with_def w_lo2_def
    using `a \<in> actions` `b \<in> actions`
    by simp
next
  case (rel_acq c)
  have "c \<in> actions" 
    using downclosed_rf `(c, b) \<in> w_rf` `b \<in> actions` unfolding downclosed_def by auto
  have "(a, c) \<in> rs2"
    using final_release_sequence `(a, c) \<in> rs` downclosed_mo `c \<in> actions`
    unfolding rs_def rs2_def 
    by metis    
  thus ?thesis
    unfolding release_acquire_fenced_synchronizes_with_def w_rf2_def rs2_def
    using rel_acq `b \<in> actions` `c \<in> actions`
    by auto
next
  case (fence1 x y z)
  have "is_na_or_non_write pre b" 
    using `is_fence b` unfolding is_na_or_non_write_def by (cases b) auto
  hence "(y, b) \<in> sbMinus pre p_sb" using `(y, b) \<in> p_sb` unfolding sbMinus_def by auto
  hence "y \<in> actions" using downclosed_sb `b \<in> actions` unfolding downclosed_def by metis  
  hence "z \<in> actions"
    using downclosed_rf `(z, y) \<in> w_rf` unfolding downclosed_def by metis  
  hence "(x, z) \<in> hrs2"
    using final_hypothetical_release_sequence `(x, z) \<in> hrs` downclosed_mo
    unfolding hrs_def hrs2_def by metis
  hence "\<exists>x\<in>p_actions. \<exists>z\<in>p_actions. \<exists>y\<in>p_actions. 
         (a, x) \<in> p_sb \<and> (x, z) \<in> hrs2 \<and> (z, y) \<in> relRestrict w_rf actions \<and> (y, b) \<in> p_sb"
    using fence1 `z \<in> actions` `y \<in> actions` by auto
  thus ?thesis
    unfolding release_acquire_fenced_synchronizes_with_def w_rf2_def
    using fence1 by auto
next
  case (fence2 x y)
  have "y \<in> actions" 
    using downclosed_rf `b \<in> actions` `(y, b) \<in> w_rf` unfolding downclosed_def by metis
  hence "(x, y) \<in> hrs2" 
    using final_hypothetical_release_sequence `(x, y) \<in> hrs` downclosed_mo
    unfolding hrs_def hrs2_def by metis
  hence "\<exists>x\<in>p_actions. \<exists>y\<in>p_actions. (a, x) \<in> p_sb \<and> (x, y) \<in> hrs2 \<and> (y, b) \<in> relRestrict w_rf actions"
    using fence2 `y \<in> actions` `b \<in> actions` by auto
  thus ?thesis 
    unfolding release_acquire_fenced_synchronizes_with_def w_rf2_def
    using fence2 by auto
next
  case (fence3 x y)
  have "is_na_or_non_write pre b" 
    using `is_fence b` unfolding is_na_or_non_write_def by (cases b) auto
  hence "(x, b) \<in> sbMinus pre p_sb" using `(x, b) \<in> p_sb` unfolding sbMinus_def by auto
  hence "x \<in> actions" using downclosed_sb `b \<in> actions` unfolding downclosed_def by metis
  hence "y \<in> actions"
    using downclosed_rf `(y, x) \<in> w_rf` unfolding downclosed_def by metis
  hence "(a, y) \<in> rs2" 
    using final_release_sequence `(a, y) \<in> rs` downclosed_mo
    unfolding rs_def rs2_def by metis    
  hence "\<exists>y\<in>p_actions. \<exists>x\<in>p_actions. (a, y) \<in> rs2 \<and> (y, x) \<in> relRestrict w_rf actions \<and> (x, b) \<in> p_sb"
    using fence3 `x \<in> actions` `y \<in> actions` by auto
  thus ?thesis
    unfolding release_acquire_fenced_synchronizes_with_def w_rf2_def
    using fence3 by auto
qed 

lemma final_release_acquire_fenced_hb:
  shows "hbCalcIsFinalForPrefixes (extractHb release_acquire_fenced_relations)"
unfolding hbCalcIsFinalForPrefixes_def 
          extractHb_def 
          release_acquire_fenced_relations_def
          Let_def
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions
  let ?rs   = "release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?rs2  = "release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?hrs  = "hypothetical_release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?hrs2 = "hypothetical_release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?sw   = "release_acquire_fenced_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit) ?rs ?hrs"
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (relRestrict (rf wit) actions) (relRestrict (lo wit) actions) ?rs2 ?hrs2"
  let ?f    = "is_na_or_non_write pre"
  assume downclosed_rf: "downclosed actions (rf wit)" 
     and downclosed_mo: "downclosed actions (mo wit)"
     and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
     and downclosed_hb: "selective_downclosed ?f actions (no_consume_hb (sb pre) ?sw)"
  have final_sw: "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> ?sw\<rbrakk> \<Longrightarrow> (x, y) \<in> ?sw2"
    unfolding release_acquire_fenced_synchronizes_with_set_def
    apply auto
    using final_release_acquire_fenced_sw[OF downclosed_rf downclosed_mo downclosed_sb]
    by metis 
  show "selective_prefixes_are_final ?f actions (no_consume_hb (sb pre) ?sw) (no_consume_hb (sb pre) ?sw2)"
    using final_no_consume_hb[OF downclosed_rf downclosed_mo downclosed_hb final_sw] by metis
qed

(* Prefixes are final in the with-consume fragment *)

lemma final_cad:
  assumes downclosed_sb: "\<And>a. (a, b) \<in> p_sb \<Longrightarrow> a \<in> actions"
      and trans_sb:      "isTransitive p_sb"
      and dd_in_sb:      "p_dd \<subseteq> p_sb"
      and b:             "b \<in> actions" 
      and cad:           "(a, b) \<in> with_consume_cad_set p_actions p_sb p_dd w_rf"
  shows   "a \<in> actions \<and> (a, b) \<in> with_consume_cad_set p_actions p_sb p_dd (relRestrict w_rf actions)"
proof -
  have downclosed_cad: "\<And>c. (c, b) \<in> (w_rf \<inter> p_sb \<union> p_dd)\<^sup>+ \<Longrightarrow> c \<in> actions"
    proof -
      fix c
      assume c: "(c, b) \<in> (w_rf \<inter> p_sb \<union> p_dd)\<^sup>+"
      have "w_rf \<inter> p_sb \<union> p_dd \<subseteq> p_sb"
        using `p_dd \<subseteq> p_sb` by auto
      hence "(w_rf \<inter> p_sb \<union> p_dd)\<^sup>+ \<subseteq> p_sb"
        using trancl_mono3[OF `isTransitive p_sb`] by auto
      hence "(c, b) \<in> p_sb" using c by auto
      thus "c \<in> actions"
        using downclosed_sb b unfolding downclosed_def by auto
    qed
  hence "a \<in> actions" using cad unfolding with_consume_cad_set_def by auto
  have "(a, b) \<in> with_consume_cad_set p_actions p_sb p_dd (relRestrict w_rf actions)"
    using cad unfolding with_consume_cad_set_def
    proof (rule converse_trancl_induct)
      fix y
      assume y: "(y, b) \<in> w_rf \<inter> p_sb \<union> p_dd"
      hence "(y, b) \<in> (w_rf \<inter> p_sb \<union> p_dd)\<^sup>+" by fast
      hence "y \<in> actions" using downclosed_cad by fast
      hence "(y, b) \<in> relRestrict w_rf actions \<inter> p_sb \<union> p_dd"
        using y b by auto
      thus "(y, b) \<in> (relRestrict w_rf actions \<inter> p_sb \<union> p_dd)\<^sup>+" by fast
    next
      fix y z
      assume y:  "(y, z) \<in> w_rf \<inter> p_sb \<union> p_dd"
         and z:  "(z, b) \<in> (w_rf \<inter> p_sb \<union> p_dd)\<^sup>+"
         and ih: "(z, b) \<in> (relRestrict w_rf actions \<inter> p_sb \<union> p_dd)\<^sup>+"
      have "z \<in> actions" using downclosed_cad[OF z] .
      have "(y, b) \<in> (w_rf \<inter> p_sb \<union> p_dd)\<^sup>+" using y z by (rule trancl_into_trancl2)
      hence "y \<in> actions" using downclosed_cad by fast
      have "(y, z) \<in> relRestrict w_rf actions \<inter> p_sb \<union> p_dd"
        using y `y \<in> actions` `z \<in> actions` by auto
      thus "(y, b) \<in> (relRestrict w_rf actions \<inter> p_sb \<union> p_dd)\<^sup>+"
        using ih by (rule trancl_into_trancl2)
    qed
  thus ?thesis using `a \<in> actions` by simp
qed

lemma final_dob:
  fixes   p_actions p_lk p_sb p_dd w_mo w_rf actions
  defines "rs \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
      and "cad \<equiv> with_consume_cad_set p_actions p_sb p_dd w_rf"
      and "cad2 \<equiv> with_consume_cad_set p_actions p_sb p_dd (relRestrict w_rf actions)"
  assumes downclosed_sb: "\<And>a. (a, d) \<in> p_sb \<Longrightarrow> a \<in> actions"
      and downclosed_rf: "downclosed actions w_rf"
      and downclosed_mo: "downclosed actions w_mo"
      and trans_sb:      "isTransitive p_sb"
      and dd_in_sb:      "p_dd \<subseteq> p_sb"
      and d:             "d \<in> actions" 
      and dob_set:       "(a, d) \<in> with_consume_dob_set p_actions w_rf rs cad"
  shows   "(a, d) \<in> with_consume_dob_set p_actions (relRestrict w_rf actions) rs2 cad2"
proof -
  have dob: "dependency_ordered_before p_actions w_rf rs cad a d"
    using dob_set unfolding with_consume_dob_set_def by auto
  obtain b e where b:   "b \<in> p_actions" "is_consume b" 
               and e:   "e \<in> p_actions" 
               and rs:  "(a, e) \<in> rs" 
               and rf:  "(e, b) \<in> w_rf"
               and cad: "(b, d) \<in> cad \<or> (b = d)"
    using dob unfolding dependency_ordered_before_def by auto
  have cad2: "((b, d) \<in> cad2 \<or> (b = d)) \<and> b \<in> actions"
    proof (cases "b = d")
      assume "b = d"
      thus ?thesis using `d \<in> actions` by simp
    next
      assume "b \<noteq> d"
      hence "(b, d) \<in> cad" using cad by simp
      hence "(b, d) \<in> cad2 \<and> b \<in> actions"
        using final_cad[OF downclosed_sb trans_sb dd_in_sb d]
        unfolding cad_def cad2_def
        by fast
      thus ?thesis by simp
    qed
  hence "e \<in> actions" using rf downclosed_rf unfolding downclosed_def by fast
  hence rf2: "(e, b) \<in> relRestrict w_rf actions" using cad2 rf by auto
  have rs2: "(a, e) \<in> rs2" 
    using rs final_release_sequence[OF downclosed_mo `e \<in> actions`]
    unfolding rs_def rs2_def
    by fast
  have "a \<in> p_actions" "d \<in> p_actions" "is_release a"
    using dob unfolding dependency_ordered_before_def by auto
  hence "dependency_ordered_before p_actions (relRestrict w_rf actions) rs2 cad2 a d"
    unfolding with_consume_dob_set_def dependency_ordered_before_def
    using b e rs2 rf2 cad2
    by auto
  thus ?thesis 
    using `a \<in> p_actions` `d \<in> p_actions` 
    unfolding with_consume_dob_set_def 
    by auto
qed

lemma final_ithb:
  fixes   p_actions p_lk p_sb p_dd w_mo w_rf actions
  defines "rs \<equiv> release_sequence_set p_actions p_lk w_mo"
      and "rs2 \<equiv> release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
      and "hrs  \<equiv> hypothetical_release_sequence_set p_actions p_lk w_mo"
      and "hrs2 \<equiv> hypothetical_release_sequence_set p_actions p_lk (relRestrict2 w_mo actions)"
      and "cad \<equiv> with_consume_cad_set p_actions p_sb p_dd w_rf"
      and "cad2 \<equiv> with_consume_cad_set p_actions p_sb p_dd (relRestrict w_rf actions)"
  assumes "dob \<equiv> with_consume_dob_set p_actions w_rf rs cad"
      and "dob2 \<equiv> with_consume_dob_set p_actions (relRestrict w_rf actions) rs2 cad2"
      and "sw \<equiv> release_acquire_fenced_synchronizes_with_set p_actions p_sb p_asw w_rf w_lo rs hrs"
      and "sw2 \<equiv> release_acquire_fenced_synchronizes_with_set p_actions p_sb p_asw w_rf2 w_lo2 rs2 hrs2"
  assumes downclosed_sb: "\<And>a. (a, b) \<in> p_sb \<Longrightarrow> a \<in> actions"
      and downclosed_rf: "downclosed actions w_rf"
      and downclosed_mo: "downclosed actions w_mo"
      and trans_sb:      "isTransitive p_sb"
      and dd_in_sb:      "p_dd \<subseteq> p_sb"
      and b:             "b \<in> actions" 
      and ithb:          "(a, b) \<in> inter_thread_happens_before p_actions p_sb sw dob"
  shows   "(a, b) \<in> inter_thread_happens_before p_actions p_sb sw2 dob2"
oops
(*
proof -
  have "xxx" using ithb unfolding inter_thread_happens_before_def Let_def
    sorry
  show ?thesis sorry
qed
*)

lemma final_happens_before:
  shows "hbCalcIsFinalForPrefixes (extractHb with_consume_relations)"
unfolding hbCalcIsFinalForPrefixes_def 
          extractHb_def 
          with_consume_relations_def
          Let_def
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions :: "action set"
  let ?rs   = "release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?rs2  = "release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?hrs  = "hypothetical_release_sequence_set (actions0 pre) (lk pre) (mo wit)"
  let ?hrs2 = "hypothetical_release_sequence_set (actions0 pre) (lk pre) (relRestrict2 (mo wit) actions)"
  let ?sw   = "release_acquire_fenced_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit) ?rs ?hrs"
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (relRestrict (rf wit) actions) (relRestrict (lo wit) actions) ?rs2 ?hrs2"
  let ?cad  = "with_consume_cad_set (actions0 pre) (sb pre) (dd pre) (rf wit)"
  let ?cad2 = "with_consume_cad_set (actions0 pre) (sb pre) (dd pre) (relRestrict (rf wit) actions)"
  let ?dob  = "with_consume_dob_set (actions0 pre) (rf wit) ?rs ?cad"
  let ?dob2 = "with_consume_dob_set (actions0 pre) (relRestrict (rf wit) actions) ?rs2 ?cad2"
  let ?ithb = "inter_thread_happens_before (actions0 pre) (sb pre) ?sw ?dob"
  let ?ithb2 = "inter_thread_happens_before (actions0 pre) (sb pre) ?sw2 ?dob2"
  let ?hb   = "happens_before (actions0 pre) (sb pre) ?ithb"
  let ?hb2  = "happens_before (actions0 pre) (sb pre) ?ithb2"
  assume "downclosed actions (rf wit)"
         "downclosed actions (mo wit)"
         "downclosed actions (sbMinus pre (sb pre))"
         "selective_downclosed (is_na_or_non_write pre) actions ?hb"
  show "selective_prefixes_are_final (is_na_or_non_write pre) actions ?hb ?hb2"
    unfolding selective_prefixes_are_final_def
    oops
(*
    proof auto
      fix a c
      assume "c \<in> actions" "is_na_or_non_write pre c" "(a, c) \<in> ?hb"
      show "(a, c) \<in> ?hb2" sorry
    next
      fix a b c
      assume "c \<in> actions" "is_na_or_non_write pre c" "(a, b) \<in> ?hb" "(b, c) \<in> ?hb"
      show "(a, b) \<in> ?hb2" sorry
    qed
qed
*)

(* The properties proven for the fragment used in the opsem *)

lemma getHbIdentity:
  shows "getHb = (extractHb release_acquire_fenced_relations)"
apply (intro ext)
unfolding getHb_def extractHb_def memory_model_def 
by simp

lemma hbRelOver:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (getHb pre wit) (actions0 pre)"
using relOver_release_acquire_fenced_hb getHbIdentity assms
by auto

lemma sbInHb:
  shows "sb pre \<subseteq> getHb pre wit"
using sbInHb_release_acquire_fenced_hb getHbIdentity
by auto

lemma loInHb:
  shows "hbCalcRespectsSyncingLocks getHb"
using loInHb_release_acquire_fenced_hb getHbIdentity
by auto

lemma hbCalcIsMonotonic:
  shows "hbCalcIsMonotonic getHb"
using monotonicity_release_acquire_fenced_hb getHbIdentity
by auto

lemma hbCalcIsFinalForPrefixes:
  shows "hbCalcIsFinalForPrefixes getHb"
using final_release_acquire_fenced_hb getHbIdentity
by auto

(* Corollaries for derived relations *)

lemma hbMinusIsMonotonic:
  shows "hbCalcIsMonotonic hbMinus"
using hbCalcIsMonotonic
unfolding hbCalcIsMonotonic_def hbMinus_def
by auto

lemma opsemOrderIsMonotonic:
  shows "hbCalcIsMonotonic opsemOrder"
unfolding hbCalcIsMonotonic_def
proof (intro allI impI)
  fix pre
  fix wit :: execution_witness
  fix actions
  assume downclosed: "downclosed actions (mo wit)"
  have "hbMinus pre (witnessRestrict wit actions) \<subseteq> hbMinus pre wit"
    using downclosed hbMinusIsMonotonic
    unfolding hbCalcIsMonotonic_def by metis
  hence subset: "hbMinus pre (witnessRestrict wit actions) \<union> 
                (relRestrict (rf wit) actions \<union> 
                 relRestrict2 (mo wit) actions) \<subseteq> 
                hbMinus pre wit \<union> (rf wit \<union> mo wit)" 
    by auto
  show "opsemOrder pre (witnessRestrict wit actions) \<subseteq> opsemOrder pre wit"
    unfolding opsemOrder_def apply simp
    using subset trancl_mono2 by metis
qed

(* Section 5 - Invariance of consistency predicates under prefixes ---------------------------- *)

lemma restriction_of_vse:
  assumes final: "selective_prefixes_are_final f actions hb hb2"
      and "hb2 \<subseteq> hb"
          "f b"
          "b \<in> actions"
  shows   "\<forall>a. (a, b) \<in> visible_side_effect_set (actions0 pre) hb2 \<longleftrightarrow>
               (a, b) \<in> visible_side_effect_set (actions0 pre) hb"
proof (intro allI iffI)
  fix a
  assume vse: "(a, b) \<in> visible_side_effect_set (actions0 pre) hb"
  have as1: "\<not> (\<exists>c\<in>actions0 pre. c \<notin> {a, b} \<and> is_write c \<and> loc_of c = loc_of b \<and> (a, c) \<in> hb2 \<and> (c, b) \<in> hb2)"
    using vse `hb2 \<subseteq> hb` unfolding visible_side_effect_set_def by auto
  have as2: "(a, b) \<in> hb \<and> is_write a \<and> is_read b \<and> loc_of a = loc_of b"
    using vse unfolding visible_side_effect_set_def by auto
  hence "(a, b) \<in> hb2"
    using final `f b` `b \<in> actions` unfolding selective_prefixes_are_final_def by auto
  thus "(a, b) \<in> visible_side_effect_set (actions0 pre) hb2"
    using as1 as2 unfolding visible_side_effect_set_def by auto
next
  fix a
  assume vse: "(a, b) \<in> visible_side_effect_set (actions0 pre) hb2"
  have "\<not> (\<exists>c\<in>actions0 pre. c \<notin> {a, b} \<and> is_write c \<and> loc_of c = loc_of b \<and> (a, c) \<in> hb2 \<and> (c, b) \<in> hb2)"
    using vse unfolding visible_side_effect_set_def by auto
  hence as1: "\<not> (\<exists>c\<in>actions0 pre. c \<notin> {a, b} \<and> is_write c \<and> loc_of c = loc_of b \<and> (a, c) \<in> hb \<and> (c, b) \<in> hb)"
    using final `f b` `b \<in> actions` unfolding selective_prefixes_are_final_def by blast
  have "(a, b) \<in> hb \<and> is_write a \<and> is_read b \<and> loc_of a = loc_of b"
    using vse `hb2 \<subseteq> hb` unfolding visible_side_effect_set_def by auto
  thus "(a, b) \<in> visible_side_effect_set (actions0 pre) hb"
    using as1 unfolding visible_side_effect_set_def by auto
qed

lemma assumptions_restriction:
  assumes "assumptions (pre, wit, [])"
  shows   "assumptions (pre, witnessRestrict wit actions, [])"
using assms
unfolding assumptions.simps finite_prefixes_def
by simp

lemma coherent_memory_use_restriction:
  assumes "coherent_memory_use (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "coherent_memory_use (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
using assms
unfolding coherent_memory_use.simps  
by auto blast+ 

lemma consistent_atomic_rf_restriction:
  assumes "consistent_atomic_rf (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "consistent_atomic_rf (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
using assms
unfolding consistent_atomic_rf.simps 
by auto

lemma consistent_hb_restriction:
  assumes "consistent_hb (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "consistent_hb (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
using assms
unfolding consistent_hb.simps 
proof simp
  assume "isIrreflexive (hb\<^sup>+)"
         "hb2 \<subseteq> hb"
  hence "hb2\<^sup>+ \<subseteq> hb\<^sup>+" using trancl_mono2 by metis
  thus "isIrreflexive (hb2\<^sup>+)" using `isIrreflexive (hb\<^sup>+)` 
    unfolding isIrreflexive_def by auto
qed

lemma consistent_mo_restriction:
  assumes "consistent_mo (pre, wit, [])"
          "downclosed actions (mo wit)"
  shows   "consistent_mo_op actions (pre, witnessRestrict wit actions, [])"
using assms
unfolding consistent_mo.simps consistent_mo_op.simps downclosed_def
by auto

lemma consistent_non_atomic_rf_restriction:
  fixes pre wit hb hb2 
  defines "vse  \<equiv>  visible_side_effect_set (actions0 pre) hb"
      and "vse2 \<equiv>  visible_side_effect_set (actions0 pre) hb2"
  assumes cons_rf:    "consistent_non_atomic_rf (pre, wit, [(''hb'', hb),(''vse'', vse)])"
      and final:      "selective_prefixes_are_final (is_na_or_non_write pre) actions hb hb2"
      and             "hb2 \<subseteq> hb"
  shows   "consistent_non_atomic_rf (pre, witnessRestrict wit actions, [(''hb'', hb2),(''vse'', vse2)])"
unfolding consistent_non_atomic_rf.simps 
proof auto
  fix a b
  assume loc: "is_at_non_atomic_location (lk pre) b"
     and      "(a, b) \<in> rf wit"
              "a \<in> actions" 
              "b \<in> actions"
  hence non_write_b: "is_na_or_non_write pre b"
    unfolding is_na_or_non_write_def by simp
  have "(a, b) \<in> vse"
    using cons_rf `(a, b) \<in> rf wit` loc unfolding consistent_non_atomic_rf.simps by auto
  thus "(a, b) \<in> vse2"
    using restriction_of_vse[OF final `hb2 \<subseteq> hb` non_write_b `b \<in> actions`] 
    unfolding vse_def vse2_def by blast
qed

lemma det_read_restriction:
  fixes pre wit hb hb2 
  defines "vse  \<equiv>  visible_side_effect_set (actions0 pre) hb"
      and "vse2 \<equiv>  visible_side_effect_set (actions0 pre) hb2"
  assumes det_read:   "det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])"
      and downclosed: "downclosed actions (rf wit)"
      and final:      "selective_prefixes_are_final (is_na_or_non_write pre) actions hb hb2"
      and             "hb2 \<subseteq> hb"
  shows   "det_read_op actions (pre, witnessRestrict wit actions, [(''hb'', hb2),(''vse'', vse2)])"
unfolding det_read.simps det_read_op.simps
proof (clarsimp)
  fix r 
  assume "r \<in> actions0 pre" 
         "is_load r" 
         "r \<in> actions" 
  hence non_write_r: "is_na_or_non_write pre r"
    unfolding is_na_or_non_write_def by (cases r) auto
  have "(\<exists>w\<in>actions0 pre. (w, r) \<in> vse2) = 
        (\<exists>w\<in>actions0 pre. (w, r) \<in> vse)"
    using restriction_of_vse[OF final `hb2 \<subseteq> hb` non_write_r `r \<in> actions`]
    unfolding vse_def vse2_def by blast
  moreover have "(\<exists>w\<in>actions0 pre. (w, r) \<in> vse) =
                 (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit)"
    using det_read `is_load r` `r \<in> actions0 pre` 
    unfolding det_read.simps by simp
  moreover have "(\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit) =
                 (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit \<and> w' \<in> actions)"
    using downclosed `r \<in> actions` unfolding downclosed_def by auto
  ultimately show "(\<exists>w\<in>actions0 pre. (w, r) \<in> vse2) = 
                   (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit \<and> w' \<in> actions)"
    by simp
qed

lemma locks_only_consistent_lo_restriction:
  assumes "locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "locks_only_consistent_lo_op actions (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms
    unfolding locks_only_consistent_lo.simps 
              locks_only_consistent_lo_op.simps
    by auto
qed

lemma locks_only_consistent_locks_restriction:
  assumes "locks_only_consistent_locks (pre, wit, [])"
          "selective_downclosed (is_na_or_non_write pre) actions (getHb pre wit)"
          "\<And>a b. \<lbrakk>is_unlock a; is_lock b; (a, b) \<in> lo wit\<rbrakk> \<Longrightarrow> (a, b) \<in> getHb pre wit"
  shows   "locks_only_consistent_locks_op actions (pre, witnessRestrict wit actions, [])"
unfolding locks_only_consistent_locks_op.simps
proof auto
  fix a b
  assume assms2: "is_successful_lock a"
                 "is_successful_lock b"
                 "a \<in> actions"
                 "b \<in> actions"
                 "(a, b) \<in> lo wit"
  hence "is_lock b" by (cases b) auto
  have "is_na_or_non_write pre b" using assms2 unfolding is_na_or_non_write_def by (cases b) auto
  obtain c where assms3: "c \<in> actions0 pre \<and> is_unlock c \<and> (a, c) \<in> lo wit \<and> (c, b) \<in> lo wit"
    using assms assms2 unfolding locks_only_consistent_locks.simps by blast
  hence "(c, b) \<in> getHb pre wit"
    using assms `is_lock b` by metis
  hence "c \<in> actions" 
    using assms assms2 `is_na_or_non_write pre b` `b \<in> actions`
    unfolding selective_downclosed_def by auto
  thus "\<exists>c\<in>actions0 pre. is_unlock c \<and> (a, c) \<in> lo wit \<and> c \<in> actions \<and> (c, b) \<in> lo wit \<and> c \<in> actions"
    using assms3 by fast
qed

lemma rmw_atomicity_restriction:
  assumes "rmw_atomicity (pre, wit, [])"
          "downclosed actions (mo wit)"
  shows   "rmw_atomicity_op actions (pre, witnessRestrict wit actions, [])"
using assms
unfolding rmw_atomicity.simps
          rmw_atomicity_op.simps
          adjacent_less_than_def
          downclosed_def
by auto

lemma sc_accesses_consistent_sc_restriction:
  assumes "sc_accesses_consistent_sc (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "sc_accesses_consistent_sc_op actions (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms
    unfolding sc_accesses_consistent_sc.simps
              sc_accesses_consistent_sc_op.simps
    by auto
qed

lemma sc_accesses_sc_reads_restricted_restriction:
  assumes "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "sc_accesses_sc_reads_restricted (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms
    unfolding sc_accesses_sc_reads_restricted.simps 
    by auto
qed

lemma sc_fenced_sc_fences_heeded_restriction:
  assumes "sc_fenced_sc_fences_heeded (pre, wit, [])"
  shows   "sc_fenced_sc_fences_heeded (pre, witnessRestrict wit actions, [])"
using assms
unfolding sc_fenced_sc_fences_heeded.simps 
(* The simp takes a long time, but it is a difficult predicate. *)
apply simp
by auto

lemma tot_empty_restriction:
  assumes "tot_empty (pre, wit, [])"
  shows   "tot_empty (pre, witnessRestrict wit actions, [])"
using assms
unfolding tot_empty.simps 
by simp

lemma well_formed_rf_restriction:
  assumes "well_formed_rf (pre, wit, [])"
  shows   "well_formed_rf_op actions (pre, witnessRestrict wit actions, [])"
using assms
unfolding well_formed_rf.simps well_formed_rf_op.simps
(* Without the clarsimp, auto takes a long, long time. *)
by clarsimp auto

lemma well_formed_threads_restriction:
  assumes "well_formed_threads (pre, wit, [])"
  shows   "well_formed_threads (pre, witnessRestrict wit actions, [])"
using assms
unfolding well_formed_threads.simps 
by simp

(* TODO: find meaningful name *)
lemma execution_restriction:
  fixes               pre wit actions
  defines             "wit' \<equiv> witnessRestrict wit actions"
  assumes cons:       "exIsConsistent (pre, wit, getRelations pre wit)"
      and downclosed: "downclosed actions (opsemOrder pre wit)"
  shows   "exIsConsistent_op actions (pre, wit', getRelations pre wit')"
proof -

  have downclosed_hbMinus: "downclosed actions (hbMinus pre wit)"
   and downclosed_rf:      "downclosed actions (rf wit)"
   and downclosed_mo:      "downclosed actions (mo wit)"
    using downclosed unfolding opsemOrder_def by simp_all
  have "sbMinus pre (sb pre) \<subseteq> hbMinus pre wit" 
    using sbInHb unfolding sbMinus_def hbMinus_def by auto
  hence downclosed_sbMinus: "downclosed actions (sbMinus pre (sb pre))"
    using downclosed_hbMinus downclosed_subset by metis
  have selective_downclosed: "selective_downclosed (is_na_or_non_write pre) actions (getHb pre wit)"
    using downclosed_hbMinus unfolding hbMinus_def by simp
  have prefixes_final: "selective_prefixes_are_final (is_na_or_non_write pre) actions (getHb pre wit) (getHb pre wit')"
    using hbCalcIsFinalForPrefixes downclosed_rf downclosed_mo downclosed_sbMinus selective_downclosed
    unfolding hbCalcIsFinalForPrefixes_def hbMinus_def wit'_def
    by auto

  have hbSubset: "getHb pre wit' \<subseteq> getHb pre wit"
    using hbCalcIsMonotonic downclosed_mo unfolding hbCalcIsMonotonic_def wit'_def by simp

  show ?thesis
    unfolding exIsConsistent_def
              exIsConsistent_op_def              
              sc_fenced_consistent_execution_def
              getRelations_def
    proof auto
      show "assumptions (pre, wit', [])"
        using cons cons_assumptions assumptions_restriction wit'_def by metis
    next
      show "det_read_op actions (pre, wit', [(''hb'', getHb pre wit'), (''vse'', getVse pre wit')])"
        using cons cons_det_read det_read_restriction downclosed_rf prefixes_final hbSubset
        unfolding getVse_def wit'_def by metis
    next
      show "coherent_memory_use (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_coherent_memory_use coherent_memory_use_restriction wit'_def hbSubset 
        by metis
    next
      show "consistent_atomic_rf (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_consistent_atomic_rf consistent_atomic_rf_restriction wit'_def hbSubset 
        by metis
    next
      show "consistent_hb (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_consistent_hb consistent_hb_restriction wit'_def hbSubset 
        by metis
    next
      show "consistent_mo_op actions (pre, wit', [])"
        using cons cons_consistent_mo consistent_mo_restriction wit'_def downclosed_mo
        by metis
    next
      show "consistent_non_atomic_rf (pre, wit', [(''hb'', getHb pre wit'), (''vse'', getVse pre wit')])"
        using cons cons_consistent_non_atomic_rf consistent_non_atomic_rf_restriction 
        using selective_downclosed prefixes_final hbSubset
        unfolding getVse_def wit'_def by metis
    next
      show "locks_only_consistent_lo_op actions (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_locks_only_consistent_lo locks_only_consistent_lo_restriction wit'_def hbSubset 
        by metis
    next
      have "\<And>a b. is_unlock a \<Longrightarrow> is_lock b \<Longrightarrow> (a, b) \<in> lo wit \<Longrightarrow> (a, b) \<in> getHb pre wit"
        using loInHb cons cons_well_formed_threads cons_locks_only_consistent_lo
        unfolding hbCalcRespectsSyncingLocks_def
        by simp
      thus "locks_only_consistent_locks_op actions (pre, wit', [])"
        using locks_only_consistent_locks_restriction[where pre=pre and wit=wit and actions=actions]
        using selective_downclosed cons cons_locks_only_consistent_locks
        unfolding wit'_def
        by simp
    next
      show "rmw_atomicity_op actions (pre, wit', [])"
        using cons cons_rmw_atomicity rmw_atomicity_restriction wit'_def downclosed_mo by metis
    next
      show "sc_accesses_consistent_sc_op actions (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_sc_accesses_consistent_sc sc_accesses_consistent_sc_restriction wit'_def hbSubset 
        by metis
    next
      show "sc_accesses_sc_reads_restricted (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_sc_accesses_sc_reads_restricted 
              sc_accesses_sc_reads_restricted_restriction wit'_def hbSubset 
        by metis
    next
      show "sc_fenced_sc_fences_heeded (pre, wit', [])"
        using cons cons_sc_fenced_sc_fences_heeded sc_fenced_sc_fences_heeded_restriction wit'_def 
        by metis
    next
      show "tot_empty (pre, wit', [])"
        using cons cons_tot_empty tot_empty_restriction wit'_def by metis
    next
      show "well_formed_rf_op actions (pre, wit', [])"
        using cons cons_well_formed_rf well_formed_rf_restriction wit'_def by metis
    next
      show "well_formed_threads (pre, wit', [])"
        using cons cons_well_formed_threads well_formed_threads_restriction wit'_def by metis
    qed
qed

(* Section 6 - Completeness -------------------------------------------------------------------- *)

lemma existenceminOpsemTrace:
  assumes cons:       "exIsConsistent (pre, wit, getRelations pre wit)"
      and finite:     "finite actions"
      and universe:   "actions \<subseteq> actions0 pre"
      and downclosed: "downclosed actions (opsemOrder pre wit)"
  shows   "\<exists> s. minOpsemTrace pre (initialState pre) s \<and> 
                exWitness s = witnessRestrict wit actions \<and> 
                committed s = actions"
proof (rule finite_downclosedsubset_induct[where R="(opsemOrder pre wit)" and B="actions0 pre"])
  show "finite actions" using finite .
next
  show "actions \<subseteq> actions0 pre" using universe .
next
  show "downclosed actions (opsemOrder pre wit)" using downclosed .
next
  show "isStrictPartialOrder (opsemOrder pre wit)" using cons opsemOrder_isStrictPartialOrder by auto
next
  have "exIsConsistent_op {} (pre, initialWitness, getRelations pre initialWitness)"
    using cons execution_restriction[where actions="{}"] by simp
  thus "\<exists>s. minOpsemTrace pre (initialState pre) s \<and> exWitness s = witnessRestrict wit {} \<and> committed s = {}"
    using minOpsemReflexive by (intro exI[where x="initialState pre"]) simp
next
  fix a :: action
  fix actions :: "action set"
  assume finite':     "finite actions"
     and              "a \<notin> actions"
     and              "a \<in> actions0 pre"
     and downclosed': "downclosed (insert a actions) (opsemOrder pre wit)"
     and max:         "\<forall>b\<in>actions. (a, b) \<notin> opsemOrder pre wit"
     and IH:          "\<exists>s. minOpsemTrace pre (initialState pre) s \<and> 
                           exWitness s = witnessRestrict wit actions \<and> 
                           committed s = actions"
  obtain s where trace:     "minOpsemTrace pre (initialState pre) s" 
             and witness:   "exWitness s = witnessRestrict wit actions"
             and committed: "committed s = actions" using IH by blast

  let ?actions' = "insert a actions"
  let ?wit'     = "witnessRestrict wit ?actions'"
  let ?s' = "\<lparr> exWitness=?wit', 
               committed=?actions', 
               stateIsDefined = exIsDefined (pre, ?wit', getRelations pre ?wit')\<rparr>"
  have downclosed_mo: "downclosed ?actions' (mo wit)"
    using downclosed' unfolding opsemOrder_def by auto
  have inOpsemOrder: "\<forall>b\<in>actions0 pre. ((b, a) \<in> opsemOrder pre (exWitness ?s') \<longrightarrow> b \<in> actions) \<and>
                                       (b \<in> actions \<longrightarrow> (a, b) \<notin> opsemOrder pre (exWitness ?s'))"
    proof auto
      fix b
      assume "b \<in> actions0 pre"
             "(b, a) \<in> opsemOrder pre (witnessRestrict wit (insert a actions))"
      hence ba_in_rel: "(b, a) \<in> opsemOrder pre wit"
        using opsemOrderIsMonotonic downclosed_mo
        unfolding hbCalcIsMonotonic_def
        by auto
      hence "b \<noteq> a"
        using opsemOrder_isStrictPartialOrder[OF cons]
        unfolding isStrictPartialOrder_def isIrreflexive_def
        by auto
      thus "b \<in> actions"
        using downclosed' ba_in_rel unfolding downclosed_def by auto
    next
      fix b
      assume "b \<in> actions"
             "(a, b) \<in> opsemOrder pre (witnessRestrict wit (insert a actions))"
      hence ba_in_rel: "(a, b) \<in> opsemOrder pre wit"
        using opsemOrderIsMonotonic downclosed_mo
        unfolding hbCalcIsMonotonic_def
        by auto
      thus False using max `b \<in> actions` committed by simp
    qed
  have "exIsConsistent_op ?actions' (pre, ?wit', getRelations pre ?wit')"
    using cons downclosed' execution_restriction by metis
  hence "minOpsemStep pre s ?s' a"
    unfolding minOpsemStep_def Let_def 
    using committed `a \<notin> actions` `a \<in> actions0 pre` witness inOpsemOrder
    by auto
  hence "minOpsemTrace pre (initialState pre) ?s'" using minOpsemStep trace by smt
  thus "\<exists>s'. minOpsemTrace pre (initialState pre) s' \<and> 
             exWitness s' = witnessRestrict wit ?actions' \<and> 
             committed s' = ?actions'"
    by (intro exI[where x="?s'"]) simp
qed

lemma relRestrict_relOver:
  assumes "relOver r a"
  shows   "relRestrict r a = r"
using assms
unfolding relOver_def relDomain_def relRange_def relRestrict_def
by auto

lemma relRestrict2_relOver:
  assumes "relOver r a"
  shows   "relRestrict2 r a = r"
using assms
unfolding relOver_def relDomain_def
by auto

lemma downclosed_relOver:
  assumes "relOver r a"
  shows   "downclosed a r"
using assms
unfolding relOver_def downclosed_def relDomain_def relRange_def by auto

lemma completenessConsistency:
  assumes axiomCons: "axiomConsistent opsem_t p (pre, wit, rl)"
      and finite:    "finite (actions0 pre)"
  shows   "minOpsemConsistent opsem_t p (pre, wit)"
proof -

  have opsem_t: "opsem_t p pre" using axiomCons unfolding axiomConsistent.simps by simp

  have "consistent memory_model = sc_fenced_consistent_execution"
    unfolding memory_model_def by simp
  hence consistent: "exIsConsistent (pre, wit, getRelations pre wit)"
    using axiomCons getRelationsIdentity
    unfolding axiomConsistent.simps exIsConsistent_def getRelations_def
    by auto

  have relOverSb: "relOver (sb pre) (actions0 pre)"
    using consistent cons_well_formed_threads
    unfolding well_formed_threads.simps
    by auto

  have "well_formed_rf (pre, wit, [])" 
    using consistent cons_well_formed_rf unfolding getRelations_def by simp
  hence relOverRf: "relOver (rf wit) (actions0 pre)"
    unfolding well_formed_rf.simps relOver_def relDomain_def relRange_def image_def fst_def snd_def 
    by auto

  have "consistent_mo (pre, wit, [])"
    using consistent cons_consistent_mo unfolding getRelations_def by simp
  hence relOverMo: "relOver (mo wit) (actions0 pre)"
    unfolding consistent_mo.simps by simp

  have "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
    using consistent cons_sc_accesses_consistent_sc unfolding getRelations_def by simp
  hence relOverSc: "relOver (sc wit) (actions0 pre)"
    unfolding sc_accesses_consistent_sc.simps by simp

  have "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
    using consistent cons_locks_only_consistent_lo unfolding getRelations_def by simp
  hence relOverLo: "relOver (lo wit) (actions0 pre)"
    unfolding locks_only_consistent_lo.simps by simp

  have "tot_empty (pre, wit, [])"
    using consistent cons_tot_empty unfolding getRelations_def by simp
  hence relOverTot: "relOver (tot wit) (actions0 pre)"
    unfolding tot_empty.simps by simp

  have wit_restrict: "witnessRestrict wit (actions0 pre) = wit" 
    using relOverRf relOverMo relOverSc relOverLo relOverTot
    unfolding witnessRestrict_def 
    by (simp add: relRestrict_relOver relRestrict2_relOver)

  have "relOver (getHb pre wit) (actions0 pre)" 
    using relOverSb hbRelOver by auto
  hence relOverHbMinus: "relOver (hbMinus pre wit) (actions0 pre)"
    unfolding hbMinus_def relOver_def relDomain_def relRange_def by auto

  have downclosed: "downclosed (actions0 pre) (opsemOrder pre wit)" 
    unfolding opsemOrder_def
    using relOverRf relOverMo relOverHbMinus
    by (simp add: downclosed_relOver)

  have "actions0 pre \<subseteq> actions0 pre" by simp
  then obtain s where "minOpsemTrace pre (initialState pre) s"
                           "exWitness s = witnessRestrict wit (actions0 pre)"
                           "committed s = (actions0 pre)"
    using consistent finite downclosed existenceminOpsemTrace 
    by metis
  thus "minOpsemConsistent opsem_t p (pre, wit)"
    unfolding minOpsemConsistent_def using opsem_t wit_restrict by auto
qed

lemma completenessUndefinedness:
  assumes axiomUndef: "axiomUndefined opsem_t p (pre, wit, rl)"
      and finite:     "finite (actions0 pre)"
  shows   "\<exists>pre wit. minOpsemUndefined opsem_t p (pre, wit)"
proof (intro exI[where x=pre] exI[where x=wit])
  have memModel: "consistent memory_model = sc_fenced_consistent_execution"
    unfolding memory_model_def by simp
  have "axiomConsistent opsem_t p (pre, wit, rl)"
    using axiomUndef unfolding axiomUndefined_def by simp
  hence "minOpsemConsistent opsem_t p (pre, wit)"
    using finite completenessConsistency by simp
  from this obtain s where assms2: "opsem_t p pre"
                                   "minOpsemTrace pre (initialState pre) s"
                                   "exWitness s = wit"
                                   "committed s = actions0 pre"
    unfolding minOpsemConsistent_def by auto
  have "\<not>exIsDefined (pre, wit, relation_calculation memory_model pre wit)"
    using axiomUndef
    unfolding axiomUndefined_def axiomConsistent.simps getRelations_def
    by auto
  hence "\<not>exIsDefined (pre, wit, getRelations pre wit)"
    using getRelationsIdentity unfolding getRelations_def by simp
  hence "\<not> stateIsDefined s" using isDefinedCorrespondence assms2 by auto
  thus "minOpsemUndefined opsem_t p (pre, wit)"
    using assms2 unfolding minOpsemUndefined_def by auto
qed

(* Equivalence ------------------------------------------------------------------------------ *)

definition pre_executions_are_finite where
  "pre_executions_are_finite = 
  (\<forall>opsem_t p pre wit rl. axiomConsistent opsem_t p (pre, wit, rl) \<longrightarrow> finite (actions0 pre))"

theorem equivalence_minOpsem_axiom:
  assumes "pre_executions_are_finite"
  shows   "minOpsemBehaviour = axiomBehaviour"
proof (intro ext)
  fix opsem_t p

  have opsemIsAxiomAux: "minOpsemBehaviour opsem_t p = axiomBehaviourAux opsem_t p"
    proof (cases "\<exists>pre wit rel. axiomUndefined opsem_t p (pre, wit, rel)")
      assume exUndef: "\<exists>pre wit rel. axiomUndefined opsem_t p (pre, wit, rel)"
      hence axiomBeh: "axiomBehaviourAux opsem_t p = Undefined"
        unfolding axiomBehaviourAux_def by auto

      obtain pre wit rel where undef: "axiomUndefined opsem_t p (pre, wit, rel)"
        using exUndef by auto

      have "axiomConsistent opsem_t p (pre, wit, rel)"
        using undef unfolding axiomUndefined_def by simp
      hence finite: "finite (actions0 pre)"
        using assms unfolding pre_executions_are_finite_def by metis

      have "\<exists>pre wit. minOpsemUndefined opsem_t p (pre, wit)"
        using undef finite completenessUndefinedness by simp
      hence "minOpsemBehaviour opsem_t p = Undefined"
        unfolding minOpsemBehaviour_def by auto
      thus "minOpsemBehaviour opsem_t p = axiomBehaviourAux opsem_t p" using axiomBeh by simp
    next
      assume nExUndef: "\<not>(\<exists>pre wit rel. axiomUndefined opsem_t p (pre, wit, rel))"
      hence axiomBeh: "axiomBehaviourAux opsem_t p = 
                       Defined {(pre, wit). \<exists>rel. axiomConsistent opsem_t p (pre, wit, rel)}"
        unfolding axiomBehaviourAux_def by auto
        
      have "\<not>(\<exists>pre wit. minOpsemUndefined opsem_t p (pre, wit))"
        using nExUndef soundnessUndefinedness by blast
      hence opsemBeh: "minOpsemBehaviour opsem_t p = 
                       Defined {(pre, wit). minOpsemConsistent opsem_t p (pre, wit)}"
        unfolding minOpsemBehaviour_def by auto

      have "\<And>pre wit. minOpsemConsistent opsem_t p (pre, wit) = 
                       (\<exists>rel. axiomConsistent opsem_t p (pre, wit, rel))"
        proof 
          fix pre wit
          assume "minOpsemConsistent opsem_t p (pre, wit)"
          thus "\<exists>rel. axiomConsistent opsem_t p (pre, wit, rel)" 
            using soundnessConsistency by blast
        next
          fix pre wit
          assume "\<exists>rel. axiomConsistent opsem_t p (pre, wit, rel)"
          from this obtain rel where axCons: "axiomConsistent opsem_t p (pre, wit, rel)" by fast
          hence finite: "finite (actions0 pre)"
            using assms unfolding pre_executions_are_finite_def by metis
          show "minOpsemConsistent opsem_t p (pre, wit)"
            using axCons finite completenessConsistency by simp
        qed
     
      thus "minOpsemBehaviour opsem_t p = axiomBehaviourAux opsem_t p"
        using axiomBeh opsemBeh by auto
    qed

  have axiomIsAxiomAux: "axiomBehaviour opsem_t p = axiomBehaviourAux opsem_t p"
    unfolding axiomBehaviourAux_def
    apply simp
    unfolding axiomUndefined_def axiomConsistent.simps exIsDefined_simp
    apply auto
    unfolding axiomBehaviour_def behaviour_def Let_def
    apply auto
    unfolding sublanguage_def sc_fenced_condition_def
    apply auto
    unfolding observable_filter_def
    by auto

  show "minOpsemBehaviour opsem_t p = axiomBehaviour opsem_t p"
    using opsemIsAxiomAux axiomIsAxiomAux by simp

qed
  
end
