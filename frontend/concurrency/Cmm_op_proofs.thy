(* (c) Kyndylan Nienhuis, University of Cambridge *)

(*<*)
theory Cmm_op_proofs

imports
Main
"lib/Cmm_op"
Cmm_master_lemmas
Nondeterminism_lemmas  
begin
(*>*)

section {* The axiomatic model *}

abbreviation "sublanguage \<equiv> with_consume_condition"
abbreviation "memory_model \<equiv> standard_memory_model"
abbreviation "axBehaviour \<equiv> standard_behaviour"
abbreviation "axUndefined \<equiv> locks_only_undefined_behaviour_alt"
abbreviation "getRelations \<equiv> standard_relations"
abbreviation "getHb \<equiv> with_consume_hb"
abbreviation "getVse \<equiv> with_consume_vse"
abbreviation "axConsistent ex \<equiv> apply_tree standard_consistent_execution ex"
abbreviation "axConsistentAlt pre wit \<equiv> axConsistent (pre, wit, getRelations pre wit)"

lemmas sublanguage_def = with_consume_condition_def
lemmas memory_model_def = with_consume_memory_model_def
lemmas axBehaviour_def = standard_behaviour_def
lemmas axUndefined_def = locks_only_undefined_behaviour_alt_def
lemmas getRelations_def = standard_relations_def
lemmas getHb_def = with_consume_hb_def
lemmas getVse_def = with_consume_vse_def
lemmas axConsistent_def = standard_consistent_execution_def
lemmas axConsistentAlt_def = axConsistent_def

lemmas getRelations_simp = standard_relations_simp
                           standard_relations_alt_def



section {* The simplified axiomatic model *}

subsection {* well_formed_threads_opsem *}

lemma rel_list_well_formed_threads_opsem [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_threads_opsem (pre, wit, rel) = well_formed_threads_opsem (pre, wit, [])"
using assms
unfolding well_formed_threads_opsem.simps
by simp

lemma witness_well_formed_threads_opsem [simp]:
  assumes "wit \<noteq> empty_witness"
  shows   "well_formed_threads_opsem (pre, wit, []) = well_formed_threads_opsem (pre, empty_witness, [])"
using assms
unfolding well_formed_threads_opsem.simps
by simp

lemma well_formed_threads_opsem_eq:
  shows "  well_formed_threads_opsem (pre, wit, rel)
         = (well_formed_threads (pre, wit, rel) \<and> finite (actions0 pre))"
unfolding well_formed_threads_opsem.simps
..

lemma  well_formed_threads_opsemE [elim]:
  assumes "well_formed_threads_opsem (pre, wit, rel)"
  obtains "finite (actions0 pre)"
      and "actions_respect_location_kinds (actions0 pre) (lk pre)"  
      and "blocking_observed (actions0 pre) (sb pre)"  
      and "inj_on aid_of (actions0 pre)"  
      and "relation_over (actions0 pre) (sb pre)"  
      and "relation_over (actions0 pre) (asw pre) "  
      and "threadwise (actions0 pre) (sb pre)"  
      and "interthread (actions0 pre) (asw pre)"  
      and "isStrictPartialOrder (sb pre)"  
      and "isStrictPartialOrder (dd pre)"  
      and "(dd pre) \<subseteq> (sb pre)"  
      and "indeterminate_sequencing pre"  
      and "irrefl (sbasw pre)"  
      and "finite_prefixes (sbasw pre) (actions0 pre)"  
      and "disjoint_allocs (actions0 pre)"
using assms
unfolding well_formed_threads_opsem_eq
by auto

subsection {* axsimpConsistent *}

abbreviation "axsimpConsistent ex \<equiv> apply_tree axsimpConsistentExecution ex"
abbreviation "axsimpConsistentAlt pre wit \<equiv> axsimpConsistent (pre, wit, getRelations pre wit)"

lemmas axsimpConsistent_def = axsimpConsistentExecution_def
lemmas axsimpConsistentAlt_def = axsimpConsistent_def

lemma axsimpConsistentI [intro?]: 
  assumes "assumptions (pre, wit, [])"
      and "tot_empty (pre, wit, [])"
      and "well_formed_threads_opsem (pre, wit, [])"
      and "well_formed_rf (pre, wit, [])"
      and "locks_only_consistent_locks (pre, wit, [])"
      and "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
      and "consistent_mo (pre, wit, [])"
      and "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
      and "sc_fenced_sc_fences_heeded (pre, wit, [])"
      and "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
      and "det_read_alt (pre, wit, [(''hb'', getHb pre wit)])"
      and "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), 
                                                (''vse'', getVse pre wit)])"
      and "consistent_atomic_rf (pre, wit, [(''hb'', getHb pre wit)])"
      and "coherent_memory_use (pre, wit, [(''hb'', getHb pre wit)])"
      and "rmw_atomicity (pre, wit, [])"
      and "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', getHb pre wit)])"
  shows   "axsimpConsistentAlt pre wit"
using assms
unfolding axsimpConsistent_def
          memory_model_def
by simp_all

lemma axsimpConsistentE [elim]: 
  assumes "axsimpConsistentAlt pre wit"
  obtains "assumptions (pre, wit, [])"
      and "tot_empty (pre, wit, [])"
      and "well_formed_threads_opsem (pre, wit, [])"
      and "well_formed_rf (pre, wit, [])"
      and "locks_only_consistent_locks (pre, wit, [])"
      and "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
      and "consistent_mo (pre, wit, [])"
      and "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
      and "sc_fenced_sc_fences_heeded (pre, wit, [])"
      and "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
      and "det_read_alt (pre, wit, [(''hb'', getHb pre wit)])"
      and "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), 
                                                (''vse'', getVse pre wit)])"
      and "consistent_atomic_rf (pre, wit, [(''hb'', getHb pre wit)])"
      and "coherent_memory_use (pre, wit, [(''hb'', getHb pre wit)])"
      and "rmw_atomicity (pre, wit, [])"
      and "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding axsimpConsistent_def
          memory_model_def
by simp_all

lemma axsimpConsistentEq:
  fixes pre wit
  defines "ex \<equiv> (pre, wit, getRelations pre wit)"
  shows   "axsimpConsistent ex = (axConsistent ex \<and> finite (actions0 pre))"
using det_read_simp 
      standard_consistent_atomic_rf_simp
      well_formed_threads_opsem_eq
unfolding axsimpConsistent_def 
          axConsistent_def
          getRelations_simp 
          with_consume_vse_def
          ex_def 
by simp metis

subsection {* axsimpMemoryModel *}

lemma axsimpMemoryModel_simps [simp]:
  shows "consistent axsimpMemoryModel = axsimpConsistentExecution"
        "relation_calculation axsimpMemoryModel = standard_relations"
        "undefined0 axsimpMemoryModel = locks_only_undefined_behaviour"
unfolding axsimpMemoryModel_def
by simp_all

section {* The incremental model *}

subsection {* Simplifications *}

abbreviation "hbMinusAlt pre wit \<equiv> hbMinus (pre,wit, getRelations pre wit)"
abbreviation "incComAlt pre wit \<equiv> incCom (pre,wit, getRelations pre wit)"
abbreviation "incCommittedSet s \<equiv> set (incCommitted s)"

lemmas hbMinusAlt_def = hbMinus.simps
lemmas incComAlt_def = incCom.simps

lemma incPreRestrict_simps [simp]:
  shows "actions0 (preRestrict pre actions) = actions0 pre \<inter> actions "
        "threads (preRestrict pre actions) = threads pre"
        "lk (preRestrict pre actions) = lk pre"
        "sb (preRestrict pre actions) = relRestrict (sb pre) actions"
        "asw (preRestrict pre actions) = relRestrict (asw pre) actions"
        "dd (preRestrict pre actions) = relRestrict (dd pre) actions"
unfolding preRestrict_def
by simp_all

lemma preRestrict_id:
  assumes "well_formed_threads_opsem (pre, empty_witness, [])"
  shows   "preRestrict pre (actions0 pre) = pre"
proof -
  have sb: "relOver (sb pre) (actions0 pre)"
    using assms by auto
  have asw: "relOver (asw pre) (actions0 pre)"
    using assms by auto
  have "dd pre \<subseteq> sb pre"
    using assms by auto
  hence dd: "relOver (dd pre) (actions0 pre)"
    using sb relOver_subset by metis
  show ?thesis
    using relRestrict_id[OF sb] 
          relRestrict_id[OF dd] 
          relRestrict_id[OF asw]
    unfolding preRestrict_def
    by simp
qed

lemma incPreRestrict_sbasw_empty [simp]:
  shows "sbasw (preRestrict pre {}) = {}"
unfolding sbasw_def
by simp

lemma incPreRestrict_sbasw_subset:
  shows "sbasw (preRestrict pre actions) \<subseteq> relRestrict (sbasw pre) actions"
proof -
  have "sbasw (preRestrict pre actions) = (relRestrict (sb pre \<union> asw pre) actions)\<^sup>+"
    unfolding sbasw_def by simp
  also have "... \<subseteq> relRestrict (sbasw pre) actions"
    unfolding sbasw_def
    using relRestrict_trancl_subset
    by metis
  finally show ?thesis .
qed

lemma incPreRestrict_sbasw_subset2:
  shows "sbasw (preRestrict pre actions) \<subseteq> sbasw pre"
using incPreRestrict_sbasw_subset
unfolding relRestrict_def
by auto

lemma incWitRestrict_simps [simp]:
  shows "rf (incWitRestrict wit actions) = relRestrict (rf wit) actions"
        "mo (incWitRestrict wit actions) = relRestrict (mo wit) actions"
        "sc (incWitRestrict wit actions) = relRestrict (sc wit) actions"
        "lo (incWitRestrict wit actions) = relRestrict (lo wit) actions"
        "tot (incWitRestrict wit actions) = relRestrict (tot wit) actions"
unfolding incWitRestrict_def
by simp_all

lemma incWitRestrict_empty1 [simp]:
  shows "incWitRestrict wit {} = empty_witness"
unfolding incWitRestrict_def empty_witness_def 
by simp

lemma incWitRestrict_empty2 [simp]:
  shows "incWitRestrict empty_witness x = empty_witness"
unfolding incWitRestrict_def empty_witness_def 
by simp

lemma incWitRestrict_multiple [simp]:
  shows "incWitRestrict (incWitRestrict x y) z = incWitRestrict x (y \<inter> z)"
unfolding incWitRestrict_def 
by auto

lemma initialState_simps [simp]:
  shows "incWit (incInitialState pre) = empty_witness"
        "incCommitted (incInitialState pre) = []"
unfolding incInitialState_def
by simp_all

lemma hbMinusE [elim]:
  assumes "(a, b) \<in> hbMinus (pre, wit, (''hb'', hb)#rel)"
  obtains "(a, b) \<in> hb"
      and "is_na_or_non_write pre b"
using assms
unfolding hbMinus.simps
by auto

lemma hbMinus_relation_rel_list [simp]:
  assumes "rel \<noteq> []"
  shows "  hbMinus (pre, wit, (''hb'', hb)#rel) 
         = hbMinus (pre, wit, [(''hb'', hb)])"
unfolding hbMinus.simps ..

lemma hbMinus_relation_rel_list2 [simp]:
  shows "  hbMinus (pre, wit, getRelations pre wit) 
         = hbMinus (pre, wit, [(''hb'', getHb pre wit)])"
unfolding getRelations_simp by simp

lemma is_na_or_non_write_relRestrict_simp [simp]:
  shows "  is_na_or_non_write (preRestrict pre actions) b
         = is_na_or_non_write pre b"
unfolding is_na_or_non_write_def
by auto

subsection {* Commitment order *}

lemma not_at_writes_in_hb_minus:
  assumes cons:         "axsimpConsistentAlt pre wit"
      and in_rel:       "(a, b) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
      and not_at_write: "is_na_or_non_write pre a"
  shows                 "(a, b) \<in> hbMinusAlt pre wit"
using in_rel
proof (elim UnE)
  assume in_rf: "(a, b) \<in> rf wit"
  hence "is_write a" "is_read b" "loc_of a = loc_of b" 
    using cons by auto
  hence "is_at_non_atomic_location (lk pre) a"
    using not_at_write unfolding is_na_or_non_write_def by simp
  hence not_at: "is_at_non_atomic_location (lk pre) b"
    using `loc_of a = loc_of b` 
    unfolding is_at_non_atomic_location_def by auto
  hence "(a, b) \<in> getVse pre wit"
    using in_rf cons by auto
  hence in_hb: "(a, b) \<in> getHb pre wit"
    by auto
  have "is_na_or_non_write pre b"
    using not_at unfolding is_na_or_non_write_def by simp
  thus "(a, b) \<in> hbMinusAlt pre wit"
    using in_hb
    apply simp
    unfolding hbMinusAlt_def
    by auto
next
  assume "(a, b) \<in> mo wit"
  hence "is_write a \<and> is_at_atomic_location (lk pre) a"
    using cons by auto
  hence False
    using not_at_write 
    unfolding is_na_or_non_write_def
    by auto
  thus "(a, b) \<in> hbMinusAlt pre wit" 
    by contradiction auto
qed auto

lemma not_at_writes_in_hb_minus_tc:
  assumes cons:         "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_tc_rel:    "(a, b) \<in> (hbMinusAlt pre wit \<union> rf wit \<union> mo wit)\<^sup>+"
      and not_at_write: "is_na_or_non_write pre a"
  shows                 "(a, b) \<in> (hbMinusAlt pre wit)\<^sup>+" 
proof (rule trancl_induct[OF in_tc_rel])
  fix y
  assume in_rel: "(a, y) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
  have "(a, y) \<in> hbMinusAlt pre wit" 
    using not_at_writes_in_hb_minus[OF cons in_rel not_at_write] .
  thus "(a, y) \<in> (hbMinusAlt pre wit)\<^sup>+" by auto
next
  fix y z
  assume ay_in_rel: "(a, y) \<in> (hbMinusAlt pre wit \<union> rf wit \<union> mo wit)\<^sup>+"
     and yz_in_rel: "(y, z) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
     and ay_in_tc:  "(a, y) \<in> (hbMinusAlt pre wit)\<^sup>+"
  hence "\<exists>c. (c, y) \<in> hbMinusAlt pre wit" 
    using tranclD2[where R="(hbMinusAlt pre wit)"] by auto
  hence "is_na_or_non_write pre y" by auto
  hence "(y, z) \<in> hbMinusAlt pre wit"
    using not_at_writes_in_hb_minus[OF cons yz_in_rel] by auto
  thus "(a, z) \<in> (hbMinusAlt pre wit)\<^sup>+" 
    using ay_in_tc by (auto simp add: trancl_into_trancl)
qed

lemma at_writes_in_mo:
  assumes cons:        "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_rel:      "(a, b) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
      and is_at_write: "\<not>is_na_or_non_write pre b"
  shows                "(a, b) \<in> mo wit"
using in_rel
proof (elim UnE)
  assume "(a, b) \<in> hbMinusAlt pre wit"
  hence "is_na_or_non_write pre b" by auto
  hence False using is_at_write by simp
  thus ?thesis by simp
next
  assume in_rf: "(a, b) \<in> rf wit"
  hence "is_read b" using cons by auto
  hence "is_RMW b" 
    using is_at_write
    unfolding is_na_or_non_write_def
    by (cases b) simp_all
  thus "(a, b) \<in> mo wit"
    using in_rf cons by auto
qed auto

lemma at_writes_in_mo_tc:
  assumes cons:        "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_rel_tc:   "(a, b) \<in> (hbMinusAlt pre wit \<union> rf wit \<union> mo wit)\<^sup>+"
      and is_at_write: "\<not>is_na_or_non_write pre b"
  shows                "(a, b) \<in> (mo wit)\<^sup>+"
proof (rule converse_trancl_induct[OF in_rel_tc]) 
  fix y
  assume in_rel: "(y, b) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
  have "(y, b) \<in> mo wit" using at_writes_in_mo[OF cons in_rel is_at_write] .
  thus "(y, b) \<in> (mo wit)\<^sup>+" by auto
next
  fix y z
  assume "(y, z) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
         "(z, b) \<in> (hbMinusAlt pre wit \<union> rf wit \<union> mo wit)\<^sup>+"
         "(z, b) \<in> (mo wit)\<^sup>+"
  hence "\<exists>c. (z, c) \<in> mo wit" 
    using tranclD[where R="mo wit"] by auto
  hence "is_write z" "is_at_atomic_location (lk pre) z"
    using cons by auto
  hence "\<not> is_na_or_non_write pre z" 
    unfolding is_na_or_non_write_def
    by auto
  hence "(y, z) \<in> mo wit"
    using `(y, z) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit`
    using at_writes_in_mo[OF cons] by auto
  thus "(y, b) \<in> (mo wit)\<^sup>+" 
    using `(z, b) \<in> (mo wit)\<^sup>+` 
    by (auto simp add: trancl_into_trancl)
qed 

lemma opsemOrder_isStrictPartialOrder:
  assumes cons: "axsimpConsistent (pre, wit, getRelations pre wit)"
  shows         "isStrictPartialOrder (incComAlt pre wit)"
proof -
  have "irrefl (incComAlt pre wit)"
    unfolding irrefl_def
    proof (intro allI notI)
      fix x
      assume "(x, x) \<in> incComAlt pre wit"
      hence in_rel: "(x, x) \<in> (hbMinusAlt pre wit \<union> rf wit \<union> mo wit)\<^sup>+"
        unfolding incComAlt_def
        by (metis Un_assoc)
      show False
        proof (cases "is_na_or_non_write pre x")
          have cons_hb: "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
            using cons by auto
          have "(hbMinusAlt pre wit) \<subseteq> getHb pre wit" by auto
          hence hbMinus_in_hb: "(hbMinusAlt pre wit)\<^sup>+ \<subseteq> (getHb pre wit)\<^sup>+" 
            using trancl_mono by auto
          hence irrefl_hbMinus: "irrefl ((hbMinusAlt pre wit)\<^sup>+)"
            using cons_hb
            unfolding consistent_hb.simps irrefl_def
            by auto
          assume "is_na_or_non_write pre x"
          hence "(x, x) \<in> (hbMinusAlt pre wit)\<^sup>+" 
            using not_at_writes_in_hb_minus_tc[OF cons in_rel] by metis
          thus False using irrefl_hbMinus unfolding irrefl_def by metis         
        next
          have cons_mo: "consistent_mo (pre, wit, [])"
            using cons by auto
          assume "\<not>is_na_or_non_write pre x"
          hence "(x, x) \<in> (mo wit)\<^sup>+" 
            using at_writes_in_mo_tc[OF cons in_rel] by metis
          hence "(x, x) \<in> mo wit"
            using cons_mo unfolding consistent_mo.simps by simp
          thus False
            using cons_mo unfolding consistent_mo.simps irrefl_def by simp            
        qed
    qed
  thus "isStrictPartialOrder (incComAlt pre wit)" 
    unfolding isStrictPartialOrder_def incComAlt_def by simp
qed

(* We define a specialised induction rule for downclosed finite sets. *)
lemma finite_downclosedsubset_induct:
  assumes fin:        "finite A"
      and universe:   "A \<subseteq> B"
      and downclosed: "downclosed A R"
      and order:      "acyclic R"
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

subsection {* Properties of happens-before *}

subsubsection {* RelOver *}

(* In this section we prove all properties of getHb that we need, so after this section we never
   need to unfold the definition of hb. This way, if hb changes, we only need to change this 
   section. *)

(* RelOver in the rel-acq-rlx fragment *)

lemma relOver_release_acquire_relaxed_sw:
  shows   "relOver (release_acquire_relaxed_synchronizes_with_set_alt pre wit) (actions0 pre)"
unfolding release_acquire_relaxed_synchronizes_with_set_alt_def
          release_acquire_relaxed_synchronizes_with_set_def 
unfolding relOver_def 
by auto
 
lemma relOver_release_acquire_relaxed_hb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (release_acquire_relaxed_hb pre wit) (actions0 pre)"
unfolding release_acquire_relaxed_hb_def no_consume_hb_def
using assms relOver_release_acquire_relaxed_sw
by simp

(* RelOver in the rel-acq-rlx-fence fragment *)

lemma relOver_release_acquire_fenced_sw:
  shows   "relOver (release_acquire_fenced_synchronizes_with_set_alt pre wit) (actions0 pre) "
unfolding release_acquire_fenced_synchronizes_with_set_alt_def
          release_acquire_fenced_synchronizes_with_set_def 
unfolding relOver_def 
unfolding sw_asw_def
          sw_lock_def
          sw_rel_acq_rs_def
          sw_fence_sb_hrs_rf_sb_def
          sw_fence_sb_hrs_rf_def
          sw_fence_rs_rf_sb_def
by auto
 
lemma relOver_release_acquire_fenced_hb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (release_acquire_fenced_hb pre wit) (actions0 pre)"
unfolding release_acquire_fenced_hb_def no_consume_hb_def
using assms relOver_release_acquire_fenced_sw
by simp

(* RelOver in the with_consume fragment *)

lemma relOver_dob:
  shows   "relOver (with_consume_dob_set_alt pre wit) (actions0 pre)"
unfolding with_consume_dob_set_alt_def with_consume_dob_set_def 
unfolding relOver_def 
by auto

lemma relOver_ithb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (inter_thread_happens_before_alt pre wit) (actions0 pre)"
unfolding inter_thread_happens_before_alt_def
          inter_thread_happens_before_step_def
          inter_thread_happens_before_r_def
using assms relOver_dob relOver_release_acquire_fenced_sw
by (simp add: relOver_relComp)
 
lemma relOver_with_consume_hb:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (with_consume_hb pre wit) (actions0 pre)"
unfolding with_consume_hb_def happens_before_def
using assms relOver_ithb
by simp

subsubsection {* Empty hb *}

(* Empty hb in the with_consume fragment *)

lemma sw_asw_empty [simp]:
  shows "sw_asw (preRestrict pre {}) = {}"
unfolding sw_asw_def
by simp

lemma sw_lock_empty [simp]:
  shows "sw_lock (preRestrict pre {}) empty_witness = {}"
unfolding sw_lock_def
by simp

lemma sw_rel_acq_rs_empty [simp]:
  shows "sw_rel_acq_rs (preRestrict pre {}) empty_witness = {}"
unfolding sw_rel_acq_rs_def
by simp

lemma sw_fence_sb_hrs_rf_sb_empty [simp]:
  shows "sw_fence_sb_hrs_rf_sb (preRestrict pre {}) empty_witness = {}"
unfolding sw_fence_sb_hrs_rf_sb_def
by simp

lemma sw_fence_sb_hrs_rf_empty [simp]:
  shows "sw_fence_sb_hrs_rf (preRestrict pre {}) empty_witness = {}"
unfolding sw_fence_sb_hrs_rf_def
by simp

lemma sw_fence_rs_rf_sb_empty [simp]:
  shows "sw_fence_rs_rf_sb (preRestrict pre {}) empty_witness = {}"
unfolding sw_fence_rs_rf_sb_def
by simp

lemma release_acquire_fenced_synchronizes_with_set_empty [simp]:
  shows "release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre {}) empty_witness = {}"
unfolding release_acquire_fenced_synchronizes_with_set_alt_def
by simp

lemma with_consume_dob_set_empty [simp]:
  shows "with_consume_dob_set_alt (preRestrict pre {}) empty_witness = {}"
unfolding with_consume_dob_set_alt_def with_consume_dob_set_def
by simp

lemma ithb_r_empty [simp]:
  shows "inter_thread_happens_before_r (preRestrict pre {}) empty_witness = {}"
unfolding inter_thread_happens_before_r_def
by simp

lemma ithb_step_empty [simp]:
  shows "inter_thread_happens_before_step (preRestrict pre {}) empty_witness = {}"
unfolding inter_thread_happens_before_step_def
by simp

lemma ithb_empty [simp]:
  shows "inter_thread_happens_before_alt (preRestrict pre {}) empty_witness = {}"
unfolding inter_thread_happens_before_alt_def
by simp

lemma happens_before_empty [simp]:
  shows "happens_before s {} {} = {}"
unfolding happens_before_def
by simp

lemma getHb_empty [simp]:
  shows "getHb (preRestrict pre {}) empty_witness = {}"
unfolding getHb_def
by simp

lemma getVse_empty [simp]:
  shows "getVse (preRestrict pre {}) empty_witness = {}"
unfolding getVse_def
by simp

subsubsection {* Sb in hb *}

(* Sb in hb in the rel-acq-rlx fragment *)

lemma sbInHb_release_acquire_relaxed_hb:
  shows "sb pre \<subseteq> release_acquire_relaxed_hb pre wit"
unfolding release_acquire_relaxed_hb_def no_consume_hb_def
by auto

(* Sb in hb in the rel-acq-rlx-fence fragment *)

lemma sbInHb_release_acquire_fenced_hb:
  shows "sb pre \<subseteq> release_acquire_fenced_hb pre wit"
unfolding release_acquire_fenced_hb_def no_consume_hb_def
by auto

(* Sb in hb in the with_consume fragment *)

lemma sbInHb_with_consume_hb:
  shows "sb pre \<subseteq> with_consume_hb pre wit"
unfolding with_consume_hb_def happens_before_def
by simp

subsubsection {* Syncing locks *}

(* Syncing locks in hb in the rel-acq-rlx fragment *)

(* To enable reuse between fragments, we isolated the properties that depend on hb. *)

type_synonym hbCalculation = "pre_execution \<Rightarrow> execution_witness \<Rightarrow> (action * action) set"

definition otherThreadLoInHb :: "hbCalculation \<Rightarrow> bool" where 
  "otherThreadLoInHb hbCalc \<equiv> \<forall>a b pre wit. tid_of a \<noteq> tid_of b \<longrightarrow> 
                                             is_unlock a \<longrightarrow> 
                                             is_lock b \<longrightarrow> 
                                             a \<in> actions0 pre \<longrightarrow> 
                                             b \<in> actions0 pre \<longrightarrow> 
                                             (a, b) \<in> lo wit \<longrightarrow> 
                                             (a, b) \<in> hbCalc pre wit"

definition hbCalcRespectsSyncingLocks  :: "hbCalculation \<Rightarrow> bool" where 
   "hbCalcRespectsSyncingLocks hbCalc = (\<forall> pre0. \<forall> wit. 
          well_formed_threads_opsem (pre0, wit, [])
      \<longrightarrow> locks_only_consistent_lo (pre0, wit, [((''hb''), hbCalc pre0 wit)])
      \<longrightarrow> (\<forall> a. \<forall> b.     (is_unlock a \<and> is_lock b \<and> (a, b) \<in> lo wit)
                     \<longrightarrow> (a, b) \<in> hbCalc pre0 wit))"

lemma otherThreadLoInHb_release_acquire_relaxed_hb:
  shows   "otherThreadLoInHb release_acquire_relaxed_hb"
unfolding otherThreadLoInHb_def
          release_acquire_relaxed_hb_def 
          no_consume_hb_def
          release_acquire_relaxed_synchronizes_with_set_alt_def
          sw_lock_def
by auto

lemma loInHb_aux:
  assumes well_formed_threads:      "well_formed_threads_opsem (pre, wit, [])"
      and locks_only_consistent_lo: "locks_only_consistent_lo (pre, wit, [(''hb'', hbCalc pre wit)])"
      and otherThreadLoInHb:        "otherThreadLoInHb hbCalc"
      and sbInHb:                   "sb pre \<subseteq> hbCalc pre wit"
      and is_lo:                    "is_unlock a" "is_lock b" "(a, b) \<in> lo wit"
  shows                             "(a, b) \<in> hbCalc pre wit"
proof -

  have "relOver (lo wit) (actions0 pre)"
    using locks_only_consistent_lo by auto
  hence in_actions: "a \<in> actions0 pre" "b \<in> actions0 pre" 
    using is_lo unfolding relOver_def by auto

  show "(a, b) \<in> hbCalc pre wit" 
    proof (cases "tid_of a = tid_of b")
      assume "tid_of a \<noteq> tid_of b"
      thus "(a, b) \<in> hbCalc pre wit"
        using otherThreadLoInHb in_actions is_lo
        unfolding otherThreadLoInHb_def
        by simp
    next
      assume tid_eq: "tid_of a = tid_of b"

      have "(b, a) \<notin> hbCalc pre wit" 
        using locks_only_consistent_lo is_lo by auto
      hence "(b, a) \<notin> sb pre" 
        using sbInHb by auto

      have "a \<noteq> b" 
        using locks_only_consistent_lo is_lo by auto

      have "is_at_mutex_location (lk pre) a" 
        using assms is_lo in_actions by auto
      hence not_na_loc: "\<not> is_at_non_atomic_location (lk pre) a"
        by auto

      have "indeterminate_sequencing pre" 
        using well_formed_threads by auto
      hence "(a, b) \<in> sb pre"
        unfolding indeterminate_sequencing_def
        using in_actions tid_eq `a \<noteq> b` not_na_loc `(b, a) \<notin> sb pre`
        by auto

      thus "(a, b) \<in> hbCalc pre wit"
        using sbInHb by auto

    qed
qed

lemma loInHb_release_acquire_relaxed_hb:
  shows "hbCalcRespectsSyncingLocks release_acquire_relaxed_hb"
unfolding hbCalcRespectsSyncingLocks_def
using sbInHb_release_acquire_relaxed_hb 
      otherThreadLoInHb_release_acquire_relaxed_hb
      loInHb_aux
by metis

(* Syncing locks in hb in the rel-acq-rlx-fence fragment *)

lemma otherThreadLoInHb_release_acquire_fenced_hb:
  shows   "otherThreadLoInHb release_acquire_fenced_hb"
unfolding otherThreadLoInHb_def
          release_acquire_fenced_hb_def 
          no_consume_hb_def
          release_acquire_fenced_synchronizes_with_set_alt_def
          sw_lock_def
by auto

lemma loInHb_release_acquire_fenced_hb:
  shows "hbCalcRespectsSyncingLocks release_acquire_fenced_hb"
unfolding hbCalcRespectsSyncingLocks_def
using sbInHb_release_acquire_fenced_hb 
      otherThreadLoInHb_release_acquire_fenced_hb
      loInHb_aux
by metis

(* Syncing locks in hb in the with_consume fragment *)

lemma otherThreadLoInHb_with_consume_hb:
  shows   "otherThreadLoInHb with_consume_hb"
unfolding otherThreadLoInHb_def
          with_consume_hb_def 
          happens_before_def
          inter_thread_happens_before_alt_def
          inter_thread_happens_before_step_def
          inter_thread_happens_before_r_def
          release_acquire_fenced_synchronizes_with_set_alt_def
          sw_lock_def
by auto

lemma loInHb_with_consume_hb:
  shows "hbCalcRespectsSyncingLocks with_consume_hb"
unfolding hbCalcRespectsSyncingLocks_def
using sbInHb_with_consume_hb 
      otherThreadLoInHb_with_consume_hb
      loInHb_aux
by metis

subsubsection {* Monotonicity *}

(* Monotonicity hb in the locks only fragment *)

lemma monotonicity_locks_only_sw:
  shows   "  locks_only_sw_set_alt (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> locks_only_sw_set_alt pre wit "
unfolding locks_only_sw_set_alt_def
          locks_only_sw_set_def 
by (auto simp add: locks_only_sw_def)

lemma monotonicity_locks_only_sw2:
  shows   "  locks_only_sw_set_alt pre (incWitRestrict wit actions)
           \<subseteq> locks_only_sw_set_alt pre wit "
unfolding locks_only_sw_set_alt_def
          locks_only_sw_set_def 
by (auto simp add: locks_only_sw_def)

lemma monotonicity_no_consume_hb:
  assumes "sw2 \<subseteq> sw"
      and "p_sb2 \<subseteq> p_sb"
  shows   "no_consume_hb p_sb2 sw2 \<subseteq> no_consume_hb p_sb sw"
using assms
unfolding no_consume_hb_def
by (metis Un_mono trancl_mono2)

lemma monotonicity_locks_only_hb:
  shows "  locks_only_hb (preRestrict pre actions) (incWitRestrict wit actions)
         \<subseteq> locks_only_hb pre wit"
unfolding locks_only_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_locks_only_sw]
by auto

lemma monotonicity_locks_only_hb2:
  shows "  locks_only_hb pre (incWitRestrict wit actions)
         \<subseteq> locks_only_hb pre wit"
unfolding locks_only_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_locks_only_sw2]
by auto

(* Monotonicity hb in the rel-acq fragment *)

lemma monotonicity_release_acquire_sw:
  shows   "  release_acquire_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions) 
           \<subseteq> release_acquire_synchronizes_with_set_alt pre wit"
apply (intro subrelI, elim release_acquire_swIE)
unfolding sw_asw_def sw_lock_def sw_rel_acq_def
by auto

lemma monotonicity_release_acquire_sw2:
  shows   "  release_acquire_synchronizes_with_set_alt pre (incWitRestrict wit actions) 
           \<subseteq> release_acquire_synchronizes_with_set_alt pre wit"
apply (intro subrelI, elim release_acquire_swIE)
unfolding sw_asw_def sw_lock_def sw_rel_acq_def
by auto

lemma monotonicity_release_acquire_hb:
  shows "  release_acquire_hb (preRestrict pre actions) (incWitRestrict wit actions) 
         \<subseteq> release_acquire_hb pre wit"
unfolding release_acquire_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_sw]
by auto

lemma monotonicity_release_acquire_hb2:
  shows "  release_acquire_hb pre (incWitRestrict wit actions) 
         \<subseteq> release_acquire_hb pre wit"
unfolding release_acquire_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_sw2]
by auto

(* Monotonicity hb in the rel-acq-rlx fragment *)

lemma monotonicity_release_sequence:
  assumes "downclosed actions (mo wit)"
          "(a, b) \<in> release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> release_sequence_set_alt pre wit"
using assms
unfolding release_sequence_set_alt_def 
          release_sequence_set_def
          downclosed_def
by auto

lemma monotonicity_release_sequence2:
  assumes "downclosed actions (mo wit)"
          "(a, b) \<in> release_sequence_set_alt pre (incWitRestrict wit actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> release_sequence_set_alt pre wit"
using assms
unfolding release_sequence_set_alt_def 
          release_sequence_set_def
          downclosed_def
by auto

lemma monotonicity_sw_rel_acq_rs:
  assumes "downclosed actions (mo wit)"
  shows   "  sw_rel_acq_rs (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> sw_rel_acq_rs pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_rel_acq_rs (preRestrict pre actions) (incWitRestrict wit actions)"
  thus   "(a, b) \<in> sw_rel_acq_rs pre wit"
    proof (cases rule: sw_rel_acq_rsIE)
      case (rel_acq_rs c)
      hence "c \<in> actions" by auto 
      hence "(a, c) \<in> release_sequence_set_alt pre wit" 
        using monotonicity_release_sequence assms rel_acq_rs
        by metis
      thus "   a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> c \<in> actions0 pre
            \<and> (a, c) \<in> release_sequence_set_alt pre wit \<and> (c, b) \<in> rf wit "
        using rel_acq_rs by auto 
    qed
qed

lemma monotonicity_sw_rel_acq_rs2:
  assumes "downclosed actions (mo wit)"
  shows   "  sw_rel_acq_rs pre (incWitRestrict wit actions)
           \<subseteq> sw_rel_acq_rs pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_rel_acq_rs pre (incWitRestrict wit actions)"
  thus   "(a, b) \<in> sw_rel_acq_rs pre wit"
    proof (cases rule: sw_rel_acq_rsIE)
      case (rel_acq_rs c)
      hence "c \<in> actions" by auto 
      hence "(a, c) \<in> release_sequence_set_alt pre wit" 
        using monotonicity_release_sequence2 assms rel_acq_rs
        by metis
      thus "   a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> c \<in> actions0 pre
            \<and> (a, c) \<in> release_sequence_set_alt pre wit \<and> (c, b) \<in> rf wit "
        using rel_acq_rs by auto 
    qed
qed

lemma monotonicity_release_acquire_relaxed_sw:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  release_acquire_relaxed_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> release_acquire_relaxed_synchronizes_with_set_alt pre wit"
using monotonicity_sw_rel_acq_rs[OF downclosed]
by (intro subrelI, elim release_acquire_relaxed_swIE)
   (auto intro!: sw_aswI sw_lockI)

lemma monotonicity_release_acquire_relaxed_sw2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  release_acquire_relaxed_synchronizes_with_set_alt pre (incWitRestrict wit actions)
           \<subseteq> release_acquire_relaxed_synchronizes_with_set_alt pre wit"
using monotonicity_sw_rel_acq_rs2[OF downclosed]
by (intro subrelI, elim release_acquire_relaxed_swIE)
   (auto intro!: sw_aswI sw_lockI)

lemma monotonicity_release_acquire_relaxed_hb:
  assumes downclosed_mo: "downclosed actions (mo wit)"
  shows   "  release_acquire_relaxed_hb (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> release_acquire_relaxed_hb pre wit"
unfolding release_acquire_relaxed_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_relaxed_sw[OF downclosed_mo]]
by auto

lemma monotonicity_release_acquire_relaxed_hb2:
  assumes downclosed_mo: "downclosed actions (mo wit)"
  shows   "  release_acquire_relaxed_hb pre (incWitRestrict wit actions)
           \<subseteq> release_acquire_relaxed_hb pre wit"
unfolding release_acquire_relaxed_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_relaxed_sw2[OF downclosed_mo]]
by auto

(* Monotonicity hb in the rel-acq-rlx-fenced fragment *)

lemma monotonicity_hypothetical_release_sequence:
  assumes "downclosed actions (mo wit)"
          "(a, b) \<in> hypothetical_release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> hypothetical_release_sequence_set_alt pre wit"
using assms
unfolding hypothetical_release_sequence_set_alt_def 
          hypothetical_release_sequence_set_def
          downclosed_def
by auto

lemma monotonicity_hypothetical_release_sequence2:
  assumes "downclosed actions (mo wit)"
          "(a, b) \<in> hypothetical_release_sequence_set_alt pre (incWitRestrict wit actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> hypothetical_release_sequence_set_alt pre wit"
using assms
unfolding hypothetical_release_sequence_set_alt_def 
          hypothetical_release_sequence_set_def
          downclosed_def
by auto

lemma monotonicity_sw_fence_sb_hrs_rf_sb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_sb_hrs_rf_sb (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf_sb (preRestrict pre actions) (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit"
    proof (cases rule: sw_fence_sb_hrs_rf_sbIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y z)
      hence "y \<in> actions" by auto 
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> z \<in> actions0 pre
            \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, z) \<in> rf wit \<and> (z, b) \<in> sb pre"
        using fence by auto 
    qed
qed

lemma monotonicity_sw_fence_sb_hrs_rf_sb2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_sb_hrs_rf_sb pre (incWitRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit"
    proof (cases rule: sw_fence_sb_hrs_rf_sbIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y z)
      hence "y \<in> actions" by auto 
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence2
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> z \<in> actions0 pre
            \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, z) \<in> rf wit \<and> (z, b) \<in> sb pre"
        using fence by auto 
    qed
qed

lemma monotonicity_sw_fence_sb_hrs_rf:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_sb_hrs_rf (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf (preRestrict pre actions) (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf pre wit"
    proof (cases rule: sw_fence_sb_hrs_rfIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y)
      hence "y \<in> actions" by auto 
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, b) \<in> rf wit"
        using fence by auto 
    qed
qed

lemma monotonicity_sw_fence_sb_hrs_rf2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_sb_hrs_rf pre (incWitRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf pre (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf pre wit"
    proof (cases rule: sw_fence_sb_hrs_rfIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y)
      hence "y \<in> actions" by auto 
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence2
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, b) \<in> rf wit"
        using fence by auto 
    qed
qed

lemma monotonicity_sw_fence_rs_rf_sb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_rs_rf_sb (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> sw_fence_rs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_rs_rf_sb (preRestrict pre actions) (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_rs_rf_sb pre wit"
    proof (cases rule: sw_fence_rs_rf_sbIE)
      let ?rs  = "release_sequence_set_alt pre wit"
      case (fence x y)
      hence "y \<in> actions" by auto
      hence "(a, x) \<in> ?rs"
        using monotonicity_release_sequence
        using downclosed fence
        by auto 
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre 
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> ?rs \<and> (x, y) \<in> (rf wit) \<and> (y, b) \<in> (sb pre)"
        using fence by auto 
    qed
qed

lemma monotonicity_sw_fence_rs_rf_sb2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_rs_rf_sb pre (incWitRestrict wit actions)
           \<subseteq> sw_fence_rs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_rs_rf_sb pre (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_rs_rf_sb pre wit"
    proof (cases rule: sw_fence_rs_rf_sbIE)
      let ?rs  = "release_sequence_set_alt pre wit"
      case (fence x y)
      hence "y \<in> actions" by auto
      hence "(a, x) \<in> ?rs"
        using monotonicity_release_sequence2
        using downclosed fence
        by auto 
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre 
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> ?rs \<and> (x, y) \<in> (rf wit) \<and> (y, b) \<in> (sb pre)"
        using fence by auto 
    qed
qed

lemma monotonicity_release_acquire_fenced_sw: 
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> release_acquire_fenced_synchronizes_with_set_alt pre wit"
using monotonicity_sw_fence_sb_hrs_rf_sb[OF downclosed]
using monotonicity_sw_fence_sb_hrs_rf[OF downclosed]
using monotonicity_sw_fence_rs_rf_sb[OF downclosed]
using monotonicity_sw_rel_acq_rs[OF downclosed]
apply (intro subrelI, elim release_acquire_fenced_swIE)
by (auto 8 2 intro!: sw_aswI sw_lockI)

lemma monotonicity_release_acquire_fenced_sw2: 
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions)
           \<subseteq> release_acquire_fenced_synchronizes_with_set_alt pre wit"
using monotonicity_sw_fence_sb_hrs_rf_sb2[OF downclosed]
using monotonicity_sw_fence_sb_hrs_rf2[OF downclosed]
using monotonicity_sw_fence_rs_rf_sb2[OF downclosed]
using monotonicity_sw_rel_acq_rs2[OF downclosed]
apply (intro subrelI, elim release_acquire_fenced_swIE)
by (auto 8 2 intro!: sw_aswI sw_lockI)

lemma monotonicity_release_acquire_fenced_hb:
  assumes "downclosed actions (mo wit)"
  shows   "  release_acquire_fenced_hb (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> release_acquire_fenced_hb pre wit"
unfolding release_acquire_fenced_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_fenced_sw[OF assms]]
by auto

lemma monotonicity_release_acquire_fenced_hb2:
  assumes "downclosed actions (mo wit)"
  shows   "  release_acquire_fenced_hb pre (incWitRestrict wit actions)
           \<subseteq> release_acquire_fenced_hb pre wit"
unfolding release_acquire_fenced_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_fenced_sw2[OF assms]]
by auto

(* Monotonicity hb in the with_consume fragment *)

lemma monotonicity_with_consume_cad:
  shows "with_consume_cad_set_alt (preRestrict pre actions) (incWitRestrict wit actions) \<subseteq> 
         with_consume_cad_set_alt pre wit"
unfolding with_consume_cad_set_alt_def
          with_consume_cad_set_def
by (intro trancl_mono2) auto

lemma monotonicity_with_consume_cad2:
  shows "with_consume_cad_set_alt pre (incWitRestrict wit actions) \<subseteq> 
         with_consume_cad_set_alt pre wit"
unfolding with_consume_cad_set_alt_def
          with_consume_cad_set_def
by (intro trancl_mono2) auto

lemma monotonicity_with_consume_dob_set:
  assumes downclosed: "downclosed actions (mo wit)"
  shows "  with_consume_dob_set_alt (preRestrict pre actions) (incWitRestrict wit actions)
         \<subseteq> with_consume_dob_set_alt pre wit"
proof (intro subrelI)
  let ?rs   = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  let ?cad  = "with_consume_cad_set_alt pre wit"
  let ?cad2 = "with_consume_cad_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  fix a b
  assume in_dob: "(a, b) \<in> with_consume_dob_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  obtain ba e where ba_e: "ba \<in> actions0 pre \<and> 
                           is_consume ba \<and> 
                           e \<in> actions0 pre \<and> 
                           (a, e) \<in> ?rs2 \<and> 
                           (e, ba) \<in> relRestrict (rf wit) actions \<and> 
                           ((ba, b) \<in> ?cad2 \<or> ba = b)"
    using in_dob
    unfolding with_consume_dob_set_alt_def
              with_consume_dob_set_def
    by (auto simp add: dependency_ordered_before_def)
  hence "e \<in> actions" unfolding relRestrict_def by auto
  hence rs: "(a, e) \<in> ?rs"
    using ba_e monotonicity_release_sequence[OF downclosed]
    by fast
  have cad2: "(ba, b) \<in> ?cad \<or> ba = b" 
    using ba_e monotonicity_with_consume_cad by auto
  show "(a, b) \<in> with_consume_dob_set_alt pre wit"
    using in_dob
    unfolding with_consume_dob_set_alt_def
              with_consume_dob_set_def
    using ba_e rs cad2 
    by (auto simp add: dependency_ordered_before_def)
qed

lemma monotonicity_with_consume_dob_set2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows "  with_consume_dob_set_alt pre(incWitRestrict wit actions)
         \<subseteq> with_consume_dob_set_alt pre wit"
proof (intro subrelI)
  let ?rs   = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt pre (incWitRestrict wit actions)"
  let ?cad  = "with_consume_cad_set_alt pre wit"
  let ?cad2 = "with_consume_cad_set_alt pre (incWitRestrict wit actions)"
  fix a b
  assume in_dob: "(a, b) \<in> with_consume_dob_set_alt pre (incWitRestrict wit actions)"
  obtain ba e where ba_e: "ba \<in> actions0 pre \<and> 
                           is_consume ba \<and> 
                           e \<in> actions0 pre \<and> 
                           (a, e) \<in> ?rs2 \<and> 
                           (e, ba) \<in> relRestrict (rf wit) actions \<and> 
                           ((ba, b) \<in> ?cad2 \<or> ba = b)"
    using in_dob
    unfolding with_consume_dob_set_alt_def
              with_consume_dob_set_def
    by (auto simp add: dependency_ordered_before_def)
  hence "e \<in> actions" unfolding relRestrict_def by auto
  hence rs: "(a, e) \<in> ?rs"
    using ba_e monotonicity_release_sequence2[OF downclosed]
    by fast
  have cad2: "(ba, b) \<in> ?cad \<or> ba = b" 
    using ba_e monotonicity_with_consume_cad2 by auto
  show "(a, b) \<in> with_consume_dob_set_alt pre wit"
    using in_dob
    unfolding with_consume_dob_set_alt_def
              with_consume_dob_set_def
    using ba_e rs cad2 
    by (auto simp add: dependency_ordered_before_def)
qed

lemma relComp_member:
  shows "(a, c) \<in> relcomp r r' = (\<exists>b. (a, b) \<in> r \<and> (b, c) \<in> r')"
by auto

lemma monotonicity_ithb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  inter_thread_happens_before_alt (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> inter_thread_happens_before_alt pre wit"
unfolding inter_thread_happens_before_alt_def
          inter_thread_happens_before_step_def
          inter_thread_happens_before_r_def
          Let_def
using monotonicity_release_acquire_fenced_sw[OF downclosed]
using monotonicity_with_consume_dob_set[OF downclosed]
by (auto intro!: trancl_mono2 Un_mono relcomp_mono del: subsetI)

lemma monotonicity_ithb2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  inter_thread_happens_before_alt pre (incWitRestrict wit actions)
           \<subseteq> inter_thread_happens_before_alt pre wit"
unfolding inter_thread_happens_before_alt_def
          inter_thread_happens_before_step_def
          inter_thread_happens_before_r_def
          Let_def
using monotonicity_release_acquire_fenced_sw2[OF downclosed]
using monotonicity_with_consume_dob_set2[OF downclosed]
by (auto intro!: trancl_mono2 Un_mono relcomp_mono del: subsetI)

lemma monotonicity_with_consume_hb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  with_consume_hb (preRestrict pre actions) (incWitRestrict wit actions)
           \<subseteq> with_consume_hb pre wit"
unfolding with_consume_hb_def happens_before_def
using monotonicity_ithb[OF downclosed]
by auto

lemma monotonicity_with_consume_hb2:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  with_consume_hb pre (incWitRestrict wit actions)
           \<subseteq> with_consume_hb pre wit"
unfolding with_consume_hb_def happens_before_def
using monotonicity_ithb2[OF downclosed]
by auto

subsubsection {* Prefixes are final *}

(* Prefixes are final in the rel-acq-rlx fragment *)

definition prefixes_are_final  :: "(action)set \<Rightarrow>(action*action)set \<Rightarrow>(action*action)set \<Rightarrow> bool "  where 
  "prefixes_are_final s r r' = (\<forall> (a, b) \<in> r. b \<in> s \<longrightarrow> (a, b) \<in> r')"

definition selective_prefixes_are_final  :: "(action \<Rightarrow> bool)\<Rightarrow>(action)set \<Rightarrow>(action*action)set \<Rightarrow>(action*action)set \<Rightarrow> bool "  where 
  "selective_prefixes_are_final f s r r' = (\<forall> (a, b) \<in> r. (b \<in> s \<and> f b) \<longrightarrow> (a, b) \<in> r')"

definition sbMinus  :: " pre_execution \<Rightarrow>(action*action)set \<Rightarrow>(action*action)set "  where 
  "sbMinus pre1 rel = (set_filter (\<lambda> (a, b). (is_na_or_non_write pre1 b)) rel)"
 
definition selective_downclosed  :: "(action \<Rightarrow> bool)\<Rightarrow>(action)set \<Rightarrow>(action*action)set \<Rightarrow> bool "  where 
  "selective_downclosed f s r = (\<forall> (a, b) \<in> r. (b \<in> s \<and> f b) \<longrightarrow> (a \<in> s))"

definition hbCalcIsFinalForPrefixes  :: "(pre_execution \<Rightarrow> execution_witness \<Rightarrow>(action*action)set)\<Rightarrow> bool "  where 
  "hbCalcIsFinalForPrefixes hbCalc = (\<forall> pre0. \<forall> wit. \<forall> actions1.  
            downclosed actions1 (rf wit)
          \<and> downclosed actions1 (mo wit)
          \<and> downclosed actions1 (sbMinus pre0 (sb pre0))
          \<and> trans (sb pre0)
          \<and> dd pre0 \<subseteq> sb pre0
          \<and> selective_downclosed (is_na_or_non_write pre0) actions1 (hbCalc pre0 wit)
     \<longrightarrow>  selective_prefixes_are_final (is_na_or_non_write pre0)
                                   actions1
                                   (hbCalc pre0 wit) 
                                   (hbCalc (preRestrict pre0 actions1) (incWitRestrict wit actions1)))"

definition hbCalcIsMonotonic  :: "(pre_execution \<Rightarrow> execution_witness \<Rightarrow>(action*action)set)\<Rightarrow> bool "  where 
  "hbCalcIsMonotonic hbCalc = (\<forall> pre0. \<forall> wit. \<forall> actions1.
          downclosed actions1 (mo wit) 
     \<longrightarrow>  hbCalc (preRestrict pre0 actions1) (incWitRestrict wit actions1) \<subseteq> hbCalc pre0 wit)"

lemma final_release_sequence:
  assumes  "downclosed actions (mo wit)"
      and  "b \<in> actions"
      and  "(a, b) \<in> release_sequence_set_alt pre wit"
  shows    "  a \<in> actions
            \<and> (a, b) \<in> release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
using assms
unfolding release_sequence_set_alt_def 
          release_sequence_set_def 
          downclosed_def
by auto

lemma final_sw_asw:
  assumes "(a, b) \<in> sw_asw pre"
      and "a \<in> actions" 
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_asw (preRestrict pre actions)"
using assms
unfolding sw_asw_def
by auto

lemma final_sw_lock:
  assumes "(a, b) \<in> sw_lock pre wit"
      and "a \<in> actions" 
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_lock (preRestrict pre actions) (incWitRestrict wit actions)"
using assms
unfolding sw_lock_def
by auto

lemma final_sw_rel_acq_rs:
  assumes "(a, b) \<in> sw_rel_acq_rs pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_rel_acq_rs (preRestrict pre actions) (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_rel_acq_rsIE, simp)
  case (rel_acq_rs c)
  hence "c \<in> actions" 
    using downclosed_rf `b \<in> actions` by (auto elim: downclosedE)
  let ?rs   = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  have "a \<in> actions \<and> (a, c) \<in> ?rs2"
    using final_release_sequence[OF downclosed_mo `c \<in> actions`]
    using rel_acq_rs
    by auto
  (* I have no idea why the simplifier did not get rid of the double occurrences. *)
  thus "a \<in> actions \<and> b \<in> actions \<and> c \<in> actions \<and> (a, c) \<in> ?rs2 \<and> c \<in> actions \<and> b \<in> actions"
    using rel_acq_rs `b \<in> actions` `c \<in> actions` by auto
qed

lemma final_release_acquire_relaxed_sw:
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "a \<in> actions" 
      and "b \<in> actions"
      and sw1: "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt pre wit"
  shows   "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
using sw1
apply (cases rule: release_acquire_relaxed_swIE)
using final_sw_asw[OF _ `a \<in> actions` `b \<in> actions`]
      final_sw_lock[OF _ `a \<in> actions` `b \<in> actions`]
      final_sw_rel_acq_rs[OF _ downclosed_rf downclosed_mo `b \<in> actions`]
by metis+

lemma final_no_consume_hb_aux:
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and                "b \<in> actions"
      and downclosed_hb: "\<And>c. (c, b) \<in> (no_consume_hb p_sb sw) \<Longrightarrow> c \<in> actions"
      and in_hb:         "(a, b) \<in> no_consume_hb p_sb sw"
      and final_sw:      "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> sw\<rbrakk> \<Longrightarrow> (x, y) \<in> sw'"
  shows   "(a, b) \<in> no_consume_hb (relRestrict p_sb actions) sw'"
proof -
  let ?hb = "no_consume_hb p_sb sw"
  let ?p_sb' = "relRestrict p_sb actions"
  have "(a, b) \<in> (p_sb \<union> sw)\<^sup>+" using in_hb unfolding no_consume_hb_def .
  hence "(a, b) \<in> (?p_sb' \<union> sw')\<^sup>+"    
    proof (rule converse_trancl_induct)
      fix y
      assume inSbSw: "(y, b) \<in> p_sb \<union> sw"
      hence "(y, b) \<in> ?hb" unfolding no_consume_hb_def by auto
      hence "y \<in> actions" using downclosed_hb by simp
      hence "(y, b) \<in> ?p_sb' \<union> sw'"
        using final_sw `b \<in> actions` inSbSw 
        by auto
      thus "(y, b) \<in> (?p_sb' \<union> sw')\<^sup>+" by auto
    next
      fix y z
      assume inSbSw:        "(y, z) \<in> p_sb \<union> sw"
         and inSbSwTrancl:  "(z, b) \<in> (p_sb \<union> sw)\<^sup>+"
         and inSbSw2Trancl: "(z, b) \<in> (?p_sb' \<union> sw')\<^sup>+"
      hence "(z, b) \<in> ?hb" unfolding no_consume_hb_def by auto
      hence "z \<in> actions" using downclosed_hb by simp
      have "(y, b) \<in> ?hb"
        unfolding no_consume_hb_def
        using inSbSw inSbSwTrancl
        by (rule trancl_into_trancl2)
      hence "y \<in> actions" using downclosed_hb by simp
      hence "(y, z) \<in> ?p_sb' \<union> sw'"
        using final_sw inSbSw `z \<in> actions`
        by auto     
      thus "(y, b) \<in> (?p_sb' \<union> sw')\<^sup>+" 
        using inSbSw2Trancl
        by (rule trancl_into_trancl2)
    qed
  thus "(a, b) \<in> no_consume_hb ?p_sb' sw'" 
    unfolding no_consume_hb_def
    by simp
qed

lemma final_no_consume_hb:
  fixes pre wit sw sw' actions
  defines "hb  \<equiv> no_consume_hb (sb pre) sw"
      and "hb' \<equiv> no_consume_hb (relRestrict (sb pre) actions) sw'"
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_hb:  "selective_downclosed f actions hb"
      and final_sw:      "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> sw\<rbrakk> \<Longrightarrow> (x, y) \<in> sw'"
  shows   "selective_prefixes_are_final f actions hb hb'"
unfolding selective_prefixes_are_final_def
proof auto
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
  shows "hbCalcIsFinalForPrefixes release_acquire_relaxed_hb"
unfolding hbCalcIsFinalForPrefixes_def
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions
  let ?sw  = "release_acquire_relaxed_synchronizes_with_set_alt pre wit"
  let ?sw2 = "release_acquire_relaxed_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  let ?f   = "is_na_or_non_write pre"
  assume downclosed_rf: "downclosed actions (rf wit)" 
     and downclosed_mo: "downclosed actions (mo wit)"
     and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
     and downclosed_hb: "selective_downclosed ?f actions (release_acquire_relaxed_hb pre wit)"
  have final_sw: "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> ?sw\<rbrakk> \<Longrightarrow> (x, y) \<in> ?sw2"
    using final_release_acquire_relaxed_sw[OF downclosed_rf downclosed_mo]
    by metis 
  show "selective_prefixes_are_final (is_na_or_non_write pre) 
                                     actions
                                     (release_acquire_relaxed_hb pre wit) 
                                     (release_acquire_relaxed_hb (preRestrict pre actions) (incWitRestrict wit actions))"
    using final_no_consume_hb[OF downclosed_rf downclosed_mo _ final_sw] downclosed_hb
    unfolding release_acquire_relaxed_hb_def
    by auto
qed

(* Prefixes are final in the rel-acq-rlx-fence fragment *)

lemma final_hypothetical_release_sequence:
  assumes  "downclosed actions (mo wit)"
      and  "b \<in> actions"
      and  "(a, b) \<in> hypothetical_release_sequence_set_alt pre wit"
  shows   "  a \<in> actions 
           \<and> (a, b) \<in> hypothetical_release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
using assms
unfolding hypothetical_release_sequence_set_alt_def 
          hypothetical_release_sequence_set_def 
          downclosed_def
by auto

lemma final_sw_fence_sb_hrs_rf_sb:
  assumes "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
      and "a \<in> actions"
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf_sb (preRestrict pre actions) (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_sb_hrs_rf_sbIE, simp)
  let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
  let ?hrs2  = "hypothetical_release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  case (fence x y z)
  have "is_na_or_non_write pre b" 
    using `is_fence b` unfolding is_na_or_non_write_def by (cases b) auto
  hence "(z, b) \<in> sbMinus pre (sb pre)" 
    using `(z, b) \<in> sb pre` unfolding sbMinus_def by auto
  hence "z \<in> actions" 
    using downclosed_sb `b \<in> actions` unfolding downclosed_def by metis  
  hence "y \<in> actions"
    using downclosed_rf `(y, z) \<in> rf wit` unfolding downclosed_def by metis  
  hence "x \<in> actions \<and> (x, y) \<in> ?hrs2"
    using final_hypothetical_release_sequence `(x, y) \<in> ?hrs` downclosed_mo
    by metis
  (* No idea why the simplifier left the double conjuncts. *)
  thus "  a \<in> actions \<and> b \<in> actions \<and> x \<in> actions \<and> y \<in> actions \<and> z \<in> actions \<and> a \<in> actions
        \<and> x \<in> actions \<and> (x, y) \<in> ?hrs2 \<and> y \<in> actions \<and> z \<in> actions \<and> b \<in> actions"
    using fence `z \<in> actions` `y \<in> actions` `a \<in> actions` `b \<in> actions` by auto
qed

lemma final_sw_fence_sb_hrs_rf:
  assumes "(a, b) \<in> sw_fence_sb_hrs_rf pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "a \<in> actions"
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf (preRestrict pre actions) (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_sb_hrs_rfIE, simp)
  let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
  let ?hrs2  = "hypothetical_release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  case (fence x y)
  have "y \<in> actions" 
    using downclosed_rf `b \<in> actions` `(y, b) \<in> rf wit` 
    unfolding downclosed_def by metis
  hence "x \<in> actions \<and> (x, y) \<in> ?hrs2" 
    using final_hypothetical_release_sequence `(x, y) \<in> ?hrs` downclosed_mo
    by metis
  thus "  a \<in> actions \<and> b \<in> actions \<and> x \<in> actions \<and> y \<in> actions \<and> a \<in> actions \<and> x \<in> actions 
        \<and> (x, y) \<in> ?hrs2 \<and> y \<in> actions \<and> b \<in> actions"
    using fence `y \<in> actions` `a \<in> actions` `b \<in> actions` by auto
qed

lemma final_sw_fence_rs_rf_sb:
  assumes "(a, b) \<in> sw_fence_rs_rf_sb pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
      and b: "b \<in> actions"
  shows   "(a, b) \<in> sw_fence_rs_rf_sb (preRestrict pre actions) (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_rs_rf_sbIE, simp)
  let ?rs  = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  case (fence x y)
  have "is_na_or_non_write pre b" 
    using `is_fence b` unfolding is_na_or_non_write_def by (cases b) auto
  hence "(y, b) \<in> sbMinus pre (sb pre)" 
    using `(y, b) \<in> sb pre` unfolding sbMinus_def by auto
  hence "y \<in> actions" 
    using downclosed_sb b unfolding downclosed_def by metis
  hence "x \<in> actions"
    using downclosed_rf `(x, y) \<in> rf wit` unfolding downclosed_def by metis
  hence "a \<in> actions \<and> (a, x) \<in> ?rs2" 
    using final_release_sequence `(a, x) \<in> ?rs` downclosed_mo
    by metis
  thus "  a \<in> actions \<and> b \<in> actions \<and> x \<in> actions \<and> y \<in> actions
        \<and> (a, x) \<in> ?rs2 \<and> x \<in> actions \<and> y \<in> actions \<and> b \<in> actions"
    using fence `x \<in> actions` `y \<in> actions` `b \<in> actions` by auto
qed

lemma final_release_acquire_fenced_sw:
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
      and "a \<in> actions"
      and "b \<in> actions"
      and sw1: "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
  shows   "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
using sw1
apply (cases rule: release_acquire_fenced_swIE)
using final_sw_asw
      final_sw_lock
      final_sw_rel_acq_rs
      final_sw_fence_sb_hrs_rf_sb
      final_sw_fence_sb_hrs_rf
      final_sw_fence_rs_rf_sb
      assms
by metis+

lemma final_release_acquire_fenced_hb:
  shows "hbCalcIsFinalForPrefixes release_acquire_fenced_hb"
unfolding hbCalcIsFinalForPrefixes_def 
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions
  let ?sw   = "release_acquire_fenced_synchronizes_with_set_alt pre wit"
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  let ?f    = "is_na_or_non_write pre"
  assume downclosed_rf: "downclosed actions (rf wit)" 
     and downclosed_mo: "downclosed actions (mo wit)"
     and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
     and downclosed_hb: "selective_downclosed ?f actions (release_acquire_fenced_hb pre wit)"
  have final_sw: "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> ?sw\<rbrakk> \<Longrightarrow> (x, y) \<in> ?sw2"
    using final_release_acquire_fenced_sw[OF downclosed_rf downclosed_mo downclosed_sb]
    by metis 
  show "selective_prefixes_are_final (is_na_or_non_write pre) 
                                     actions 
                                     (release_acquire_fenced_hb pre wit) 
                                     (release_acquire_fenced_hb (preRestrict pre actions) (incWitRestrict wit actions))"
    using final_no_consume_hb[OF downclosed_rf downclosed_mo] downclosed_hb final_sw
    unfolding release_acquire_fenced_hb_def
    by auto
qed

(* Prefixes are final in the with-consume fragment *)

lemma final_cad:
  assumes downclosed_sb: "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and trans_sb:      "trans (sb pre)"
      and dd_in_sb:      "dd pre \<subseteq> sb pre"
      and b:             "b \<in> actions" 
      and cad:           "(a, b) \<in> with_consume_cad_set_alt pre wit"
  shows   "a \<in> actions \<and> (a, b) \<in> with_consume_cad_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
proof -
  have downclosed_cad: "\<And>c. (c, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+ \<Longrightarrow> c \<in> actions"
    proof -
      fix c
      assume c: "(c, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+"
      have "rf wit \<inter> sb pre \<union> dd pre \<subseteq> sb pre"
        using `dd pre \<subseteq> sb pre` by auto
      hence "(rf wit \<inter> sb pre \<union> dd pre)\<^sup>+ \<subseteq> sb pre"
        using trancl_mono3[OF `trans (sb pre)`] by auto
      hence "(c, b) \<in> sb pre" using c by auto
      thus "c \<in> actions"
        using downclosed_sb b unfolding downclosed_def by auto
    qed
  hence "a \<in> actions" 
    using cad unfolding with_consume_cad_set_alt_def with_consume_cad_set_def by auto
  have "(a, b) \<in> with_consume_cad_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
    using cad unfolding with_consume_cad_set_alt_def with_consume_cad_set_def
    proof (rule converse_trancl_induct)
      fix y
      assume y: "(y, b) \<in> rf wit \<inter> sb pre \<union> dd pre"
      hence "(y, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+" by fast
      hence "y \<in> actions" using downclosed_cad by fast
      hence "(y, b) \<in> relRestrict (rf wit) actions \<inter> relRestrict (sb pre) actions \<union> relRestrict (dd pre) actions"
        using y b by auto
      thus "(y, b) \<in> (rf (incWitRestrict wit actions) \<inter> sb (preRestrict pre actions) \<union> dd (preRestrict pre actions))\<^sup>+" 
        by auto
    next
      fix y z
      assume y:  "(y, z) \<in> rf wit \<inter> sb pre \<union> dd pre"
         and z:  "(z, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+"
         and ih: "(z, b) \<in> (rf (incWitRestrict wit actions) \<inter> sb (preRestrict pre actions) \<union> dd (preRestrict pre actions))\<^sup>+"
      have "z \<in> actions" using downclosed_cad[OF z] .
      have "(y, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+" 
        using y z by (rule trancl_into_trancl2)
      hence "y \<in> actions" using downclosed_cad by fast
      have "(y, z) \<in> relRestrict (rf wit) actions \<inter> relRestrict (sb pre) actions \<union> relRestrict (dd pre) actions"
        using y `y \<in> actions` `z \<in> actions` by auto
      thus "(y, b) \<in> (rf (incWitRestrict wit actions) \<inter> sb (preRestrict pre actions) \<union> dd (preRestrict pre actions))\<^sup>+"
        using ih by (auto simp add: trancl_into_trancl2)
    qed
  thus ?thesis using `a \<in> actions` by simp
qed

lemma final_dob:
  assumes downclosed_sb: "\<And>a. (a, d) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and trans_sb:      "trans (sb pre)"
      and dd_in_sb:      "dd pre \<subseteq> sb pre"
      and d:             "d \<in> actions" 
      and dob_set:       "(a, d) \<in> with_consume_dob_set_alt pre wit"
  shows   "(a, d) \<in> with_consume_dob_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
proof -
  obtain c b where a:  "a \<in> actions0 pre" "is_release a"
               and rs: "(a, b) \<in> release_sequence_set_alt pre wit"
               and b:  "b \<in> actions0 pre"
               and rf: "(b, c) \<in> rf wit"
               and c:  "c \<in> actions0 pre" "is_consume c"
               and cad_or_eq: "(c, d) \<in> with_consume_cad_set_alt pre wit \<or> c = d"
               and d2: "d \<in> actions0 pre"
    using dob_set
    unfolding with_consume_dob_set_alt_def 
              with_consume_dob_set_def
    by (auto simp add: dependency_ordered_before_def)
  have cad2: "  (    (c, d) \<in> with_consume_cad_set_alt (preRestrict pre actions) (incWitRestrict wit actions) 
                  \<or> (c = d))
              \<and> c \<in> actions"
    using cad_or_eq
    proof
      assume "c = d"
      thus ?thesis using `d \<in> actions` by simp
    next
      assume "(c, d) \<in> with_consume_cad_set_alt pre wit"
      thus ?thesis
        using final_cad[OF downclosed_sb trans_sb dd_in_sb d]
        by fast
    qed
  hence "b \<in> actions"
    using rf downclosed_rf unfolding downclosed_def by fast
  hence rf2: "(b, c) \<in> relRestrict (rf wit) actions" 
    using cad2 rf by auto
  have rs2: "  a \<in> actions 
             \<and> (a, b) \<in> release_sequence_set_alt (preRestrict pre actions) (incWitRestrict wit actions)" 
    using rs final_release_sequence[OF downclosed_mo `b \<in> actions`]
    by fast
  thus ?thesis
    using a c d d2 b rs2 rf2 cad2
    unfolding with_consume_dob_set_alt_def with_consume_dob_set_def
    by (auto simp add: dependency_ordered_before_def)
qed

lemma UnMember_mono:
  assumes "x \<in> s \<union> r"
      and "x \<in> s \<Longrightarrow> x \<in> s'"
      and "x \<in> r \<Longrightarrow> x \<in> r'"
  shows   "x \<in> s' \<union> r'"
using assms
by auto

lemma composeMember_mono:
  assumes "(a, c) \<in> s O r"
      and "\<And>b. (a, b) \<in> s \<Longrightarrow> (b, c) \<in> r \<Longrightarrow> (a, b) \<in> s' \<and> (b, c) \<in> r'"
  shows   "(a, c) \<in> s' O r'"
using assms
by auto

lemma final_ithb_r:
  assumes downclosed_sb:  "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and downclosed_sb2: "downclosed actions (sbMinus pre (sb pre))"
      and downclosed_rf:  "downclosed actions (rf wit)"
      and downclosed_mo:  "downclosed actions (mo wit)"
      and trans_sb:       "trans (sb pre)"
      and dd_in_sb:       "dd pre \<subseteq> sb pre"
      and a:              "a \<in> actions" 
      and b:              "b \<in> actions" 
      and ithb:           "(a, b) \<in> inter_thread_happens_before_r pre wit"
  shows   "(a, b) \<in> inter_thread_happens_before_r (preRestrict pre actions) (incWitRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_r_def
apply (elim UnMember_mono)
defer defer
apply (simp, elim composeMember_mono)
proof simp
  assume "(a, b) \<in> with_consume_dob_set_alt pre wit"
  thus "(a, b) \<in> with_consume_dob_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
    using final_dob[OF downclosed_sb downclosed_rf downclosed_mo trans_sb dd_in_sb b]
    by auto
next
  assume "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
  thus "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
    using final_release_acquire_fenced_sw[OF downclosed_rf downclosed_mo downclosed_sb2 a b]
    by metis
next
  fix y
  assume sw: "(a, y) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
     and sb: "(y, b) \<in> sb pre"
  have "y \<in> actions"
    using sb downclosed_sb by auto
  thus "(a, y) \<in> release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)
         \<and> y \<in> actions \<and> b \<in> actions"
    using sw sb `b \<in> actions`
    using final_release_acquire_fenced_sw[OF downclosed_rf downclosed_mo downclosed_sb2 a]
    by metis
qed

lemma final_ithb_step:
  assumes downclosed_sb:  "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and downclosed_sb2: "downclosed actions (sbMinus pre (sb pre))"
      and downclosed_rf:  "downclosed actions (rf wit)"
      and downclosed_mo:  "downclosed actions (mo wit)"
      and downclosed_ithb: "\<And>x.     (x, b) \<in> inter_thread_happens_before_alt pre wit
                                 \<Longrightarrow> x \<in> actions"
      and trans_sb:       "trans (sb pre)"
      and dd_in_sb:       "dd pre \<subseteq> sb pre"
      and a:              "a \<in> actions" 
      and b:              "b \<in> actions" 
      and ithb:           "(a, b) \<in> inter_thread_happens_before_step pre wit"
  shows   "(a, b) \<in> inter_thread_happens_before_step (preRestrict pre actions) (incWitRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_step_def
apply (elim UnMember_mono)
defer 
apply (simp, elim composeMember_mono)
proof simp
  assume "(a, b) \<in> inter_thread_happens_before_r pre wit"
  thus "(a, b) \<in> inter_thread_happens_before_r (preRestrict pre actions) (incWitRestrict wit actions)"
    using final_ithb_r[OF downclosed_sb downclosed_sb2 downclosed_rf downclosed_mo
                          trans_sb dd_in_sb a b]
    by metis
next
  fix y
  assume sb: "(a, y) \<in> sb pre"
     and r:  "(y, b) \<in> inter_thread_happens_before_r pre wit"
  hence "(y, b) \<in> inter_thread_happens_before_alt pre wit"
    unfolding inter_thread_happens_before_step_def
              inter_thread_happens_before_alt_def 
    by auto
  hence "y \<in> actions"
    using downclosed_ithb by auto
  thus "  a \<in> actions \<and> y \<in> actions
        \<and> (y, b) \<in> inter_thread_happens_before_r (preRestrict pre actions) (incWitRestrict wit actions)"
    using final_ithb_r[OF downclosed_sb downclosed_sb2 downclosed_rf downclosed_mo
                          trans_sb dd_in_sb]
    using r a b sb
    by metis
qed

lemma final_ithb:
  assumes downclosed_sb:  "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and downclosed_sb2: "downclosed actions (sbMinus pre (sb pre))"
      and downclosed_rf:  "downclosed actions (rf wit)"
      and downclosed_mo:  "downclosed actions (mo wit)"
      and downclosed_ithb: "\<And>x.     (x, b) \<in> inter_thread_happens_before_alt pre wit
                                 \<Longrightarrow> x \<in> actions"
      and trans_sb:       "trans (sb pre)"
      and dd_in_sb:       "dd pre \<subseteq> sb pre"
      and b:              "b \<in> actions" 
      and ithb:           "(a, b) \<in> inter_thread_happens_before_alt pre wit"
  shows   "(a, b) \<in> inter_thread_happens_before_alt (preRestrict pre actions) (incWitRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_alt_def
proof (induct rule: converse_trancl_induct)
  fix y
  assume step: "(y, b) \<in> inter_thread_happens_before_step pre wit"
  hence "y \<in> actions"
    using downclosed_ithb
    unfolding inter_thread_happens_before_alt_def
    by auto
  thus "(y, b) \<in> (inter_thread_happens_before_step (preRestrict pre actions) (incWitRestrict wit actions))\<^sup>+"
    using final_ithb_step[OF downclosed_sb downclosed_sb2 downclosed_rf 
                             downclosed_mo downclosed_ithb trans_sb dd_in_sb _ b step]
    by auto
next
  fix y z
  assume yz: "(y, z) \<in> inter_thread_happens_before_step pre wit"
     and zb: "(z, b) \<in> (inter_thread_happens_before_step pre wit)\<^sup>+"
     and ih: "(z, b) \<in> (inter_thread_happens_before_step (preRestrict pre actions) (incWitRestrict wit actions))\<^sup>+"
  have z: "z \<in> actions"
    using zb downclosed_ithb
    unfolding inter_thread_happens_before_alt_def
    by auto
  have "(y, b) \<in> (inter_thread_happens_before_step pre wit)\<^sup>+"
    using yz zb by auto
  hence y: "y \<in> actions"
    using downclosed_ithb
    unfolding inter_thread_happens_before_alt_def
    by auto
  have downclosed_sb1b: "\<And>x. (x, z) \<in> sb pre \<Longrightarrow> x \<in> actions"
    proof -
      fix x
      assume sb: "(x, z) \<in> sb pre"
      obtain w where zw: "(z, w) \<in> inter_thread_happens_before_step pre wit"
                 and wb: "(w, b) \<in> (inter_thread_happens_before_step pre wit)\<^sup>*"
        using zb tranclD[of z b] by auto
      have "(x, w) \<in> compose0 (sb pre) (inter_thread_happens_before_r pre wit)"
        using zw 
        unfolding inter_thread_happens_before_step_def
        proof
          assume "(z, w) \<in> inter_thread_happens_before_r pre wit"
          thus "(x, w) \<in> compose0 (sb pre) (inter_thread_happens_before_r pre wit)"
            using sb by auto
        next
          assume "(z, w) \<in> compose0 (sb pre) (inter_thread_happens_before_r pre wit)"
          then obtain v where zv: "(z, v) \<in> sb pre"
                          and vw: "(v, w) \<in> inter_thread_happens_before_r pre wit"
            by auto
          have "(x, v) \<in> sb pre"
            using sb zv trans_sb by (auto elim: transE)
          thus "(x, w) \<in> compose0 (sb pre) (inter_thread_happens_before_r pre wit)"
            using vw by auto
        qed
      hence "(x, w) \<in> inter_thread_happens_before_step pre wit"
        unfolding inter_thread_happens_before_step_def by auto
      hence "(x, b) \<in> inter_thread_happens_before_alt pre wit"
        using wb unfolding inter_thread_happens_before_alt_def by auto
      thus "x \<in> actions" using downclosed_ithb by auto
    qed
  have downclosed_ithb2: "\<And>x. (x, z) \<in> inter_thread_happens_before_alt pre wit \<Longrightarrow> x \<in> actions"
    proof -
      fix x
      assume "(x, z) \<in> inter_thread_happens_before_alt pre wit"
      hence "(x, b) \<in> inter_thread_happens_before_alt pre wit"
        using zb unfolding inter_thread_happens_before_alt_def by auto
      thus "x \<in> actions" using downclosed_ithb by auto
    qed
  hence "(y, z) \<in> (inter_thread_happens_before_step (preRestrict pre actions) (incWitRestrict wit actions))\<^sup>+"
    using final_ithb_step[OF downclosed_sb1b downclosed_sb2 downclosed_rf 
                             downclosed_mo downclosed_ithb2 trans_sb dd_in_sb y z yz]
    by auto
  thus "(y, b) \<in> (inter_thread_happens_before_step (preRestrict pre actions) (incWitRestrict wit actions))\<^sup>+"
    using ih by auto
qed

lemma final_with_consume_hb_aux:
  assumes downclosed_sb:  "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and downclosed_sb2: "downclosed actions (sbMinus pre (sb pre))"
      and downclosed_rf:  "downclosed actions (rf wit)"
      and downclosed_mo:  "downclosed actions (mo wit)"
      and downclosed_ithb: "\<And>x.     (x, b) \<in> inter_thread_happens_before_alt pre wit
                                 \<Longrightarrow> x \<in> actions"
      and trans_sb:      "trans (sb pre)"
      and dd_in_sb:      "dd pre \<subseteq> sb pre"
      and b:             "b \<in> actions" 
      and hb:            "(a, b) \<in> with_consume_hb pre wit"
  shows   "(a, b) \<in> with_consume_hb (preRestrict pre actions) (incWitRestrict wit actions)"
using hb
unfolding with_consume_hb_def happens_before_def
proof (rule UnMember_mono)
  assume "(a, b) \<in> sb pre"
  hence "a \<in> actions" using downclosed_sb by auto
  thus "(a, b) \<in> sb (preRestrict pre actions)"
    using `(a, b) \<in> sb pre` b by auto
next
  assume ithb: "(a, b) \<in> inter_thread_happens_before_alt pre wit"
  show "(a, b) \<in> inter_thread_happens_before_alt (preRestrict pre actions) (incWitRestrict wit actions)"
    using final_ithb[OF downclosed_sb downclosed_sb2 downclosed_rf downclosed_mo
                        downclosed_ithb trans_sb dd_in_sb b(1) ithb]
    by simp
qed

lemma final_with_consume_hb:
  shows   "hbCalcIsFinalForPrefixes with_consume_hb"
unfolding hbCalcIsFinalForPrefixes_def 
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions
  let ?sw   = "release_acquire_fenced_synchronizes_with_set_alt pre wit"
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set_alt (preRestrict pre actions) (incWitRestrict wit actions)"
  let ?f    = "is_na_or_non_write pre"
  assume downclosed_rf: "downclosed actions (rf wit)" 
     and downclosed_mo: "downclosed actions (mo wit)"
     and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
     and downclosed_hb: "selective_downclosed ?f actions (with_consume_hb pre wit)"
     and trans_sb:      "trans (sb pre)"
     and dd_in_sb:      "dd pre \<subseteq> sb pre"
  show "selective_prefixes_are_final (is_na_or_non_write pre) 
                                     actions 
                                     (with_consume_hb pre wit) 
                                     (with_consume_hb (preRestrict pre actions) (incWitRestrict wit actions))"
    unfolding selective_prefixes_are_final_def
    proof auto
      fix a b
      assume b:  "b \<in> actions" "is_na_or_non_write pre b"
         and ab: "(a, b) \<in> with_consume_hb pre wit"
      have downclosed_sb2:  "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
        using downclosed_hb b
        unfolding selective_downclosed_def 
                  with_consume_hb_def 
                  happens_before_def
        by auto
      have downclosed_ithb: "\<And>x. (x, b) \<in> inter_thread_happens_before_alt pre wit \<Longrightarrow> x \<in> actions" 
        using downclosed_hb b
        unfolding selective_downclosed_def 
                  with_consume_hb_def 
                  happens_before_def
        by auto
      show "(a, b) \<in> with_consume_hb (preRestrict pre actions) (incWitRestrict wit actions)"
        using final_with_consume_hb_aux[OF downclosed_sb2 downclosed_sb downclosed_rf
                                           downclosed_mo downclosed_ithb trans_sb
                                           dd_in_sb b(1) ab]
        by metis
    qed
qed

subsubsection {* Summary *}

(* The properties proven for the fragment used in the opsem *)

lemma hbRelOver:
  assumes "relOver (sb pre) (actions0 pre)"
  shows   "relOver (getHb pre wit) (actions0 pre)"
using relOver_with_consume_hb assms
by auto

lemma sbInHb:
  shows "sb pre \<subseteq> getHb pre wit"
using sbInHb_with_consume_hb
by auto

lemma loInHb:
  shows "hbCalcRespectsSyncingLocks getHb"
using loInHb_with_consume_hb 
by auto

lemma hbCalcIsMonotonic:
  shows "hbCalcIsMonotonic getHb"
using monotonicity_with_consume_hb 
unfolding hbCalcIsMonotonic_def
by auto

lemma hbCalcIsFinalForPrefixes:
  shows "hbCalcIsFinalForPrefixes getHb"
using final_with_consume_hb 
by auto

(* Corollaries for derived relations *)

lemma hbMinusIsMonotonic:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "hbMinusAlt pre (incWitRestrict wit actions) \<subseteq> hbMinusAlt pre wit"
using monotonicity_with_consume_hb2[OF downclosed]
unfolding getRelations_simp 
          hbMinusAlt_def
by auto

lemma opsemOrderIsMonotonic:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "incComAlt pre (incWitRestrict wit actions) \<subseteq> incComAlt pre wit"
proof -
  have "hbMinusAlt pre (incWitRestrict wit actions) \<subseteq> hbMinusAlt pre wit"
    using downclosed hbMinusIsMonotonic
    unfolding hbCalcIsMonotonic_def by metis
  hence subset: "hbMinusAlt pre (incWitRestrict wit actions) \<union> 
                (rf (incWitRestrict wit actions) \<union> 
                 mo (incWitRestrict wit actions)) \<subseteq> 
                hbMinusAlt pre wit \<union> (rf wit \<union> mo wit)" 
    by auto
  show "incComAlt pre (incWitRestrict wit actions) \<subseteq> incComAlt pre wit"
    unfolding incComAlt_def 
    using subset trancl_mono2
    by metis
qed

(*
unfolding hbCalcIsMonotonic_def
proof (intro allI impI)
  fix pre
  fix wit :: execution_witness
  fix actions
  assume downclosed: "downclosed actions (mo wit)"
  have "hbMinusAlt (preRestrict pre actions) (incWitRestrict wit actions) \<subseteq> hbMinusAlt pre wit"
    using downclosed hbMinusIsMonotonic
    unfolding hbCalcIsMonotonic_def by metis
  hence subset: "hbMinusAlt (preRestrict pre actions) (incWitRestrict wit actions) \<union> 
                (rf (incWitRestrict wit actions) \<union> 
                 mo (incWitRestrict wit actions)) \<subseteq> 
                hbMinusAlt pre wit \<union> (rf wit \<union> mo wit)" 
    by auto
  show "incComAlt (preRestrict pre actions) (incWitRestrict wit actions) \<subseteq> incComAlt pre wit"
    unfolding incComAlt_def 
    using subset trancl_mono2
    by metis
qed *)

subsection {* Invariance of consistency predicates under prefixes *}

lemma final_vse:
  assumes final: "selective_prefixes_are_final f actions hb hb2"
      and        "hb2 \<subseteq> hb"
                 "f b"
                 "b \<in> actions"
      and vse:   "(a, b) \<in> visible_side_effect_set (actions0 pre) hb"
  shows          "(a, b) \<in> visible_side_effect_set (actions0 pre) hb2"
proof -
  have as1: "\<not> (\<exists>c\<in>actions0 pre. c \<notin> {a, b} \<and> is_write c \<and> loc_of c = loc_of b \<and> (a, c) \<in> hb2 \<and> (c, b) \<in> hb2)"
    using vse `hb2 \<subseteq> hb` unfolding visible_side_effect_set_def by auto
  have as2: "(a, b) \<in> hb \<and> is_write a \<and> is_read b \<and> loc_of a = loc_of b"
    using vse unfolding visible_side_effect_set_def by auto
  hence "(a, b) \<in> hb2"
    using final `f b` `b \<in> actions` unfolding selective_prefixes_are_final_def by auto
  thus "(a, b) \<in> visible_side_effect_set (actions0 pre) hb2"
    using as1 as2 unfolding visible_side_effect_set_def by auto
qed

lemma assumptions_restriction:
  assumes "assumptions (pre, wit, [])"
  shows   "assumptions (preRestrict pre actions, incWitRestrict wit actions, [])"
using assms
unfolding assumptions.simps finite_prefixes_def
by auto

lemma coherent_memory_use_restriction:
  assumes "coherent_memory_use (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "coherent_memory_use (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
using assms
unfolding coherent_memory_use.simps  
by auto blast+ 

lemma consistent_atomic_rf_restriction:
  assumes "consistent_atomic_rf (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "consistent_atomic_rf (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
using assms
unfolding consistent_atomic_rf.simps 
by auto

lemma consistent_hb_restriction:
  assumes "consistent_hb (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "consistent_hb (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
using assms
unfolding consistent_hb.simps 
proof auto
  assume "irrefl (hb\<^sup>+)" 
     and "hb2 \<subseteq> hb"
  hence "hb2\<^sup>+ \<subseteq> hb\<^sup>+" using trancl_mono2 by metis
  thus "irrefl (hb2\<^sup>+)" using `irrefl (hb\<^sup>+)` 
    unfolding irrefl_def by auto
next
  assume "finite_prefixes hb (actions0 pre)"
     and "hb2 \<subseteq> hb"
  thus "finite_prefixes hb2 (actions0 pre \<inter> actions)"
    using finite_prefix_subset
    by force
qed

lemma consistent_mo_restriction:
  assumes "consistent_mo (pre, wit, [])"
          "downclosed actions (mo wit)"
  shows   "consistent_mo (preRestrict pre actions, incWitRestrict wit actions, [])"
using assms
unfolding consistent_mo.simps downclosed_def
by auto

lemma consistent_non_atomic_rf_restriction:
  fixes pre wit hb hb2 actions
  defines "vse  \<equiv>  visible_side_effect_set (actions0 pre) hb"
      and "vse2 \<equiv>  visible_side_effect_set (actions0 (preRestrict pre actions)) hb2"
  assumes cons_rf: "consistent_non_atomic_rf (pre, wit, [(''hb'', hb),(''vse'', vse)])"
      and final:   "selective_prefixes_are_final (is_na_or_non_write pre) actions hb hb2"
      and          "hb2 \<subseteq> hb"
  shows   "consistent_non_atomic_rf (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2),(''vse'', vse2)])"
unfolding consistent_non_atomic_rf.simps 
proof auto
  fix a b
  assume loc: "is_at_non_atomic_location (lk pre) b"
     and      "(a, b) \<in> rf wit"
              "a \<in> actions" 
              "b \<in> actions"
  hence non_write_b: "is_na_or_non_write pre b"
    unfolding is_na_or_non_write_def by simp
  have vse: "(a, b) \<in> vse"
    using cons_rf `(a, b) \<in> rf wit` loc unfolding consistent_non_atomic_rf.simps by auto
  thus "(a, b) \<in> vse2"
    using final_vse[OF final `hb2 \<subseteq> hb` non_write_b `b \<in> actions`, where a=a] 
    using `a \<in> actions` `b \<in> actions`
    unfolding vse_def vse2_def visible_side_effect_set_def by auto
qed

lemma det_read_alt_restriction:
  assumes det_read:      "det_read_alt (pre, wit, [(''hb'', hb)])"
      and conshb:        "consistent_hb (pre, wit, [(''hb'', hb)])"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_hb: "downclosed actions (hbMinus (pre, wit, [(''hb'', hb)]))"
      and final:         "selective_prefixes_are_final (is_na_or_non_write pre) actions hb hb2"
      and                "hb2 \<subseteq> hb"
  shows   "det_read_alt (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
unfolding det_read_alt.simps
proof (clarsimp)
  fix r 
  assume "r \<in> actions0 pre" 
         "is_load r"
         "r \<in> actions"
  hence non_write_r: "is_na_or_non_write pre r"
    unfolding is_na_or_non_write_def by (cases r) auto
  hence hb_eq: "\<And>w. ((w, r) \<in> hb2) = ((w, r) \<in> hb)"
    using `hb2 \<subseteq> hb` final `r \<in> actions`
    unfolding selective_prefixes_are_final_def 
    by auto  
  show "  (\<exists>w\<in>actions0 pre \<inter> actions. (w, r) \<in> hb2 \<and> is_write w \<and> loc_of w = loc_of r)  
        = (\<exists>w'\<in>actions0 pre \<inter> actions. (w', r) \<in> rf wit)"
    proof auto
      fix w
      assume w: "w \<in> actions0 pre"
                "w \<in> actions"
                "(w, r) \<in> hb2"
                "is_write w"
                "loc_of w = loc_of r"
      hence "(w, r) \<in> hb" using hb_eq by auto
      then obtain w' where w': "w'\<in>actions0 pre" "(w', r) \<in> rf wit"
        using w det_read `is_load r` `r \<in> actions0 pre`
        unfolding det_read_alt.simps 
        by auto
      hence "w' \<in> actions"
        using downclosed_rf `r \<in> actions` unfolding downclosed_def by auto
      thus "\<exists>w'\<in>actions0 pre \<inter> actions. (w', r) \<in> rf wit"
        using w' by auto
    next
      fix w'
      assume w': "(w', r) \<in> rf wit"
                 "w' \<in> actions0 pre"
                 "w' \<in> actions"
      then obtain w where w: "w \<in> actions0 pre"
                              "(w, r) \<in> hb"
                              "is_write w"
                              "loc_of w = loc_of r"
        using w' det_read `is_load r` `r \<in> actions0 pre`
        unfolding det_read_alt.simps 
        by auto
      hence "w \<in> actions"
        using non_write_r downclosed_hb `r \<in> actions`
        unfolding hbMinus.simps downclosed_def
        by auto
      have "(w, r) \<in> hb2" using `(w, r) \<in> hb` hb_eq by auto
      thus "\<exists>w\<in>actions0 pre \<inter> actions. (w, r) \<in> hb2 \<and> is_write w \<and> loc_of w = loc_of r"
        using w `w \<in> actions` by auto
    qed
qed

lemma locks_only_consistent_lo_restriction:
  assumes "locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "locks_only_consistent_lo (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms relRestrict_relOver relRestrict_isTransitive relRestrict_isIrreflexive
    unfolding locks_only_consistent_lo.simps 
    by auto
qed

lemma locks_only_consistent_locks_restriction:
  assumes "locks_only_consistent_locks (pre, wit, [])"
          "selective_downclosed (is_na_or_non_write pre) actions (getHb pre wit)"
          "\<And>a b. \<lbrakk>is_unlock a; is_lock b; (a, b) \<in> lo wit\<rbrakk> \<Longrightarrow> (a, b) \<in> getHb pre wit"
  shows   "locks_only_consistent_locks (preRestrict pre actions, incWitRestrict wit actions, [])"
unfolding locks_only_consistent_locks.simps
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
  thus "\<exists>c\<in>actions0 pre \<inter> actions. is_unlock c \<and> (a, c) \<in> lo wit \<and> (c, b) \<in> lo wit"
    using assms3 by fast
qed

lemma rmw_atomicity_restriction:
  assumes "rmw_atomicity (pre, wit, [])"
          "downclosed actions (mo wit)"
  shows   "rmw_atomicity (preRestrict pre actions, incWitRestrict wit actions, [])"
using assms
unfolding rmw_atomicity.simps
          adjacent_less_than_def
          downclosed_def
by auto

lemma sc_accesses_consistent_sc_restriction:
  assumes "sc_accesses_consistent_sc (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "sc_accesses_consistent_sc (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms relRestrict_relOver relRestrict_isTransitive relRestrict_isIrreflexive
    unfolding sc_accesses_consistent_sc.simps
    by auto
qed

lemma sc_accesses_sc_reads_restricted_restriction:
  assumes "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "sc_accesses_sc_reads_restricted (preRestrict pre actions, incWitRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms
    unfolding sc_accesses_sc_reads_restricted.simps 
    by auto
qed

lemma sc_fenced_sc_fences_heeded_restriction:
  assumes "sc_fenced_sc_fences_heeded (pre, wit, [])"
  shows   "sc_fenced_sc_fences_heeded (preRestrict pre actions, incWitRestrict wit actions, [])"
using assms
unfolding sc_fenced_sc_fences_heeded.simps 
(* The simp takes a long time, but it is a difficult predicate. *)
apply simp
by auto

lemma tot_empty_restriction:
  assumes "tot_empty (pre, wit, [])"
  shows   "tot_empty (preRestrict pre actions, incWitRestrict wit actions, [])"
using assms
unfolding tot_empty.simps 
by simp

lemma well_formed_rf_restriction:
  assumes "well_formed_rf (pre, wit, [])"
  shows   "well_formed_rf (preRestrict pre actions, incWitRestrict wit actions, [])"
using assms
unfolding well_formed_rf.simps 
(* Without the clarsimp, auto takes a long, long time. *)
by clarsimp auto

lemma well_formed_threads_restriction:
  assumes "well_formed_threads (pre, wit, [])"
  shows   "well_formed_threads (preRestrict pre actions, wit2, [])"
proof -
  have "actions_respect_location_kinds (actions0 pre \<inter> actions) (lk pre)"
    using assms
    unfolding well_formed_threads.simps actions_respect_location_kinds_def
    by auto
  moreover have "irrefl (sbasw (preRestrict pre actions))"
    using assms isIrreflexive_subset[OF _ incPreRestrict_sbasw_subset2]
    unfolding well_formed_threads.simps 
    by simp
  moreover have "finite_prefixes (sbasw (preRestrict pre actions)) (actions0 pre \<inter> actions)"
    using assms  finite_prefix_subset[OF _ incPreRestrict_sbasw_subset2]
    unfolding well_formed_threads.simps
    by auto
  ultimately show ?thesis
    using assms incPreRestrict_sbasw_subset
    unfolding well_formed_threads.simps
    unfolding blocking_observed_def
              Cmm_csem.inj_on_def
              threadwise_def
              interthread_def
              isStrictPartialOrder_def
              indeterminate_sequencing_def
              disjoint_allocs_def
    by auto
qed

lemma well_formed_threads_opsem_restriction:
  assumes "well_formed_threads_opsem (pre, wit, [])"
  shows   "well_formed_threads_opsem (preRestrict pre actions, wit2, [])"
using assms
unfolding well_formed_threads_opsem_eq
using well_formed_threads_restriction
by auto

lemma axsimpConsistent_restriction:
  assumes cons:       "axsimpConsistentAlt pre wit"
      and downclosed: "downclosed actions (incComAlt pre wit)"
  shows   "axsimpConsistentAlt (preRestrict pre actions) (incWitRestrict wit actions)"
proof -
  let ?wit' = "incWitRestrict wit actions"
  let ?pre' = "preRestrict pre actions"
  have downclosed_hbMinus: "downclosed actions (hbMinusAlt pre wit)"
   and downclosed_rf:      "downclosed actions (rf wit)"
   and downclosed_mo:      "downclosed actions (mo wit)"
    using downclosed unfolding incComAlt_def by simp_all
  have "sbMinus pre (sb pre) \<subseteq> hbMinusAlt pre wit" 
    using sbInHb unfolding sbMinus_def getRelations_simp hbMinus.simps by auto
  hence downclosed_sbMinus: "downclosed actions (sbMinus pre (sb pre))"
    using downclosed_hbMinus downclosed_subset by metis
  have selective_downclosed: "selective_downclosed (is_na_or_non_write pre) actions (getHb pre wit)"
    using downclosed_hbMinus
    unfolding getRelations_simp
              hbMinus.simps
              selective_downclosed_def
              downclosed_def
    by auto
  have trans_sb: "trans (sb pre)"
    using cons
    by auto
  have dd_subset_sb: "dd pre \<subseteq> sb pre"
    using cons
    by auto
  have prefixes_final: "selective_prefixes_are_final (is_na_or_non_write pre) actions (getHb pre wit) (getHb ?pre' ?wit')"
    using hbCalcIsFinalForPrefixes downclosed_rf downclosed_mo 
          downclosed_sbMinus selective_downclosed trans_sb dd_subset_sb
    unfolding hbCalcIsFinalForPrefixes_def  
    by auto

  have hbSubset: "getHb ?pre' ?wit' \<subseteq> getHb pre wit"
    using hbCalcIsMonotonic downclosed_mo unfolding hbCalcIsMonotonic_def by auto
  
  show ?thesis
    unfolding axsimpConsistent_def
    proof auto
      show "assumptions (?pre', ?wit', [])"
        using cons assumptions_restriction by auto
    next
      show "det_read_alt (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons det_read_alt_restriction[OF _ _ downclosed_rf _ prefixes_final hbSubset]
        using downclosed_hbMinus
        by auto
    next
      show "coherent_memory_use (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons coherent_memory_use_restriction hbSubset 
        by auto
    next
      show "consistent_atomic_rf (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons consistent_atomic_rf_restriction hbSubset 
        by auto
    next
      show "consistent_hb (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons consistent_hb_restriction hbSubset 
        by auto
    next
      show "consistent_mo (?pre', ?wit', [])"
        using cons consistent_mo_restriction downclosed_mo
        by auto
    next
      have "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
        using cons by auto
      thus "consistent_non_atomic_rf (?pre', ?wit', [(''hb'', getHb ?pre' ?wit'), (''vse'', getVse ?pre' ?wit')])"
        using consistent_non_atomic_rf_restriction[OF _ prefixes_final hbSubset, where wit=wit]
        unfolding getVse_def
        by auto
    next
      show "locks_only_consistent_lo (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons locks_only_consistent_lo_restriction hbSubset 
        by auto
    next
      have "\<And>a b. is_unlock a \<Longrightarrow> is_lock b \<Longrightarrow> (a, b) \<in> lo wit \<Longrightarrow> (a, b) \<in> getHb pre wit"
        using loInHb cons 
        unfolding hbCalcRespectsSyncingLocks_def
        by auto
      thus "locks_only_consistent_locks (?pre', ?wit', [])"
        using locks_only_consistent_locks_restriction[where pre=pre and wit=wit and actions=actions]
        using selective_downclosed cons 
        by auto
    next
      show "rmw_atomicity (?pre', ?wit', [])"
        using cons rmw_atomicity_restriction downclosed_mo by auto
    next
      show "sc_accesses_consistent_sc (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons sc_accesses_consistent_sc_restriction hbSubset by auto
    next
      show "sc_accesses_sc_reads_restricted (?pre', ?wit', [(''hb'', getHb ?pre' ?wit')])"
        using cons sc_accesses_sc_reads_restricted_restriction hbSubset by auto
    next
      show "sc_fenced_sc_fences_heeded (?pre', ?wit', [])"
        using cons sc_fenced_sc_fences_heeded_restriction by auto
    next
      show "tot_empty (?pre', ?wit', [])"
        using cons tot_empty_restriction by auto
    next
      show "well_formed_rf (?pre', ?wit', [])"
        using cons well_formed_rf_restriction by auto
    next
      show "well_formed_threads_opsem (?pre', ?wit', [])"
        using cons well_formed_threads_opsem_restriction by auto
    qed
qed

subsection {* Soundness *}

(* Consistency of empty_witness *)

lemma assumptions_empty_witness [simp]:
  shows "assumptions ((preRestrict pre {}), empty_witness, [])"
unfolding assumptions.simps
by simp

lemma well_formed_threads_empty_witness [simp]:
  shows "well_formed_threads ((preRestrict pre {}), empty_witness, [])"
unfolding well_formed_threads.simps indeterminate_sequencing_def
by simp

lemma well_formed_threads_opsem_empty_witness [simp]:
  shows "well_formed_threads_opsem ((preRestrict pre {}), empty_witness, [])"
unfolding well_formed_threads_opsem_eq
by simp

lemma det_read_op_empty_witness [simp]:
  shows "det_read_alt ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding det_read_alt.simps
by simp

lemma coherent_memory_use_empty_witness [simp]:
  shows "coherent_memory_use ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding coherent_memory_use.simps
by simp

lemma consistent_atomic_rf_empty_witness [simp]:
  shows "consistent_atomic_rf ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding consistent_atomic_rf.simps
by simp

lemma consistent_mo_op_empty_witness [simp]:
  shows "consistent_mo ((preRestrict pre {}), empty_witness, [])"
unfolding consistent_mo.simps
by simp

lemma consistent_hb_empty_witness [simp]:
  shows "consistent_hb ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding consistent_hb.simps 
by simp

lemma consistent_non_atomic_rf_empty_witness [simp]:
  shows "consistent_non_atomic_rf ((preRestrict pre {}), empty_witness, [(''hb'', {}), (''vse'', {})])"
unfolding consistent_non_atomic_rf.simps
by simp

lemma locks_only_consistent_lo_op_empty_witness [simp]:
  shows "locks_only_consistent_lo ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding locks_only_consistent_lo.simps 
by simp

lemma locks_only_consistent_locks_op_empty_witness [simp]:
  shows "locks_only_consistent_locks ((preRestrict pre {}), empty_witness, [])"
unfolding locks_only_consistent_locks.simps
by simp

lemma rmw_atomicity_op_empty_witness [simp]:
  shows "rmw_atomicity ((preRestrict pre {}), empty_witness, [])"
unfolding rmw_atomicity.simps
by simp

lemma sc_accesses_consistent_sc_op_empty_witness [simp]:
  shows "sc_accesses_consistent_sc ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding sc_accesses_consistent_sc.simps 
by simp

lemma sc_accesses_sc_reads_restricted_empty_witness [simp]:
  shows "sc_accesses_sc_reads_restricted ((preRestrict pre {}), empty_witness, [(''hb'', {})])"
unfolding sc_accesses_sc_reads_restricted.simps
by simp

lemma sc_fenced_sc_fences_heeded_empty_witness [simp]:
  shows "sc_fenced_sc_fences_heeded ((preRestrict pre {}), empty_witness, [])"
unfolding sc_fenced_sc_fences_heeded.simps
by simp

lemma tot_empty_empty_witness [simp]:
  shows "tot_empty ((preRestrict pre {}), empty_witness, [])"
unfolding tot_empty.simps
by simp

lemma well_formed_rf_op_empty_witness [simp]:
  shows "well_formed_rf ((preRestrict pre {}), empty_witness, [])"
unfolding well_formed_rf.simps
by simp

lemma consistencyEmptyExecution [simp]:
  shows "axsimpConsistentAlt (preRestrict pre {}) empty_witness"
unfolding axsimpConsistentAlt_def
by simp

lemma incTraceConsistency: 
  assumes "incTrace pre r s"
          "r = incInitialState pre"
  shows   "  axsimpConsistentAlt (preRestrict pre (incCommittedSet s)) (incWit s)
           \<and> well_formed_threads_opsem (pre, empty_witness, [])
           \<and> incCommittedSet s \<subseteq> actions0 pre"
using assms 
proof induct
  case incStep
  thus ?case unfolding incStep_def incToEx_def Let_def by auto
qed simp

lemma incConsistentSoundness:
  assumes "incConsistent (pre, wit, getRelations pre wit)"
  shows   "axsimpConsistent (pre, wit, getRelations pre wit)"
using assms
proof -
  assume "incConsistent (pre, wit, getRelations pre wit)"
  then obtain s where trace: "incTrace pre (incInitialState pre) s"
                  and   wit: "incWit s = wit"
                  and   com: "incCommittedSet s = actions0 pre"
    unfolding incConsistent_def consistencyFromTrace.simps
    by auto
  thus "axsimpConsistent (pre, wit, getRelations pre wit)" 
    using incTraceConsistency[OF trace] preRestrict_id wit
    by metis
qed

subsection {* Completeness *}

lemma existenceIncTrace:
  assumes cons:       "axsimpConsistentAlt pre wit"
      and finite:     "finite actions"
      and universe:   "actions \<subseteq> actions0 pre"
      and downclosed: "downclosed actions (incComAlt pre wit)"
  shows   "\<exists> s. incTrace pre (incInitialState pre) s \<and> 
                incWit s = incWitRestrict wit actions \<and> 
                incCommittedSet s = actions"
proof (rule finite_downclosedsubset_induct[OF finite universe downclosed])
  show "acyclic (incComAlt pre wit)"
    using opsemOrder_isStrictPartialOrder[OF cons]
    unfolding isStrictPartialOrder_def acyclic_def irrefl_def
    by auto
next
  have "well_formed_threads_opsem (pre, wit, [])"
    using cons by auto
  hence "well_formed_threads_opsem (pre, empty_witness, [])"
    by (cases "wit = empty_witness") simp_all
  thus "\<exists>s.   incTrace pre (incInitialState pre) s 
            \<and> incWit s = incWitRestrict wit {} 
            \<and> incCommittedSet s = {}"
    using incReflexive by (intro exI[where x="incInitialState pre"]) simp
next
  fix a :: action
  fix actions :: "action set"
  assume finite':     "finite actions"
     and              "a \<notin> actions"
     and              "a \<in> actions0 pre"
     and downclosed': "downclosed (insert a actions) (incComAlt pre wit)"
     and max:         "\<forall>b\<in>actions. (a, b) \<notin> incComAlt pre wit"
     and IH:          "\<exists>s. incTrace pre (incInitialState pre) s \<and> 
                           incWit s = incWitRestrict wit actions \<and> 
                           incCommittedSet s = actions"
  obtain s where trace:     "incTrace pre (incInitialState pre) s" 
             and witness:   "incWit s = incWitRestrict wit actions"
             and committed: "incCommittedSet s = actions" using IH by blast

  let ?actions' = "insert a actions"
  let ?pre'     = "preRestrict pre ?actions'"
  let ?wit'     = "incWitRestrict wit ?actions'"
  let ?s' = "\<lparr> incWit=?wit', 
               incCommitted=a#(incCommitted s)\<rparr>"
  have downclosed_mo: "downclosed ?actions' (mo wit)"
    using downclosed' unfolding incComAlt_def by auto
  have inOpsemOrder: "respectsCom (actions0 pre) (incCommitted s) (incComAlt pre (incWit ?s')) a"
    unfolding respectsCom_def
    proof auto
      fix b
      assume "b \<in> actions0 pre"
             "(b, a) \<in> incComAlt pre ?wit'"
      hence ba_in_rel: "(b, a) \<in> incComAlt pre wit"
        using opsemOrderIsMonotonic[OF downclosed_mo]
        by auto
      hence "b \<noteq> a"
        using opsemOrder_isStrictPartialOrder[OF cons]
        unfolding isStrictPartialOrder_def irrefl_def
        by auto
      thus "b \<in> incCommittedSet s"
        using downclosed' ba_in_rel committed 
        unfolding downclosed_def 
        by auto
    next
      fix b
      assume "b \<in> actions0 pre"
             "b \<in> incCommittedSet s"
             "(a, b) \<in> incComAlt pre ?wit'"
      hence ba_in_rel: "(a, b) \<in> incComAlt pre wit"
        using opsemOrderIsMonotonic[OF downclosed_mo]
        by auto
      thus False using max `b \<in> incCommittedSet s` committed  by metis 
    qed
  have "axsimpConsistentAlt ?pre' ?wit'"
    using cons downclosed' axsimpConsistent_restriction by metis
  hence "incStep pre s ?s' a"
    unfolding incStep_def Let_def incToEx_def
    using committed `a \<notin> actions` `a \<in> actions0 pre` witness inOpsemOrder
    by auto
  hence "incTrace pre (incInitialState pre) ?s'" using incStep trace by smt
  thus "\<exists>s'. incTrace pre (incInitialState pre) s' \<and> 
             incWit s' = incWitRestrict wit ?actions' \<and> 
             incCommittedSet s' = ?actions'"
    using committed
    by (intro exI[where x="?s'"]) simp
qed

lemma incConsistentCompleteness:
  assumes cons: "axsimpConsistent (pre, wit, getRelations pre wit)"
  shows         "incConsistent (pre, wit, getRelations pre wit)"
proof -
  have relOverSb: "relOver (sb pre) (actions0 pre)"
    using cons by (auto 4 3)
  have "well_formed_rf (pre, wit, [])" 
    using cons by auto
  hence relOverRf: "relOver (rf wit) (actions0 pre)"
    unfolding well_formed_rf.simps relOver_def 
    by auto
  have relOverMo: "relOver (mo wit) (actions0 pre)"
    using cons by auto
  have relOverSc: "relOver (sc wit) (actions0 pre)"
    using cons by auto
  have relOverLo: "relOver (lo wit) (actions0 pre)"
    using cons by auto
  have "tot_empty (pre, wit, [])"
    using cons by auto
  hence relOverTot: "relOver (tot wit) (actions0 pre)"
    unfolding tot_empty.simps by simp
  have wit_restrict: "incWitRestrict wit (actions0 pre) = wit" 
    using relOverRf relOverMo relOverSc relOverLo relOverTot
    unfolding incWitRestrict_def 
    by (simp add: relRestrict_id)
  have "relOver (getHb pre wit) (actions0 pre)" 
    using relOverSb hbRelOver by auto
  hence relOverHbMinus: "relOver (hbMinusAlt pre wit) (actions0 pre)"
    unfolding hbMinus.simps 
              relOver_def 
              getRelations_simp
    by auto
  have downclosed: "downclosed (actions0 pre) (incComAlt pre wit)" 
    unfolding incComAlt_def
    using relOverRf relOverMo relOverHbMinus
    by (simp add: downclosed_relOver)
  have finite: "finite (actions0 pre)"
    using cons by auto
  obtain s where "incTrace pre (incInitialState pre) s"
                           "incWit s = incWitRestrict wit (actions0 pre)"
                           "incCommittedSet s = (actions0 pre)"
    using existenceIncTrace[OF cons finite _ downclosed]
    by auto
  thus ?thesis
    unfolding incConsistent_def consistencyFromTrace.simps
    using wit_restrict
    by auto
qed

subsection {* Equivalence *}

corollary incConsistentEquivalence_aux:
  shows "  incConsistent (pre, wit, getRelations pre wit)
         = axsimpConsistent (pre, wit, getRelations pre wit)"
using incConsistentSoundness incConsistentCompleteness
by metis

corollary incConsistentEquivalence:
  shows "  incConsistent (pre, wit, getRelations pre wit)
         = (axConsistent (pre, wit, getRelations pre wit) \<and> finite (actions0 pre))"
using incConsistentEquivalence_aux axsimpConsistentEq
by metis



section {* The monadic model *}

subsubsection {* monInvariant *}

definition monInvariant :: "pre_execution \<Rightarrow> incState \<Rightarrow> bool" where
  "monInvariant pre s \<equiv> 
        axsimpConsistentAlt (preRestrict pre (incCommittedSet s)) (incWit s)
      \<and> well_formed_threads_opsem (pre, empty_witness, [])
      \<and> incCommittedSet s \<subseteq> actions0 pre"

lemma monInvariantE [elim]:
  assumes "monInvariant pre s"
  obtains "axsimpConsistentAlt (preRestrict pre (incCommittedSet s)) (incWit s)"
      and "well_formed_threads_opsem (pre, empty_witness, [])"
      and "incCommittedSet s \<subseteq> actions0 pre"
using assms
unfolding monInvariant_def
by simp

subsection {* Elims of auxiliaries *}

subsubsection {* list comprehensions *}

lemma setFoldr_filter_simp [simp]:
  shows "  set (foldr (\<lambda>e x2. if P e then f e # x2 else x2) l [])
         = f ` {e. e \<in> set l \<and> P e}"
by (induct l) auto

lemma setFoldr_map_simp [simp]:
  shows "  set (foldr (\<lambda>b. op # (f b)) l [])
         = f ` (set l)"
by (induct l) auto

subsubsection {* sameLocWrites *}

abbreviation "sameLocWritesSet actions a \<equiv> set (sameLocWrites actions a)"

lemmas sameLocWritesSet_def = sameLocWrites_def

lemma sameLocWritesE [elim]:
  assumes "x \<in> set (sameLocWrites actions a)"
  obtains "x \<in> set actions" "is_write x" "loc_of x = loc_of a"
using assms
unfolding sameLocWrites_def
by auto

lemma sameLocInMo:
  assumes sameLoc:    "w \<in> sameLocWritesSet committed a"
      and cons2:      "axsimpConsistentAlt pre wit"
      and committed:  "actions0 pre = insert a (set committed)"
      and downclosed: "downclosed (set committed) (mo wit)"
      and a:          "is_at_atomic_location (lk pre) a"
                      "is_write a"
                      "a \<in> actions0 pre"
                      "a \<notin> set committed"
  shows   "(w, a) \<in> mo wit"
proof -  
  have bc: "loc_of w = loc_of a" 
           "is_write w" 
           "w \<in> set committed"
    using sameLoc by auto
  hence bc2: "w \<noteq> a" 
             "is_write a" 
             "is_at_atomic_location (lk pre) a"
             "w \<in> actions0 pre"
             "a \<in> actions0 pre"
             "a \<notin> set committed"
    using a committed by auto
  hence "(a, w) \<notin> mo wit"
    using downclosed bc by (auto elim: downclosedE)
  thus "(w, a) \<in> mo wit" 
    using cons2 bc bc2 by (auto elim: consistent_moE_inv)
qed

subsubsection {* sameLocLocksUnlocks *}

abbreviation "sameLocLocksUnlocksSet actions a \<equiv> set (sameLocLocksUnlocks actions a)"

lemmas sameLocLocksUnlocksSet_def = sameLocLocksUnlocks_def

lemma sameLocLocksUnlocksE [elim]:
  assumes "x \<in> set (sameLocLocksUnlocks actions a)"
  obtains "x \<in> set actions" "is_lock x \<or> is_unlock x" "loc_of x = loc_of a"
using assms
unfolding sameLocLocksUnlocks_def
by auto

subsubsection {* scActions *}

abbreviation "scActionsSet actions \<equiv> set (scActions actions)"

lemmas scActionsSet_def = scActions_def

lemma scActionsE [elim]:
  assumes "x \<in> set (scActions actions)"
  obtains "x \<in> set actions" "is_seq_cst x"
using assms
unfolding scActions_def
by auto

subsubsection {* checkValuesAreEqual *}

lemmas checkValuesAreEqual.simps [simp]

lemma checkValuesAreEqual_simp [simp]:
  shows "() [\<in>] checkValuesAreEqual b = (b = None \<or> (\<exists>a. b = Some (a, a)))"
by (cases b) auto

subsubsection {* addToTransitiveOrder *}

lemma addToTransitiveOrderE [elim?]:
  assumes "rel' [\<in>] addToTransitiveOrder domain a rel"
  obtains y where "y \<in> set domain"
                  "rel' = insert (y, a) 
                                 (   rel 
                                   \<union> (\<lambda>c. (c, a)) ` {c \<in> set domain. (c, y) \<in> rel}
                                   \<union> Pair a ` {c \<in> set domain. (y, c) \<in> rel}
                                 )"
        | "rel' = rel \<union> Pair a ` set domain"
using assms
unfolding addToTransitiveOrder_def
by auto

lemma addToTransitiveOrderE_elem [elim?]:
  assumes "rel' [\<in>] addToTransitiveOrder domain a rel"
      and "(x, y) \<in> rel'"
  obtains "(x, y) \<in> rel"
        | "x = a" "y \<in> set domain"
        | "y = a" "x \<in> set domain"
using assms
unfolding addToTransitiveOrder_def
by auto

subsection {* Elims of relation constructions *}

subsubsection {* mo *}

lemma monAddToMoE [elim?]:
  assumes step: "rel [\<in>] monAddToMo pre a s"
      and inv:  "monInvariant pre s"
  obtains "rel = mo (incWit s) \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s) a"
using assms
unfolding monAddToMo_def Let_def 
by auto

subsubsection {* rf *}

lemma auxAddPairToRfE [elim]: 
  assumes step: "(rel', v_w, v_r) [\<in>] auxAddPairToRf rel w r "
  obtains "rel' = insert (w, r) rel"
          "value_written_by w = Some v_w"
          "value_read_by r = Some v_r"
using assms
unfolding auxAddPairToRf_def
apply (cases "value_written_by w", auto)
by (cases "value_read_by r", auto)

lemma auxAddToRfLoadE [elim?]:
  assumes step: "(rel, v) [\<in>] auxAddToRfLoad pre a s"
  obtains w v_w v_r where "w \<in> sameLocWritesSet (incCommitted s) a" 
                          "(rel, v_w, v_r) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
                          "v = Some (v_w, v_r)"
        | "rel = rf (incWit s)"
          "v = None"
proof (cases "v = None")
  case True
  hence "rel = rf (incWit s)"
    using step 
    unfolding auxAddToRfLoad_def
    by auto
  thus ?thesis using True that by metis
next
  case False
  then obtain w v_w v_r 
        where w: "w \<in> sameLocWritesSet (incCommitted s) a"
                 "(rel, v_w, v_r) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
                 "v = Some (v_w, v_r)"
    using step 
    unfolding auxAddToRfLoad_def
    by auto
  thus ?thesis using w that by auto
qed

lemma monAddToRfLoadE [elim?]:
  assumes step: "rel [\<in>] monAddToRfLoad pre a s"
  obtains w v where "w \<in> sameLocWritesSet (incCommitted s) a" 
                    "(rel, v, v) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
        | "rel = rf (incWit s)"
proof -
  obtain vs where vs: "(rel, vs) [\<in>] auxAddToRfLoad pre a s"
              and eq: "() [\<in>] checkValuesAreEqual vs"
    using step
    unfolding monAddToRfLoad_def
    by auto
  thus ?thesis
    proof (cases "vs = None")
      case True
      hence "rel = rf (incWit s)"
        using that auxAddToRfLoadE[OF vs]
        by auto
      thus ?thesis using that by metis
    next
      case False
      then obtain w v_w v_r 
            where w: "w \<in> sameLocWritesSet (incCommitted s) a" 
                     "(rel, v_w, v_r) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
                     "vs = Some (v_w, v_r)"
        using auxAddToRfLoadE[OF vs] by auto
      hence "v_w = v_r" using eq by auto
      thus ?thesis using that w by auto
    qed
qed

lemma auxAddToRfRmwE [elim?]:
  assumes step: "(rel, v) [\<in>] auxAddToRfRmw pre a s"
  obtains w v_w v_r where "w \<in> sameLocWritesSet (incCommitted s) a"
                          "\<forall>w' \<in> sameLocWritesSet (incCommitted s) a. (w, w') \<notin> mo (incWit s)"
                          "(rel, v_w, v_r) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
                          "v = Some (v_w, v_r)"
        | "sameLocWrites (incCommitted s) a = []"
          "rel = rf (incWit s)"
          "v = None"
proof (cases "sameLocWrites (incCommitted s) a = []")
  case True
  thus ?thesis 
    using step that unfolding auxAddToRfRmw_def by auto
next
  case False
  then obtain w v_w v_r 
        where w: "w \<in> sameLocWritesSet (incCommitted s) a"
                 "\<forall>w' \<in> sameLocWritesSet (incCommitted s) a. (w, w') \<notin> mo (incWit s)"
                 "(rel, v_w, v_r) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
                 "v = Some (v_w, v_r)"
    using step 
    unfolding auxAddToRfRmw_def Let_def
    by auto
  thus ?thesis using w that by metis
qed

lemma monAddToRfRmwE [elim?]:
  assumes step: "rel [\<in>] monAddToRfRmw pre a s"
  obtains w v where "w \<in> sameLocWritesSet (incCommitted s) a" 
                    "\<forall>w' \<in> sameLocWritesSet (incCommitted s) a. (w, w') \<notin> mo (incWit s)"
                    "(rel, v, v) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
        | "sameLocWrites (incCommitted s) a = []"
          "rel = rf (incWit s)"
proof -
  obtain vs where vs: "(rel, vs) [\<in>] auxAddToRfRmw pre a s"
              and eq: "() [\<in>] checkValuesAreEqual vs"
    using step
    unfolding monAddToRfRmw_def
    by auto
  thus ?thesis
    proof (cases "vs = None")
      case True
      hence "rel = rf (incWit s)" 
            "sameLocWrites (incCommitted s) a = []"
        using auxAddToRfRmwE[OF vs]
        by auto
      thus ?thesis using that by metis
    next
      case False
      then obtain w v_w v_r 
            where w: "w \<in> sameLocWritesSet (incCommitted s) a" 
                     "\<forall>w' \<in> sameLocWritesSet (incCommitted s) a. (w, w') \<notin> mo (incWit s)"
                     "(rel, v_w, v_r) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
                     "vs = Some (v_w, v_r)"
        using auxAddToRfRmwE[OF vs] by auto
      hence "v_w = v_r" using eq by auto
      thus ?thesis using that w by auto
    qed
qed

subsubsection {* sc *}

subsubsection {* lo *}

lemma monAddToLoE [elim?]:
  assumes "rel' [\<in>] monAddToLo pre a s"
  obtains y where "y \<in> sameLocLocksUnlocksSet (incCommitted s) a"
                  "rel' = insert (y, a) 
                                 (   lo (incWit s) 
                                   \<union> (\<lambda>c. (c, a)) ` {c \<in> sameLocLocksUnlocksSet (incCommitted s) a. (c, y) \<in> lo (incWit s)}
                                   \<union> Pair a ` {c \<in> sameLocLocksUnlocksSet (incCommitted s) a. (y, c) \<in> lo (incWit s)}
                                 )"
        | "rel' = lo (incWit s) \<union> Pair a ` (sameLocLocksUnlocksSet (incCommitted s) a)"
using assms
unfolding monAddToLo_def
by (elim addToTransitiveOrderE) auto

lemma monAddToLoE_elem [elim?]:
  assumes "rel' [\<in>] monAddToLo pre a s"
      and "(x, y) \<in> rel'"
  obtains "(x, y) \<in> lo (incWit s)"
        | "x = a" "y \<in> sameLocLocksUnlocksSet (incCommitted s) a"
        | "y = a" "x \<in> sameLocLocksUnlocksSet (incCommitted s) a"
using assms
unfolding monAddToLo_def
by (elim addToTransitiveOrderE_elem) auto

subsection {* Elims of monStep *}

lemma monStepE_action [elim]:
  assumes monStep:  "(a, s2) [\<in>] monStep pre s1"
      and inv:  "monInvariant pre s"
  obtains "a \<in> actions0 pre" 
          "a \<in> incCommittedSet s2"
          "a \<notin> incCommittedSet s1"
proof -
  have "finite (actions0 pre)"
    using inv by auto
  hence "a \<in> actions0 pre" 
        "a \<in> incCommittedSet s2"
        "a \<notin> incCommittedSet s1"
    using monStep
    unfolding monStep_def Let_def
    by auto
  thus ?thesis using that by simp
qed

lemma monStepE_committed [elim]:
  assumes monStep:  "(a, s2) [\<in>] monStep pre s1"
  obtains "incCommitted s2 = a#(incCommitted s1)"
using monStep
unfolding monStep_def Let_def
by auto

lemmas monPerformActions_def = 
  monPerformAction_def
  monPerformLock_def
  monPerformUnlock_def
  monPerformLoad_def
  monPerformStore_def
  monPerformRmw_def
  monPerformFence_def

subsubsection {* rf *}

lemma monStepE_rf [elim?, consumes 1]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
  obtains (load)   "is_load a" "rf (incWit s2) [\<in>] monAddToRfLoad pre a s1"
        | (rmw)    "is_RMW a" "rf (incWit s2) [\<in>] monAddToRfRmw pre a s1"
        | (other)  "\<not>is_read a" "rf (incWit s2) = rf (incWit s1)"
using assms
unfolding monStep_def monPerformActions_def Let_def
by (cases a) auto

lemma monStepE_rf2 [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
  obtains w where "rf (incWit s2) = insert (w, a) (rf (incWit s1))"
                  "w \<in> sameLocWritesSet (incCommitted s1) a"
        | "rf (incWit s2) = rf (incWit s1)"
proof (cases rule: monStepE_rf[OF monStep])
  case 1
  thus ?thesis
    using that
    by (cases rule: monAddToRfLoadE[OF 1(2)]) auto
next
  case 2
  thus ?thesis
    using that
    by (cases rule: monAddToRfRmwE[OF 2(2)]) auto
next
  case 3
  thus ?thesis using that by auto
qed

lemma monStepE_rf_pair [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
      and in_rf:   "(x, y) \<in> rf (incWit s2)"
  obtains "y = a"
          "x \<in> sameLocWritesSet (incCommitted s1) a"
        | "(x, y) \<in> rf (incWit s1)"
          "x \<in> incCommittedSet s1"
          "y \<in> incCommittedSet s1"
proof -
  have cons_rf: "well_formed_rf (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  hence incCom_s1: "(x, y) \<in> rf (incWit s1) \<Longrightarrow> x \<in> incCommittedSet s1 \<and> y \<in> incCommittedSet s1"
    by auto
  show ?thesis
    using incCom_s1 in_rf that
    by (cases rule: monStepE_rf2[OF monStep]) auto
qed

subsubsection {* mo *}

lemma monStepE_mo [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  obtains (store) "is_write a" 
                  "is_at_atomic_location (lk pre) a"
                  "mo (incWit s2) [\<in>] monAddToMo pre a s1"
        | (other) "\<not>is_RMW a"
                  "\<not>(is_store a \<and> is_at_atomic_location (lk pre) a)" 
                  "mo (incWit s2) = mo (incWit s1)"
proof (cases "is_write a \<and> is_at_atomic_location (lk pre) a")
  assume a: "is_write a \<and> is_at_atomic_location (lk pre) a"
  hence "mo (incWit s2) [\<in>] monAddToMo pre a s1"
    using monStep
    unfolding monStep_def monPerformActions_def Let_def
    by (cases a) auto
  thus ?thesis using a store by auto
next
  assume a: "\<not>(is_write a \<and> is_at_atomic_location (lk pre) a)"
  hence a2: "\<not>(is_store a \<and> is_at_atomic_location (lk pre) a)" 
    by (cases a) auto
  have "a \<in> actions0 pre"
    using monStep inv by auto
  have "actions_respect_location_kinds (actions0 pre) (lk pre)"
    using inv by auto
  hence "is_RMW a \<Longrightarrow> is_at_atomic_location (lk pre) a"
    using is_RMWE_location_kind[OF _ `a \<in> actions0 pre`]
    by auto
  hence a3: "\<not>is_RMW a" using a  `a \<in> actions0 pre` by auto
  hence "mo (incWit s2) = mo (incWit s1)"
    using a monStep
    unfolding monStep_def monPerformActions_def Let_def
    by (cases a) auto
  thus ?thesis using a2 a3 other by auto
qed

lemma monStepE_mo2 [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  obtains (store) "is_write a" 
                  "is_at_atomic_location (lk pre) a"
                  "mo (incWit s2) =    mo (incWit s1)
                                    \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s1) a"
        | (other) "\<not>is_RMW a"
                  "\<not>(is_store a \<and> is_at_atomic_location (lk pre) a)" 
                  "mo (incWit s2) = mo (incWit s1)"
proof (cases rule: monStepE_mo[OF monStep inv])
  case 1
  thus ?thesis
    using monAddToMoE[OF _ inv] using that by metis
next
  case 2
  thus ?thesis using that by auto
qed

lemma monStepE_mo3 [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  obtains "mo (incWit s1) = relRestrict (mo (incWit s2)) (incCommittedSet s1)"
proof -
  have cons_mo: "consistent_mo (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  hence s1: "mo (incWit s1) = relRestrict (mo (incWit s1)) (incCommittedSet s1)"
    unfolding relRestrict_def by auto 
  show ?thesis
    proof (cases rule: monStepE_mo2[OF monStep inv])
      case 1
      have "a \<notin> incCommittedSet s1" using monStep inv by auto
      hence "  relRestrict (mo (incWit s2)) (incCommittedSet s1)
             = relRestrict (mo (incWit s1)) (incCommittedSet s1)"
        using 1 by auto
      thus ?thesis using 1 s1 that by auto
    next
      case 2
      thus ?thesis using 2 s1 that by auto
    qed
qed

lemma monStepE_mo_pair [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
      and in_mo:   "(x, y) \<in> mo (incWit s2)"
  obtains "x \<in> actions0 pre" 
          "x \<in> incCommittedSet s1"
          "y \<in> actions0 pre"
          "y \<in> incCommittedSet s2"
          "y \<notin> incCommittedSet s1"
          "y = a"
          "x \<noteq> a"
          "loc_of x = loc_of y"
          "is_write x"
          "is_write y"
          "is_at_atomic_location (lk pre) x"
          "is_at_atomic_location (lk pre) y"
        | "(x, y) \<in> mo (incWit s1)"
          "x \<in> actions0 pre" 
          "x \<in> incCommittedSet s1"
          "y \<in> actions0 pre"
          "y \<in> incCommittedSet s1"
          "x \<noteq> y"
          "loc_of x = loc_of y"
          "is_write x"
          "is_write y"
          "is_at_atomic_location (lk pre) x"
          "is_at_atomic_location (lk pre) y"
proof -
  have cons_mo: "consistent_mo (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  show ?thesis
    proof (cases "(x, y) \<in> mo (incWit s1)")
      case True
      thus ?thesis
        using cons_mo in_mo that
        by auto
    next
      case False
      hence "mo (incWit s2) \<noteq> mo (incWit s1)"
        using in_mo by auto
      hence a:     "is_write a" "is_at_atomic_location (lk pre) a"
        and mo_s2: "mo (incWit s2) = mo (incWit s1) \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s1) a"           
        by (auto intro: monStepE_mo2[OF monStep inv])
      hence x: "x \<in> sameLocWritesSet (incCommitted s1) a" 
        and y: "y = a"
        using False in_mo by auto
      hence x2: "is_write x" 
                "x \<in> incCommittedSet s1" 
                "loc_of x = loc_of y" 
                "x \<in> actions0 pre"
        using inv by auto
      hence x3: "is_at_atomic_location (lk pre) x"
        using a y same_loc_atomic_location by metis
      have a2: "a \<in> incCommittedSet s2" 
               "a \<in> actions0 pre" 
               "a \<notin> incCommittedSet s1"
        using monStep inv by auto
      show ?thesis
        using a a2 x x2 x3 y that
        by auto
    qed
qed

subsubsection {* lo *}

lemma monStepE_lo [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
  obtains (lock)  "is_lock a \<or> is_unlock a" 
                  "lo (incWit s2) [\<in>] monAddToLo pre a s1"
        | (other) "\<not>is_lock a" 
                  "\<not>is_unlock a" 
                  "lo (incWit s2) = lo (incWit s1)"
using assms
unfolding monStep_def monPerformActions_def Let_def
by (cases a) auto

lemma monStepE_lo2 [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
  obtains (lock1) y 
    where "is_lock a \<or> is_unlock a" 
          "y \<in> sameLocLocksUnlocksSet (incCommitted s1) a"
          "lo (incWit s2) = insert (y, a) 
                                   (   lo (incWit s1) 
                                     \<union> (\<lambda>c. (c, a)) ` {c \<in> sameLocLocksUnlocksSet (incCommitted s1) a. (c, y) \<in> lo (incWit s1)}
                                     \<union> Pair a ` {c \<in> sameLocLocksUnlocksSet (incCommitted s1) a. (y, c) \<in> lo (incWit s1)}
                                   )"
        | (lock2) "is_lock a \<or> is_unlock a" 
                  "lo (incWit s2) = lo (incWit s1) \<union> Pair a ` (sameLocLocksUnlocksSet (incCommitted s1) a)"
        | (other) "\<not>is_lock a" 
                  "\<not>is_unlock a" 
                  "lo (incWit s2) = lo (incWit s1)"
proof (cases rule: monStepE_lo[OF monStep])
  case 1
  show ?thesis
    using that 1(1)
    by (cases rule: monAddToLoE[OF 1(2)]) auto
next
  case 2
  thus ?thesis using that by auto
qed

lemma monStepE_lo3 [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  obtains "lo (incWit s1) = relRestrict (lo (incWit s2)) (incCommittedSet s1)"
proof -
  have cons_lo: "locks_only_consistent_lo (preRestrict pre (incCommittedSet s1), 
                                           incWit s1, 
                                           [(''hb'', getHb (preRestrict pre (incCommittedSet s1)) (incWit s1))])"
    using inv by auto
  hence s1: "lo (incWit s1) = relRestrict (lo (incWit s1)) (incCommittedSet s1)" by auto
  show ?thesis
    proof (cases rule: monStepE_lo2[OF monStep])
      case 1
      have "a \<notin> incCommittedSet s1" using monStep inv by auto
      hence "  relRestrict (lo (incWit s2)) (incCommittedSet s1)
             = relRestrict (lo (incWit s1)) (incCommittedSet s1)"
        using 1 by auto
      thus ?thesis using 1 s1 that by auto
    next
      case 2
      have "a \<notin> incCommittedSet s1" using monStep inv by auto
      hence "  relRestrict (lo (incWit s2)) (incCommittedSet s1)
             = relRestrict (lo (incWit s1)) (incCommittedSet s1)"
        unfolding 2(2) by auto
      thus ?thesis using 2 s1 that by auto
    next
      case 3
      thus ?thesis using s1 that by auto
    qed
qed

lemma monStepE_lo_pair [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
      and in_lo:   "(x, y) \<in> lo (incWit s2)"
  obtains "(x, y) \<notin> lo (incWit s1)"
          "x \<in> actions0 pre" 
          "x \<in> incCommittedSet s2"
          "x \<notin> incCommittedSet s1"
          "y \<in> actions0 pre"
          "y \<in> incCommittedSet s1"
          "x = a"
          "y \<noteq> a"
          "loc_of x = loc_of y"
          "is_lock x \<or> is_unlock x"
          "is_lock y \<or> is_unlock y"
          "is_at_mutex_location (lk pre) x"
          "is_at_mutex_location (lk pre) y"
        | "(x, y) \<notin> lo (incWit s1)"
          "x \<in> actions0 pre" 
          "x \<in> incCommittedSet s1"
          "y \<in> actions0 pre"
          "y \<in> incCommittedSet s2"
          "y \<notin> incCommittedSet s1"
          "y = a"
          "x \<noteq> a"
          "loc_of x = loc_of y"
          "is_lock x \<or> is_unlock x"
          "is_lock y \<or> is_unlock y"
          "is_at_mutex_location (lk pre) x"
          "is_at_mutex_location (lk pre) y"
        | "(x, y) \<in> lo (incWit s1)"
          "x \<in> actions0 pre" 
          "x \<in> incCommittedSet s1"
          "y \<in> actions0 pre"
          "y \<in> incCommittedSet s1"
          "x \<noteq> y"
          "x \<noteq> a"
          "y \<noteq> a"
          "loc_of x = loc_of y"
          "is_lock x \<or> is_unlock x"
          "is_lock y \<or> is_unlock y"
          "is_at_mutex_location (lk pre) x"
          "is_at_mutex_location (lk pre) y"
proof -

  have cons_lo: "locks_only_consistent_lo (preRestrict pre (incCommittedSet s1), 
                                           incWit s1, 
                                           [(''hb'', getHb (preRestrict pre (incCommittedSet s1)) (incWit s1))])"
    using inv by auto
  have loc_kinds: "actions_respect_location_kinds (actions0 pre) (lk pre)"
    using inv by auto
  have a2: "a \<in> incCommittedSet s2" 
           "a \<in> actions0 pre" 
           "a \<notin> incCommittedSet s1"
    using monStep inv by auto
  show ?thesis
    proof (cases "(x, y) \<in> lo (incWit s1)")
      case True
      hence "x \<in> incCommittedSet s1" "y \<in> incCommittedSet s1" using cons_lo by auto
      hence "x \<noteq> a" "y \<noteq> a" using monStep inv by auto
      thus ?thesis 
        using True cons_lo that(3) by auto
    next
      case False
      hence "lo (incWit s2) \<noteq> lo (incWit s1)"
        using in_lo by auto
      thus ?thesis
        proof (cases rule: monStepE_lo2[OF monStep])
          case (1 z)
          hence z: "z \<in> actions0 pre" using inv by auto
          hence loc_z: "is_at_mutex_location (lk pre) z" 
            using loc_kinds 1(2)
            unfolding actions_respect_location_kinds_def is_at_mutex_location_def
            by (cases z) auto
          hence loc_a: "is_at_mutex_location (lk pre) a"
            using 1(2) unfolding is_at_mutex_location_def by auto
          show ?thesis 
            using 1(3) in_lo False 
            proof auto
              assume "y = a" "x = z"
              have "y \<notin> incCommittedSet s1" using `y = a` monStep inv by auto
              hence "(x, y) \<notin> lo (incWit s1)" using cons_lo by auto
              thus ?thesis 
                using a2 1(1) 1(2) z loc_z loc_a that(2) `y = a` `x = z`
                unfolding sameLocLocksUnlocksSet_def
                by auto
            next
              assume xy: "y = a" "x \<in> sameLocLocksUnlocksSet (incCommitted s1) a"
              hence x2: "x \<in> actions0 pre" "is_at_mutex_location (lk pre) x" 
                using inv loc_a unfolding is_at_mutex_location_def by auto
              have "y \<notin> incCommittedSet s1" using `y = a` monStep inv by auto
              hence "(x, y) \<notin> lo (incWit s1)" using cons_lo by auto
              thus ?thesis 
                using xy x2 a2 1(1) loc_a that(2)
                unfolding sameLocLocksUnlocksSet_def
                by auto
            next
              assume xy: "x = a" "y \<in> sameLocLocksUnlocksSet (incCommitted s1) a"
              hence y2: "y \<in> actions0 pre" "is_at_mutex_location (lk pre) y" 
                using inv loc_a unfolding is_at_mutex_location_def by auto
              have "x \<notin> incCommittedSet s1" using `x = a` monStep inv by auto
              hence "(x, y) \<notin> lo (incWit s1)" using cons_lo by auto
              thus ?thesis 
                using xy y2 a2 1(1) loc_a that(1)
                unfolding sameLocLocksUnlocksSet_def
                by auto
            qed
        next
          case 2
          hence xy: "x = a" "y \<in> sameLocLocksUnlocksSet (incCommitted s1) a"
            using False in_lo by auto
          hence loc_a: "is_at_mutex_location (lk pre) a"
            using a2 2(1) loc_kinds
            unfolding actions_respect_location_kinds_def is_at_mutex_location_def
            by (cases a) auto
          hence y2: "y \<in> actions0 pre" "is_at_mutex_location (lk pre) y" 
            using xy inv unfolding is_at_mutex_location_def by auto
          have "x \<notin> incCommittedSet s1" using `x = a` monStep inv by auto
          hence "(x, y) \<notin> lo (incWit s1)" using cons_lo by auto
          thus ?thesis 
            using xy y2 a2 2(1) loc_a that(1)
            unfolding sameLocLocksUnlocksSet_def
            by auto
        qed simp
    qed
qed

subsubsection {* sc *}

lemma monStepE_sc [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
  obtains (sc)    "is_seq_cst a" 
                  "sc (incWit s2) [\<in>] monAddToSc pre a s1"
        | (other) "\<not>is_seq_cst a" 
                  "sc (incWit s2) = sc (incWit s1)"
using assms
unfolding monStep_def monPerformActions_def Let_def 
apply (cases a, auto)
by (cases "is_seq_cst a", auto)+

subsubsection {* tot *}

lemma monStepE_tot [elim?]:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
  obtains "tot (incWit s2) = tot (incWit s1)"
unfolding incToEx_def Let_def tot_empty.simps
using monStep
unfolding monStep_def monPerformActions_def Let_def
by (cases a) auto

subsection {* Simps of checkXxx predicates *}

lemma monCheckWitRestrict_simp [simp]:
  shows "  x [\<in>] monCheckWitRestrict wit1 committed wit2
         = (incWitRestrict wit1 committed = wit2)"
unfolding monCheckWitRestrict_def
by simp

lemma monCheckCommitmentOrder_simp [simp]:
  shows "  x [\<in>] monCheckCommitmentOrder pre wit committed a
         = (respectsCom (actions0 pre) committed (incComAlt pre wit) a)"
unfolding monCheckCommitmentOrder_def Let_def
by simp

subsection {* Soundness *}

subsubsection {* tot_empty *}

lemma monStep_tot_empty:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "tot_empty (incToEx pre s2)"
proof -
  have "tot (incWit s1) = {}"
    using inv by auto
  thus ?thesis
    using monStepE_tot[OF monStep]
    unfolding tot_empty.simps Let_def incToEx_def
    by auto
qed

subsubsection {* well_formed_threads_opsem *}

lemma monStep_well_formed_threads_opsem:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "well_formed_threads_opsem (incToEx pre s2)"
proof -
  have "well_formed_threads_opsem (pre, empty_witness, [])"
    using inv by auto
  hence "well_formed_threads_opsem (preRestrict pre (incCommittedSet s2), empty_witness, [])"
    using well_formed_threads_opsem_restriction by auto
  thus ?thesis
    unfolding incToEx_def Let_def
    by (cases "incWit s2 = empty_witness") auto
qed

subsubsection {* well_formed_rf *}

lemma monStep_well_formed_rf_aux:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
      and rf:      "rf (incWit s2) = rf (incWit s1)"
  shows   "well_formed_rf (incToEx pre s2)"
proof -
  have cons_rf: "well_formed_rf (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv unfolding incToEx_def Let_def by auto
  have com: "incCommitted s2 = a#(incCommitted s1)"
    using monStep by auto
  show ?thesis
    unfolding incToEx_def Let_def well_formed_rf.simps 
    unfolding com rf
    using cons_rf
    by auto
qed

lemma well_formed_rfIE:
  assumes cons_rf:  "well_formed_rf (pre, wit, rel)"
      and rf:       "rf wit' = insert (w, r) (rf wit)"
      and actions:  "actions0 pre' \<supseteq> actions0 pre"
      and r_and_w:  "w \<in> actions0 pre'"
                    "r \<in> actions0 pre'"
                    "loc_of w = loc_of r"
                    "is_write w"
                    "is_read r"
                    "value_read_by r = value_written_by w"
      and r_is_new: "r \<notin> actions0 pre"
  shows   "well_formed_rf (pre', wit', rel')"
proof (intro well_formed_rfI)
  fix a b
  assume in_rf: "(a, b) \<in> rf wit'"
  thus "a \<in> actions0 pre'"
       "b \<in> actions0 pre'"
       "loc_of a = loc_of b"
       "is_write a"
       "is_read b"
       "value_read_by b = value_written_by a"
    unfolding rf using cons_rf r_and_w actions by auto
  fix a'
  assume in_rf': "(a', b) \<in> rf wit'"
  thus "a = a'"
    proof (cases "b = r")
      case True
      have "(a, r) \<notin> rf wit" "(a', r) \<notin> rf wit"
        using cons_rf r_is_new by auto
      hence "a = w" "a' = w"
        using in_rf in_rf' True unfolding rf by auto
      thus ?thesis by auto
    next
      case False
      hence "(a, b) \<in> rf wit" "(a', b) \<in> rf wit"
        using in_rf in_rf' unfolding rf by auto
      thus "a = a'"
        using cons_rf by auto
    qed
qed

lemma monStep_well_formed_rf:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "well_formed_rf (incToEx pre s2)"
proof -
  have cons_rf: "well_formed_rf (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv unfolding incToEx_def Let_def by auto
  have com: "incCommitted s2 = a#(incCommitted s1)"
    using monStep by auto
  have a: "a \<in> incCommittedSet s2" "a \<in> actions0 pre" "a \<notin> incCommittedSet s1"
    using monStep inv by auto
  show ?thesis
    proof (cases rule: monStepE_rf[OF monStep])
      case 1 (* load *)
      hence "is_read a" by (intro is_readI) auto
      show ?thesis
        proof (cases rule: monAddToRfLoadE[OF 1(2)])
          case (1 w) 
          hence wit: "rf (incWit s2) = insert (w, a) (rf (incWit s1))"
            by auto
          show ?thesis
            using cons_rf
            unfolding incToEx_def Let_def 
            apply (elim well_formed_rfIE[OF _ wit])
            using 1 com inv a `is_read a`
            by auto          
        next
          case 2 (* rf (incWit s2) = rf (incWit s1) *)
          thus ?thesis
            using monStep_well_formed_rf_aux monStep inv
            by metis
        qed
    next
      case 2 (* rmw *)
      hence "is_read a" by auto
      show ?thesis
        proof (cases rule: monAddToRfRmwE[OF 2(2)])
          case (1 w)
          hence wit: "rf (incWit s2) = insert (w, a) (rf (incWit s1))"
            by auto
          show ?thesis
            using cons_rf
            unfolding incToEx_def Let_def 
            apply (elim well_formed_rfIE[OF _ wit])
            (* assumption 1(2) criples auto, so we don't add it. *)
            using 1(1) 1(3) com inv a `is_read a`
            by auto
        next
          case 2 (* rf (incWit s2) = rf (incWit s1) *)
          thus ?thesis
            using monStep_well_formed_rf_aux monStep inv
            by metis
        qed
    next
      case 3 (* other *)
      thus ?thesis
        using monStep_well_formed_rf_aux monStep inv
        by metis
    qed
qed

subsubsection {* consistent_mo *}

lemma monStep_consistent_mo:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "consistent_mo (incToEx pre s2)"
unfolding incToEx_def Let_def
proof (intro consistent_moI, simp_all)
  have cons_mo: "consistent_mo (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  have a: "a \<notin> incCommittedSet s1" "a \<in> actions0 pre"
    using monStep inv by auto
  fix x y
  assume in_mo_s2: "(x, y) \<in> mo (incWit s2)"
  show "sameLocAtWrites (preRestrict pre (incCommittedSet s2)) x y"
    unfolding sameLocAtWrites_def
    using a monStep
    by (cases rule: monStepE_mo_pair[OF monStep inv in_mo_s2]) auto
  fix z
  assume yz_in_mo_s2: "(y, z) \<in> mo (incWit s2)"
  have z: "is_write z" "is_at_atomic_location (lk pre) z"
    using monStepE_mo_pair[OF monStep inv yz_in_mo_s2] by auto
  hence z2: "is_store z \<or> is_RMW z"
    by (cases z) auto
  have "y \<in> incCommittedSet s1" "loc_of y = loc_of z"
    using monStepE_mo_pair[OF monStep inv yz_in_mo_s2] by auto
  hence x: "x \<in> incCommittedSet s1" 
           "(x, y) \<in> mo (incWit s1)"
           "x \<in> actions0 pre"
           "is_write x"
           "loc_of x = loc_of z"
    using monStepE_mo_pair[OF monStep inv in_mo_s2] by auto
  hence x2: "x \<in> sameLocWritesSet (incCommitted s1) z"
    unfolding sameLocWrites_def by auto
  show "(x, z) \<in> mo (incWit s2)"
    proof (cases "z = a")
      assume "z = a"
      hence "  mo (incWit s2)
             = mo (incWit s1) \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s1) a"
        using z z2 monStepE_mo2[OF monStep inv] by metis
      thus ?thesis using x2 `z = a` by auto
    next
      assume "z \<noteq> a"
      hence "(y, z) \<in> mo (incWit s1)"
        using monStepE_mo_pair[OF monStep inv yz_in_mo_s2] by auto
      hence "(x, z) \<in> mo (incWit s1)"
        using x cons_mo
        unfolding consistent_mo.simps trans_def
        by metis
      thus ?thesis
        using monStepE_mo2[OF monStep inv] by fast
    qed
next
  have cons_mo: "consistent_mo (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  fix x y
  assume xy: "x \<in> actions0 pre \<and> x \<in> incCommittedSet s2"
             "y \<in> actions0 pre \<and> y \<in> incCommittedSet s2"
             "x \<noteq> y"
             "loc_of x = loc_of y"
             "is_write x"
             "is_write y"
             "is_at_atomic_location (lk pre) x"
             "is_at_atomic_location (lk pre) y"
  hence x2: "is_store x \<or> is_RMW x"
    by (cases x) auto
  have y2: "is_store y \<or> is_RMW y" 
    using xy by (cases y) auto
  show "(x, y) \<in> mo (incWit s2) \<or> (y, x) \<in> mo (incWit s2)"
    proof (cases "x = a")
      assume "x = a"
      hence mo_s2: "  mo (incWit s2)
                    = mo (incWit s1) \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s1) a"
        using xy x2 monStepE_mo2[OF monStep inv] by metis
      have "y \<in> incCommittedSet s1"
        using xy `x = a` monStep by auto
      hence "y \<in> sameLocWritesSet (incCommitted s1) x"
        using xy unfolding sameLocWrites_def by auto
      hence "(y, x) \<in> mo (incWit s2)"
        using `x = a` mo_s2 by auto
      thus ?thesis by auto
    next
      assume "x \<noteq> a"
      have x3: "x \<in> incCommittedSet s1"
        using xy `x \<noteq> a` monStep by auto
      show ?thesis
        proof (cases "y = a")
          assume "y = a"
          hence mo_s2: "  mo (incWit s2)
                        = mo (incWit s1) \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s1) a"
            using xy y2 monStepE_mo2[OF monStep inv] by metis
          have "x \<in> incCommittedSet s1"
            using xy `y = a` monStep by auto
          hence "x \<in> sameLocWritesSet (incCommitted s1) y"
            using xy unfolding sameLocWrites_def by auto
          hence "(x, y) \<in> mo (incWit s2)"
            using `y = a` mo_s2 by auto
          thus ?thesis by auto
        next
          assume "y \<noteq> a"
          have y3: "y \<in> incCommittedSet s1"
            using xy `y \<noteq> a` monStep by auto
          have "(x, y) \<in> mo (incWit s1) \<or> (y, x) \<in> mo (incWit s1)"
            using cons_mo xy x3 y3
            unfolding consistent_mo.simps
            by auto
          thus ?thesis
            using monStepE_mo2[OF monStep inv] by fast
        qed
    qed
qed

subsubsection {* rmw_atomicity *}

lemma monStep_rmw_atomicity:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "rmw_atomicity (incToEx pre s2)"
unfolding incToEx_def Let_def
proof (intro rmw_atomicityI, clarsimp)
  have cons_rf: "well_formed_rf (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  have cons_mo: "consistent_mo (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  have cons_rmw: "rmw_atomicity (preRestrict pre (incCommittedSet s1), incWit s1, [])"
    using inv by auto
  have com: "incCommitted s2 = a#(incCommitted s1)"
    using monStep by auto
  fix w r
  assume w: "w \<in> actions0 pre" "w \<in> incCommittedSet s2"
     and r: "r \<in> actions0 pre" "r \<in> incCommittedSet s2" "is_RMW r"
  have a: "a \<notin> incCommittedSet s1" "a \<in> actions0 pre"
    using monStep inv by auto
  hence "(a, r) \<notin> rf (incWit s1)"
    using cons_rf by auto
  hence "(a, r) \<notin> rf (incWit s2)"
    using a
    by (cases rule: monStepE_rf2[OF monStep]) auto
  have "(a, r) \<notin> mo (incWit s1)"
    using a cons_mo by auto
  hence "(a, r) \<notin> mo (incWit s2)"
    using a
    by (cases rule: monStepE_mo2[OF monStep inv]) auto
  have "(w, a) \<notin> rf (incWit s1)"
    using a cons_rf by auto
  show "adjacent_less_than (mo (incWit s2)) (actions0 pre \<inter> incCommittedSet s2) w r 
        = ((w, r) \<in> rf (incWit s2))"
    proof (cases "w = a")
      assume "w = a"
      have "\<not>adjacent_less_than (mo (incWit s2)) (actions0 pre \<inter> incCommittedSet s2) a r "
        using `(a, r) \<notin> mo (incWit s2)` by auto
      thus ?thesis
        using `(a, r) \<notin> rf (incWit s2)` `w = a` by auto
    next
      assume "w \<noteq> a"
      hence w2: "w \<in> incCommittedSet s1"
        using w monStep by auto
      show ?thesis
        proof (cases "r = a")
          assume "r \<noteq> a"
          hence r2: "r \<in> incCommittedSet s1"
            using r monStep by auto
          have mo_eq: "((w, r) \<in> mo (incWit s1)) = ((w, r) \<in> mo (incWit s2))"
            using w w2 r r2 by (cases rule: monStepE_mo3[OF monStep inv]) auto       
          have "  (\<exists>z\<in>actions0 pre \<inter> incCommittedSet s2. 
                       (w, z) \<in> mo (incWit s2) \<and> (z, r) \<in> mo (incWit s2))
                 = (\<exists>z\<in>actions0 pre \<inter> incCommittedSet s1. 
                       (w, z) \<in> mo (incWit s1) \<and> (z, r) \<in> mo (incWit s1))"
            unfolding com
            using `(a, r) \<notin> mo (incWit s2)` w2 r2
            by (cases rule: monStepE_mo3[OF monStep inv]) auto
          hence "  adjacent_less_than (mo (incWit s2)) (actions0 pre \<inter> incCommittedSet s2) w r
                = adjacent_less_than (mo (incWit s1)) (actions0 pre \<inter> incCommittedSet s1) w r"
            unfolding adjacent_less_than_def using mo_eq by auto
          also have "... = ((w, r) \<in> rf (incWit s1))"
            using cons_rmw w w2 r r2 by auto
          also have "... = ((w, r) \<in> rf (incWit s2))"
            using `r \<noteq> a`
            by (cases rule: monStepE_rf2[OF monStep]) auto
          finally show ?thesis .
        next
          assume "r = a"
          hence "is_RMW a" using r by auto
          hence mo_s2: "  mo (incWit s2)
                        = mo (incWit s1) \<union> (\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s1) a"
             by (cases rule: monStepE_mo2[OF monStep inv]) auto
          have rmw_step: "rf (incWit s2) [\<in>] monAddToRfRmw pre a s1"
            using `is_RMW a`
            by (cases rule: monStepE_rf[OF monStep], cases a) auto
          show ?thesis
            proof (cases "w \<in> sameLocWritesSet (incCommitted s1) a")
              assume w_not_same_loc: "w \<notin> sameLocWritesSet (incCommitted s1) a"
              hence "(w, a) \<notin> rf (incWit s2)"
                using `(w, a) \<notin> rf (incWit s1)` 
                by (cases rule: monAddToRfRmwE[OF rmw_step]) auto
              have "(w, a) \<notin> mo (incWit s1)"
                using a cons_mo by auto
              hence "(w, a) \<notin> mo (incWit s2)"
                 using w_not_same_loc mo_s2 by auto
              hence "\<not> adjacent_less_than (mo (incWit s2)) (actions0 pre \<inter> incCommittedSet s2) w a"
                 by auto                 
              thus ?thesis 
                using `r = a` `(w, a) \<notin> rf (incWit s2)` by auto
            next
              assume w_same_loc: "w \<in> sameLocWritesSet (incCommitted s1) a"
              then obtain w' where w':     "w' \<in> sameLocWritesSet(incCommitted s1) a"
                               and w'_max: "\<forall>w''\<in>sameLocWritesSet (incCommitted s1) a. 
                                                  (w', w'') \<notin> mo (incWit s1)"
                               and rf_s2:  "rf (incWit s2) = insert (w', a) (rf (incWit s1))"
                by (cases rule: monAddToRfRmwE[OF rmw_step]) auto
              have w'_a_in_mo: "(w', a) \<in> mo (incWit s2)"
                using w' mo_s2 by auto
              show ?thesis
                proof (cases "w = w'")
                  assume "w = w'"
                  have "adjacent_less_than (mo (incWit s2)) (actions0 pre \<inter> incCommittedSet s2) w' a"
                    unfolding adjacent_less_than_def
                    using w'_a_in_mo
                    proof auto
                      fix z
                      assume "(z, a) \<in> mo (incWit s2)"
                      moreover have "(z, a) \<notin> mo (incWit s1)"
                        using a cons_mo by auto
                      ultimately have "z \<in> sameLocWritesSet (incCommitted s1) a"
                        using mo_s2 by auto
                      hence "(w', z) \<notin> mo (incWit s1)" "z \<noteq> a"
                        using w'_max a by auto
                      hence "(w', z) \<notin> mo (incWit s2)"
                        using mo_s2 by auto
                      moreover assume "(w', z) \<in> mo (incWit s2)"
                      ultimately show False by simp
                    qed
                  thus ?thesis using rf_s2 `r = a` `w = w'` by auto
                next
                  assume "w \<noteq> w'"
                  hence "(w, a) \<notin> rf (incWit s2)"
                    using rf_s2 `(w, a) \<notin> rf (incWit s1)` by auto
                  have w'2: "w' \<in> actions0 pre" 
                            "w' \<in> incCommittedSet s1"
                            "is_write w'"
                            "loc_of w' = loc_of a"
                    using w' inv by auto
                  have w2: "w \<in> actions0 pre" 
                           "w \<in> incCommittedSet s1"
                           "is_write w"
                           "loc_of w = loc_of a"
                    using w_same_loc inv by auto
                  have "is_at_atomic_location (lk pre) a"
                    using is_RMWE_location_kind[OF `is_RMW a` ]
                    using inv a
                    by auto
                  hence "is_at_atomic_location (lk pre) w" 
                    using w2 same_loc_atomic_location by metis
                  hence "(w, w') \<in> mo (incWit s1) \<or> (w', w) \<in> mo (incWit s1)"
                    using cons_mo w2 w'2 `w \<noteq> w'` 
                    unfolding consistent_mo.simps
                    by auto
                  hence "(w, w') \<in> mo (incWit s1)" 
                    using w'_max w_same_loc by auto
                  hence "(w, w') \<in> mo (incWit s2)" 
                    using mo_s2 by auto
                  hence "\<not> adjacent_less_than (mo (incWit s2)) (actions0 pre \<inter> incCommittedSet s2) w a"
                     unfolding adjacent_less_than_def
                     using w'_a_in_mo w'2 com
                     by auto
                  thus ?thesis using `(w, a) \<notin> rf (incWit s2)` `r = a` by auto
                qed
            qed
        qed
    qed
qed

subsubsection {* Invariant *}

lemma monStepInvariant:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "monInvariant pre s2"
proof -
  have finite: "finite (actions0 pre)"
    using inv by auto
  have committed: "incCommittedSet s2 \<subseteq> actions0 pre"
    using monStep finite inv
    unfolding monStep_def Let_def monInvariant_def 
    by auto
  have cons: "() [\<in>] monCheckConsistency (incToEx pre s2)"
    using monStep  
    unfolding monStep_def Let_def incToEx_def
    by auto
  hence "axsimpConsistentAlt (preRestrict pre (incCommittedSet s2)) (incWit s2)"
    using monStep_tot_empty[OF monStep inv]
    using monStep_well_formed_threads_opsem[OF monStep inv]
    using monStep_well_formed_rf[OF monStep inv]
    using monStep_consistent_mo[OF monStep inv]
    using monStep_rmw_atomicity[OF monStep inv]
    unfolding incToEx_def Let_def monCheckConsistency_def
    by (intro axsimpConsistentI) auto
  thus ?thesis
    using inv committed
    unfolding monInvariant_def
    by auto
qed

lemma monTraceInvariant:
  assumes monTrace: "monTrace pre s1 s2"
      and init:     "s1 = incInitialState pre"
  shows   "monInvariant pre s2"
using assms
proof induct
  case (monReflexive pre s)
  thus "monInvariant pre s"
    unfolding monInvariant_def
    by auto
next
  case (monStep pre x y z a)
  thus "monInvariant pre z"
    using monStepInvariant by auto
qed

subsubsection {* Soundness *}

lemma monStepSoundness:
  assumes monStep: "(a, s2) [\<in>] monStep pre s1"
      and inv:     "monInvariant pre s1"
  shows   "incStep pre s1 s2 a"
using monStep inv
using monStepInvariant[OF monStep inv]
unfolding monInvariant_def
          monStep_def Let_def incStep_def incToEx_def
by auto

lemma monTraceSoundness_aux:
  assumes monTrace: "monTrace pre s1 s2"
      and init:     "s1 = incInitialState pre"
  shows   "incTrace pre s1 s2"
using assms
proof induct
  case (monReflexive pre s)
  thus "incTrace pre s s"
    using incReflexive by auto
next
  case (monStep pre x y z a)
  hence "incStep pre y z a" 
    using monStepSoundness monTraceInvariant
    by auto
  thus "incTrace pre x z"
    using monStep incStep by auto
qed

corollary monTraceSoundness:
  assumes "monTrace pre (incInitialState pre) s"
  shows   "incTrace pre (incInitialState pre) s"
using assms monTraceSoundness_aux by simp

subsection {* Completeness *}

subsubsection {* modification order *}

lemma step_mo_not_atomic_write:
  assumes cons:      "axsimpConsistentAlt pre' wit'"
      and wit:       "(incWit s) = incWitRestrict wit' committed"
      and committed: "actions0 pre' = insert a committed"
      and a:         "is_at_non_atomic_location (lk pre') a \<or> \<not> is_write a"
  shows              "mo wit' = mo (incWit s)"
unfolding wit
proof auto
  fix b c
  assume in_mo: "(b, c) \<in> mo wit'"
  hence b: "b \<in> actions0 pre' \<and> is_at_atomic_location (lk pre') b \<and> is_write b" 
    and c: "c \<in> actions0 pre' \<and> is_at_atomic_location (lk pre') c \<and> is_write c"
    using cons by auto
  hence "a \<noteq> b" "a \<noteq> c" using a by auto
  thus "b \<in> committed" "c \<in> committed" 
    using b c committed by auto
qed

lemma step_mo_atomic_write:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and wit:        "(incWit s) = incWitRestrict wit' (incCommittedSet s)"
      and committed:  "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed: "downclosed (incCommittedSet s) (mo wit')"
      and a:          "is_at_atomic_location (lk pre') a"
                      "is_write a"
                      "a \<in> actions0 pre'"
                      "a \<notin> incCommittedSet s"
  shows   "mo wit' [\<in>] monAddToMo pre a s"
unfolding monAddToMo_def Let_def
proof simp
  let ?succ     = "(\<lambda>b. (b, a)) ` sameLocWritesSet (incCommitted s) a"
  let ?new_mo   = "mo (incWit s) \<union> ?succ"
  show "mo wit' = ?new_mo"
    proof (intro equalityI subsetI)
      fix x
      assume "x \<in> mo wit'"
      then obtain b c where x:     "(b, c) = x" 
                        and in_mo: "(b, c) \<in> mo wit'" by (cases x) fast
      have "(b, c) \<in> ?new_mo"
        proof (cases "c = a")
        next
          assume "c = a"
          hence b: "is_write b" 
                   "loc_of b = loc_of a" 
                   "b \<in> actions0 pre'" 
                   "b \<noteq> a"
            using in_mo cons2 by auto
          hence "b \<in> incCommittedSet s" using committed by auto
          hence "b \<in> sameLocWritesSet (incCommitted s) a"
            unfolding sameLocWrites_def using b by auto
          thus "(b, c) \<in> ?new_mo" using `c = a` by simp
        next
          assume "c \<noteq> a"
          have "c \<in> actions0 pre'" using in_mo cons2 by auto
          hence c: "c \<in> incCommittedSet s" using committed `c \<noteq> a` by simp
          hence "b \<in> incCommittedSet s" 
            using downclosed in_mo by (auto elim: downclosedE)
          hence "(b, c) \<in> mo (incWit s)" using wit in_mo c by auto
          thus "(b, c) \<in> ?new_mo" by simp
        qed
      thus "x \<in> ?new_mo" using x by simp
    next
      fix x
      assume "x \<in> ?new_mo"
      then obtain b c where x:     "(b, c) = x" 
                        and in_mo: "(b, c) \<in> ?new_mo" by (cases x) fast
      have "(b, c) \<in> mo wit'"
        using in_mo
        proof (elim UnE)
          assume "(b, c) \<in> mo (incWit s)" 
          thus "(b, c) \<in> mo wit'" using wit by auto
        next
          assume "(b, c)  \<in> ?succ"
          thus ?thesis
            using sameLocInMo[OF _ cons2 committed downclosed a]
            by auto
        qed
      thus "x \<in> mo wit'" using x by simp
    qed
qed

subsubsection {* reads-from *}

lemma step_rf_aux:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and downclosed: "downclosed committed (rf wit')"
      and wit:        "wit = incWitRestrict wit' committed"
      and committed:  "actions0 pre' = insert a committed"
      and in_rf:      "(b, c) \<in> rf wit'"
  shows               "(b, c) \<in> rf wit \<or> (c = a)"
proof (intro disjCI)
  assume "c \<noteq> a"
  have "b \<in> actions0 pre'" "c \<in> actions0 pre'"
    using in_rf cons2 by auto
  hence b: "b \<in> insert a committed" 
    and c: "c \<in> committed"
    using `c \<noteq> a` committed by auto
  hence "b \<in> committed" 
    using in_rf downclosed
    unfolding downclosed_def 
    by auto
  hence "(b, c) \<in> rf (incWitRestrict wit' committed)" 
    using in_rf c by simp
  thus "(b, c) \<in> rf wit" using wit by simp
qed  

lemma step_rf_aux2:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and downclosed: "downclosed committed (rf wit')"
      and wit:        "wit = incWitRestrict wit' committed"
      and committed:  "actions0 pre' = insert a committed"
  obtains         "rf wit' = rf wit"
        | w where "rf wit' = insert (w, a) (rf wit)"
proof (cases "rf wit' = rf wit")
  case True
  thus ?thesis using that by auto
next
  case False
  have "rf wit \<subseteq> rf wit'"
    using wit by auto
  then obtain x y where in_rf:  "(x, y) \<in> rf wit'" 
                    and nin_rf: "(x, y) \<notin> rf wit"
    using False by auto
  hence "(x, a) \<in> rf wit'" 
    using step_rf_aux[OF cons2 downclosed wit committed]
    by auto
  hence "rf wit' = insert (x, a) (rf wit)"
    using `rf wit \<subseteq> rf wit'`
    proof auto
      fix u v
      assume "(u, v) \<in> rf wit'" "(u, v) \<notin> rf wit"
      thus "v = a"
        using step_rf_aux[OF cons2 downclosed wit committed] by auto
      thus "u = x"
        using `(x, a) \<in> rf wit'` `(u, v) \<in> rf wit'`
        using cons2
        by auto
    qed
  thus ?thesis using that by auto
qed

lemma step_rf_non_read:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and downclosed: "downclosed committed (rf wit')"
      and wit:        "wit = incWitRestrict wit' committed"
      and committed:  "actions0 pre' = insert a committed"
      and a:          "\<not> is_read a" "a \<notin> committed"
  shows               "rf wit' = rf wit"
proof (cases rule: step_rf_aux2[OF cons2 downclosed wit committed])
  case (2 w)
  hence "(w, a) \<in> rf wit'" by simp
  hence "is_read a" using cons2 by auto
  hence False using a by auto
  thus ?thesis by simp
qed 

lemma step_rf_auxAddPairToRf:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and downclosed: "downclosed (set committed) (rf wit')"
      and wit:        "wit = incWitRestrict wit' (set committed)"
      and committed:  "actions0 pre' = insert a (set committed)"
      and a:          "a \<notin> (set committed)"
      and in_rf:      "(w, a) \<in> rf wit'"
  obtains value0
          where "w \<in> sameLocWritesSet committed a"
                "(rf wit', value0, value0) [\<in>] auxAddPairToRf (rf wit) w a"
proof -
  have "is_write w" using in_rf cons2 by auto
  then obtain value_w where value_w: "value_written_by w = Some value_w"
    by (cases w) auto
  have "is_read a" using in_rf cons2 by auto
  then obtain value_a where value_a: "value_read_by a = Some value_a"
    by (cases a) auto
  have "value_read_by a = value_written_by w"
    using in_rf cons2 
    (* For some reason, auto can't find the proof unless we increase the bounds, or unfold the
    definition. *)  
    unfolding axsimpConsistentAlt_def 
    by auto
  hence "value_w = value_a"
    using value_w value_a by auto
  have "rf wit' = insert (w, a) (rf wit)"
    using in_rf
    proof auto
      fix b c
      assume "(b, c) \<in> rf wit"
      thus "(b, c) \<in> rf wit'" using wit by auto
    next
      fix b c
      assume bc_in_rf2:  "(b, c) \<in> rf wit'"
         and bc_nin_rf1: "(b, c) \<notin> rf wit"
      have "(b, c) \<in> rf wit \<or> (c = a)"
        using step_rf_aux[OF cons2 downclosed wit committed bc_in_rf2] .
      thus "c = a" using bc_nin_rf1 by simp
      thus "b = w" using bc_in_rf2 cons2 in_rf by auto
    qed
  hence inAddPair: "(rf wit', value_w, value_w) [\<in>] auxAddPairToRf (rf wit) w a"
    using value_w value_a `value_w = value_a`
    unfolding auxAddPairToRf_def
    by simp
  have "w \<in> actions0 pre'" "w \<noteq> a"
    using in_rf cons2 
    apply (metis axsimpConsistentE well_formed_rfE)
    using in_rf cons2 
    by (metis axsimpConsistentE irreflRf)
  hence "w \<in> set committed" using committed by auto
  hence "w \<in> sameLocWritesSet committed a"
    unfolding sameLocWritesSet_def
    using in_rf cons2
    by auto
  thus thesis
    using that inAddPair by metis
qed

lemma step_rf_load:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and downclosed: "downclosed (incCommittedSet s) (rf wit')"
      and wit:        "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:  "actions0 pre' = insert a (incCommittedSet s)"
      and a:          "is_load a" "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
  shows               "rf wit' [\<in>] monAddToRfLoad pre a s"
proof (cases rule: step_rf_aux2[OF cons2 downclosed wit committed])
  case 1
  thus ?thesis
    unfolding monAddToRfLoad_def auxAddToRfLoad_def
    by auto
next
  case (2 x)
  then obtain value0 
        where "x \<in> sameLocWritesSet (incCommitted s) a"
              "(rf wit', value0, value0) [\<in>] auxAddPairToRf (rf (incWit s)) x a"
    using step_rf_auxAddPairToRf[OF cons2 downclosed wit committed a(3)]
    by auto
  thus ?thesis
    unfolding monAddToRfLoad_def auxAddToRfLoad_def
    by auto
qed

lemma step_rf_rmw:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and downclosed_mo: "downclosed (incCommittedSet s) (mo wit')"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and a:             "is_RMW a" "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
  shows                  "rf wit' [\<in>] monAddToRfRmw pre a s"
proof (cases "sameLocWrites (incCommitted s) a = []")
  case True
  hence "\<not> (\<exists>w. (w, a) \<in> rf wit')" 
    using step_rf_auxAddPairToRf[OF cons2 downclosed_rf wit committed a(3)]
    by auto
  hence "rf (incWit s) = rf wit'"
    using step_rf_aux2[OF cons2 downclosed_rf wit committed] by auto
  thus ?thesis
    unfolding monAddToRfRmw_def auxAddToRfRmw_def Let_def
    using True
    by auto
next
  let ?same_loc_writes = "sameLocWritesSet (incCommitted s) a"
  let ?S = "{w. w \<in> actions0 pre' \<and> (w, a) \<in> mo wit'}"
  have "actions_respect_location_kinds (actions0 pre') (lk pre')"
    using cons2 by auto
  hence a2: "is_at_atomic_location (lk pre') a" "is_write a"
    using a(1) is_RMWE_location_kind[OF a(1) a(2)] by auto
  have eq_sets: "?S = ?same_loc_writes"
    proof auto
      fix w'
      assume w': "w' \<in> sameLocWritesSet (incCommitted s) a"
      show ca_in_mo: "(w', a) \<in> mo wit'"
        using sameLocInMo[OF w' cons2 committed downclosed_mo] a a2
        by auto
      thus "w' \<in> actions0 pre'" using cons2 by auto
    next
      fix w'
      assume "w' \<in> actions0 pre'" "(w', a) \<in> mo wit'"
      thus "w' \<in> sameLocWritesSet (incCommitted s) a"
        unfolding sameLocWritesSet_def
        using committed cons2
        by auto
    qed
  case False
  then obtain w' where "w' \<in> ?same_loc_writes" by auto
  hence non_empty: "?S \<noteq> {}" using eq_sets by auto
  have "assumptions (pre', wit' , [])" 
    using cons2 by auto
  hence "finite_prefixes (mo wit') (actions0 pre')"
    unfolding assumptions.simps by simp
  hence finite: "finite ?S"
    unfolding finite_prefixes_def using a by fast
  hence "irrefl (mo wit') \<and> trans (mo wit')"
    using cons2 by auto
  hence isOrder: "isStrictPartialOrder (mo wit')" unfolding isStrictPartialOrder_def .
  obtain w where w:   "w \<in> ?S" 
             and max: "(\<forall>y. y \<in> ?S \<longrightarrow> (w, y) \<notin> mo wit')"
    using supremum_partial_order[OF finite non_empty isOrder] .
  have adjacent: "adjacent_less_than (mo wit') (actions0 pre') w a"
    using w max unfolding adjacent_less_than_def by auto
  hence in_rf: "(w, a) \<in> rf wit'"
    using cons2 a by auto
  then obtain value0 
        where w:  "w \<in> sameLocWritesSet (incCommitted s) a"
          and rf: "(rf wit', value0, value0) [\<in>] auxAddPairToRf (rf (incWit s)) w a"
    using step_rf_auxAddPairToRf[OF cons2 downclosed_rf wit committed a(3)] by auto
  have max: "\<forall>c\<in>sameLocWritesSet (incCommitted s) a. (w, c) \<notin> mo (incWit s)" 
    proof 
      fix c
      assume sameLoc: "c \<in> sameLocWritesSet (incCommitted s) a"
      have "actions_respect_location_kinds (actions0 pre') (lk pre')"
        using cons2 by auto
      hence "is_at_atomic_location (lk pre') a" "is_write a"
        using a(1) is_RMWE_location_kind[OF a(1) a(2)] by auto
      hence ca_in_mo: "(c, a) \<in> mo wit'"
        using sameLocInMo[OF sameLoc cons2 committed downclosed_mo] a
        by auto
      hence "c \<in> actions0 pre'" using cons2 by auto
      hence "(w, c) \<notin> mo wit'"
        using adjacent ca_in_mo unfolding adjacent_less_than_def by auto
      thus "(w, c) \<notin> mo (incWit s)" using wit by auto
    qed
  thus ?thesis
    unfolding monAddToRfRmw_def auxAddToRfRmw_def Let_def
    using w rf False
    by auto
qed

subsubsection {* sc-order*}

lemma step_sc_isnot_sc:
  assumes cons2:     "axsimpConsistentAlt pre' wit'"
      and wit:       "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed: "actions0 pre' = insert a (incCommittedSet s)"
      and n_sc:      "\<not> is_seq_cst a"
  shows              "sc wit'= sc (incWit s)"
proof auto
  fix b c
  assume "(b, c) \<in> sc (incWit s)"
  thus "(b, c) \<in> sc wit'" using wit by simp
next
  fix b c
  assume in_sc: "(b, c) \<in> sc wit'"
  hence "is_seq_cst b" "b \<in> actions0 pre'" 
        "is_seq_cst c" "c \<in> actions0 pre'"
     using cons2 by auto
  hence "b \<in> incCommittedSet s" "c \<in> incCommittedSet s"
     using cons2 n_sc in_sc committed by auto
  thus "(b, c) \<in> sc (incWit s)" 
    using cons2 committed in_sc wit by auto
qed

lemma step_sc_is_sc:
  assumes cons2:     "axsimpConsistentAlt pre' wit'"
      and wit:       "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed: "actions0 pre' = insert a (incCommittedSet s)"
      and a:         "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and is_sc:     "is_seq_cst a"
  shows              "sc wit' [\<in>] monAddToSc pre a s"
unfolding monAddToSc_def 
proof -
  let ?sc_list = "scActions (incCommitted s)"
  let ?sc_set  = "scActionsSet (incCommitted s)"
  show "sc wit' [\<in>] addToTransitiveOrder ?sc_list a (sc (incWit s))"
    proof (cases "\<exists>b. (b, a) \<in> sc wit'")
      assume max: "\<not> (\<exists>b. (b, a) \<in> sc wit')"
      have "sc wit' = sc (incWit s) \<union> Pair a ` ?sc_set"
        proof auto
          fix c
          assume "c \<in> scActionsSet (incCommitted s)"
          hence c: "c \<in> incCommittedSet s" "is_seq_cst c" "c \<in> actions0 pre'"
            using committed by auto
          hence "c \<noteq> a" using a by auto
          have "(c, a) \<notin> sc wit'" using max by auto
          thus "(a, c) \<in> sc wit'"
            using cons2 a(1) c is_sc `c \<noteq> a` by auto
        next
          fix b c
          assume "(b, c) \<in> sc (incWit s)"
          thus "(b, c) \<in> sc wit'" using wit by simp
        next
          fix b c
          assume in_sc: "(b, c) \<in> sc wit'"
             and not_new: "(b, c) \<notin> Pair a ` scActionsSet (incCommitted s)"
          have "c \<noteq> a" using in_sc max by auto
          have c: "is_seq_cst c" "c \<in> actions0 pre'" "b \<in> actions0 pre'"
            using cons2 in_sc by auto
          hence "c \<in> incCommittedSet s"
            using `c \<noteq> a` committed by auto
          hence "c \<in> scActionsSet (incCommitted s)"
            unfolding scActionsSet_def
            using c by auto
          hence "b \<noteq> a" using not_new by auto
          hence "b \<in> incCommittedSet s"
            using committed `b \<in> actions0 pre'` by auto          
          thus "(b, c) \<in> sc (incWit s)" 
            using wit in_sc `c \<in> incCommittedSet s` by auto
        qed
      thus ?thesis unfolding addToTransitiveOrder_def by auto
    next
      assume "\<exists>b'. (b', a) \<in> sc wit'"
      then obtain b' where b': "(b', a) \<in> sc wit'" by fast

      let ?sc_set2 = "{x. (x, a) \<in> sc wit'}"
  
      have "b' \<in> ?sc_set2" using b' by simp
      hence non_empty: "?sc_set2 \<noteq> {}" by fast
      have "finite_prefixes (sc wit') (actions0 pre')"
        using cons2 by auto
      hence finite: "finite ?sc_set2"
        unfolding finite_prefixes_def using a by fast
      have irreflexive: "irrefl (sc wit')"
      and   transitive:  "trans (sc wit')"
        using cons2 by auto 
      hence isOrder: "isStrictPartialOrder (sc wit')" 
        unfolding isStrictPartialOrder_def by simp
      obtain b where b:   "b \<in> ?sc_set2" 
                 and max: "(\<forall>y. y \<in> ?sc_set2 \<longrightarrow> (b, y) \<notin> sc wit')"
        using supremum_partial_order[OF finite non_empty isOrder] by auto
      have b2: "b \<in> actions0 pre'" using b cons2 by auto
      hence b3: "b \<in> incCommittedSet s" "is_seq_cst b" "b \<noteq> a"
        using b committed cons2 by auto

      let ?prev = "(\<lambda>c. (c, a)) ` {x \<in> incCommittedSet s. is_seq_cst x \<and>
                                   (x, b) \<in> sc (incWit s)}"
      let ?succ = "(\<lambda>c. (a, c)) ` {x \<in> incCommittedSet s. is_seq_cst x \<and> 
                                   (b, x) \<in> sc (incWit s)}"

      have "sc (incWit s) \<subseteq> sc wit'" using wit by auto 
      moreover have "?prev \<subseteq> sc wit'"
        proof auto
          fix c
          assume "(c, b) \<in> sc (incWit s)"
          hence "(c, b) \<in> sc wit'" using wit by auto
          thus "(c, a) \<in> sc wit'" using transitive b transE by auto
        qed
      moreover have "?succ \<subseteq> sc wit'"
        proof auto
          fix c
          assume in_sc: "(b, c) \<in> sc (incWit s)"
          hence c: "c \<in> incCommittedSet s" 
                   "c \<in> actions0 pre'" 
                   "is_seq_cst c" 
            using cons2 wit a by auto
          have "(b, c) \<in> sc wit'" using in_sc wit by auto
          hence "(c, a) \<notin> sc wit'" using max c by auto
          thus "(a, c) \<in> sc wit'" 
            using cons2 c a is_sc by auto
        qed
      moreover have "sc wit' \<subseteq> sc (incWit s) \<union> {(b, a)} \<union> ?prev \<union> ?succ"
        proof auto
          fix c d
          assume in_sc2: "(c, d) \<in> sc wit'"
             and nin_sc1: "(c, d) \<notin> sc (incWit s)"
             and nin_prev: "(c, d) \<notin> ?prev"
             and nin_succ: "(c, d) \<notin> ?succ"
          have d: "is_seq_cst d" "d \<in> actions0 pre'" "d \<noteq> c"
            using cons2 in_sc2 by auto
          have c:  "is_seq_cst c" "c \<in> actions0 pre'" "d \<noteq> c"
            using cons2 in_sc2 by auto
          have "c \<noteq> a"
            proof
              assume "c = a"
              hence d2: "d \<in> incCommittedSet s" using d committed by simp
              have "(b, d) \<in> sc wit'" 
                using transE[OF transitive] b in_sc2 `c = a` by auto
              hence "(b, d) \<in> sc (incWit s)" using b3 d2 wit by auto
              hence "(c, d) \<in> ?succ" using d d2 `c = a` by auto
              thus False using nin_succ by simp
            qed
          hence c2: "c \<in> incCommittedSet s" using c committed by auto
          thus "d = a" 
            using d committed in_sc2 nin_sc1 wit by auto
          have bc_nin_sc: "(b, c) \<notin> sc wit'" using max c in_sc2 `d = a` by simp
          have "(c, b) \<notin> sc (incWit s)" using nin_prev `d = a` c c2 by auto
          hence "(c, b) \<notin> sc wit'" using b3 c2 wit by auto
          thus "c = b" 
            using cons2 bc_nin_sc b2 b3(2) c(1) c(2) by auto
        qed
      ultimately have "sc wit' = sc (incWit s) \<union> ?prev \<union> ?succ \<union> {(b, a)}" 
        using b by auto        
      thus ?thesis
        using b b3 
        unfolding addToTransitiveOrder_def scActionsSet_def
        by auto
    qed
qed

corollary step_sc:
  assumes cons2:     "axsimpConsistentAlt pre' wit'"
      and wit:       "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed: "actions0 pre' = insert a (incCommittedSet s)"
      and a:         "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
  shows              "if is_seq_cst a 
                      then sc wit' [\<in>] monAddToSc pre a s 
                      else sc wit' = sc (incWit s)"
proof (cases "is_seq_cst a")
  assume "is_seq_cst a"
  thus ?thesis 
    using step_sc_is_sc[OF cons2 wit committed] a by simp
next
  assume "\<not>is_seq_cst a"
  thus ?thesis 
    using step_sc_isnot_sc[OF cons2 wit committed] a by simp
qed

subsubsection {* lo-order *}

lemma step_lo_not_lock_unlock:
  assumes cons2:     "axsimpConsistentAlt pre' wit'"
      and wit:       "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed: "actions0 pre' = insert a (incCommittedSet s)"
      and a:         "a \<notin> incCommittedSet s \<and> \<not>is_lock a \<and> \<not>is_unlock a"
  shows              "lo wit' = lo (incWit s)"
proof (intro equalityI subsetI, auto)
  fix b c
  assume "(b, c) \<in> lo (incWit s)"
  thus "(b, c) \<in> lo wit'" using wit by simp
next
  fix b c
  assume in_lo: "(b, c) \<in> lo wit'"
  have "(is_lock b \<or> is_unlock b)" "b \<in> actions0 pre'" 
       "(is_lock c \<or> is_unlock c)" "c \<in> actions0 pre'"
    using cons2 in_lo by auto
  hence "b \<in> incCommittedSet s" "c \<in> incCommittedSet s"
     using cons2 a in_lo committed by auto
  thus "(b, c) \<in> lo (incWit s)"
    using cons2 wit committed in_lo by auto
qed


lemma step_lo_lock_unlock:
  assumes cons2:     "axsimpConsistentAlt pre' wit'"
      and wit:       "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed: "actions0 pre' = insert a (incCommittedSet s)"
      and a:         "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and is_lo_ulo: "is_lock a \<or> is_unlock a"
  shows              "lo wit' [\<in>] monAddToLo pre a s"
(* This lemma is an almost-clone of step_sc_is_sc. *)
unfolding monAddToLo_def
proof -
  let ?lo_list = "sameLocLocksUnlocks (incCommitted s) a"
  let ?lo_set  = "sameLocLocksUnlocksSet (incCommitted s) a"
  have "actions_respect_location_kinds (actions0 pre') (lk pre')"
    using cons2 by auto
  hence mutex: "is_at_mutex_location (lk pre') a"
    unfolding actions_respect_location_kinds_def is_at_mutex_location_def
    using a is_lo_ulo by (cases a) auto
  show "lo wit' [\<in>] addToTransitiveOrder ?lo_list a (lo (incWit s))"
    proof (cases "\<exists>b. (b, a) \<in> lo wit'")
      assume max: "\<not> (\<exists>b. (b, a) \<in> lo wit')"
      have "lo wit' = lo (incWit s) \<union> Pair a ` ?lo_set"
        proof auto
          fix c
          assume "c \<in> sameLocLocksUnlocksSet (incCommitted s) a"
          hence c: "c \<in> incCommittedSet s" 
                   "loc_of a = loc_of c" 
                   "is_lock c \<or> is_unlock c" 
                   "c \<in> actions0 pre'"
            using committed by auto
          hence "a \<noteq> c" using a by auto
          have "(c, a) \<notin> lo wit'" using max by auto
          thus "(a, c) \<in> lo wit'"
            using cons2 a(1) c is_lo_ulo `a \<noteq> c` mutex 
            by (auto elim: locks_only_consistent_loE2_inv)
          fix c
        next
          fix b c
          assume "(b, c) \<in> lo (incWit s)"
          thus "(b, c) \<in> lo wit'" using wit by simp
        next
          fix b c
          assume in_lo: "(b, c) \<in> lo wit'"
             and not_new: "(b, c) \<notin> Pair a ` ?lo_set"
          have "c \<noteq> a" using in_lo max by auto
          have c: "loc_of b = loc_of c" "is_lock c \<or> is_unlock c"
                  "c \<in> actions0 pre'" "b \<in> actions0 pre'"
            using cons2 in_lo by auto
          hence "c \<in> incCommittedSet s"
            using `c \<noteq> a` committed by auto
          hence "b \<noteq> a \<or> loc_of c \<noteq> loc_of a"
            using not_new
            unfolding sameLocLocksUnlocksSet_def
            using c by auto
          hence "b \<noteq> a" using c by auto
          hence "b \<in> incCommittedSet s"
            using committed `b \<in> actions0 pre'` by auto          
          thus "(b, c) \<in> lo (incWit s)" 
            using wit in_lo `c \<in> incCommittedSet s` by auto
        qed
      thus ?thesis unfolding addToTransitiveOrder_def by auto
    next
      assume "\<exists>b'. (b', a) \<in> lo wit'"
      then obtain b' where b': "(b', a) \<in> lo wit'" by fast

      let ?lo_set2 = "{x. (x, a) \<in> lo wit'}"
  
      have "b' \<in> ?lo_set2" using b' by simp
      hence non_empty: "?lo_set2 \<noteq> {}" by fast
      hence "finite_prefixes (lo wit') (actions0 pre')"
        using cons2 by auto
      hence finite: "finite ?lo_set2"
        unfolding finite_prefixes_def using a by fast
      hence irreflexive: "irrefl (lo wit')"
      and   transitive:  "trans (lo wit')"
        using cons2 by auto 
      hence isOrder: "isStrictPartialOrder (lo wit')" 
        unfolding isStrictPartialOrder_def by simp
      obtain b where b:   "b \<in> ?lo_set2"
                 and max: "(\<forall>y. y \<in> ?lo_set2 \<longrightarrow> (b, y) \<notin> lo wit')"
        using supremum_partial_order[OF finite non_empty isOrder] by auto
      have b2: "b \<in> actions0 pre'" using b cons2 by auto
      hence b3: "b \<in> incCommittedSet s" "b \<noteq> a" "loc_of b = loc_of a" 
               "is_lock b \<or> is_unlock b" "is_at_mutex_location (lk pre') b"
        using b cons2 unfolding committed by auto

      let ?prev = "(\<lambda>c. (c, a)) ` {x \<in> ?lo_set. (x, b) \<in> lo (incWit s)}"
      let ?succ = "(\<lambda>c. (a, c)) ` {x \<in> ?lo_set. (b, x) \<in> lo (incWit s)}"

      have "lo (incWit s) \<subseteq> lo wit'" using wit by auto 
      moreover have "?prev \<subseteq> lo wit'" 
        proof clarify
          fix c
          assume "(c, b) \<in> lo (incWit s)"
          hence "(c, b) \<in> lo wit'" using wit by auto
          thus "(c, a) \<in> lo wit'" using transitive b transE by auto
        qed
      moreover have "?succ \<subseteq> lo wit'"
        proof auto
          fix c
          assume sameLoc: "c \<in> sameLocLocksUnlocksSet (incCommitted s) a"
          assume in_sc: "(b, c) \<in> lo (incWit s)"
          hence c: "c \<in> actions0 pre'" 
                   "c \<in> incCommittedSet s" 
                   "loc_of a = loc_of c" 
                   "is_lock c \<or> is_unlock c"
            using cons2 wit a sameLoc by auto
          have "(b, c) \<in> lo wit'" using in_sc wit by auto
          hence "(c, a) \<notin> lo wit'" using max c by auto
          thus "(a, c) \<in> lo wit'" 
            using sameLoc cons2 c a is_lo_ulo mutex
            by (auto elim: locks_only_consistent_loE2_inv)
        qed
      moreover have "lo wit' \<subseteq> lo (incWit s) \<union> {(b, a)} \<union> ?prev \<union> ?succ"
        proof auto
          fix c d
          assume in_lo2: "(c, d) \<in> lo wit'"
             and nin_lo1: "(c, d) \<notin> lo (incWit s)"
             and nin_prev: "(c, d) \<notin> ?prev"
             and nin_succ: "(c, d) \<notin> ?succ"
          have d: "d \<in> actions0 pre'" "d \<noteq> c" 
                  "loc_of c = loc_of d" "is_lock d \<or> is_unlock d"
            using cons2 in_lo2 by auto
          have c: "c \<in> actions0 pre'" "d \<noteq> c" 
                  "loc_of c = loc_of d" "is_lock c \<or> is_unlock c"
            using cons2 in_lo2 by auto
          have "c \<noteq> a"
            proof
              assume "c = a"
              hence d2: "d \<in> incCommittedSet s" using d committed by simp
              have "(b, d) \<in> lo wit'" 
                using transE[OF transitive] b in_lo2 `c = a` by auto
              hence "(b, d) \<in> lo (incWit s)" using b3 d2 wit by auto
              hence "(c, d) \<in> ?succ" 
                unfolding sameLocLocksUnlocksSet_def
                using d d2 `c = a` 
                by auto
              thus False using nin_succ by simp
            qed
          hence c2: "c \<in> incCommittedSet s" using c committed by auto
          thus "d = a" 
            using d committed in_lo2 nin_lo1 wit by auto
          have bc_nin_lo: "(b, c) \<notin> lo wit'" using max c in_lo2 `d = a` by simp
          have loc: "loc_of b = loc_of c" using b3 c `d = a` by auto
          have "(c, b) \<notin> lo (incWit s)"
            using nin_prev `d = a` c c2
            unfolding sameLocLocksUnlocksSet_def 
            by auto
          hence "(c, b) \<notin> lo wit'" using b3 c2 wit by auto
          thus "c = b" 
            using cons2 bc_nin_lo b2 b3(4) b3(5) c(1) c(4) loc 
            by (auto elim: locks_only_consistent_loE2_inv)
        qed
      ultimately have "lo wit' = lo (incWit s) \<union> ?prev \<union> ?succ \<union> {(b, a)}" 
        using b by auto             
      thus ?thesis
        using b b3 
        unfolding addToTransitiveOrder_def sameLocLocksUnlocksSet_def Let_def
        by auto
    qed
qed

subsubsection {* tot-order *}

lemma step_tot:
  assumes cons2: "axsimpConsistentAlt pre' wit'"
      and wit:   "incWit s = incWitRestrict wit' (incCommittedSet s)"
  shows          "tot wit' = tot (incWit s)"
proof -
  have "tot wit' = {}"
    using cons2 by auto
  thus "tot wit' = tot (incWit s)"
    using wit by auto
qed

subsubsection {* Perform action *}

lemma monPerformLoadCompleteness:
  assumes cons2:      "axsimpConsistentAlt pre' wit'"
      and wit:        "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:  "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed: "downclosed (incCommittedSet s) (rf wit')"
      and a:          "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:         "is_load a"
  shows               "wit' [\<in>] monPerformLoad pre s a"
proof -
  have "\<not> is_write a" using a2 by (cases a) auto
  hence mo: "mo wit' = mo (incWit s)" 
    using step_mo_not_atomic_write[OF cons2 wit committed] a by simp
  have rf: "rf wit' [\<in>] monAddToRfLoad pre a s"
    using step_rf_load[OF cons2 downclosed wit committed] a a2 by simp
  have sc: "if is_seq_cst a 
            then sc wit' [\<in>] monAddToSc pre a s 
            else sc wit' = sc (incWit s)"
    using step_sc[OF cons2 wit committed] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a2 by (cases a) auto
  hence lo: "lo wit' = lo (incWit s)" 
    using step_lo_not_lock_unlock[OF cons2 wit committed] a by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    unfolding monPerformLoad_def
    using cons2 rf mo lo sc tot
    apply auto
    (* Don't know why auto can't figure this out. *)
    apply (intro exI[where x="sc wit'"])
    by auto
qed   

lemma monPerformStoreCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_mo: "downclosed (incCommittedSet s) (mo wit')"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and lk:            "case loc_of a of None \<Rightarrow> true | Some v \<Rightarrow> (lk pre') v = (lk pre) v"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:            "is_store a"
  shows                  "wit' [\<in>] monPerformStore pre s a"
proof -
  have mo: "if is_at_atomic_location (lk pre) a
            then mo wit' [\<in>] monAddToMo pre a s 
            else mo wit' = mo (incWit s)"
    proof 
      assume "is_at_atomic_location (lk pre) a"
      hence loc: "is_at_atomic_location (lk pre') a"
        unfolding is_at_atomic_location_def 
        using lk
        by (cases "loc_of a") auto
      have "is_write a" using a2 by (cases a) auto
      thus "mo wit' [\<in>] monAddToMo pre a s"
        using loc step_mo_atomic_write[OF cons2 wit committed downclosed_mo] a a2
        by simp
    next
      assume loc: "\<not>is_at_atomic_location (lk pre) a"
      hence loc: "\<not>is_at_atomic_location (lk pre') a" 
        unfolding is_at_atomic_location_def 
        using lk
        by (cases "loc_of a") auto
      have "actions_respect_location_kinds (actions0 pre') (lk pre')"
        using cons2 by auto
      hence "is_at_non_atomic_location (lk pre') a"
        unfolding actions_respect_location_kinds_def 
        using loc a a2
        unfolding is_at_atomic_location_def is_at_non_atomic_location_def
        by (cases a) auto
      thus "mo wit' = mo (incWit s)"
        using loc step_mo_not_atomic_write[OF cons2 wit committed] by auto
    qed      
  have "\<not> is_read a" using a2 by (cases a) auto
  hence rf: "rf wit' = rf (incWit s)" 
    using step_rf_non_read[OF cons2 downclosed_rf wit committed] a by simp
  have sc: "if is_seq_cst a 
            then sc wit' [\<in>] monAddToSc pre a s 
            else sc wit' = sc (incWit s)"
    using step_sc[OF cons2 wit committed] a by simp             
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a2 by (cases a) auto
  hence lo: "lo wit' = lo (incWit s)" 
    using step_lo_not_lock_unlock[OF cons2 wit committed] a by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    unfolding monPerformStore_def 
    using cons2 rf mo lo sc tot
    apply auto
    (* Don't know why auto can't figure this out. *)
    apply (intro exI[where x="sc wit'"])
    by auto
qed   

lemma monPerformRmwCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_mo: "downclosed (incCommittedSet s) (mo wit')"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:            "is_RMW a"
  shows                  "wit' [\<in>] monPerformRmw pre s a"
proof -
  have loc: "is_at_atomic_location (lk pre') a"
    using is_RMWE_location_kind[OF a2 a(1)] cons2 by auto
  have "is_write a" using a2 by (cases a) auto
  hence mo: "mo wit' [\<in>] monAddToMo pre a s"
    using loc step_mo_atomic_write[OF cons2 wit committed downclosed_mo] a a2
    by simp
  have rf: "rf wit' [\<in>] monAddToRfRmw pre a s"
    using step_rf_rmw[OF cons2 downclosed_rf downclosed_mo wit committed] a a2 by simp
  have sc: "if is_seq_cst a 
            then sc wit' [\<in>] monAddToSc pre a s 
            else sc wit' = sc (incWit s)"
    using step_sc[OF cons2 wit committed] a by simp             
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a2 by (cases a) auto
  hence lo: "lo wit' = lo (incWit s)" 
    using step_lo_not_lock_unlock[OF cons2 wit committed] a by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    unfolding monPerformRmw_def 
    using cons2 rf mo lo sc tot
    apply simp
    (* Don't know why auto can't figure this out. *)
    apply (intro exI[where x="sc wit'"])
    apply auto
    apply (intro exI[where x="rf wit'"])
    defer
    apply (intro exI[where x="rf wit'"])
    by auto
qed

lemma monPerformLockCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:            "is_lock a"
  shows                  "wit' [\<in>] monPerformLock pre s a"
proof -
  have "\<not> is_write a" using a2 by (cases a) auto
  hence mo: "mo wit' = mo (incWit s)" 
    using step_mo_not_atomic_write[OF cons2 wit committed] a by simp
  have "\<not> is_read a" using a2 by (cases a) auto
  hence rf: "rf wit' = rf (incWit s)" 
    using step_rf_non_read[OF cons2 downclosed_rf wit committed] a by simp
  have "\<not> is_seq_cst a" using a2 by (cases a) auto
  hence sc: "sc wit' = sc (incWit s)"
    using step_sc_isnot_sc[OF cons2 wit committed] a by simp          
  hence lo: "lo wit' [\<in>] monAddToLo pre a s" 
    using step_lo_lock_unlock[OF cons2 wit committed] a a2 by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    unfolding monPerformLock_def
    using cons2 rf mo lo sc tot
    by auto
qed   

lemma monPerformUnlockCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:            "is_unlock a"
  shows                  "wit' [\<in>] monPerformUnlock pre s a"
proof -
  have "\<not> is_write a" using a2 by (cases a) auto
  hence mo: "mo wit' = mo (incWit s)" 
    using step_mo_not_atomic_write[OF cons2 wit committed] a by simp
  have "\<not> is_read a" using a2 by (cases a) auto
  hence rf: "rf wit' = rf (incWit s)" 
    using step_rf_non_read[OF cons2 downclosed_rf wit committed] a by simp
  have "\<not> is_seq_cst a" using a2 by (cases a) auto
  hence sc: "sc wit' = sc (incWit s)"
    using step_sc_isnot_sc[OF cons2 wit committed] a by simp          
  hence lo: "lo wit' [\<in>] monAddToLo pre a s" 
    using step_lo_lock_unlock[OF cons2 wit committed] a a2 by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    unfolding monPerformUnlock_def
    using cons2 rf mo lo sc tot
    by auto
qed   

lemma monPerformFenceCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:            "is_fence a"
  shows                  "wit' [\<in>] monPerformFence pre s a"
proof -
  have "\<not> is_write a" using a2 by (cases a) auto
  hence mo: "mo wit' = mo (incWit s)" 
    using step_mo_not_atomic_write[OF cons2 wit committed] a by simp
  have "\<not> is_read a" using a2 by (cases a) auto
  hence rf: "rf wit' = rf (incWit s)" 
    using step_rf_non_read[OF cons2 downclosed_rf wit committed] a by simp
  have sc: "if is_seq_cst a 
            then sc wit' [\<in>] monAddToSc pre a s 
            else sc wit' = sc (incWit s)"
    using step_sc[OF cons2 wit committed] a by simp         
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a2 by (cases a) auto
  hence lo: "lo wit' = lo (incWit s)" 
    using step_lo_not_lock_unlock[OF cons2 wit committed] a by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    unfolding monPerformFence_def
    using cons2 rf mo lo sc tot
    by auto
qed     

lemma ignoreActionCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
      and a2:            "\<not> is_write a" 
                         "\<not> is_read a" 
                         "\<not> is_seq_cst a" 
                         "\<not> is_lock a" 
                         "\<not> is_unlock a"
  shows                  "wit' = incWit s"
proof -
  have mo: "mo wit' = mo (incWit s)" 
    using step_mo_not_atomic_write[OF cons2 wit committed] a2 by simp
  have rf: "rf wit' = rf (incWit s)" 
    using step_rf_non_read[OF cons2 downclosed_rf wit committed] a a2 by simp
  have sc: "sc wit' = sc (incWit s)"
    using step_sc_isnot_sc[OF cons2 wit committed] a a2 by simp          
  have lo: "lo wit' = lo (incWit s)" 
    using step_lo_not_lock_unlock[OF cons2 wit committed] a a2 by simp
  have tot: "tot wit' = tot (incWit s)" 
    using step_tot[OF cons2 wit] by simp
  show ?thesis
    using cons2 rf mo lo sc tot
    by auto
qed

lemma monPerformActionCompleteness:
  assumes cons2:         "axsimpConsistentAlt pre' wit'"
      and wit:           "incWit s = incWitRestrict wit' (incCommittedSet s)"
      and committed:     "actions0 pre' = insert a (incCommittedSet s)"
      and downclosed_rf: "downclosed (incCommittedSet s) (rf wit')"
      and downclosed_mo: "downclosed (incCommittedSet s) (mo wit')"
      and lk:            "case loc_of a of None \<Rightarrow> true | Some v \<Rightarrow> (lk pre') v = (lk pre) v"
      and a:             "a \<in> actions0 pre'" "a \<notin> incCommittedSet s"
  shows                  "wit' [\<in>] monPerformAction pre s a"
proof (cases a)
  case Load
  thus ?thesis
    unfolding monPerformAction_def
    using monPerformLoadCompleteness[OF cons2 wit committed downclosed_rf a]
    by auto
next
  case Store
  thus ?thesis
    unfolding monPerformAction_def
    using monPerformStoreCompleteness[OF cons2 wit committed downclosed_mo downclosed_rf lk a]
    by auto
next
  case RMW
  thus ?thesis
    unfolding monPerformAction_def
    using monPerformRmwCompleteness[OF cons2 wit committed downclosed_mo downclosed_rf a]
    by auto
next
  case Lock
  thus ?thesis
    unfolding monPerformAction_def
    using monPerformLockCompleteness[OF cons2 wit committed downclosed_rf a] 
    by auto
next
  case Unlock
  thus ?thesis
    unfolding monPerformAction_def
    using monPerformUnlockCompleteness[OF cons2 wit committed downclosed_rf a] 
    by auto
next
  case Fence
  thus ?thesis
    unfolding monPerformAction_def
    using monPerformFenceCompleteness[OF cons2 wit committed downclosed_rf a] 
    by auto
next
  case Blocked_rmw
  thus ?thesis
    unfolding monPerformAction_def
    using ignoreActionCompleteness[OF cons2 wit committed downclosed_rf a]
    by auto
next
  case Alloc
  thus ?thesis
    unfolding monPerformAction_def
    using ignoreActionCompleteness[OF cons2 wit committed downclosed_rf a]
    by auto
next
  case Dealloc
  thus ?thesis
    unfolding monPerformAction_def
    using ignoreActionCompleteness[OF cons2 wit committed downclosed_rf a]
    by auto
qed

subsubsection {* monStep, monTrace *}

lemma monStepCompleteness:
  assumes step:      "incStep pre s1 s2 a"
      and finite:    "finite (actions0 pre)"
      and invariant: "incCommittedSet s1 \<subseteq> actions0 pre"
  shows              "(a, s2) [\<in>] monStep pre s1"
proof -
  let ?pre' = "preRestrict pre (incCommittedSet s2)"
  have cons:      "axsimpConsistentAlt ?pre' (incWit s2)"
   and a:         "a \<in> actions0 pre" "a \<notin> incCommittedSet s1"
   and committed: "incCommitted s2 = a # (incCommitted s1)"
   and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommittedSet s1)"
   and order:     "respectsCom (actions0 pre) (incCommitted s1) (incComAlt pre (incWit s2)) a"
    using step unfolding incStep_def Let_def incToEx_def by auto
  have committed2: "actions0 ?pre' = insert a (incCommittedSet s1)"
    using committed a invariant by auto
  have lk: "case loc_of a of 
              None \<Rightarrow> True 
            | Some v \<Rightarrow> lk (preRestrict pre (incCommittedSet s2)) v = lk pre v"
    by (cases "loc_of a") simp_all
  have a2: "a \<in> actions0 ?pre'"
    using a committed by auto    
  have downclosed_rf: "downclosed (incCommittedSet s1) (rf (incWit s2))"
    unfolding downclosed_def
    proof auto
      fix x y
      assume y:     "y \<in> incCommittedSet s1" 
         and in_rf: "(x, y) \<in> rf (incWit s2)"
      have "y \<in> actions0 ?pre'" using cons in_rf by blast
      hence "y \<in> actions0 pre" by simp
      hence "(a, y) \<notin> incComAlt pre (incWit s2)"
        using in_rf order y
        unfolding respectsCom_def
        by auto
      hence "(a, y) \<notin> rf (incWit s2)"
        unfolding incComAlt_def by auto
      hence "x \<noteq> a" using in_rf by auto
      have "x \<in> actions0 ?pre'" using cons in_rf by blast
      hence "x \<in> incCommittedSet s2" by simp
      thus "x \<in> incCommittedSet s1" using `x \<noteq> a` committed by simp
    qed
  have downclosed_mo: "downclosed (incCommittedSet s1) (mo (incWit s2))"
    (* Clone of the proof of downclosed_rf. *)
    unfolding downclosed_def
    proof auto
      fix x y
      assume y:     "y \<in> incCommittedSet s1" 
         and in_rf: "(x, y) \<in> mo (incWit s2)"
      have "y \<in> actions0 ?pre'" using cons in_rf by blast
      hence "y \<in> actions0 pre" by simp
      hence "(a, y) \<notin> incComAlt pre (incWit s2)"
        using in_rf order y
        unfolding respectsCom_def
        by auto
      hence "(a, y) \<notin> mo (incWit s2)"
        unfolding incComAlt_def by auto
      hence "x \<noteq> a" using in_rf by auto
      have "x \<in> actions0 ?pre'" using cons in_rf by blast
      hence "x \<in> incCommittedSet s2" by simp
      thus "x \<in> incCommittedSet s1" using `x \<noteq> a` committed by simp
    qed
  have performAction: "incWit s2 [\<in>] monPerformAction pre s1 a"
    using monPerformActionCompleteness[OF cons wit committed2 downclosed_rf 
                                           downclosed_mo lk a2 a(2)] .
  have cons2: "() [\<in>] monCheckConsistency (?pre', incWit s2, getRelations ?pre' (incWit s2))"
    unfolding monCheckConsistency_def
    using cons
    by auto
  show ?thesis
    unfolding monStep_def Let_def
    using wit committed performAction order a finite cons2
    apply auto
    apply (intro exI[where x=a])
    by auto
qed

lemma monTraceCompleteness_aux:
  assumes "incTrace pre r s"
          "r = incInitialState pre"
  shows   "monTrace pre r s"
using assms
proof induct
  case (incReflexive pre s)
  thus "monTrace pre s s"
    using monReflexive by auto
next
  case (incStep pre x y z a)
  have finite: "finite (actions0 pre)"
    using incStep incTraceConsistency by auto
  have inv: "incCommittedSet y \<subseteq> actions0 pre"
    using incStep incTraceConsistency by auto
  have "(a, z) [\<in>] monStep pre y" 
    using monStepCompleteness[OF _ finite inv] incStep by auto
  thus "monTrace pre x z"
    using incStep monStep by auto
qed

corollary monTraceCompleteness:
  assumes "incTrace pre (incInitialState pre) s"
  shows   "monTrace pre (incInitialState pre) s"
using assms monTraceCompleteness_aux by simp

subsection {* Equivalence *}

corollary monTraceEquivalence:
  shows "  monTrace pre (incInitialState pre) s 
         = incTrace pre (incInitialState pre) s"
using monTraceSoundness monTraceCompleteness
by metis

lemma consistencyFromTraceEq:
  assumes "\<And>pre s.  trace pre (incInitialState pre) s
                   = trace' pre (incInitialState pre) s"
  shows "consistencyFromTrace trace = consistencyFromTrace trace'"
apply (intro ext, clarify)
unfolding consistencyFromTrace.simps
using assms
by auto

lemma monConsistentEquivalence_aux:  
  shows "monConsistent = incConsistent"
unfolding monConsistent_def incConsistent_def
using consistencyFromTraceEq monTraceEquivalence
by metis

corollary monConsistentEquivalence:  
  shows "  monConsistent (pre, wit, getRelations pre wit)
         = (axConsistent (pre, wit, getRelations pre wit) \<and> finite (actions0 pre))"
using monConsistentEquivalence_aux incConsistentEquivalence 
by metis

(*<*)
end
(*>*)
