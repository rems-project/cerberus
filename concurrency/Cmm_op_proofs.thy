theory Cmm_op_proofs

imports
  Main
  "_bin/Cmm_op"
  Cmm_master_lemmas
begin

(* The axiomatic model ------------------------------------------------- *)

abbreviation "sublanguage \<equiv> true_condition"
abbreviation "memory_model \<equiv> standard_memory_model"
abbreviation "axBehaviour \<equiv> standard_behaviour"
abbreviation "axUndefined \<equiv> locks_only_undefined_behaviour_alt"
abbreviation "getRelations \<equiv> standard_relations"
abbreviation "getHb \<equiv> with_consume_hb"
abbreviation "getVse \<equiv> with_consume_vse"
abbreviation "axConsistent ex \<equiv> apply_tree standard_consistent_execution ex"
abbreviation "axConsistentAlt pre wit \<equiv> axConsistent (pre, wit, getRelations pre wit)"

lemmas sublanguage_def = true_condition_def
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



(* The simplified axiomatic model ------------------------------------- *)

abbreviation "axsimpConsistent ex \<equiv> apply_tree axsimpConsistentExecution ex"
abbreviation "axsimpConsistentAlt pre wit \<equiv> axsimpConsistent (pre, wit, getRelations pre wit)"

lemmas axsimpConsistent_def = axsimpConsistentExecution_def
lemmas axsimpConsistentAlt_def = axsimpConsistent_def

lemma axsimpConsistentE [elim]: 
  assumes "axsimpConsistentAlt pre wit"
  obtains "assumptions (pre, wit, [])"
      and "tot_empty (pre, wit, [])"
      and "well_formed_threads (pre, wit, [])"
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
  shows   "axsimpConsistent ex = axConsistent ex"
using assms
      det_read_simp 
      standard_consistent_atomic_rf_simp
unfolding axsimpConsistent_def
          axConsistent_def
          getRelations_simp 
          with_consume_vse_def
by auto

lemma axsimpMemoryModel_simps [simp]:
  shows "consistent axsimpMemoryModel = axsimpConsistentExecution"
        "relation_calculation axsimpMemoryModel = standard_relations"
        "undefined0 axsimpMemoryModel = locks_only_undefined_behaviour"
unfolding axsimpMemoryModel_def
by simp_all

lemma axsimpBehaviourEq:
  shows "axsimpBehaviour = axBehaviour"
proof (intro ext)
  fix opsem_t
  fix p :: program
  let ?consEx1 = "{(Xo, Xw, rl). opsem_t p Xo \<and> axsimpConsistent (Xo, Xw, rl) \<and> rl = getRelations Xo Xw}"
  let ?consEx2 = "{(Xo, Xw, rl). opsem_t p Xo \<and> axConsistent (Xo, Xw, rl) \<and> rl = getRelations Xo Xw}"
  have consEx: "?consEx1 = ?consEx2"
    using axsimpConsistentEq by auto
  thus "axsimpBehaviour opsem_t p = axBehaviour opsem_t p"
    unfolding axsimpBehaviour_def axBehaviour_def
              behaviour_def Let_def
    by simp
qed



(* The incremental model ----------------------------------------------- *)

abbreviation "hbMinusAlt pre wit \<equiv> hbMinus (pre,wit, getRelations pre wit)"
abbreviation "incComAlt pre wit \<equiv> incCom (pre,wit, getRelations pre wit)"

lemmas hbMinusAlt_def = hbMinus.simps
lemmas incComAlt_def = incCom.simps

(* Simplifications *)

lemma initialWitness_simps [simp]:
  shows "rf initialWitness = {}"
        "mo initialWitness = {}"
        "sc initialWitness = {}"
        "lo initialWitness = {}"
        "tot initialWitness = {}"
unfolding initialWitness_def
by simp_all

lemma incPreRestrict_simps [simp]:
  shows "actions0 (preRestrict pre actions) = actions0 pre \<inter> actions "
        "threads (preRestrict pre actions) = threads pre"
        "lk (preRestrict pre actions) = lk pre"
        "sb (preRestrict pre actions) = relRestrict (sb pre) actions"
        "asw (preRestrict pre actions) = relRestrict (asw pre) actions"
        "dd (preRestrict pre actions) = relRestrict (dd pre) actions"
unfolding preRestrict_def
by simp_all

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
  shows "incWitRestrict wit {} = initialWitness"
unfolding incWitRestrict_def initialWitness_def 
by simp

lemma incWitRestrict_empty2 [simp]:
  shows "incWitRestrict initialWitness x = initialWitness"
unfolding incWitRestrict_def initialWitness_def 
by simp

lemma incWitRestrict_multiple [simp]:
  shows "incWitRestrict (incWitRestrict x y) z = incWitRestrict x (y \<inter> z)"
unfolding incWitRestrict_def 
by auto

lemma initialState_simps [simp]:
  shows "incWit (incInitialState pre) = initialWitness"
        "incCommitted (incInitialState pre) = {}"
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

(* Commitment order *)

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
    (* TODO: fix how hbMinus works, so we don't have to do simp before unfolding. *)
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

(* Properties of happens-before --------------------------------------------------- *)

(* In this section we prove all properties of getHb that we need, so after this section we never
   need to unfold the definition of hb. This way, if hb changes, we only need to change this 
   section. *)

(* RelOver in the rel-acq-rlx fragment *)

lemma relOver_release_acquire_relaxed_sw:
  shows   "relOver (release_acquire_relaxed_synchronizes_with_set_alt pre wit) (actions0 pre)"
unfolding release_acquire_relaxed_synchronizes_with_set_alt_def
          release_acquire_relaxed_synchronizes_with_set_def 
unfolding relOver_def 
(* TODO define relOver elim for all the relations *)
unfolding sw_asw_def
          sw_lock_def
          sw_rel_acq_rs_def
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
(* TODO define relOver elim for all the relations *)
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
          well_formed_threads (pre0, wit, [])
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
    unfolding relOver_def by force+

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
                  irrefl_def
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

(* Monotonicity hb in the locks only fragment *)

lemma monotonicity_locks_only_sw:
  shows   "locks_only_sw_set_alt pre (incWitRestrict wit actions) \<subseteq> 
           locks_only_sw_set_alt pre wit "
unfolding locks_only_sw_set_alt_def
          locks_only_sw_set_def 
by (auto simp add: locks_only_sw_def)

lemma monotonicity_no_consume_hb:
  assumes "sw2 \<subseteq> sw"
  shows   "no_consume_hb p_sb sw2 \<subseteq> no_consume_hb p_sb sw"
using assms
unfolding no_consume_hb_def
by (metis Un_mono order_refl trancl_mono2)

lemma monotonicity_locks_only_hb:
  shows "locks_only_hb pre (incWitRestrict wit actions) \<subseteq> locks_only_hb pre wit"
unfolding locks_only_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_locks_only_sw]
by auto

(* Monotonicity hb in the rel-acq fragment *)

lemma monotonicity_release_acquire_sw:
  shows   "release_acquire_synchronizes_with_set_alt pre (incWitRestrict wit actions)  \<subseteq> 
           release_acquire_synchronizes_with_set_alt pre wit"
apply (intro subrelI, elim release_acquire_swIE)
unfolding sw_asw_def sw_lock_def sw_rel_acq_def
by auto
(* by (auto elim: relRestrictE) *)

lemma monotonicity_release_acquire_hb:
  shows "release_acquire_hb pre (incWitRestrict wit actions) \<subseteq> release_acquire_hb pre wit"
unfolding release_acquire_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_sw]
by auto

(* Monotonicity hb in the rel-acq-rlx fragment *)

lemma monotonicity_release_sequence:
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
  shows   "  sw_rel_acq_rs pre (incWitRestrict wit actions)
           \<subseteq> sw_rel_acq_rs pre wit"
(* TODO: for some reason "cases rule: sw_rel_acq_rsIE" doesn't work after the "intro subrelI". When
everything is made explicit (the fix, assume, thus) then it does do the right thing. *)
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_rel_acq_rs pre (incWitRestrict wit actions)"
  thus   "(a, b) \<in> sw_rel_acq_rs pre wit"
    proof (cases rule: sw_rel_acq_rsIE)
      case (rel_acq_rs c)
      hence "c \<in> actions" by auto (* by (auto elim: relRestrictE) *)
      hence "(a, c) \<in> release_sequence_set_alt pre wit" 
        using monotonicity_release_sequence assms rel_acq_rs
        by metis
      thus "   a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> c \<in> actions0 pre
            \<and> (a, c) \<in> release_sequence_set_alt pre wit \<and> (c, b) \<in> rf wit "
        using rel_acq_rs by auto (* by (auto elim: relRestrictE) *)
    qed
qed

lemma monotonicity_release_acquire_relaxed_sw:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "release_acquire_relaxed_synchronizes_with_set_alt pre (incWitRestrict wit actions) \<subseteq> 
           release_acquire_relaxed_synchronizes_with_set_alt pre wit"
using monotonicity_sw_rel_acq_rs[OF downclosed]
by (intro subrelI, elim release_acquire_relaxed_swIE)
   (auto intro!: sw_aswI sw_lockI)
(* by (intro subrelI, elim release_acquire_relaxed_swIE)
   (auto elim!: sw_lockE sw_aswE 
         intro!: sw_aswI sw_lockI 
         elim: relRestrictE) *)

lemma monotonicity_release_acquire_relaxed_hb:
  assumes "downclosed actions (mo wit)"
  shows   "release_acquire_relaxed_hb pre (incWitRestrict wit actions) \<subseteq> release_acquire_relaxed_hb pre wit"
unfolding release_acquire_relaxed_hb_def 
using monotonicity_no_consume_hb monotonicity_release_acquire_relaxed_sw assms
by metis

(* Monotonicity hb in the rel-acq-rlx-fenced fragment *)

lemma monotonicity_hypothetical_release_sequence:
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
  shows   "  sw_fence_sb_hrs_rf_sb pre (incWitRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre (incWitRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit"
    proof (cases rule: sw_fence_sb_hrs_rf_sbIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y z)
      hence "y \<in> actions" by auto (* by (auto elim: relRestrictE) *)
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> z \<in> actions0 pre
            \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, z) \<in> rf wit \<and> (z, b) \<in> sb pre"
        using fence by auto (* by (auto elim: relRestrictE) *)
    qed
qed

lemma monotonicity_sw_fence_sb_hrs_rf:
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
      hence "y \<in> actions" by auto (* by (auto elim: relRestrictE) *)
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, b) \<in> rf wit"
        using fence by auto (* by (auto elim: relRestrictE) *)
    qed
qed

lemma monotonicity_sw_fence_rs_rf_sb:
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
      hence "y \<in> actions" by auto (* by (auto elim: relRestrictE) *)
      hence "(a, x) \<in> ?rs"
        using monotonicity_release_sequence
        using downclosed fence
        by auto (* by (auto elim: relRestrictE) *)
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre 
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> ?rs \<and> (x, y) \<in> (rf wit) \<and> (y, b) \<in> (sb pre)"
        using fence by auto (* by (auto elim: relRestrictE) *)
    qed
qed

lemma monotonicity_release_acquire_fenced_sw: 
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions) \<subseteq> 
           release_acquire_fenced_synchronizes_with_set_alt pre wit"
using monotonicity_sw_fence_sb_hrs_rf_sb[OF downclosed]
using monotonicity_sw_fence_sb_hrs_rf[OF downclosed]
using monotonicity_sw_fence_rs_rf_sb[OF downclosed]
using monotonicity_sw_rel_acq_rs[OF downclosed]
apply (intro subrelI, elim release_acquire_fenced_swIE)
by (auto 8 2 intro!: sw_aswI sw_lockI)
(* 
by (auto 8 2 elim!: sw_lockE sw_aswE 
             intro!: sw_aswI sw_lockI) *)

lemma monotonicity_release_acquire_fenced_hb:
  assumes "downclosed actions (mo wit)"
  shows   "release_acquire_fenced_hb pre (incWitRestrict wit actions) \<subseteq> release_acquire_fenced_hb pre wit"
unfolding release_acquire_fenced_hb_def 
using monotonicity_no_consume_hb monotonicity_release_acquire_fenced_sw assms
by metis

(* Monotonicity hb in the with_consume fragment *)

lemma monotonicity_with_consume_cad:
  shows "with_consume_cad_set_alt pre (incWitRestrict wit actions) \<subseteq> 
         with_consume_cad_set_alt pre wit"
unfolding with_consume_cad_set_alt_def
          with_consume_cad_set_def
by (intro trancl_mono2) auto

lemma monotonicity_with_consume_dob_set:
  assumes downclosed: "downclosed actions (mo wit)"
  shows "with_consume_dob_set_alt pre (incWitRestrict wit actions) \<subseteq>
         with_consume_dob_set_alt pre wit"
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

lemma relComp_member:
  shows "(a, c) \<in> relcomp r r' = (\<exists>b. (a, b) \<in> r \<and> (b, c) \<in> r')"
by auto

lemma monotonicity_ithb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "inter_thread_happens_before_alt pre (incWitRestrict wit actions) \<subseteq> 
           inter_thread_happens_before_alt pre wit"
unfolding inter_thread_happens_before_alt_def
          inter_thread_happens_before_step_def
          inter_thread_happens_before_r_def
          Let_def
using monotonicity_release_acquire_fenced_sw[OF downclosed]
using monotonicity_with_consume_dob_set[OF downclosed]
by (auto intro!: trancl_mono2 Un_mono relcomp_mono del: subsetI)

lemma monotonicity_with_consume_hb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "with_consume_hb pre (incWitRestrict wit actions) \<subseteq> with_consume_hb pre wit"
unfolding with_consume_hb_def happens_before_def
using monotonicity_ithb[OF downclosed]
by auto

(* Prefixes are final in the rel-acq-rlx fragment *)

(* TODO: the following defintions can be refactored into something simpler. *)

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
                                   (hbCalc pre0 (incWitRestrict wit actions1)))"

definition hbCalcIsMonotonic  :: "(pre_execution \<Rightarrow> execution_witness \<Rightarrow>(action*action)set)\<Rightarrow> bool "  where 
  "hbCalcIsMonotonic hbCalc = (\<forall> pre0. \<forall> wit. \<forall> actions1.
          downclosed actions1 (mo wit) 
     \<longrightarrow>  hbCalc pre0 (incWitRestrict wit actions1) \<subseteq> hbCalc pre0 wit)"

lemma final_release_sequence:
  assumes  "downclosed actions (mo wit)"
      and  "b \<in> actions"
      and  "(a, b) \<in> release_sequence_set_alt pre wit"
  shows   "(a, b) \<in> release_sequence_set_alt pre (incWitRestrict wit actions)"
using assms
unfolding release_sequence_set_alt_def 
          release_sequence_set_def 
          downclosed_def
by auto

lemma final_sw_asw:
  assumes "(a, b) \<in> sw_asw pre wit"
  shows   "(a, b) \<in> sw_asw pre (incWitRestrict wit actions)"
using assms
unfolding sw_asw_def
by auto

lemma final_sw_lock:
  assumes "(a, b) \<in> sw_lock pre wit"
      and "a \<in> actions" 
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_lock pre (incWitRestrict wit actions)"
using assms
unfolding sw_lock_def
by auto

lemma final_sw_rel_acq_rs:
  assumes "(a, b) \<in> sw_rel_acq_rs pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_rel_acq_rs pre (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_rel_acq_rsIE, simp)
  case (rel_acq_rs c)
  hence "c \<in> actions" 
    using downclosed_rf `b \<in> actions` by (auto elim: downclosedE)
  let ?rs   = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt pre (incWitRestrict wit actions)"
  have "(a, c) \<in> ?rs2"
    using final_release_sequence[OF downclosed_mo `c \<in> actions`]
    using rel_acq_rs
    by auto
  thus "(a, c) \<in> ?rs2 \<and> c \<in> actions \<and> b \<in> actions"
    using rel_acq_rs `b \<in> actions` `c \<in> actions` by auto
qed

lemma final_release_acquire_relaxed_sw:
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "a \<in> actions" 
      and "b \<in> actions"
      and sw1: "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt pre wit"
  shows   "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
using sw1
apply (cases rule: release_acquire_relaxed_swIE)
using final_sw_asw
      final_sw_lock
      final_sw_rel_acq_rs
      assms
by metis+

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
  let ?sw2 = "release_acquire_relaxed_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
  let ?f   = "is_na_or_non_write pre"
  assume downclosed: "downclosed actions (rf wit)" 
                     "downclosed actions (mo wit)"
                     "downclosed actions (sbMinus pre (sb pre))"
                     "selective_downclosed ?f actions (release_acquire_relaxed_hb pre wit)"
  have "\<And>x y. \<lbrakk>x \<in> actions; y \<in> actions; (x, y) \<in> ?sw\<rbrakk> \<Longrightarrow> (x, y) \<in> ?sw2"
    using final_release_acquire_relaxed_sw downclosed
    by metis 
  thus "selective_prefixes_are_final (is_na_or_non_write pre) 
                                     actions
                                     (release_acquire_relaxed_hb pre wit) 
                                     (release_acquire_relaxed_hb pre (incWitRestrict wit actions))"
    using final_no_consume_hb downclosed 
    unfolding release_acquire_relaxed_hb_def
    by metis   
qed

(* Prefixes are final in the rel-acq-rlx-fence fragment *)

lemma final_hypothetical_release_sequence:
  assumes  "downclosed actions (mo wit)"
      and  "b \<in> actions"
      and  "(a, b) \<in> hypothetical_release_sequence_set_alt pre wit"
  shows   "(a, b) \<in> hypothetical_release_sequence_set_alt pre (incWitRestrict wit actions)"
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
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_sb_hrs_rf_sbIE, simp)
  let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
  let ?hrs2  = "hypothetical_release_sequence_set_alt pre (incWitRestrict wit actions)"
  case (fence x y z)
  have "is_na_or_non_write pre b" 
    using `is_fence b` unfolding is_na_or_non_write_def by (cases b) auto
  hence "(z, b) \<in> sbMinus pre (sb pre)" 
    using `(z, b) \<in> sb pre` unfolding sbMinus_def by auto
  hence "z \<in> actions" 
    using downclosed_sb `b \<in> actions` unfolding downclosed_def by metis  
  hence "y \<in> actions"
    using downclosed_rf `(y, z) \<in> rf wit` unfolding downclosed_def by metis  
  hence "(x, y) \<in> ?hrs2"
    using final_hypothetical_release_sequence `(x, y) \<in> ?hrs` downclosed_mo
    by metis
  thus "(x, y) \<in> ?hrs2 \<and> y \<in> actions \<and> z \<in> actions"
    using fence `z \<in> actions` `y \<in> actions` by auto
qed

lemma final_sw_fence_sb_hrs_rf:
  assumes "(a, b) \<in> sw_fence_sb_hrs_rf pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf pre (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_sb_hrs_rfIE, simp)
  let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
  let ?hrs2  = "hypothetical_release_sequence_set_alt pre (incWitRestrict wit actions)"
  case (fence x y)
  have "y \<in> actions" 
    using downclosed_rf `b \<in> actions` `(y, b) \<in> rf wit` 
    unfolding downclosed_def by metis
  hence "(x, y) \<in> ?hrs2" 
    using final_hypothetical_release_sequence `(x, y) \<in> ?hrs` downclosed_mo
    by metis
  thus "(x, y) \<in> ?hrs2 \<and> y \<in> actions \<and> b \<in> actions"
    using fence `y \<in> actions` `b \<in> actions` by auto
qed

lemma final_sw_fence_rs_rf_sb:
  assumes "(a, b) \<in> sw_fence_rs_rf_sb pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
      and b: "b \<in> actions"
  shows   "(a, b) \<in> sw_fence_rs_rf_sb pre (incWitRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_rs_rf_sbIE, simp)
  let ?rs  = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt pre (incWitRestrict wit actions)"
  case (fence x y)
  have "is_na_or_non_write pre b" 
    using `is_fence b` unfolding is_na_or_non_write_def by (cases b) auto
  hence "(y, b) \<in> sbMinus pre (sb pre)" 
    using `(y, b) \<in> sb pre` unfolding sbMinus_def by auto
  hence "y \<in> actions" 
    using downclosed_sb b unfolding downclosed_def by metis
  hence "x \<in> actions"
    using downclosed_rf `(x, y) \<in> rf wit` unfolding downclosed_def by metis
  hence "(a, x) \<in> ?rs2" 
    using final_release_sequence `(a, x) \<in> ?rs` downclosed_mo
    by metis
  thus "(a, x) \<in> ?rs2 \<and> x \<in> actions \<and> y \<in> actions"
    using fence `x \<in> actions` `y \<in> actions` by auto
qed

lemma final_release_acquire_fenced_sw:
  assumes downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and downclosed_sb: "downclosed actions (sbMinus pre (sb pre))"
      and "a \<in> actions"
      and "b \<in> actions"
      and sw1: "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
  shows   "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
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
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
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
                                     (release_acquire_fenced_hb pre (incWitRestrict wit actions))"
    using final_no_consume_hb[OF downclosed_rf downclosed_mo] downclosed_hb final_sw
    unfolding release_acquire_fenced_hb_def
    by metis
qed

(* Prefixes are final in the with-consume fragment *)

lemma final_cad:
  assumes downclosed_sb: "\<And>a. (a, b) \<in> sb pre \<Longrightarrow> a \<in> actions"
      and trans_sb:      "trans (sb pre)"
      and dd_in_sb:      "dd pre \<subseteq> sb pre"
      and b:             "b \<in> actions" 
      and cad:           "(a, b) \<in> with_consume_cad_set_alt pre wit"
  shows   "a \<in> actions \<and> (a, b) \<in> with_consume_cad_set_alt pre (incWitRestrict wit actions)"
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
  have "(a, b) \<in> with_consume_cad_set_alt pre (incWitRestrict wit actions)"
    using cad unfolding with_consume_cad_set_alt_def with_consume_cad_set_def
    proof (rule converse_trancl_induct)
      fix y
      assume y: "(y, b) \<in> rf wit \<inter> sb pre \<union> dd pre"
      hence "(y, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+" by fast
      hence "y \<in> actions" using downclosed_cad by fast
      hence "(y, b) \<in> relRestrict (rf wit) actions \<inter> sb pre \<union> dd pre"
        using y b by auto
      thus "(y, b) \<in> (rf (incWitRestrict wit actions) \<inter> sb pre \<union> dd pre)\<^sup>+" by auto
    next
      fix y z
      assume y:  "(y, z) \<in> rf wit \<inter> sb pre \<union> dd pre"
         and z:  "(z, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+"
         and ih: "(z, b) \<in> (rf (incWitRestrict wit actions) \<inter> sb pre \<union> dd pre)\<^sup>+"
      have "z \<in> actions" using downclosed_cad[OF z] .
      have "(y, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+" using y z by (rule trancl_into_trancl2)
      hence "y \<in> actions" using downclosed_cad by fast
      have "(y, z) \<in> relRestrict (rf wit) actions \<inter> sb pre \<union> dd pre"
        using y `y \<in> actions` `z \<in> actions` by auto
      thus "(y, b) \<in> (rf (incWitRestrict wit actions) \<inter> sb pre \<union> dd pre)\<^sup>+"
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
  shows   "(a, d) \<in> with_consume_dob_set_alt pre (incWitRestrict wit actions)"
proof -
  obtain b e where a:  "a \<in> actions0 pre" "is_release a"
               and b:  "b \<in> actions0 pre" "is_consume b"
               and d2: "d \<in> actions0 pre"
               and e:  "e \<in> actions0 pre"
               and rs: "(a, e) \<in> release_sequence_set_alt pre wit"
               and rf: "(e, b) \<in> rf wit"
               and cad_or_eq: "(b, d) \<in> with_consume_cad_set_alt pre wit \<or> b = d"
    using dob_set
    unfolding with_consume_dob_set_alt_def 
              with_consume_dob_set_def
    by (auto simp add: dependency_ordered_before_def)
  have cad2: "((b, d) \<in> with_consume_cad_set_alt pre (incWitRestrict wit actions) \<or> (b = d)) \<and> b \<in> actions"
    using cad_or_eq
    proof
      assume "b = d"
      thus ?thesis using `d \<in> actions` by simp
    next
      assume "(b, d) \<in> with_consume_cad_set_alt pre wit"
      thus ?thesis
        using final_cad[OF downclosed_sb trans_sb dd_in_sb d]
        by fast
    qed
  hence "e \<in> actions"
    using rf downclosed_rf unfolding downclosed_def by fast
  hence rf2: "(e, b) \<in> relRestrict (rf wit) actions" 
    using cad2 rf by auto
  have rs2: "(a, e) \<in> release_sequence_set_alt pre (incWitRestrict wit actions)" 
    using rs final_release_sequence[OF downclosed_mo `e \<in> actions`]
    by fast
  thus ?thesis
    using a b d d2 e rs2 rf2 cad2
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
  shows   "(a, b) \<in> inter_thread_happens_before_r pre (incWitRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_r_def
apply (elim UnMember_mono)
defer defer
apply (simp, elim composeMember_mono)
proof simp
  assume "(a, b) \<in> with_consume_dob_set_alt pre wit"
  thus "(a, b) \<in> with_consume_dob_set_alt pre (incWitRestrict wit actions)"
    using final_dob[OF downclosed_sb downclosed_rf downclosed_mo trans_sb dd_in_sb b]
    by auto
next
  assume "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
  thus "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
    using final_release_acquire_fenced_sw[OF downclosed_rf downclosed_mo downclosed_sb2 a b]
    by metis
next
  fix y
  assume sw: "(a, y) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
     and sb: "(y, b) \<in> sb pre"
  have "y \<in> actions"
    using sb downclosed_sb by auto
  thus "(a, y) \<in> release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
    using sw sb
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
  shows   "(a, b) \<in> inter_thread_happens_before_step pre (incWitRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_step_def
apply (elim UnMember_mono)
defer 
apply (simp, elim composeMember_mono)
proof simp
  assume "(a, b) \<in> inter_thread_happens_before_r pre wit"
  thus "(a, b) \<in> inter_thread_happens_before_r pre (incWitRestrict wit actions)"
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
  thus "(y, b) \<in> inter_thread_happens_before_r pre (incWitRestrict wit actions)"
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
  shows   "(a, b) \<in> inter_thread_happens_before_alt pre (incWitRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_alt_def
proof (induct rule: converse_trancl_induct)
  fix y
  assume step: "(y, b) \<in> inter_thread_happens_before_step pre wit"
  hence "y \<in> actions"
    using downclosed_ithb
    unfolding inter_thread_happens_before_alt_def
    by auto
  thus "(y, b) \<in> (inter_thread_happens_before_step pre (incWitRestrict wit actions))\<^sup>+"
    using final_ithb_step[OF downclosed_sb downclosed_sb2 downclosed_rf 
                             downclosed_mo downclosed_ithb trans_sb dd_in_sb _ b step]
    by auto
next
  fix y z
  assume yz: "(y, z) \<in> inter_thread_happens_before_step pre wit"
     and zb: "(z, b) \<in> (inter_thread_happens_before_step pre wit)\<^sup>+"
     and ih: "(z, b) \<in> (inter_thread_happens_before_step pre (incWitRestrict wit actions))\<^sup>+"
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
  (* TODO: refactor the following. *)
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
          from this obtain v where zv: "(z, v) \<in> sb pre"
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
  (* TODO: and also refactor the following. *)
  have downclosed_ithb2: "\<And>x. (x, z) \<in> inter_thread_happens_before_alt pre wit \<Longrightarrow> x \<in> actions"
    proof -
      fix x
      assume "(x, z) \<in> inter_thread_happens_before_alt pre wit"
      hence "(x, b) \<in> inter_thread_happens_before_alt pre wit"
        using zb unfolding inter_thread_happens_before_alt_def by auto
      thus "x \<in> actions" using downclosed_ithb by auto
    qed
  hence "(y, z) \<in> (inter_thread_happens_before_step pre (incWitRestrict wit actions))\<^sup>+"
    using final_ithb_step[OF downclosed_sb1b downclosed_sb2 downclosed_rf 
                             downclosed_mo downclosed_ithb2 trans_sb dd_in_sb y z yz]
    by auto
  thus "(y, b) \<in> (inter_thread_happens_before_step pre (incWitRestrict wit actions))\<^sup>+"
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
      and ithb:          "(a, b) \<in> with_consume_hb pre wit"
  shows   "(a, b) \<in> with_consume_hb pre (incWitRestrict wit actions)"
proof -
  show ?thesis
    using ithb
    using final_ithb[OF downclosed_sb downclosed_sb2 downclosed_rf downclosed_mo
                        downclosed_ithb trans_sb dd_in_sb b(1)]
    unfolding with_consume_hb_def 
              happens_before_def
    by auto
qed

lemma final_with_consume_hb:
  shows   "hbCalcIsFinalForPrefixes with_consume_hb"
unfolding hbCalcIsFinalForPrefixes_def 
proof auto
  fix pre :: pre_execution
  fix wit :: execution_witness
  fix actions
  let ?sw   = "release_acquire_fenced_synchronizes_with_set_alt pre wit"
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set_alt pre (incWitRestrict wit actions)"
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
                                     (with_consume_hb pre (incWitRestrict wit actions))"
    unfolding selective_prefixes_are_final_def
    (* TODO: remove redundancies *)
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
      show "(a, b) \<in> with_consume_hb pre (incWitRestrict wit actions)"
        using final_with_consume_hb_aux[OF downclosed_sb2 downclosed_sb downclosed_rf
                                           downclosed_mo downclosed_ithb trans_sb
                                           dd_in_sb b(1) ab]
        by metis
    qed
qed

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
  shows "hbCalcIsMonotonic hbMinusAlt"
using hbCalcIsMonotonic
(* TODO: make a simp for "hbMinus pre wit getRelations" to "hbMinus pre wit getHb". *)
unfolding hbCalcIsMonotonic_def 
          getRelations_simp 
          hbMinusAlt_def
by auto

lemma opsemOrderIsMonotonic:
  shows "hbCalcIsMonotonic incComAlt"
unfolding hbCalcIsMonotonic_def
proof (intro allI impI)
  fix pre
  fix wit :: execution_witness
  fix actions
  assume downclosed: "downclosed actions (mo wit)"
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

(* Soundness ---------------------------------------------------------------------------------- *)

lemma incTraceConsistency: 
  assumes "incTrace pre r s"
          "r = incInitialState pre"
  shows   "axsimpConsistentAlt pre (incWit s)"
using assms 
proof induct
  case incStep
  thus ?case unfolding incStep_def Let_def by auto
qed simp

lemma incConsistentSoundness:
  assumes "incConsistent (pre, wit, getRelations pre wit)"
  shows   "axsimpConsistent (pre, wit, getRelations pre wit)"
using assms
proof -
  assume "incConsistent (pre, wit, getRelations pre wit)"
  from this obtain s where trace: "incTrace pre (incInitialState pre) s"
                     and   wit:   "incWit s = wit"
                     and   com:   "incCommitted s = actions0 pre"
    unfolding incConsistent.simps by auto
  thus "axsimpConsistent (pre, wit, getRelations pre wit)" 
    by (metis trace wit incTraceConsistency)
qed

(* Invariance of consistency predicates under prefixes ---------------------------------------- *)

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
      from this obtain w' where w': "w'\<in>actions0 pre" "(w', r) \<in> rf wit"
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
      from this obtain w where w: "w \<in> actions0 pre"
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
(*
  hence "  (\<exists>w\<in>actions0 pre \<inter> actions. (w, r) \<in> hb2 \<and> is_write w \<and> loc_of w = loc_of r)
         = (\<exists>w\<in>actions0 pre \<inter> actions. (w, r) \<in> hb \<and> is_write w \<and> loc_of w = loc_of r)"
    by auto
  also have "... = (\<exists>w'\<in>actions0 pre \<inter> actions. (w', r) \<in> rf wit)"
    using det_read `is_load r` `r \<in> actions0 pre` downclosed_rf downclosed_hb non_write_r
    unfolding det_read_alt.simps downclosed_def hbMinus.simps
    by auto
  also have "... = (\<exists>w'\<in>actions0 pre \<inter> actions. (w', r) \<in> rf wit)"
    using downclosed_rf `r \<in> actions` unfolding downclosed_def by auto
  finally show "  (\<exists>w\<in>actions0 pre \<inter> actions. (w, r) \<in> hb2 \<and> is_write w \<and> loc_of w = loc_of r)  
                = (\<exists>w'\<in>actions0 pre \<inter> actions. (w', r) \<in> rf wit)" .
*)
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
  shows   "well_formed_threads (preRestrict pre actions, incWitRestrict wit actions, [])"
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
              Cmm_master.inj_on_def
              threadwise_def
              interthread_def
              isStrictPartialOrder_def
              indeterminate_sequencing_def
              disjoint_allocs_def
    by auto
qed

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
    unfolding hbCalcIsFinalForPrefixes_def hbMinus_def 
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
      show "well_formed_threads (?pre', ?wit', [])"
        using cons well_formed_threads_restriction by auto
    qed
qed



end
