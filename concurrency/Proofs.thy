(* Aims to prove the equivalence of the operational semantics and the axiomatic model. *)
(* Kyndylan Nienhuis *)

theory "Proofs"

imports
Main
"_bin/Cmm_master"
"_bin/Opsem"
begin

(* --------------------------------------------------------------------------------------------- *)
(* Termination proofs *)

(* Of Cmm *)
termination apply_tree by lexicographic_order
(* Of Opsem *)
termination assemblePreEx by lexicographic_order
termination assembleEx by lexicographic_order
termination actionsOfTrace by lexicographic_order
termination respectsHb by lexicographic_order

(* --------------------------------------------------------------------------------------------- *)
(* Simplifications *)

(* TODO: find out how simplifications with assumptions work 
   (e.g. is there a danger of looping, or making auto inefficient?) *)

(* Simplifications of Lem-library functions *)

lemma isIrreflexive_empty [simp]:
  shows "isIrreflexive {}"
unfolding isIrreflexive_def
by simp

(* TODO: Speed issue, consider manual use *)
lemma isIrreflexive_intersection [simp]:
  assumes "isIrreflexive x"
  shows   "isIrreflexive (x \<inter> y)"
using assms
unfolding isIrreflexive_def
by simp

lemma isTransitive_empty [simp]:
  shows "isTransitive {}"
unfolding isTransitive_def
by simp

lemma isTransitive_cross [simp]:
  shows "isTransitive (x \<times> x)"
unfolding isTransitive_def relApply_def
by simp

lemma isTransitive_intersection [simp]:
  assumes "isTransitive x"
          "isTransitive y"
  shows   "isTransitive (x \<inter> y)"
using assms
unfolding isTransitive_def relApply_def
by auto

lemma isStrictPartialOrder_empty [simp]:
  shows "isStrictPartialOrder {}"
unfolding isStrictPartialOrder_def
by simp

lemma relDomain_empty [simp]:
  shows "relDomain {} = {}"
unfolding relDomain_def
by simp

lemma relRange_empty [simp]:
  shows "relRange {} = {}"
unfolding relRange_def
by simp

lemma relRange_union [simp]:
  shows "relRange (x \<union> y) = relRange x \<union> relRange y"
unfolding relRange_def
by auto

lemma relRange_inter [simp]:
  assumes "a \<in> relRange (x \<inter> y)"
  shows   "a \<in> relRange x \<inter> relRange y"
using assms
unfolding relRange_def
by auto

lemma relRange_cross_id [simp]:
  shows "relRange (x \<times> x) = x"
unfolding relRange_def
by simp

lemma relOver_empty [simp]:
  shows "relOver {} {}"
unfolding relOver_def
by simp

lemma relOver_empty2 [simp]:
  assumes "relOver x {}"
  shows   "x = {}"
using assms 
unfolding relOver_def relDomain_def relRange_def 
by simp

lemma relOver_intersect [simp]:
  assumes "relOver x y"
  shows   "relOver (x \<inter> a \<times> a) (y \<inter> a)"
using assms
unfolding relOver_def relDomain_def relRange_def 
by auto

lemma relRestrict_inter [simp]:
  shows "relRestrict rel res = rel \<inter> res \<times> res"
unfolding relRestrict_def
by fast

lemma relRestrict_empty1 [simp]:
  shows "relRestrict x {} = {}"
unfolding relRestrict_def
by simp

lemma relRestrict_empty2 [simp]:
  shows "relRestrict {} x = {}"
unfolding relRestrict_def
by simp

lemma trancl_intersection [simp]:
  assumes "(a, b) \<in> (x \<inter> y)\<^sup>+"
  shows   "(a, b) \<in> x\<^sup>+"
using assms
by (rule trancl_induct, auto)

(* Simplifications for initial executions *)

(* TODO: aggregate them together *)
lemma actions_initialPreEx [simp]:
  shows "actions0 initialPreEx = {}"
        "threads initialPreEx = {}"
unfolding initialPreEx_def
by simp_all

lemma sb_initialPreEx [simp]:
  shows "sb initialPreEx = {}"
unfolding initialPreEx_def
by simp

lemma asw_initialPreEx [simp]:
  shows "asw initialPreEx = {}"
unfolding initialPreEx_def
by simp

lemma dd_initialPreEx [simp]:
  shows "dd initialPreEx = {}"
unfolding initialPreEx_def
by simp

lemma rf_initialWitness [simp]:
  shows "rf initialWitness = {}"
unfolding initialWitness_def
by simp

lemma mo_initialWitness [simp]:
  shows "mo initialWitness = {}"
unfolding initialWitness_def
by simp

lemma sc_initialWitness [simp]:
  shows "sc initialWitness = {}"
unfolding initialWitness_def
by simp

lemma lo_initialWitness [simp]:
  shows "lo initialWitness = {}"
unfolding initialWitness_def
by simp

lemma ao_initialWitness [simp]:
  shows "ao initialWitness = {}"
unfolding initialWitness_def
by simp

lemma tot_initialWitness [simp]:
  shows "tot initialWitness = {}"
unfolding initialWitness_def
by simp

lemma sw_initialEx [simp]:
  shows "calcSw initialPreEx initialWitness = {}"
unfolding calcSw_def release_acquire_synchronizes_with_set_def 
by auto

lemma hb_initialEx [simp]:
  shows "calcHb initialPreEx initialWitness = {}"
unfolding calcHb_def no_consume_hb_def
by auto

lemma vse_initialEx [simp]:
  shows "calcVse initialPreEx initialWitness = {}"
unfolding calcVse_def visible_side_effect_set_def
by auto

lemma calcRel_initialEx [simp]:
  shows "calcRel initialPreEx initialWitness = 
         [(''hb'', {}),
          (''vse'', {}),
          (''sw'', {})]"
unfolding calcRel_def
by auto

(* Simplifications for extensions *)

lemma actionsOfExtention [simp]:
  shows "actions0 (extendPreEx pre s) = insert (action s) (actions0 pre)"
unfolding extendPreEx_def
by simp

lemma actionsOfAssembly [simp]:
  shows "actions0 (assemblePreEx trace) = actionsOfTrace trace"
by (induct trace) simp_all

(* Simplification for prefix *)

lemma isHbPrefix_simp [simp]:
  assumes "isHbPrefix actions pre wit"
  and     "(a, b) \<in> calcHb pre wit"
  and     "b \<in> actions"
  shows   "a \<in> actions"
using assms
unfolding isHbPrefix_def
by auto

(* Simplifications for restrictions *)

lemma preExRestrict_initialPreEx [simp]:
  shows "preExRestrict x {} = initialPreEx"
unfolding preExRestrict_def initialPreEx_def
by simp

lemma witnessRestrict_initialWitness [simp]:
  shows "witnessRestrict x {} = initialWitness"
unfolding initialWitness_def witnessRestrict_def
by simp

lemma witnessRestrict_multiple [simp]:
  shows "witnessRestrict (witnessRestrict x y) z = witnessRestrict x (y \<inter> z)"
unfolding witnessRestrict_def
by auto

lemma exRestrict_initialEx [simp]:
  shows "exRestrict x {} = (initialPreEx, initialWitness)"
unfolding exRestrict_def
by simp

lemma preExRestrict_actions [simp]:
  shows "actions0 (preExRestrict pre actions) = actions0 pre \<inter> actions"
unfolding preExRestrict_def 
by simp

lemma preExRestrict_threads [simp]:
  shows "threads (preExRestrict pre actions) = threads pre \<inter> (Set.image tid_of actions)"
unfolding preExRestrict_def 
by simp

lemma preExRestrict_lk [simp]:
  shows "lk (preExRestrict pre actions) l = 
         (if (\<exists>a \<in> actions. loc_of a = Some l) then (lk pre) l else defaultLk)"
unfolding preExRestrict_def
by simp

lemma preExRestrict_lk_is_at_mutex_location [simp]:
  assumes "a \<in> actions"
  shows   "is_at_mutex_location (lk (preExRestrict pre actions)) a =
           is_at_mutex_location (lk pre) a"
proof (cases "loc_of a")
  case None
  thus ?thesis 
    unfolding is_at_mutex_location_def by auto
next
  case (Some l)
  thus ?thesis using assms 
    unfolding is_at_mutex_location_def by auto
qed

lemma preExRestrict_lk_is_at_atomic_location [simp]:
  assumes "a \<in> actions"
  shows   "is_at_atomic_location (lk (preExRestrict pre actions)) a =
           is_at_atomic_location (lk pre) a"
proof (cases "loc_of a")
  case None
  thus ?thesis 
    unfolding is_at_atomic_location_def by auto
next
  case (Some l)
  thus ?thesis using assms 
    unfolding is_at_atomic_location_def by auto
qed

lemma preExRestrict_lk_is_at_non_atomic_location [simp]:
  assumes "a \<in> actions"
  shows   "is_at_non_atomic_location (lk (preExRestrict pre actions)) a =
           is_at_non_atomic_location (lk pre) a"
proof (cases "loc_of a")
  case None
  thus ?thesis 
    unfolding is_at_non_atomic_location_def by auto
next
  case (Some l)
  thus ?thesis using assms 
    unfolding is_at_non_atomic_location_def by auto
qed

lemma preExRestrict_sb [simp]:
  shows "sb (preExRestrict pre actions) = sb pre \<inter> actions \<times> actions"
unfolding preExRestrict_def Let_def
by simp

lemma preExRestrict_asw [simp]:
  shows "asw (preExRestrict pre actions) = asw pre \<inter> actions \<times> actions"
unfolding preExRestrict_def Let_def
by simp

lemma preExRestrict_dd [simp]:
  shows "dd (preExRestrict pre actions) = dd pre \<inter> actions \<times> actions"
unfolding preExRestrict_def Let_def
by simp

lemma witnessExRestrict_rf [simp]:
  shows "rf (witnessRestrict wit actions) = rf wit \<inter> actions \<times> actions"
unfolding witnessRestrict_def
by simp

lemma witnessExRestrict_mo [simp]:
  shows "mo (witnessRestrict wit actions) = mo wit \<inter> actions \<times> actions"
unfolding witnessRestrict_def
by simp

lemma witnessExRestrict_sc [simp]:
  shows "sc (witnessRestrict wit actions) = sc wit \<inter> actions \<times> actions"
unfolding witnessRestrict_def
by simp

lemma witnessExRestrict_lo [simp]:
  shows "lo (witnessRestrict wit actions) = lo wit \<inter> actions \<times> actions"
unfolding witnessRestrict_def
by simp

lemma witnessExRestrict_ao [simp]:
  shows "ao (witnessRestrict wit actions) = ao wit \<inter> actions \<times> actions"
unfolding witnessRestrict_def
by simp

lemma witnessExRestrict_tot [simp]:
  shows "tot (witnessRestrict wit actions) = tot wit \<inter> actions \<times> actions"
unfolding witnessRestrict_def
by simp

(* Simplifications for initialState *)

lemma twopState_initialState [simp]: 
  shows "twopState (initialState twop c) = init twop c"
unfolding initialState_def
by simp

lemma preEx_initialState [simp]: 
  shows "preEx (initialState twop c) = initialPreEx"
unfolding initialState_def
by simp

lemma exWitness_initialState [simp]: 
  shows "exWitness (initialState twop c) = initialWitness"
unfolding initialState_def
by simp

lemma stateIsDefined_initialState [simp]:
  shows "stateIsDefined (initialState twop c)"
unfolding initialState_def
by simp

(* We defined wrappers around the following functions, 
   so we can use their definition as simplifications *)
declare assumptions.simps [simp]
declare well_formed_threads.simps [simp]
declare well_formed_rf.simps [simp]
declare locks_only_consistent_locks.simps [simp]
declare locks_only_consistent_lo.simps [simp]
declare consistent_mo.simps [simp]
declare sc_accesses_consistent_sc.simps [simp]
declare sc_fenced_sc_fences_heeded.simps [simp]
declare consistent_hb.simps [simp]
declare consistent_non_atomic_rf.simps [simp]
declare consistent_atomic_rf.simps [simp]
declare det_read.simps [simp]
declare coherent_memory_use.simps [simp]
declare rmw_atomicity.simps [simp]
declare sc_accesses_sc_reads_restricted.simps [simp]
declare unsequenced_races.simps [simp]
declare data_races.simps [simp]
declare indeterminate_reads.simps [simp]
declare locks_only_bad_mutexes.simps [simp]
(* The following function is used in the above wrappers. *)
declare calcRel_def [simp]
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

(* Properties of Cmm *)

lemma sbInHb [simp]:
  assumes "x \<in> sb pre"
  shows   "x \<in> calcHb pre wit"
using assms
unfolding calcHb_def no_consume_hb_def
by (metis Un_iff r_into_trancl')

lemma swInHb [simp]:
  assumes "x \<in> calcSw pre wit"
  shows   "x \<in> calcHb pre wit"
using assms
unfolding calcHb_def no_consume_hb_def
by (metis Un_iff r_into_trancl')
 
lemma aswInSw [simp]:
  assumes "well_formed_threads2 pre wit"
          "(a, b) \<in> asw pre"
  shows   "(a, b) \<in> calcSw pre wit"
proof - 
  have "relOver (asw pre) (actions0 pre)" using assms
    unfolding well_formed_threads2_def by simp
  hence "a \<in> actions0 pre \<and> b \<in> actions0 pre" using assms 
    unfolding relOver_def relRange_def relDomain_def
    by force
  moreover have "tid_of a \<noteq> tid_of b" using assms
    unfolding well_formed_threads2_def by fastforce
  ultimately show ?thesis using assms
    unfolding calcSw_def release_acquire_synchronizes_with_set_def
    by (simp add: release_acquire_synchronizes_with_def)
qed

lemma loInSw [simp]:
  assumes "well_formed_threads2 pre wit"
          "locks_only_consistent_lo2 pre wit"
          "is_unlock a"
          "is_lock b"
          "(a, b) \<in> lo wit"
  shows   "(a, b) \<in> calcHb pre wit"
using assms
proof -
  fix a b
  assume as2: "is_unlock a"
              "is_lock b"  
              "(a, b) \<in> lo wit"
  have "relOver (lo wit) (actions0 pre)" using assms
    unfolding locks_only_consistent_lo2_def by simp
  hence as3: "a \<in> actions0 pre \<and> b \<in> actions0 pre" using as2
    unfolding relOver_def relRange_def relDomain_def by force    
  show "(a, b) \<in> calcHb pre wit" 
    proof (cases "tid_of a = tid_of b")
      assume "tid_of a \<noteq> tid_of b"
      hence "(a, b) \<in> calcSw pre wit" using as2 as3
        unfolding calcSw_def release_acquire_synchronizes_with_set_def
        by (simp add: release_acquire_synchronizes_with_def)
      thus "(a, b) \<in> calcHb pre wit" by simp
    next
      assume as4: "tid_of a = tid_of b"
      have "(b, a) \<notin> calcHb pre wit" using assms as2 as3
        unfolding locks_only_consistent_lo2_def by simp
      hence as5: "(b, a) \<notin> sb pre" by (metis sbInHb)
      have as6: "a \<noteq> b" using assms as2 as3
        unfolding locks_only_consistent_lo2_def
                  locks_only_consistent_lo.simps 
                  isIrreflexive_def
        by auto
      have "is_at_mutex_location (lk pre) a" using assms as2 as3
        unfolding locks_only_consistent_lo2_def 
        by force
      hence as7: "\<not> is_at_non_atomic_location (lk pre) a"
        unfolding is_at_mutex_location_def is_at_non_atomic_location_def
        by (cases "loc_of a") auto
      from as3 as4 as5 as6 as7 assms have "(a, b) \<in> sb pre"
        unfolding well_formed_threads2_def 
                  well_formed_threads.simps 
                  indeterminate_sequencing_def
        by auto
      thus "(a, b) \<in> calcHb pre wit" by simp
    qed
qed

lemma vseInHb [simp]:
  assumes "x \<in> calcVse pre wit"
  shows   "x \<in> calcHb pre wit"
using assms
unfolding calcVse_def visible_side_effect_set_def
by simp

lemma loadIsRead [simp]:
  assumes "is_load a"
  shows   "is_read a"
using assms
by (cases a) auto

lemma rmwIsRead [simp]:
  assumes "is_RMW a"
  shows   "is_read a"
using assms
by (cases a) auto

lemma readIsRmwOrLoad [simp]:
  assumes "is_read a"
  shows   "is_RMW a \<or> is_load a"
using assms
by (cases a) auto

lemma successfulLockIsLock [simp]:
  assumes "is_successful_lock a"
  shows   "is_lock a"
using assms
by (cases a) auto

lemma blockedLockIsLock [simp]:
  assumes "is_blocked_lock a"
  shows   "is_lock a"
using assms
by (cases a) auto

(* --------------------------------------------------------------------------------------------- *)
(* Proof that (speculative) consistency is invariant under restrictions *)

lemma exRestrict_sw [simp]:
  shows "calcSw (preExRestrict pre actions) (witnessRestrict wit actions) =
         calcSw pre wit \<inter> actions \<times> actions"
unfolding calcSw_def release_acquire_synchronizes_with_set_def
by (auto simp add: release_acquire_synchronizes_with_def) 

(* TODO: streamline proof *)
lemma exRestrict_trancl [simp]: 
  assumes "isHbPrefix actions pre wit"
          "r \<subseteq> calcHb pre wit"
  shows   "(r \<inter> actions \<times> actions)\<^sup>+ = r\<^sup>+ \<inter> actions \<times> actions"
proof -
  let ?left = "(r \<inter> actions \<times> actions)\<^sup>+"
  let ?right = "r\<^sup>+ \<inter> actions \<times> actions"
  show "?left = ?right"
(* Handy: find all intros for current goal: find_theorems (100) intro  *)
    proof 
(*TODO:  proof (intro set_eqI iffI) *)
      show "?left \<subseteq> ?right"
        proof
          fix x
          assume as1: "x \<in> ?left"
          obtain a b where as2: "x = (a, b)" by force
          have "(a, b) \<in> ?left" using as1 as2 by simp
          hence "(a, b) \<in> ?right"
            proof (rule trancl_induct)
              fix y z
              assume "(a, y) \<in> r\<^sup>+ \<inter> actions \<times> actions"
                     "(y, z) \<in> r \<inter> actions \<times> actions"
              thus "(a, z) \<in> r\<^sup>+ \<inter> actions \<times> actions" 
                by (metis Int_iff SigmaI mem_Sigma_iff trancl.simps)
            qed blast
          thus "x \<in> ?right" using as2 by simp
        qed
    next
      show "?right \<subseteq> ?left"
        proof
          fix x
          assume as1: "x \<in> ?right"
          obtain a b where as2: "x = (a, b)" by force
          have as3: "a \<in> actions" "b \<in> actions" using as1 as2 by auto
          have "(a, b) \<in> r\<^sup>+" using as1 as2 by auto
          hence "(a, b) \<in> ?left"
            proof (rule converse_trancl_induct)
              fix y
              assume as4: "(y, b) \<in> r"
              hence "(y, b) \<in> calcHb pre wit" using assms(2) by auto
              hence "y \<in> actions" using assms(1) by (metis as3(2) isHbPrefix_simp)                
              thus "(y, b) \<in> ?left" using as3 as4 by fast
            next
              fix y z
              assume as5: "(y, z) \<in> r"
                          "(z, b) \<in> r\<^sup>+"
                          "(z, b) \<in> (r \<inter> actions \<times> actions)\<^sup>+"
              from as5(2) assms(2) have "(z, b) \<in> (calcHb pre wit)\<^sup>+" by (rule trancl_mono)
              hence "(z, b) \<in> calcHb pre wit" unfolding calcHb_def no_consume_hb_def by auto
              with as3(2) assms have as6: "z \<in> actions" by simp
              with as5(1) assms have "y \<in> actions" 
                by (metis isHbPrefix_simp set_rev_mp)
              with as5(1) as6 have "(y, z) \<in> r \<inter> actions \<times> actions" by simp
              thus "(y, b) \<in> ?left" using as5(3) by (rule trancl_into_trancl2)
            qed
          thus "x \<in> ?left" using as2 by simp
        qed
    qed
qed

lemma exRestrict_hb [simp]: 
  assumes "isHbPrefix actions pre wit"
  shows   "calcHb (preExRestrict pre actions) (witnessRestrict wit actions) =
           calcHb pre wit \<inter> actions \<times> actions" 
proof -
  have "sb pre \<union> calcSw pre wit \<subseteq> calcHb pre wit" using assms by auto
  hence "((sb pre \<union> calcSw pre wit) \<inter> actions \<times> actions)\<^sup>+ =
         (sb pre \<union> calcSw pre wit)\<^sup>+ \<inter> actions \<times> actions" using assms by simp
  thus ?thesis unfolding calcHb_def no_consume_hb_def by simp (metis inf_sup_distrib2)
qed

lemma exRestrict_sbasw [simp]: 
  assumes "isHbPrefix actions pre wit"
          "well_formed_threads2 pre wit"
  shows   "sbasw (preExRestrict pre actions) =
           sbasw pre \<inter> actions \<times> actions" 
proof -
  have "sb pre \<union> asw pre \<subseteq> calcHb pre wit" using assms by auto
  hence "((sb pre \<union> asw pre) \<inter> actions \<times> actions)\<^sup>+ =
         (sb pre \<union> asw pre)\<^sup>+ \<inter> actions \<times> actions" using assms by simp
  thus ?thesis unfolding sbasw_def by simp (metis inf_sup_distrib2)
qed

lemma exRestrict_vse [simp]:
  assumes "isHbPrefix actions pre wit"
  shows   "calcVse (preExRestrict pre actions) (witnessRestrict wit actions) =
           calcVse pre wit \<inter> actions \<times> actions"
using assms
unfolding calcVse_def visible_side_effect_set_def
by auto

(* For each consistency predicate X, we prove that X_spec and allSpecResolved implies X; and that
   X_Spec is invariant under restrictions *)

lemma assumptions_initial [simp]:
  shows "assumptions2 initialPreEx initialWitness"
unfolding assumptions2_def assumptions.simps finite_prefixes_def
by simp

(*
lemma assumptions_restriction2:
  shows "assumptions ex"
proof -

  obtain x1 x2 x3 where ex_eq[simp]: "ex = (x1, x2, x3)" by (cases ex) auto

apply (cases ex)
apply simp
unfolding assumptions.simps

using assms
unfolding assumptions2_def assumptions.simps finite_prefixes_def
by auto
*)

lemma assumptions_restriction:
  assumes "assumptions2 pre wit"
  shows   "assumptions2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding assumptions2_def assumptions.simps finite_prefixes_def
by auto

lemma well_formed_threads_initial [simp]:
  shows   "well_formed_threads2 initialPreEx initialWitness"
unfolding well_formed_threads2_def 
          well_formed_threads.simps
          disjoint_creates_def
          finite_prefixes_def
          isIrreflexive_def
          sbasw_def
          indeterminate_sequencing_def
          interthread_def
          threadwise_def
          inj_on_def
          blocking_observed_def
          actions_respect_location_kinds_def
          well_formed_action_def
          relation_over_def
by simp

lemma actions_respect_location_kinds_restriction:
  assumes "actions_respect_location_kinds (actions0 pre) (lk pre)"
  shows   "actions_respect_location_kinds (actions0 pre \<inter> actions) (lk (preExRestrict pre actions))"
unfolding actions_respect_location_kinds_def
proof (intro ballI)
  fix x
  assume assms2: "x \<in> actions0 pre \<inter> actions"
  hence "\<exists>a\<in>actions. loc_of a = loc_of x" by fast
  thus "case x of 
           Lock x xa l xb \<Rightarrow> lk (preExRestrict pre actions) l = Mutex 
         | Unlock x xa l \<Rightarrow> lk (preExRestrict pre actions) l = Mutex
         | Load x xa mem l xb \<Rightarrow> mem = NA \<and> lk (preExRestrict pre actions) l = Non_Atomic \<or> 
                                 mem \<noteq> NA \<and> lk (preExRestrict pre actions) l = Atomic
         | Store x xa mem l xb \<Rightarrow> mem = NA \<and> lk (preExRestrict pre actions) l = Non_Atomic \<or> 
                                  lk (preExRestrict pre actions) l = Atomic 
         | RMW x xa xb l xc xd \<Rightarrow> lk (preExRestrict pre actions) l = Atomic
         | Blocked_rmw x xa l \<Rightarrow> lk (preExRestrict pre actions) l = Atomic | _ \<Rightarrow> True"
    using assms assms2 unfolding actions_respect_location_kinds_def
    by (cases x) auto
qed

lemma well_formed_threads_restriction:
  assumes "isHbPrefix actions pre wit"
          "well_formed_threads2 pre wit"
  shows   "well_formed_threads2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding well_formed_threads2_def 
          well_formed_threads.simps
          well_formed_action.simps
          isStrictPartialOrder_def
          interthread_def
          threadwise_def
          inj_on_def
          disjoint_creates_def
          indeterminate_sequencing_def
          blocking_observed_def
          finite_prefixes_def
using assms(2) (* We unfolded the assumption, but we also need it intact *)
by (auto simp add: actions_respect_location_kinds_restriction)

lemma well_formed_rf_initial [simp]:
  shows   "well_formed_rf2 initialPreEx initialWitness"
unfolding well_formed_rf2_def
by simp

lemma well_formed_rf_restriction:
  assumes "well_formed_rf2 pre wit"
  shows   "well_formed_rf2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding well_formed_rf2_def
by auto

lemma locks_only_consistent_locks_initial [simp]:
  shows   "locks_only_consistent_locks2 initialPreEx initialWitness"
unfolding locks_only_consistent_locks2_def
by simp

lemma locks_only_consistent_locks_restriction:
  assumes "isHbPrefix actions pre wit"
          "well_formed_threads2 pre wit"
          "locks_only_consistent_lo2 pre wit"
  and     "locks_only_consistent_locks2 pre wit"
  shows   "locks_only_consistent_locks2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding locks_only_consistent_locks2_def locks_only_consistent_locks.simps
proof (intro ballI impI, auto)
  fix a c
  assume as1: "\<forall>x\<in>lo wit. case x of (a, c) \<Rightarrow> is_successful_lock a \<and> is_successful_lock c \<longrightarrow>
               (\<exists>b\<in>actions0 pre. is_unlock b \<and> (a, b) \<in> lo wit \<and> (b, c) \<in> lo wit)"
              "(a, c) \<in> lo wit"
              "a \<in> actions"
              "c \<in> actions"
              "is_successful_lock a"
              "is_successful_lock c"
  from this obtain b where as2: "b \<in> actions0 pre \<and> is_unlock b \<and> (a, b) \<in> lo wit \<and> (b, c) \<in> lo wit"
    by (smt splitD)
  have as3: "(b, c) \<in> calcHb pre wit" using as1 as2 assms by simp 
  have "b \<in> actions" using assms(1) as3 as1(4) by (rule isHbPrefix_simp)
  with as2 show "\<exists>ba\<in>actions0 pre \<inter> actions. is_unlock ba \<and> (a, ba) \<in> lo wit \<and> (ba, c) \<in> lo wit" by blast
qed

lemma locks_only_consistent_lo_initial [simp]:
  shows   "locks_only_consistent_lo2 initialPreEx initialWitness"
unfolding locks_only_consistent_lo2_def
by simp

lemma locks_only_consistent_lo_restriction:
  assumes "isHbPrefix actions pre wit"
  and     "locks_only_consistent_lo2 pre wit"
  shows   "locks_only_consistent_lo2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding locks_only_consistent_lo2_def 
by simp

lemma consistent_mo_initial [simp]:
  shows "consistent_mo2 initialPreEx initialWitness"
unfolding consistent_mo2_def
by simp

lemma consistent_mo_restriction:
  assumes "consistent_mo2 pre wit"
  shows   "consistent_mo2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding consistent_mo2_def
by simp

lemma sc_accesses_consistent_sc_initial [simp]:
  shows "sc_accesses_consistent_sc2 initialPreEx initialWitness"
unfolding sc_accesses_consistent_sc2_def
by simp

lemma sc_accesses_consistent_sc_restriction:
  assumes "isHbPrefix actions pre wit"
          "sc_accesses_consistent_sc2 pre wit"
  shows   "sc_accesses_consistent_sc2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding sc_accesses_consistent_sc2_def 
by simp

lemma sc_fenced_sc_fences_heeded_initial [simp]:
  shows "sc_fenced_sc_fences_heeded2 initialPreEx initialWitness"
unfolding sc_fenced_sc_fences_heeded2_def
by simp

lemma sc_fenced_sc_fences_heeded_restriction:
  assumes "sc_fenced_sc_fences_heeded2 pre wit"
  shows   "sc_fenced_sc_fences_heeded2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding sc_fenced_sc_fences_heeded2_def 
by auto

lemma consistent_hb_initial [simp]:
  shows "consistent_hb2 initialPreEx initialWitness"
unfolding consistent_hb2_def
by simp

lemma consistent_hb_restriction:
  assumes "isHbPrefix actions pre wit"
          "consistent_hb2 pre wit"
  shows   "consistent_hb2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding consistent_hb2_def 
by (simp add: isIrreflexive_def)    

lemma det_read_spec_intro [simp]:
  assumes "det_read2 pre wit"
  shows   "det_read2_spec pre wit"
using assms
unfolding det_read2_def det_read2_spec_def 
by auto

lemma det_read_resolved_intro [simp]:
  assumes "det_read2 pre wit"
  shows   "det_read2_resolved pre wit"
using assms
unfolding det_read2_def det_read2_resolved_def
by auto

lemma det_read_spec_initial [simp]:
  shows "det_read2_spec initialPreEx initialWitness"
unfolding det_read2_spec_def det_read2_def
by simp

lemma det_read_spec_resolves:
  assumes "det_read2_resolved pre wit"
  and     "det_read2_spec pre wit"
  shows   "det_read2 pre wit"
using assms
unfolding det_read2_def det_read2_spec_def det_read2_resolved_def
by auto

lemma det_read_spec_restriction:
  assumes "isHbPrefix actions pre wit"
          "det_read2_spec pre wit"
  shows   "det_read2_spec (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding det_read2_spec_def det_read2_def 
by simp (metis Int_iff isHbPrefix_simp vseInHb)

lemma consistent_non_atomic_rf_initial [simp]:
  shows "consistent_non_atomic_rf2 initialPreEx initialWitness"
unfolding consistent_non_atomic_rf2_def
by simp

lemma consistent_non_atomic_rf_restriction:
  assumes "isHbPrefix actions pre wit"
          "consistent_non_atomic_rf2 pre wit"
  shows   "consistent_non_atomic_rf2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding consistent_non_atomic_rf2_def  
by auto

lemma consistent_atomic_rf_initial [simp]:
  shows "consistent_atomic_rf2 initialPreEx initialWitness"
unfolding consistent_atomic_rf2_def
by simp

lemma consistent_atomic_rf_restriction:
  assumes "isHbPrefix actions pre wit"
          "consistent_atomic_rf2 pre wit"
  shows   "consistent_atomic_rf2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding consistent_atomic_rf2_def 
by auto

lemma coherent_memory_use_initial [simp]:
  shows "coherent_memory_use2 initialPreEx initialWitness"
unfolding coherent_memory_use2_def
by simp

lemma coherent_memory_use_restriction:
  assumes "isHbPrefix actions pre wit"
          "coherent_memory_use2 pre wit"
  shows   "coherent_memory_use2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding coherent_memory_use2_def  
by auto

lemma rmw_atomicity_spec_intro [simp]:
  assumes "rmw_atomicity2 pre wit"
  shows   "rmw_atomicity2_spec pre wit"
using assms
unfolding rmw_atomicity2_def rmw_atomicity2_spec_def 
by simp

lemma rmw_atomicity_resolved_intro [simp]:
  assumes "rmw_atomicity2 pre wit"
  shows   "rmw_atomicity2_resolved pre wit"
using assms
unfolding rmw_atomicity2_def rmw_atomicity2_resolved_def 
by simp

lemma rmw_atomicity_spec_initial [simp]:
  shows "rmw_atomicity2_spec initialPreEx initialWitness"
unfolding rmw_atomicity2_spec_def
by simp

lemma rmw_atomicity_spec_resolves:
  assumes "rmw_atomicity2_resolved pre wit"
  and     "rmw_atomicity2_spec pre wit"
  shows   "rmw_atomicity2 pre wit"
using assms
unfolding rmw_atomicity2_def 
          rmw_atomicity2_spec_def 
          rmw_atomicity2_resolved_def
by auto

lemma rmw_atomicity_spec_restriction:
  assumes "isHbPrefix actions pre wit"
          "well_formed_threads2 pre wit"
          "consistent_mo2 pre wit"
          "rmw_atomicity2_spec pre wit"
  shows   "rmw_atomicity2_spec (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding rmw_atomicity2_spec_def adjacent_less_than_def
by auto 

lemma sc_accesses_sc_reads_restricted_initial [simp]:
  shows "sc_accesses_sc_reads_restricted2 initialPreEx initialWitness"
unfolding sc_accesses_sc_reads_restricted2_def
by simp

lemma sc_accesses_sc_reads_restricted_restriction:
  assumes "isHbPrefix actions pre wit"
          "sc_accesses_sc_reads_restricted2 pre wit"
  shows   "sc_accesses_sc_reads_restricted2 (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding sc_accesses_sc_reads_restricted2_def 
by auto

lemma consistency_spec_intro [simp]:
  assumes "exIsConsistent pre wit"
  shows   "exIsConsistent_spec pre wit"
using assms
unfolding exIsConsistent_spec_def exIsConsistent_def
by simp

lemma consistency_resovled_intro [simp]:
  assumes "exIsConsistent pre wit"
  shows   "allSpecsAreResolved pre wit"
using assms
unfolding allSpecsAreResolved_def exIsConsistent_def
by simp
  
lemma consistency_spec_intial [simp]:
  shows "exIsConsistent_spec initialPreEx initialWitness"
unfolding exIsConsistent_spec_def
by simp

lemma consistency_spec_resolves:
  assumes "allSpecsAreResolved pre wit"
  and     "exIsConsistent_spec pre wit"
  shows   "exIsConsistent pre wit"
using assms
unfolding exIsConsistent_spec_def exIsConsistent_def allSpecsAreResolved_def
by (metis det_read_spec_resolves 
          rmw_atomicity_spec_resolves)

lemma consistency_spec_restriction:
  assumes "isHbPrefix actions pre wit"
          "exIsConsistent_spec pre wit"
  shows   "exIsConsistent_spec (preExRestrict pre actions) (witnessRestrict wit actions)"
using assms
unfolding exIsConsistent_spec_def
by (metis assumptions_restriction 
          coherent_memory_use_restriction
          consistent_atomic_rf_restriction
          consistent_hb_restriction
          consistent_mo_restriction
          consistent_non_atomic_rf_restriction
          det_read_spec_restriction
          locks_only_consistent_lo_restriction
          locks_only_consistent_locks_restriction
          rmw_atomicity_spec_restriction
          sc_accesses_consistent_sc_restriction
          sc_accesses_sc_reads_restricted_restriction
          sc_fenced_sc_fences_heeded_restriction
          well_formed_rf_restriction
          well_formed_threads_restriction)

lemma unsequenced_races_initial [simp]:
  shows "\<not>unsequenced_races2 initialPreEx initialWitness"
unfolding unsequenced_races2_def
by simp

lemma data_races_initial [simp]:
  shows "\<not>data_races2 initialPreEx initialWitness"
unfolding data_races2_def
by simp

lemma indeterminate_reads_initial [simp]:
  shows "\<not>indeterminate_reads2 initialPreEx initialWitness"
unfolding indeterminate_reads2_def
by simp

lemma locks_only_bad_mutexes_initial [simp]:
  shows "\<not>locks_only_bad_mutexes2 initialPreEx initialWitness"
unfolding locks_only_bad_mutexes2_def
by simp

lemma exIsDefined_initial [simp]:
  shows "exIsDefined initialPreEx initialWitness"
unfolding exIsDefined_def
by simp

(* --------------------------------------------------------------------------------------------- *)
(* Start of proof *)

lemma traceCorrespondence: 
  assumes "opsemTrace twop s s' trace"
  shows   "twopTrace twop (twopState s) (twopState s') trace"
using assms 
proof (induct trace)
  case opsemReflexive
  show ?case using twopReflexive by simp
next
  case opsemInternalStep
  thus ?case using twopInternalStep by metis
next
  case opsemStep
  thus ?case using twopStep 
    unfolding opsemStep_def by metis
qed

lemma assemblyEqualsPreEx:
  assumes "opsemTrace twop r s trace"
  and     "r = initialState twop c"
  shows   "assemblePreEx trace = preEx s"
using assms
proof (induct trace)
  case (opsemInternalStep twop x y z tail)
  have "preEx z = preEx y" using opsemInternalStep
    thm state.update_convs
    by (metis state.ext_inject state.surjective state.update_convs(1)) 
  thus ?case using opsemInternalStep by simp
next
  case opsemStep
  thus ?case unfolding opsemStep_def by auto
qed auto
  
lemma consistencySpecTrace: 
  assumes "opsemTrace twop r s trace"
  and     "r = initialState twop c"
  shows   "exIsConsistent_spec (preEx s) (exWitness s)"
using assms proof (induct trace)
  case (opsemInternalStep twop x y z tail)
  moreover have "preEx z = preEx y" using opsemInternalStep
    by (metis state.ext_inject state.surjective state.update_convs(1)) 
  moreover have "exWitness z = exWitness y" using opsemInternalStep
    by (metis state.ext_inject state.surjective state.update_convs(1))
  ultimately show ?case by simp
next
  case opsemStep
  thus ?case unfolding opsemStep_def by auto
qed auto

lemma isDefinedCorrespondence:
  assumes "opsemTrace twop r s trace"
          "r = initialState twop c"
  shows   "stateIsDefined s = exIsDefined (preEx s) (exWitness s)"
using assms
proof (induct trace)
  case opsemReflexive
  show ?case using opsemReflexive by simp
next
  case (opsemInternalStep twop x y z tail)
  moreover have "preEx z = preEx y" using opsemInternalStep
    by (metis state.ext_inject state.surjective state.update_convs(1)) 
  moreover have "exWitness z = exWitness y" using opsemInternalStep
    by (metis state.ext_inject state.surjective state.update_convs(1))
  moreover have "stateIsDefined z = stateIsDefined y" using opsemInternalStep
    by (metis state.ext_inject state.surjective state.update_convs(1)) 
  ultimately show ?case by simp
next
  case opsemStep
  thus ?case using twopStep 
    unfolding opsemStep_def by metis
qed 

lemma soundnessConsistency: 
  assumes "opsemConsistent twop c ex"
  shows   "axiomConsistent twop c ex"
using assms
proof -
  fix twop c ex
  assume "opsemConsistent twop c ex"
  from this obtain s trace where as1: "opsemTrace twop (initialState twop c) s trace"
                           and   as2: "preEx s = fst ex \<and> exWitness s = snd ex"
                           and   as3: "allSpecsAreResolved (preEx s) (exWitness s)"
    unfolding opsemConsistent_def by auto
  from as1 as2 assemblyEqualsPreEx traceCorrespondence
  have "twopToTls twop c (fst ex)"
    unfolding twopToTls_def twopInitTrace_def
    by (metis twopState_initialState)
  moreover have "exIsConsistent (fst ex) (snd ex)" 
    by (metis as1 as2 as3 consistencySpecTrace consistency_spec_resolves)
  ultimately show "axiomConsistent twop c ex"
    unfolding axiomConsistent_def twopInitTrace_def by simp
qed

lemma soundnessUndefinedness:
  assumes "opsemUndefined twop c ex"
  shows   "\<exists> ex2. axiomUndefined twop c ex2"
using assms
proof -
  fix twop c ex
  assume as: "opsemUndefined twop c ex"
  from this obtain s trace where as1: "opsemTrace twop (initialState twop c) s trace"
                           and   as2: "preEx s = fst ex \<and> exWitness s = snd ex"
                           and   as3: "\<not> stateIsDefined s"
    unfolding opsemUndefined_def by auto
  hence as4: "\<not>exIsDefined (fst ex) (snd ex)" using isDefinedCorrespondence by metis
  have "opsemConsistent twop c ex" using as
    unfolding opsemUndefined_def opsemConsistent_def by blast
  hence "axiomConsistent twop c ex" using soundnessConsistency by metis
  hence "axiomUndefined twop c ex" using as2 as4
    unfolding axiomUndefined_def by simp  
  thus "\<exists>ex2. axiomUndefined twop c ex2" by blast
qed

lemma foo10:
  assumes "twopTrace twop r s trace"
          "r = init twop c"
          "assemblePreEx trace = preExRestrict pre (actionsOfTrace trace)"
          "respectsHb trace pre wit"
          "exIsConsistent_spec pre wit"
  shows   "\<exists> s'. opsemTrace twop (initialState twop c) s' trace \<and> 
                 exWitness s' = witnessRestrict wit (actionsOfTrace trace) \<and>
                 twopState s' = s"
using assms
proof (induct trace)
  case (twopReflexive twop x)
  thus ?case using opsemReflexive
    by (intro exI[where x="(initialState twop c)"]) simp
next
  case (twopStep twop x y z head tail)
  hence as0: "assemblePreEx tail = preExRestrict pre (actionsOfTrace tail)"
    apply simp sorry (* Most probably true *)
  have "respectsHb tail pre wit" using twopStep by simp
  from this as0 twopStep 
  obtain y' where as1: "opsemTrace twop (initialState twop c) y' tail"
            and   as2: "exWitness y' = witnessRestrict wit (actionsOfTrace tail)"
            and   as3: "twopState y' = y"
    by blast
  let ?newPre  = "preExRestrict pre (actionsOfTrace (head # tail))"
  let ?newWit  = "witnessRestrict wit (actionsOfTrace (head # tail))"
  let ?z'      = "\<lparr>twopState = z, 
                   preEx = ?newPre, 
                   exWitness = ?newWit, 
                   stateIsDefined = exIsDefined ?newPre ?newWit \<rparr>"
  have "exIsConsistent_spec ?newPre ?newWit" using twopStep consistency_spec_restriction by simp
  moreover have "assemblePreEx tail = preEx y'" using as1 assemblyEqualsPreEx by simp
  ultimately have "opsemStep twop y' ?z' head" using twopStep as2 as3
    unfolding opsemStep_def 
    by simp (metis Int_insert_left actionsOfAssembly inf_idem insert_absorb) 
  hence as3: "opsemTrace twop (initialState twop c) ?z' (head#tail)" 
    using as1 opsemStep by metis
  thus ?case by auto
next
  case (twopInternalStep twop x y z tail)
  thus ?case using opsemInternalStep sorry (* Trivial, but not so trivial that auto can do it *)
qed 

lemma foo3:
  assumes "exIsConsistent pre wit"
          "respectsHb trace pre wit"
          "twopTrace twop (init twop c) s trace"
          "assemblePreEx trace = pre"
  shows   "opsemConsistent twop c (pre, wit)"
using assms
proof -
  have as0: "actionsOfTrace trace = actions0 pre" sorry
  hence "assemblePreEx trace = preExRestrict pre (actionsOfTrace trace)" sorry
  from this obtain s' where as1: "opsemTrace twop (initialState twop c) s' trace"
                                 "exWitness s' = witnessRestrict wit (actionsOfTrace trace)"
    using foo10 assms by (metis consistency_spec_intro)
  have as2: "exWitness s' = wit" using as0 as1 sorry
  have "preEx s' = pre" using assemblyEqualsPreEx as1 assms by simp
  with as1 as2 show ?thesis unfolding opsemConsistent_def
    by (metis assms(1) consistency_resovled_intro fst_conv snd_conv)
qed
  
lemma completenessConsistency:
  assumes "twopIsReorderingClosed twop"
          "axiomConsistent twop c ex"
  shows   "opsemConsistent twop c ex"
using assms
proof -
  fix twop :: twop
  fix c :: command 
  fix ex :: observable_execution
  assume as: "axiomConsistent twop c ex"
  from as have consistent: "exIsConsistent (fst ex) (snd ex)" sorry
  from as have "twopToTls twop c (fst ex)" sorry
  from this obtain trace s where as3: "twopTrace twop (init twop c) s trace"
                                       "assemblePreEx trace = fst ex"
    unfolding twopToTls_def twopInitTrace_def by auto
  from assms have prefix: " respectsHb trace (fst ex) (snd ex)" sorry 
  with consistent foo3 as3 show "opsemConsistent twop c ex" by fastforce
qed

lemma completenessUndefinedness:
  assumes "twopIsReorderingClosed twop"
          "axiomUndefined twop c ex"
  shows   "\<exists> ex2. opsemUndefined twop c ex2"
using assms
proof -
  fix twop :: twop
  fix c :: command 
  fix ex :: observable_execution
  assume as: "axiomUndefined twop c ex" 
             "twopIsReorderingClosed twop"
  have as2: "axiomConsistent twop c ex" and
       as3: "\<not>exIsDefined (fst ex) (snd ex)" using as
    unfolding axiomUndefined_def by blast+
  hence "opsemConsistent twop c ex" using completenessConsistency as(2) by metis
  from this obtain s trace where as4: "opsemTrace twop (initialState twop c) s trace"
                           and   as5: "preEx s = fst ex \<and> exWitness s = snd ex"
                           and   as6: "allSpecsAreResolved (preEx s) (exWitness s)"
    unfolding opsemConsistent_def by auto
  hence "\<not> stateIsDefined s" using as3 by (metis exIsDefined_def)
  hence "opsemUndefined twop c ex" using as4 as5 as6
    unfolding opsemUndefined_def opsemConsistent_def by fast
  thus "\<exists> ex2. opsemUndefined twop c ex2" by fast
qed

theorem equivalence:
  assumes "twopIsReorderingClosed twop"
  shows   "opsemBehaviour twop = axiomBehaviour twop"
proof  
  fix command :: Language.command
  from completenessConsistency completenessUndefinedness
       soundnessConsistency soundnessUndefinedness
       assms
  show "opsemBehaviour twop command = axiomBehaviour twop command"
    unfolding opsemBehaviour_def axiomBehaviour_def 
    by (metis Collect_cong)
qed

end 
