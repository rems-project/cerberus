theory "EquivalenceRelationalOpsem"

imports
Main
"_bin/Cmm_master"
"_bin/MinimalOpsem"
"_bin/RelationalOpsem"
"EquivalenceMinimalOpsem"
begin

(* Section 1 - Auxilaries ---------------------------------------------------------------------- *)

(*
lemma incWitRestrict_equality:
  shows "(incWitRestrict wit2 actions = wit) = (relRestrict2 (mo wit2) actions = mo wit \<and>
                                                 relRestrict (rf wit2) actions = rf wit \<and>
                                                 relRestrict (sc wit2) actions = sc wit \<and>
                                                 relRestrict (lo wit2) actions = lo wit \<and>
                                                 relRestrict (ao wit2) actions = ao wit \<and>
                                                 relRestrict (tot wit2) actions = tot wit)"
unfolding incWitRestrict_def
by auto

lemma incWitRestrictI []:
  assumes "relRestrict2 (mo wit2) actions = mo wit"
          "relRestrict (rf wit2) actions = rf wit"
          "relRestrict (sc wit2) actions = sc wit"
          "relRestrict (lo wit2) actions = lo wit"
          "relRestrict (ao wit2) actions = ao wit"
          "relRestrict (tot wit2) actions = tot wit"
  shows "incWitRestrict wit2 actions = wit"
unfolding incWitRestrict_def using assms by auto

lemma incWitRestrictE []:
  assumes "incWitRestrict wit2 actions = wit"
  shows   "relRestrict2 (mo wit2) actions = mo wit"
          "relRestrict (rf wit2) actions = rf wit"
          "relRestrict (sc wit2) actions = sc wit"
          "relRestrict (lo wit2) actions = lo wit"
          "relRestrict (ao wit2) actions = ao wit"
          "relRestrict (tot wit2) actions = tot wit"
unfolding incWitRestrict_def using assms by auto

lemma relRestrict_step:
  assumes "relRestrict r actions = r"
          "a \<notin> actions"
          "r \<subseteq> r2 \<and> r2 - r \<subseteq> {a} \<times> insert a actions \<union> insert a actions \<times> {a}"
  shows   "relRestrict r2 actions = r"
          "relRestrict r2 (insert a actions) = r2"
using assms unfolding relRestrict_def by auto

lemma relRestrict2_step:
  assumes "relRestrict2 r actions = r"
          "a \<notin> actions"
          "r \<subseteq> r2 \<and> r2 - r \<subseteq> {a} \<times> insert a actions"
  shows   "relRestrict2 r2 actions = r"
          "relRestrict2 r2 (insert a actions) = r2"
using assms unfolding relRestrict2_def by auto

lemma incWitRestrict_step [consumes 3, case_names mo rf sc lo ao tot]:
  assumes "incWitRestrict wit actions = wit"
          "a \<notin> actions"
          "actions2 = insert a actions"
          "mo wit \<subseteq> mo wit2 \<and> mo wit2 - mo wit \<subseteq> {a} \<times> insert a actions"
          "rf wit \<subseteq> rf wit2 \<and> rf wit2 - rf wit \<subseteq> {a} \<times> insert a actions \<union> insert a actions \<times> {a}"
          "sc wit \<subseteq> sc wit2 \<and> sc wit2 - sc wit \<subseteq> {a} \<times> insert a actions \<union> insert a actions \<times> {a}"
          "lo wit \<subseteq> lo wit2 \<and> lo wit2 - lo wit \<subseteq> {a} \<times> insert a actions \<union> insert a actions \<times> {a}"
          "ao wit \<subseteq> ao wit2 \<and> ao wit2 - ao wit \<subseteq> {a} \<times> insert a actions \<union> insert a actions \<times> {a}"
          "tot wit \<subseteq> tot wit2 \<and> tot wit2 - tot wit \<subseteq> {a} \<times> insert a actions \<union> insert a actions \<times> {a}"
  shows   "incWitRestrict wit2 actions = wit \<and> incWitRestrict wit2 actions2 = wit2"
oops
*)

(* Section 2 - Soundness ----------------------------------------------------------------------- *)

lemma soundness_relPerformLoad:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformLoad pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_load a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step unfolding relPerformLoad_def by simp_all

(* This is the start of the proof the incWitRestrict ... holds. When it is finished, we do not need
   to assert it in the opsem anymore. *)
(*
lemma incWitRestrict_relPerformLoad:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and wit:       "incWitRestrict (incWit s1) (incCommitted s1) = incWit s1"
      and step:      "relPerformLoad pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "a \<notin> incCommitted s1"
  shows  "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1 \<and> 
          incWitRestrict (incWit s2) (incCommitted s2) = incWit s2"
using wit a incCommitted
proof (cases rule: incWitRestrict_step)
  case mo
  show "mo (incWit s1) \<subseteq> mo (incWit s2) \<and> mo (incWit s2) - mo (incWit s1) \<subseteq> {a} \<times> insert a (incCommitted s1)"
    using step unfolding relPerformLoad_def by auto
next
  case rf
  show "rf (incWit s1) \<subseteq> rf (incWit s2) \<and> rf (incWit s2) - rf (incWit s1) \<subseteq> {a} \<times> insert a (incCommitted s1) \<union> insert a (incCommitted s1) \<times> {a}"
    using step unfolding relPerformLoad_def rf_step_load_def 
    apply (cases "\<exists>w\<in>actions0 pre. (w, a) \<in> getVse pre (incWit s2)") apply auto
oops
*)

lemma soundness_relPerformStore:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformStore pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_store a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformStore_def 
by simp_all

lemma soundness_relPerformRmw:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformRmw pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_RMW a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformRmw_def 
by simp_all

lemma soundness_relPerformBlocked_rmw:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformBlocked_rmw pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_blocked_rmw a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformBlocked_rmw_def 
by simp_all

lemma soundness_relPerformLock:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformLock pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_lock a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformLock_def 
by simp_all

lemma soundness_relPerformUnlock:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformUnlock pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_unlock a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformUnlock_def 
by simp_all

lemma soundness_relPerformFence:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformFence pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_fence a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformFence_def 
by simp_all

lemma soundness_relPerformAlloc:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformAlloc pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_alloc a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformAlloc_def 
by simp_all

lemma soundness_relPerformDealloc:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relPerformDealloc pre s1 s2 a"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_dealloc a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows  "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
         "incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
using step
unfolding relPerformDealloc_def 
by simp_all

lemma soundness_step:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "relOpsemStep pre s1 s2 a"
  shows              "minOpsemStep pre s1 s2 a"
proof -
  have a: "a \<in> actions0 pre \<and> a \<notin> incCommitted s1 \<and> incCommitted s2 = insert a (incCommitted s1)"
    using step unfolding relOpsemStep_def by simp
  have order: "isInOpsemOrder_step pre s1 s2 a"
    using step unfolding relOpsemStep_def by simp
  have definedness: "stateIsDefined s2 = exIsDefined (pre, incWit s2, getRelations pre (incWit s2))"
    using step unfolding relOpsemStep_def by simp
  have "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2)) \<and> 
        incWitRestrict (incWit s2) (incCommitted s1) = incWit s1"
    proof (cases a)
      case Load
      hence "is_load a" by auto
      have "relPerformLoad pre s1 s2 a" 
        using step Load unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformLoad[OF cons] 
        using a `is_load a` by auto
    next
      case Store
      hence "is_store a" by auto
      have "relPerformStore pre s1 s2 a" 
        using step Store unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformStore[OF cons]
        using a `is_store a` by auto
    next
      case RMW
      hence "is_RMW a" by auto
      have "relPerformRmw pre s1 s2 a" 
        using step RMW unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformRmw[OF cons]
        using a `is_RMW a` by auto
    next
      case Blocked_rmw
      hence "is_blocked_rmw a" by auto
      have "relPerformBlocked_rmw pre s1 s2 a" 
        using step Blocked_rmw unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformBlocked_rmw[OF cons]
        using a `is_blocked_rmw a` by auto
    next
      case Lock
      hence "is_lock a" by auto
      have "relPerformLock pre s1 s2 a" 
        using step Lock unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformLock[OF cons]
        using a `is_lock a` by auto
    next
      case Unlock
      hence "is_unlock a" by auto
      have "relPerformUnlock pre s1 s2 a" 
        using step Unlock unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformUnlock[OF cons]
        using a `is_unlock a` by auto
    next
      case Fence
      hence "is_fence a" by auto
      have "relPerformFence pre s1 s2 a" 
        using step Fence unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformFence[OF cons]
        using a `is_fence a` by auto
    next
      case Alloc
      hence "is_alloc a" by auto
      have "relPerformAlloc pre s1 s2 a" 
        using step Alloc unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformAlloc[OF cons]
        using a `is_alloc a` by auto
    next
      case Dealloc
      hence "is_dealloc a" by auto
      have "relPerformDealloc pre s1 s2 a" 
        using step Dealloc unfolding relOpsemStep_def by simp
      thus ?thesis 
        using soundness_relPerformDealloc[OF cons]
        using a `is_dealloc a` by auto
    qed
  thus ?thesis 
    using a order definedness
    unfolding minOpsemStep_def isInOpsemOrder_step_def 
    by auto
qed  

(* Consistency of initialWitness *)

lemma assumptions_initialWitness [simp]:
  shows "assumptions (pre, initialWitness, [])"
unfolding assumptions.simps
by simp

lemma det_read_op_initialWitness [simp]:
  shows "det_read_op {} (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
unfolding det_read_op.simps
by simp

lemma coherent_memory_use_initialWitness [simp]:
  shows "coherent_memory_use (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
unfolding coherent_memory_use.simps
by simp

lemma consistent_atomic_rf_initialWitness [simp]:
  shows "consistent_atomic_rf (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
unfolding consistent_atomic_rf.simps
by simp

lemma consistent_mo_op_initialWitness [simp]:
  shows "consistent_mo_op {} (pre, initialWitness, [])"
unfolding consistent_mo_op.simps
by simp

lemma consistent_non_atomic_rf_initialWitness [simp]:
  shows "consistent_non_atomic_rf (pre, initialWitness, [(''hb'', getHb pre initialWitness), (''vse'', getVse pre initialWitness)])"
unfolding consistent_non_atomic_rf.simps
by simp

lemma isInOpsemOrder_initialWitness [simp]:
  shows "isInOpsemOrder {} (pre, initialWitness, [])"
unfolding isInOpsemOrder_def
by simp

lemma locks_only_consistent_lo_op_initialWitness [simp]:
  shows "locks_only_consistent_lo_op {} (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
unfolding locks_only_consistent_lo_op.simps
by simp

lemma locks_only_consistent_locks_op_initialWitness [simp]:
  shows "locks_only_consistent_locks_op {} (pre, initialWitness, [])"
unfolding locks_only_consistent_locks_op.simps
by simp

lemma rmw_atomicity_op_initialWitness [simp]:
  shows "rmw_atomicity_op {} (pre, initialWitness, [])"
unfolding rmw_atomicity_op.simps
by simp

lemma sc_accesses_consistent_sc_op_initialWitness [simp]:
  shows "sc_accesses_consistent_sc_op {} (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
unfolding sc_accesses_consistent_sc_op.simps
by simp

lemma sc_accesses_sc_reads_restricted_initialWitness [simp]:
  shows "sc_accesses_sc_reads_restricted (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
unfolding sc_accesses_sc_reads_restricted.simps
by simp

lemma sc_fenced_sc_fences_heeded_initialWitness [simp]:
  shows "sc_fenced_sc_fences_heeded (pre, initialWitness, [])"
unfolding sc_fenced_sc_fences_heeded.simps
by simp

lemma tot_empty_initialWitness [simp]:
  shows "tot_empty (pre, initialWitness, [])"
unfolding tot_empty.simps
by simp

lemma well_formed_rf_op_initialWitness [simp]:
  shows "well_formed_rf_op {} (pre, initialWitness, [])"
unfolding well_formed_rf_op.simps
by simp

(* Top level soundness predicates *)

lemma soundnessRelTrace_aux:
  assumes "relOpsemTrace pre r s"
          "r = initialState pre"
  shows   "minOpsemTrace pre r s"
using assms
proof induct
  case (relOpsemReflexive pre s)
  hence "well_formed_threads (pre, initialWitness, [])"
  and   "consistent_hb (pre, initialWitness, getRelations pre initialWitness)"
    unfolding Let_def release_acquire_fenced_relations_simp release_acquire_fenced_relations_alt_def
    by auto
  hence "exIsConsistent_op {} (pre, initialWitness, getRelations pre initialWitness)"
    unfolding exIsConsistent_op_def release_acquire_fenced_relations_simp release_acquire_fenced_relations_alt_def
    by auto
  thus "minOpsemTrace pre s s"
    using minOpsemReflexive relOpsemReflexive by auto
next
  case (relOpsemStep pre x y z a)
  have x: "x = initialState pre" using relOpsemStep by auto
  have minTrace: "minOpsemTrace pre x y" using relOpsemStep by auto
  have cons: "exIsConsistent_op (incCommitted y) (pre, incWit y, getRelations pre (incWit y))"
    using EquivalenceMinimalOpsem.consistencySpecTrace[OF minTrace x] .    
  have "minOpsemStep pre y z a" 
    using soundness_step[OF cons] relOpsemStep by auto
  thus "minOpsemTrace pre x z"
    using `minOpsemTrace pre x y` minOpsemStep[where ?pre0.0=pre] by auto
qed

corollary soundnessRelTrace:
  assumes "relOpsemTrace pre (initialState pre) s"
  shows   "minOpsemTrace pre (initialState pre) s"
using assms soundnessRelTrace_aux by simp  

(* Section X - completeness stepwise consistency predicates ------------------------------------ *)

(* mo-order *)

lemma consistent_mo_aux1:
  assumes cons:   "axsimpConsistent (pre, wit, getRelations pre wit)"
      and ab_def: "a \<in> actions0 pre \<and>
                   b \<in> actions0 pre \<and>
                   a \<noteq> b \<and>
                   is_write a \<and>
                   is_write b \<and>
                   loc_of a = loc_of b \<and>
                   is_at_atomic_location (lk pre) a \<and>
                   (a \<in> actions \<or> b \<in> actions)"
  shows           "(a, b) \<in> mo wit \<or> (b, a) \<in> mo wit"
proof -
  have cons_mo: "consistent_mo_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  thus ?thesis 
    using ab_def
    unfolding consistent_mo_op.simps relation_over_def by auto  
qed

lemma consistent_mo_aux2:
  assumes cons:  "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_mo: "(a, b) \<in> mo wit"
    shows        "a \<in> actions0 pre \<and>
                  b \<in> actions0 pre \<and>
                  a \<noteq> b \<and>
                  is_write a \<and>
                  is_write b \<and>
                  loc_of a = loc_of b \<and>
                  is_at_atomic_location (lk pre) a \<and>
                  is_at_atomic_location (lk pre) b \<and>
                  a \<in> actions \<and>
                  (b, a) \<notin> mo wit"
proof -
  have cons_mo: "consistent_mo_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  have "irrefl (mo wit)" "trans (mo wit)"
    using cons_mo unfolding consistent_mo_op.simps by simp_all
  hence "(b, a) \<notin> mo wit" 
    using in_mo unfolding irrefl_def trans_def by auto 
  have "relOver (mo wit) (actions0 pre)" 
    using cons_mo unfolding consistent_mo_op.simps relation_over_def by simp
  hence abInPreActions: "a \<in> actions0 pre" "b \<in> actions0 pre" 
    using in_mo relOver_simp by auto
  hence "loc_of a = loc_of b \<and> is_at_atomic_location (lk pre) a"
    using cons_mo in_mo unfolding consistent_mo_op.simps relation_over_def by auto
  hence "is_at_atomic_location (lk pre) b"
    unfolding is_at_atomic_location_def by auto
  thus ?thesis
    using cons_mo in_mo abInPreActions `(b, a) \<notin> mo wit`
    unfolding consistent_mo_op.simps relation_over_def by auto  
qed

lemma step_mo_not_atomic_write:
  assumes cons:      "axsimpConsistent (pre, wit', getRelations pre wit')"
      and wit:       "wit = incWitRestrict wit' (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "is_at_non_atomic_location (lk pre) a \<or> \<not> is_write a"
  shows              "mo wit' = mo wit"
proof (intro Set.equalityI subsetI, auto)
  fix b c
  assume "(b, c) \<in> mo wit"
  hence "(b, c) \<in> mo (incWitRestrict wit' (incCommitted s))" using wit by simp
  thus "(b, c) \<in> mo wit'" by simp
next
  fix b c
  assume in_mo: "(b, c) \<in> mo wit'"
  have b: "b \<in> insert a (incCommitted s)"
    using cons in_mo consistent_mo_aux2 incCommitted by metis
  have "is_at_atomic_location (lk pre) b \<and> is_write b"
    using cons in_mo consistent_mo_aux2 by metis
  hence "a \<noteq> b" using a at_implies_not_na by auto
  hence "b \<in> incCommitted s" using b by simp
  hence "(b, c) \<in> mo (incWitRestrict wit' (incCommitted s))" 
    using `(b, c) \<in> mo wit'` by simp
  thus "(b, c) \<in> mo wit" using wit by simp
qed

lemma step_mo_atomic_write:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "is_at_atomic_location (lk pre) a \<and> is_write a \<and> a \<in> actions0 pre \<and> a \<notin> incCommitted s"
  shows          "mo_step_atomic_write pre s s' a"
unfolding mo_step_atomic_write_def Let_def
proof -
  let ?succ     = "Pair a ` {x \<in> actions0 pre. x \<notin> incCommitted s \<and> x \<noteq> a \<and> is_write x \<and> loc_of x = loc_of a}"
  let ?new_mo   = "mo (incWit s) \<union> ?succ"
  show "mo (incWit s')  = ?new_mo"
    proof (intro equalityI subsetI)
      fix x
      assume "x \<in> mo (incWit s')"
      then obtain b c where "(b, c) = x" "(b, c) \<in> mo (incWit s')" by (cases x) fast
      have "(b, c) \<in> ?new_mo"
        proof (cases "b = a")
        next
          assume "b = a"
          have not_in_mo_bc: "(b, c) \<notin> mo (incWit s)" using a wit `b = a` by auto
          have "(c, b) \<notin> mo (incWit s')" 
            using consistent_mo_aux2[OF cons2 `(b, c) \<in> mo (incWit s')`] by simp
          hence not_in_mo_cb: "(c, b) \<notin> mo (incWit s)" using wit by auto 
          have "c \<notin> incCommitted s"
            proof
              assume "c \<in> incCommitted s"
              have "b \<in> actions0 pre \<and> c \<in> actions0 pre \<and> b \<noteq> c \<and> 
                    is_write b \<and> is_write c \<and> loc_of b = loc_of c \<and> 
                    is_at_atomic_location (lk pre) b"
                using consistent_mo_aux2[OF cons2 `(b, c) \<in> mo (incWit s')`] incCommitted
                by auto
              hence "(b, c) \<in> mo (incWit s) \<or> (c, b) \<in> mo (incWit s)"
                using `c \<in> incCommitted s` consistent_mo_aux1[OF cons1] by auto
              thus False using not_in_mo_bc not_in_mo_cb by simp
              qed
          hence "(b, c) \<in> ?succ"
            using `b = a` consistent_mo_aux2[OF cons2 `(b, c) \<in> mo (incWit s')`] by auto
          thus "(b, c) \<in> ?new_mo" by simp
        next
          assume "b \<noteq> a"
          hence "b \<in> incCommitted s" 
            using consistent_mo_aux2[OF cons2 `(b, c) \<in> mo (incWit s')`] incCommitted by auto  
          hence "(b, c) \<in> mo (incWit s)"
            using wit `(b, c) \<in> mo (incWit s')` by auto
          thus "(b, c) \<in> ?new_mo" by simp
        qed
      thus "x \<in> ?new_mo" using `(b, c) = x` by simp
    next
      fix x
      assume "x \<in> ?new_mo"
      show "x \<in> mo (incWit s')"
        using `x \<in> ?new_mo`
        proof (elim UnE)
          assume "x \<in> mo (incWit s)" 
          thus "x \<in> mo (incWit s')" using wit by auto
        next
          assume "x \<in> ?succ"
          then obtain b c where "(b, c) = x" "(b, c) \<in> ?succ" by (cases x) fast
          hence "(c, b) \<notin> mo (incWit s')" using consistent_mo_aux2[OF cons2] incCommitted by fast
          hence "(b, c) \<in> mo (incWit s')"
            using `(b, c) \<in> ?succ` a cons2 incCommitted 
            using consistent_mo_aux1[where a=a and b=c and wit="incWit s'"] 
            by auto
          thus "x \<in> mo (incWit s')" using `(b, c) = x` by simp
        qed
    qed
qed

(* rf-order *)

lemma well_formed_rf_aux:
  assumes cons:  "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_rf: "(a, b) \<in> rf wit"
  shows          "a \<in> actions0 pre \<and>
                  b \<in> actions0 pre \<and> 
                  a \<in> actions \<and> 
                  b \<in> actions \<and> 
                  loc_of a = loc_of b \<and> 
                  is_write a \<and> 
                  is_read b \<and> 
                  a \<noteq> b \<and>
                  value_read_by b = value_written_by a"
proof -
  have cons_rf: "well_formed_rf_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  have cons_rmw: "rmw_atomicity_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  have cons_mo: "consistent_mo_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  have "a \<noteq> b"
    proof
      assume "a = b"
      have ab: "is_write a \<and> is_read b \<and> a \<in> actions0 pre \<and> a \<in> actions"
        using in_rf cons_rf unfolding well_formed_rf_op.simps by auto
      hence "is_RMW a" using `a = b` by (cases a) auto
      hence "adjacent_less_than (mo wit) (actions0 pre) a a" 
        using cons_rmw ab `a = b` in_rf unfolding rmw_atomicity_op.simps by auto
      hence "(a, a) \<in> mo wit" unfolding adjacent_less_than_def by simp
      thus False using cons_mo unfolding consistent_mo_op.simps irrefl_def by auto
    qed
  thus ?thesis
    using in_rf cons_rf unfolding well_formed_rf_op.simps by auto
qed

lemma well_formed_rf_aux2:
  assumes cons:  "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_rf: "(a, c) \<in> rf wit"
                 "(b, c) \<in> rf wit"
  shows          "a = b"
proof -
  have "b \<in> actions0 pre"
    using cons in_rf well_formed_rf_aux by metis
  have cons_rf: "well_formed_rf_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  hence "\<forall>a'\<in>actions0 pre. (a', c) \<in> rf wit \<longrightarrow> a = a'"
    using in_rf unfolding well_formed_rf_op.simps by auto
  thus ?thesis
    using in_rf `b \<in> actions0 pre` by metis
qed

lemma det_read_aux:
  assumes cons: "axsimpConsistent (pre, wit, getRelations pre wit)"
      and b:    "is_load b \<and> b \<in> actions"
    shows       "(\<exists>a.   (a, b) \<in> getHb pre wit \<and> is_write a \<and> loc_of a = loc_of b) 
                      = (\<exists>a'. (a', b) \<in> rf wit)"
proof (intro iffI, auto)
  fix a
  assume a: "(a, b) \<in> getHb pre wit" "is_write a" "loc_of a = loc_of b"
  have "well_formed_threads (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  hence relOver_sb: "relOver (sb pre) (actions0 pre)"
    unfolding well_formed_threads.simps by simp
  have det_read: "det_read_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  have "a \<in> actions0 pre" "b \<in> actions0 pre" 
    using a hbRelOver relOver_simp relOver_sb by fast+
  hence "\<exists>a'\<in>actions0 pre. (a', b) \<in> getHb pre wit \<and> is_write a' \<and> loc_of a' = loc_of b"
    using a by auto
  hence "\<exists>a'\<in>actions0 pre. (a', b) \<in> rf wit" 
    using det_read b `b \<in> actions0 pre`
    unfolding det_read_op.simps getRelations_def
    by auto
  thus "\<exists>a'. (a', b) \<in> rf wit" by auto
next
  fix a 
  have det_read: "det_read_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  assume in_rf: "(a, b) \<in> rf wit"
  hence "a \<in> actions0 pre"  "b \<in> actions0 pre" using cons well_formed_rf_aux by auto
  hence "\<exists>a'\<in>actions0 pre. (a', b) \<in> rf wit" using in_rf by auto
  hence "\<exists>a'\<in>actions0 pre. (a', b) \<in> getHb pre wit \<and> is_write a' \<and> loc_of a' = loc_of b"
    using det_read b `b \<in> actions0 pre` 
    unfolding det_read_op.simps getRelations_def
    by auto
  thus "\<exists>a. (a, b) \<in> getHb pre wit \<and> is_write a \<and> loc_of a = loc_of b" by auto
qed

lemma rmw_atomicity_aux:
  assumes cons: "axsimpConsistent (pre, wit, getRelations pre wit)"
      and b:    "is_RMW b \<and> b \<in> actions"
    shows       "adjacent_less_than (mo wit) (actions0 pre) a b = ((a, b) \<in> rf wit)"
proof 
  assume in_rf: "(a, b) \<in> rf wit"
  hence in_pre_actions: "a \<in> actions0 pre" "b \<in> actions0 pre"
    using well_formed_rf_aux[OF cons] by simp_all
  have rmw_at: "rmw_atomicity_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  thus "adjacent_less_than (mo wit) (actions0 pre) a b"
    unfolding rmw_atomicity_op.simps
    using in_pre_actions b in_rf
    by auto
next
  assume in_mo: "adjacent_less_than (mo wit) (actions0 pre) a b"
  hence "(a, b) \<in> mo wit" unfolding adjacent_less_than_def by simp
  hence in_pre_actions: "a \<in> actions0 pre" "b \<in> actions0 pre"
    using consistent_mo_aux2[OF cons] by simp_all
  have rmw_at: "rmw_atomicity_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  thus "(a, b) \<in> rf wit"
    unfolding rmw_atomicity_op.simps
    using in_pre_actions b in_mo
    by auto
qed

lemma step_rf_aux:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and order:     "isInOpsemOrder_step pre s s' a"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and in_rf:     "(b, c) \<in> rf (incWit s')"
  shows              "(b, c) \<in> rf (incWit s ) \<or> (c = a)"
proof (intro disjCI)
  assume "c \<noteq> a"
  hence b: "b \<in> insert a (incCommitted s)" and c: "c \<in> incCommitted s"
    using in_rf well_formed_rf_aux[OF cons2] incCommitted by auto
  have "c \<in> actions0 pre" 
    using well_formed_rf_aux[OF cons2 in_rf] by simp
  hence "(a, c) \<notin> opsemOrder (pre, (incWit s'), getRelations pre (incWit s'))"
    using order `c \<in> incCommitted s` unfolding isInOpsemOrder_step_def by auto
  hence "(a, c) \<notin> rf (incWit s')"
    unfolding opsemOrder.simps by auto
  hence "a \<noteq> b" using in_rf by auto
  hence "b \<in> incCommitted s" using b by simp
  hence "(b, c) \<in> rf (incWitRestrict (incWit s') (incCommitted s))" using in_rf c by simp
  thus "(b, c) \<in> rf (incWit s)" using wit by simp
qed  

lemma step_rf_aux2:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and order:     "isInOpsemOrder_step pre s s' a"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and in_rf:     "(w, a) \<in> rf (incWit s')"
  shows              "rf (incWit s') = insert (w, a) (rf (incWit s))"
(* TODO: remove applies *)
apply (intro equalityI subsetI) apply clarify defer apply clarsimp apply (elim disjE)
proof -
  fix b c
  assume "b = w \<and> c = a"
  thus "(b, c) \<in> rf (incWit s')" using in_rf by simp
next
  fix b c
  assume "(b, c) \<in> rf (incWit s)"
  thus "(b, c) \<in> rf (incWit s')" using wit by auto
next
  fix b c
  assume bc_in_rf2:  "(b, c) \<in> rf (incWit s')"
     and bc_nin_rf1: "(b, c) \<notin> rf (incWit s)"
  have "(b, c) \<in> rf (incWit s) \<or> (c = a)"
    using step_rf_aux[OF cons1 cons2 order wit incCommitted bc_in_rf2] .
  hence "c = a" using bc_nin_rf1 by simp
  thus "b = w \<and> c = a" using bc_in_rf2 well_formed_rf_aux2[OF cons2 in_rf] by simp
qed

lemma step_rf_non_read:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and order:     "isInOpsemOrder_step pre s s' a"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "\<not> is_read a"
  shows              "rf (incWit s') = rf (incWit s)"
proof (intro Set.equalityI subsetI, auto)
  fix b c
  assume "(b, c) \<in> rf (incWit s)"
  hence "(b, c) \<in> rf (incWitRestrict (incWit s') (incCommitted s))" using wit by simp
  thus "(b, c) \<in> rf (incWit s')" by simp
next
  fix b c
  assume in_rf: "(b, c) \<in> rf (incWit s')"
  have "is_read c"
    using well_formed_rf_aux[OF cons2 in_rf] by simp
  hence "a \<noteq> c" using a by auto
  have "(b, c) \<in> rf (incWit s) \<or> (c = a)"
    using step_rf_aux[OF cons1 cons2 order wit incCommitted in_rf] .
  thus "(b, c) \<in> rf (incWit s)" using `a \<noteq> c` by simp
qed

(* TODO: refactor *)
lemma vse_simp [simp]:
  shows "RelationalOpsem.getHb = getHb"
apply (intro ext)
unfolding RelationalOpsem.getHb_def 
          getRelations_def
by auto

lemma step_rf_load:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and order:     "isInOpsemOrder_step pre s s' a"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "is_load a \<and> a \<in> actions0 pre"
  shows              "rf_step_load pre s s' a"
unfolding rf_step_load_def
proof auto
  fix b c
  assume "(b, c) \<in> rf (incWit s)"
  thus "(b, c) \<in> rf (incWit s')" using wit by auto
next
  fix b c
  assume in_rf:  "(b, c) \<in> rf (incWit s')"
     and no_vse: "     \<forall>w\<in>actions0 pre. is_write w
                   \<longrightarrow> (w, a) \<in> EquivalenceMinimalOpsem.getHb pre (incWit s')
                   \<longrightarrow> loc_of w \<noteq> loc_of a"
  have "det_read_op (incCommitted s') (pre, incWit s', getRelations pre (incWit s'))"
    using cons2 unfolding exIsConsistent_op_def by simp
  hence "  (\<exists>w\<in>actions0 pre. (w, a) \<in> getHb pre (incWit s') \<and> is_write w \<and> loc_of w = loc_of a) 
         = (\<exists>w'\<in>actions0 pre. (w', a) \<in> rf (incWit s'))"
    using a incCommitted 
    apply simp
    unfolding det_read_op.simps 
    by auto
  hence no_rf: "\<forall>w\<in>actions0 pre. (w, a) \<notin> rf (incWit s')"
    using no_vse by auto    
  have "b \<in> actions0 pre" using well_formed_rf_aux[OF cons2 in_rf] by simp
  hence "(b, a) \<notin> rf (incWit s')" using no_rf by simp
  hence "c \<noteq> a" using in_rf by auto
  have "(b, c) \<in> rf (incWit s) \<or> (c = a)"
    using step_rf_aux[OF cons1 cons2 order wit incCommitted in_rf] .
  thus "(b, c) \<in> rf (incWit s)" using `c \<noteq> a` by simp
next
  fix w'
  assume "w' \<in> actions0 pre" 
         "(w', a) \<in> getHb pre (incWit s')"
         "is_write w'" "loc_of w' = loc_of a"
  hence "\<exists>w. (w, a) \<in> rf (incWit s')" using det_read_aux[OF cons2] a incCommitted by auto
  then obtain w where w_in_rf: "(w, a) \<in> rf (incWit s')" by fast
  have w: "w \<in> actions0 pre \<and> w \<in> incCommitted s \<and> is_write w \<and> loc_of w = loc_of a \<and> 
            value_written_by w = value_read_by a"
    using well_formed_rf_aux[OF cons2 w_in_rf] incCommitted by auto
  have "rf (incWit s') = insert (w, a) (rf (incWit s))"
    using step_rf_aux2[OF cons1 cons2 order wit incCommitted w_in_rf] .
  thus "\<exists>w\<in>actions0 pre. w \<in> incCommitted s \<and> is_write w \<and> loc_of w = loc_of a \<and> 
        value_written_by w = value_read_by a \<and> 
        rf (incWit s') = insert (w, a) (rf (incWit s))"
     using w by auto
qed

lemma step_rf_rmw:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and order:     "isInOpsemOrder_step pre s s' a"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "is_RMW a \<and> a \<in> actions0 pre \<and> a \<notin> incCommitted s"
  shows              "rf_step_rmw pre s s' a"
proof -
  let ?same_loc_writes = "{x \<in> incCommitted s. x \<in> actions0 pre \<and> is_write x \<and> loc_of x = loc_of a}"
  show ?thesis
    proof (cases "?same_loc_writes = {}")
      assume empty: "?same_loc_writes = {}"
      have "rf (incWit s') = rf (incWit s)"
        proof (auto)
          fix b c
          assume "(b, c) \<in> rf (incWit s)"
          thus "(b, c) \<in> rf (incWit s')" using wit by auto
        next
          fix b c
          assume in_rf: "(b, c) \<in> rf (incWit s')"
          have no_mo: "\<forall>w. w \<in> incCommitted s \<longrightarrow> w \<in> actions0 pre \<longrightarrow> is_write w \<longrightarrow> loc_of w \<noteq> loc_of a"
            using empty by auto
          have "b =  a \<or> b \<in> incCommitted s" using well_formed_rf_aux[OF cons2 in_rf] incCommitted by simp
          hence "(b, a) \<notin> mo (incWit s')"
            proof
              assume "b = a"
              thus "(b, a) \<notin> mo (incWit s')" using consistent_mo_aux2[OF cons2] by auto
            next
              assume "b \<in> incCommitted s"
              have "is_write b" "b \<in> actions0 pre" using well_formed_rf_aux[OF cons2 in_rf] by simp_all
              hence "loc_of b \<noteq> loc_of a" using no_mo `b \<in> incCommitted s` by simp
              thus "(b, a) \<notin> mo (incWit s')" using consistent_mo_aux2[OF cons2] by auto
            qed
          hence "\<not> adjacent_less_than (mo (incWit s')) (actions0 pre) b a"
            unfolding adjacent_less_than_def by simp
          hence "(b, a) \<notin> rf (incWit s')" 
            using rmw_atomicity_aux[OF cons2] a incCommitted by auto
          hence "c \<noteq> a" using in_rf by auto
          have "(b, c) \<in> rf (incWit s) \<or> (c = a)"
            using step_rf_aux[OF cons1 cons2 order wit incCommitted in_rf] .
          thus "(b, c) \<in> rf (incWit s)" using `c \<noteq> a` by simp
        qed
      thus ?thesis unfolding rf_step_rmw_def using empty by auto
    next
      assume not_empty: "?same_loc_writes \<noteq> {}"
      let ?S = "{w. w \<in> actions0 pre \<and> (w, a) \<in> mo (incWit s')}"
      have eq_sets: "?S = ?same_loc_writes"
        proof (intro equalityI subsetI, simp_all)
          fix w'
          assume w': "w' \<in> incCommitted s \<and> w' \<in> actions0 pre \<and> is_write w' \<and> loc_of w' = loc_of a"
          have "is_write a" using a by (cases a) auto
          have "w' \<noteq> a" using a w' by auto
          have "actions_respect_location_kinds (actions0 pre) (lk pre)"
            using cons1 unfolding exIsConsistent_op_def well_formed_threads.simps by simp
          hence "is_at_atomic_location (lk pre) a"
            unfolding actions_respect_location_kinds_def is_at_atomic_location_def
            using a by (cases a) auto
          hence mo_related: "(w', a) \<in> mo (incWit s) \<or> (a, w') \<in> mo (incWit s)" 
            using consistent_mo_aux1[OF cons1, where a=a and b=w']
            using w' a incCommitted `is_write a` `w' \<noteq> a` 
            by auto
          have "(a, w') \<notin> mo (incWit s)"
            using consistent_mo_aux2[OF cons1] a by auto 
          hence "(w', a) \<in> mo (incWit s)" using mo_related by simp
          thus "(w', a) \<in> mo (incWit s')" using wit by simp
        next
          fix w'
          assume "w' \<in> actions0 pre \<and> (w', a) \<in> mo (incWit s')"
          thus "w' \<in> incCommitted s \<and> is_write w' \<and> loc_of w' = loc_of a"
            using consistent_mo_aux2[OF cons2, where a=w' and b=a] incCommitted 
            by auto
        qed
      hence non_empty: "?S \<noteq> {}" using not_empty by simp
      have "assumptions (pre, incWit s' , [])" 
        using cons2 unfolding exIsConsistent_op_def by simp
      hence "finite_prefixes (mo (incWit s')) (actions0 pre)"
        unfolding assumptions.simps by simp
      hence finite: "finite ?S"
        unfolding finite_prefixes_def using a by fast
      hence "irrefl (mo (incWit s')) \<and> trans (mo (incWit s'))"
        using cons2 unfolding exIsConsistent_op_def consistent_mo_op.simps by auto
      hence isOrder: "isStrictPartialOrder (mo (incWit s'))" unfolding isStrictPartialOrder_def .
      obtain w where "w \<in> ?S \<and> (\<forall>y. y \<in> ?S \<longrightarrow> (w, y) \<notin> mo (incWit s'))"
        using supremum_partial_order[OF finite non_empty isOrder] by auto
      hence w:    "w \<in> actions0 pre \<and> (w, a) \<in> mo (incWit s')"
      and   w2:   "w \<in> ?same_loc_writes"
      and   max:  "\<forall>y. y \<in> actions0 pre \<and> (y, a) \<in> mo (incWit s') \<longrightarrow> (w, y) \<notin> mo (incWit s')"
        using eq_sets by auto
      have max2: "\<forall>y. y \<in> ?same_loc_writes \<longrightarrow> (w, y) \<notin> mo (incWit s)"
        using max wit eq_sets by auto
      have adjacent: "adjacent_less_than (mo (incWit s')) (actions0 pre) w a"
        using w max unfolding adjacent_less_than_def by auto
      hence w_in_rf: "(w, a) \<in> rf (incWit s')"
        using cons2 a w incCommitted unfolding exIsConsistent_op_def rmw_atomicity_op.simps by auto
      have "rf (incWit s') = insert (w, a) (rf (incWit s))"
        using step_rf_aux2[OF cons1 cons2 order wit incCommitted w_in_rf] .
      thus ?thesis unfolding rf_step_rmw_def using not_empty w2 max2 by auto
    qed
qed

(* sc-order *)

lemma consistent_sc_aux1:
  assumes cons:     "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_sc:    "(b, c) \<in> sc wit"
  shows             "is_seq_cst b \<and> 
                     is_seq_cst c \<and> 
                     b \<in> actions \<and> 
                     c \<in> actions \<and>
                     b \<noteq> c \<and>
                     b \<in> actions0 pre \<and>
                     c \<in> actions0 pre"
proof -
  have cons_sc: "sc_accesses_consistent_sc_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  hence "relOver (sc wit) (actions0 pre)"
    apply simp unfolding sc_accesses_consistent_sc_op.simps by simp
  hence "b \<in> actions0 pre" "c \<in> actions0 pre"
    using relOver_simp in_sc by auto
  thus ?thesis
    using cons_sc in_sc
    apply simp
    unfolding sc_accesses_consistent_sc_op.simps 
    by auto
qed

lemma consistent_sc_aux2:
  assumes cons:     "axsimpConsistent (pre, wit, getRelations pre wit)"
      and ab_def:   "is_seq_cst b \<and> 
                     is_seq_cst c \<and> 
                     b \<in> actions \<and> 
                     c \<in> actions \<and>
                     b \<noteq> c \<and>
                     b \<in> actions0 pre \<and>
                     c \<in> actions0 pre"
    shows           "(b, c) \<in> sc wit \<or> (c, b) \<in> sc wit"
proof -
  have cons_sc: "sc_accesses_consistent_sc_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  thus ?thesis
    using cons_sc ab_def
    apply simp
    unfolding sc_accesses_consistent_sc_op.simps 
    by auto
qed

lemma consistent_sc_aux3:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and in_sc:     "(b, c) \<in> sc (incWit s')"
  shows              "b = a \<or> c = a \<or> (b, c) \<in> sc (incWit s)"
proof auto
  assume "b \<noteq> a" and n_in_sc: "(b, c) \<notin> sc (incWit s)"
  have "b \<in> incCommitted s'" "c \<in> incCommitted s'"
    using consistent_sc_aux1[OF cons2 in_sc] by simp_all
  hence "b \<in> incCommitted s" using incCommitted `b \<noteq> a` by simp
  hence "c \<notin> incCommitted s" using in_sc n_in_sc wit by simp_all
  thus "c = a" using `c \<in> incCommitted s'` incCommitted by simp
qed

lemma step_sc_isnot_sc:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "a \<in> actions0 pre \<and> a \<notin> incCommitted s"
      and n_sc:      "\<not> is_seq_cst a"
  shows              "sc (incWit s') = sc (incWit s)"
unfolding sc_step_def
proof auto
  fix b c
  assume "(b, c) \<in> sc (incWit s)"
  thus "(b, c) \<in> sc (incWit s')" using wit by simp
next
  fix b c
  assume in_sc: "(b, c) \<in> sc (incWit s')"
  have "is_seq_cst b" "is_seq_cst c" using consistent_sc_aux1[OF cons2 in_sc] by simp_all
  hence "b \<noteq> a" "c \<noteq> a" using n_sc by auto
  thus "(b, c) \<in> sc (incWit s)" 
    using consistent_sc_aux3[OF cons1 cons2 wit incCommitted in_sc] by simp
qed

lemma step_sc_is_sc:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "a \<in> actions0 pre \<and> a \<notin> incCommitted s"
      and is_sc:     "is_seq_cst a"
  shows              "sc_step pre s s' a"
unfolding sc_step_def
proof auto
  let ?sc_set = "{x \<in> incCommitted s. is_seq_cst x \<and> x \<in> actions0 pre}"
  show "expandsOrder ?sc_set a (sc (incWit s)) (sc (incWit s'))"
    proof (cases "\<exists>b. (b, a) \<in> sc (incWit s')")
      assume max: "\<not> (\<exists>b. (b, a) \<in> sc (incWit s'))"
      have "sc (incWit s') = sc (incWit s) \<union> Pair a ` ?sc_set"
        proof auto
          fix c
          assume c: "c \<in> incCommitted s" "is_seq_cst c" "c \<in> actions0 pre"
          hence "c \<noteq> a" using a by auto
          hence "(a, c) \<in> sc (incWit s') \<or> (c, a) \<in> sc (incWit s')"
            using consistent_sc_aux2[OF cons2] a c incCommitted is_sc 
            by auto
          thus "(a, c) \<in> sc (incWit s')" using max by auto
        next
          fix b c
          assume "(b, c) \<in> sc (incWit s)"
          thus "(b, c) \<in> sc (incWit s')" using wit by simp
        next
          fix b c
          assume in_sc: "(b, c) \<in> sc (incWit s')"
             and not_new: "(b, c) \<notin> Pair a ` {x \<in> incCommitted s. is_seq_cst x \<and> x \<in> actions0 pre}"
          have "c \<noteq> a" using in_sc max by auto
          hence "c \<in> incCommitted s" "is_seq_cst c" "c \<in> actions0 pre"
            using consistent_sc_aux1[OF cons2 in_sc] incCommitted by auto
          hence "b \<noteq> a" using not_new by auto
          thus "(b, c) \<in> sc (incWit s)" 
            using consistent_sc_aux3[OF cons1 cons2 wit incCommitted in_sc] `c \<noteq> a` by simp
        qed
      thus ?thesis unfolding expandsOrder_def by auto
    next
      assume "\<exists>b'. (b', a) \<in> sc (incWit s')"
      then obtain b' where b': "(b', a) \<in> sc (incWit s')" by fast

      let ?sc_set2 = "{x. x \<in> actions0 pre \<and> (x, a) \<in> sc (incWit s')}"
  
      have "b' \<in> actions0 pre" using consistent_sc_aux1[OF cons2 b'] by simp
      hence "b' \<in> ?sc_set2" using b' by simp
      hence non_empty: "?sc_set2 \<noteq> {}" by fast
      have "assumptions (pre, incWit s' , [])" 
        using cons2 unfolding exIsConsistent_op_def by simp
      hence "finite_prefixes (sc (incWit s')) (actions0 pre)"
        unfolding assumptions.simps by simp
      hence finite: "finite ?sc_set2"
        unfolding finite_prefixes_def using a by fast
      hence irreflexive: "irrefl (sc (incWit s'))"
      and   transitive:  "trans (sc (incWit s'))"
        using cons2 
        unfolding exIsConsistent_op_def 
        by (auto simp add: sc_accesses_consistent_sc_op.simps)
      hence isOrder: "isStrictPartialOrder (sc (incWit s'))" 
        unfolding isStrictPartialOrder_def by simp
      obtain b where "b \<in> ?sc_set2 \<and> (\<forall>y. y \<in> ?sc_set2 \<longrightarrow> (b, y) \<notin> sc (incWit s'))"
        using supremum_partial_order[OF finite non_empty isOrder] by auto
      hence b:   "b \<in> actions0 pre \<and> (b, a) \<in> sc (incWit s')"
      and   max: "\<forall>y. y \<in> actions0 pre \<and> (y, a) \<in> sc (incWit s') \<longrightarrow> (b, y) \<notin> sc (incWit s')"
        by auto

      have b2: "b \<in> incCommitted s" "is_seq_cst b" "b \<noteq> a"
        using b incCommitted consistent_sc_aux1[OF cons2] by fast+

      let ?prev = "(\<lambda>c. (c, a)) ` {x \<in> incCommitted s. is_seq_cst x \<and>
                                   x \<in> actions0 pre \<and> (x, b) \<in> sc (incWit s)}"
      let ?succ = "(\<lambda>c. (a, c)) ` {x \<in> incCommitted s. is_seq_cst x \<and> 
                                   x \<in> actions0 pre \<and> (b, x) \<in> sc (incWit s)}"

      have "sc (incWit s) \<subseteq> sc (incWit s')" using wit by auto 
      moreover have "?prev \<subseteq> sc (incWit s')"
        proof auto
          fix c
          assume "(c, b) \<in> sc (incWit s)"
          hence "(c, b) \<in> sc (incWit s')" using wit by auto
          thus "(c, a) \<in> sc (incWit s')" using transitive_simp[OF transitive] b by fast
        qed
      moreover have "?succ \<subseteq> sc (incWit s')"
        proof auto
          fix c
          assume in_sc: "(b, c) \<in> sc (incWit s)"
          hence c: "c \<in> actions0 pre" "c \<in> incCommitted s" "is_seq_cst c"
            using consistent_sc_aux1[OF cons1] by fast+
          have in_sc2: "(b, c) \<in> sc (incWit s')" using in_sc wit by auto
          have "(c, a) \<notin> sc (incWit s')" using max in_sc2 c by fast
          thus "(a, c) \<in> sc (incWit s')" 
            using consistent_sc_aux2[OF cons2] c a incCommitted is_sc by auto
        qed
      moreover have "sc (incWit s') \<subseteq> sc (incWit s) \<union> {(b, a)} \<union> ?prev \<union> ?succ"
        proof clarify
          fix c d
          assume in_sc2: "(c, d) \<in> sc (incWit s')"
             and nin_sc1: "(c, d) \<notin> sc (incWit s)"
             and nin_prev: "(c, d) \<notin> ?prev"
             and nin_succ: "(c, d) \<notin> ?succ"
          have d: "d \<in> incCommitted s'" "is_seq_cst d" "d \<in> actions0 pre" "d \<noteq> c"
            using consistent_sc_aux1[OF cons2 in_sc2] by auto
          have c: "c \<in> incCommitted s'" "is_seq_cst c" "c \<in> actions0 pre" "d \<noteq> c"
            using consistent_sc_aux1[OF cons2 in_sc2] by auto
          have "c \<noteq> a"
            proof
              assume "c = a"
              hence d2: "d \<in> incCommitted s" using d incCommitted by simp
              have "(b, d) \<in> sc (incWit s')" 
                using transitive_simp[OF transitive] b in_sc2 `c = a` by fast
              hence "(b, d) \<in> sc (incWit s)" using b2 d2 wit by auto
              hence "(c, d) \<in> ?succ" using d d2 `c = a` by auto
              thus False using nin_succ by simp
            qed
          hence "d = a" 
            using consistent_sc_aux3[OF cons1 cons2 wit incCommitted in_sc2] nin_sc1 by simp
          hence c2: "c \<in> incCommitted s" using c incCommitted by simp
          have bc_nin_sc: "(b, c) \<notin> sc (incWit s')" using max c in_sc2 `d = a` by simp
          have "(c, b) \<notin> sc (incWit s)" using nin_prev `d = a` c c2 by auto
          hence "(c, b) \<notin> sc (incWit s')" using b2 c2 wit by auto
          hence "c = b" 
            using consistent_sc_aux2[OF cons2] bc_nin_sc b b2 c incCommitted by auto
          thus "c = b \<and> d = a" using `d = a` by simp
        qed
      ultimately have "sc (incWit s') = sc (incWit s) \<union> ?prev \<union> ?succ \<union> {(b, a)}" 
        using b by auto        
      thus ?thesis using b b2 unfolding expandsOrder_def by auto
    qed
qed

corollary step_sc:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "a \<in> actions0 pre \<and> a \<notin> incCommitted s"
  shows              "if is_seq_cst a then sc_step pre s s' a else sc (incWit s') = sc (incWit s)"
proof (cases "is_seq_cst a")
  assume "is_seq_cst a"
  thus ?thesis 
    using step_sc_is_sc[OF cons1 cons2 wit incCommitted] a by simp
next
  assume "\<not>is_seq_cst a"
  thus ?thesis 
    using step_sc_isnot_sc[OF cons1 cons2 wit incCommitted] a by simp
qed

(* lo-order *)

(* TODO: lo is a duplicate of sc *)

lemma consistent_lo_aux1:
  assumes cons:     "axsimpConsistent (pre, wit, getRelations pre wit)"
      and in_lo:    "(b, c) \<in> lo wit"
  shows             "(is_lock b \<or> is_unlock b) \<and> 
                     (is_lock c \<or> is_unlock c) \<and> 
                     loc_of b = loc_of c \<and>
                     is_at_mutex_location (lk pre) b \<and>
                     is_at_mutex_location (lk pre) c \<and>
                     b \<in> actions \<and> 
                     c \<in> actions \<and>
                     b \<noteq> c \<and>
                     b \<in> actions0 pre \<and>
                     c \<in> actions0 pre"
proof -
  have cons_lo: "locks_only_consistent_lo_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  hence "relOver (lo wit) (actions0 pre)"
    apply simp unfolding locks_only_consistent_lo_op.simps by simp
  hence "b \<in> actions0 pre" "c \<in> actions0 pre"
    using relOver_simp in_lo by auto
  thus ?thesis
    using cons_lo in_lo
    apply simp
    unfolding locks_only_consistent_lo_op.simps 
    by auto
qed

lemma consistent_lo_aux2:
  assumes cons:     "axsimpConsistent (pre, wit, getRelations pre wit)"
      and ab_def:   "(is_lock b \<or> is_unlock b) \<and> 
                     (is_lock c \<or> is_unlock c) \<and> 
                     loc_of b = loc_of c \<and>
                     is_at_mutex_location (lk pre) b \<and>
                     b \<in> actions \<and> 
                     c \<in> actions \<and>
                     b \<noteq> c \<and>
                     b \<in> actions0 pre \<and>
                     c \<in> actions0 pre"
    shows           "(b, c) \<in> lo wit \<or> (c, b) \<in> lo wit"
proof -
  have cons_lo: "locks_only_consistent_lo_op actions (pre, wit, getRelations pre wit)"
    using cons unfolding exIsConsistent_op_def by simp
  thus ?thesis
    using cons_lo ab_def
    apply simp
    unfolding locks_only_consistent_lo_op.simps 
    by auto
qed

lemma consistent_lo_aux3:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and in_lo:     "(b, c) \<in> lo (incWit s')"
  shows              "b = a \<or> c = a \<or> (b, c) \<in> lo (incWit s)"
proof auto
  assume "b \<noteq> a" and n_in_lo: "(b, c) \<notin> lo (incWit s)"
  have "b \<in> incCommitted s'" "c \<in> incCommitted s'"
    using consistent_lo_aux1[OF cons2 in_lo] by simp_all
  hence "b \<in> incCommitted s" using incCommitted `b \<noteq> a` by simp
  hence "c \<notin> incCommitted s" using in_lo n_in_lo wit by simp_all
  thus "c = a" using `c \<in> incCommitted s'` incCommitted by simp
qed

lemma step_lo_not_lock_unlock:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "a \<in> actions0 pre \<and> a \<notin> incCommitted s \<and> \<not>is_lock a \<and> \<not>is_unlock a"
  shows              "lo (incWit s') = lo (incWit s)"
proof (intro equalityI subsetI, auto)
  fix b c
  assume "(b, c) \<in> lo (incWit s)"
  thus "(b, c) \<in> lo (incWit s')" using wit by simp
next
  fix b c
  assume in_lo: "(b, c) \<in> lo (incWit s')"
  have "(is_lock b \<or> is_unlock b)" "(is_lock c \<or> is_unlock c)"
    using consistent_lo_aux1[OF cons2 in_lo] by simp_all
  hence "b \<noteq> a" "c \<noteq> a" using a by auto
  thus "(b, c) \<in> lo (incWit s)"
    using consistent_lo_aux3[OF cons1 cons2 wit incCommitted in_lo] by simp
qed

lemma step_lo_lock_unlock:
  assumes cons1:     "axsimpConsistent (pre, incWit s , getRelations pre (incWit s ))"
      and cons2:     "axsimpConsistent (pre, incWit s', getRelations pre (incWit s'))"
      and wit:       "incWit s = incWitRestrict (incWit s') (incCommitted s)"
      and committed: "incCommitted s' = insert a (incCommitted s)"
      and a:         "a \<in> actions0 pre \<and> a \<notin> incCommitted s \<and> (is_lock a \<or> is_unlock a)"
  shows              "lo_step_lock_unlock pre s s' a"
(* TODO: this lemma is a clone of step_sc. *)
unfolding lo_step_lock_unlock_def
proof auto
  let ?lo_set = " {x \<in> incCommitted s. x \<in> actions0 pre \<and> (is_lock x \<or> is_unlock x) \<and> loc_of x = loc_of a}"
  have "actions_respect_location_kinds (actions0 pre) (lk pre)"
    using cons1 unfolding exIsConsistent_op_def well_formed_threads.simps by simp
  hence mutex: "is_at_mutex_location (lk pre) a"
    unfolding actions_respect_location_kinds_def is_at_mutex_location_def
    using a by (cases a) auto
  show "expandsOrder ?lo_set a (lo (incWit s)) (lo (incWit s'))"
    proof (cases "\<exists>b. (b, a) \<in> lo (incWit s')")
      assume max: "\<not> (\<exists>b. (b, a) \<in> lo (incWit s'))"
      have "lo (incWit s') = lo (incWit s) \<union> Pair a ` ?lo_set"
        proof auto
          fix c
          assume c: "c \<in> incCommitted s" "c \<in> actions0 pre" "loc_of c = loc_of a" "is_lock c"
          hence "c \<noteq> a" using a by auto
          hence "(a, c) \<in> lo (incWit s') \<or> (c, a) \<in> lo (incWit s')"
            using consistent_lo_aux2[OF cons2] a mutex c incCommitted  
            by auto
          thus "(a, c) \<in> lo (incWit s')" using max by auto
        next
          fix c
          assume c: "c \<in> incCommitted s" "c \<in> actions0 pre" "loc_of c = loc_of a" "is_unlock c"
          hence "c \<noteq> a" using a by auto
          hence "(a, c) \<in> lo (incWit s') \<or> (c, a) \<in> lo (incWit s')"
            using consistent_lo_aux2[OF cons2] a mutex c incCommitted  
            by auto
          thus "(a, c) \<in> lo (incWit s')" using max by auto
        next
          fix b c
          assume "(b, c) \<in> lo (incWit s)"
          thus "(b, c) \<in> lo (incWit s')" using wit by simp
        next
          fix b c
          assume in_lo: "(b, c) \<in> lo (incWit s')"
             and not_new: "(b, c) \<notin> Pair a ` ?lo_set"
          have "c \<noteq> a" using in_lo max by auto
          hence "c \<in> incCommitted s" "c \<in> actions0 pre" "loc_of c = loc_of b" "is_lock c \<or> is_unlock c"
            using consistent_lo_aux1[OF cons2 in_lo] incCommitted by auto
          hence "b \<noteq> a" using not_new by auto
          thus "(b, c) \<in> lo (incWit s)" 
            using consistent_lo_aux3[OF cons1 cons2 wit incCommitted in_lo] `c \<noteq> a` by simp
        qed
      thus ?thesis unfolding expandsOrder_def by auto
    next
      assume "\<exists>b'. (b', a) \<in> lo (incWit s')"
      then obtain b' where b': "(b', a) \<in> lo (incWit s')" by fast

      let ?lo_set2 = "{x. x \<in> actions0 pre \<and> (x, a) \<in> lo (incWit s')}"
  
      have "b' \<in> actions0 pre" using consistent_lo_aux1[OF cons2 b'] by simp
      hence "b' \<in> ?lo_set2" using b' by simp
      hence non_empty: "?lo_set2 \<noteq> {}" by fast
      have "assumptions (pre, incWit s' , [])" 
        using cons2 unfolding exIsConsistent_op_def by simp
      hence "finite_prefixes (lo (incWit s')) (actions0 pre)"
        unfolding assumptions.simps by simp
      hence finite: "finite ?lo_set2"
        unfolding finite_prefixes_def using a by fast
      hence irreflexive: "irrefl (lo (incWit s'))"
      and   transitive:  "trans (lo (incWit s'))"
        using cons2 
        unfolding exIsConsistent_op_def   
        by (auto simp add: locks_only_consistent_lo_op.simps)
      hence isOrder: "isStrictPartialOrder (lo (incWit s'))" 
        unfolding isStrictPartialOrder_def by simp
      obtain b where "b \<in> ?lo_set2 \<and> (\<forall>y. y \<in> ?lo_set2 \<longrightarrow> (b, y) \<notin> lo (incWit s'))"
        using supremum_partial_order[OF finite non_empty isOrder] by auto
      hence b:   "b \<in> actions0 pre" and b_in_lo: "(b, a) \<in> lo (incWit s')"
      and   max: "\<forall>y. y \<in> actions0 pre \<and> (y, a) \<in> lo (incWit s') \<longrightarrow> (b, y) \<notin> lo (incWit s')"
        by auto

      have b2: "b \<in> incCommitted s" "b \<noteq> a" "loc_of a = loc_of b" 
               "is_lock b \<or> is_unlock b" "is_at_mutex_location (lk pre) b"
        using incCommitted consistent_lo_aux1[OF cons2 b_in_lo] by auto

      let ?prev = "(\<lambda>c. (c, a)) ` {x \<in> ?lo_set. (x, b) \<in> lo (incWit s)}"
      let ?succ = "(\<lambda>c. (a, c)) ` {x \<in> ?lo_set. (b, x) \<in> lo (incWit s)}"

      have "lo (incWit s) \<subseteq> lo (incWit s')" using wit by auto 
      moreover have "?prev \<subseteq> lo (incWit s')" 
        proof clarify
          fix c
          assume "(c, b) \<in> lo (incWit s)"
          hence "(c, b) \<in> lo (incWit s')" using wit by auto
          thus "(c, a) \<in> lo (incWit s')" using transitive_simp[OF transitive] b_in_lo by fast
        qed
      moreover have "?succ \<subseteq> lo (incWit s')"
        proof clarify
          fix c
          assume in_lo: "(b, c) \<in> lo (incWit s)"
          have c: "c \<in> actions0 pre" "c \<in> incCommitted s" "loc_of c = loc_of b" "is_lock c \<or> is_unlock c"
            using consistent_lo_aux1[OF cons1 in_lo] by auto
          have in_lo2: "(b, c) \<in> lo (incWit s')" using in_lo wit by auto
          have "(c, a) \<notin> lo (incWit s')" using max in_lo2 c by fast
          thus "(a, c) \<in> lo (incWit s')" 
            using consistent_lo_aux2[OF cons2, where b=a and c=c] c a mutex b2 incCommitted by auto
        qed
      moreover have "lo (incWit s') \<subseteq> lo (incWit s) \<union> {(b, a)} \<union> ?prev \<union> ?succ"
        proof clarify
          fix c d
          assume in_lo2: "(c, d) \<in> lo (incWit s')"
             and nin_lo1: "(c, d) \<notin> lo (incWit s)"
             and nin_prev: "(c, d) \<notin> ?prev"
             and nin_succ: "(c, d) \<notin> ?succ"
          have d: "d \<in> incCommitted s'" "d \<in> actions0 pre" "d \<noteq> c" 
                  "loc_of c = loc_of d" "is_lock d \<or> is_unlock d"
            using consistent_lo_aux1[OF cons2 in_lo2] by auto
          have c: "c \<in> incCommitted s'" "c \<in> actions0 pre" "d \<noteq> c" 
                  "loc_of c = loc_of d" "is_lock c \<or> is_unlock c"
            using consistent_lo_aux1[OF cons2 in_lo2] by auto
          have "c \<noteq> a"
            proof
              assume "c = a"
              hence d2: "d \<in> incCommitted s" using d incCommitted by simp
              have "(b, d) \<in> lo (incWit s')" 
                using transitive_simp[OF transitive] b_in_lo in_lo2 `c = a` by fast
              hence "(b, d) \<in> lo (incWit s)" using b2 d2 wit by auto
              hence "(c, d) \<in> ?succ" using d d2 `c = a` by auto
              thus False using nin_succ by simp
            qed
          hence "d = a" 
            using consistent_lo_aux3[OF cons1 cons2 wit incCommitted in_lo2] nin_lo1 by simp
          hence c2: "c \<in> incCommitted s" using c incCommitted by simp
          have bc_nin_lo: "(b, c) \<notin> lo (incWit s')" using max c in_lo2 `d = a` by simp
          have loc: "loc_of b = loc_of c" using b2 c `d = a` by auto
          have "(c, b) \<notin> lo (incWit s)" using nin_prev `d = a` c c2 by auto
          hence "(c, b) \<notin> lo (incWit s')" using b2 c2 wit by auto
          hence "c = b" 
            using consistent_lo_aux2[OF cons2] bc_nin_lo b b2 c incCommitted loc by fast
          thus "c = b \<and> d = a" using `d = a` by simp
        qed
      ultimately have "lo (incWit s') = lo (incWit s) \<union> ?prev \<union> ?succ \<union> {(b, a)}" 
        using b b_in_lo by auto        
      thus ?thesis using b b2 unfolding expandsOrder_def Let_def by auto
    qed
qed

(* Section X - Completeness -------------------------------------------------------------------- *)

lemma completeness_relPerformLoad:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_load a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformLoad pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have rf: "rf_step_load pre s1 s2 a"
    using step_rf_load[OF cons1 cons2 order wit incCommitted] a by simp
  have sc: "if is_seq_cst a then sc_step pre s1 s2 a else sc (incWit s2) = sc (incWit s1)"
    using step_sc[OF cons1 cons2 wit incCommitted] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformLoad_def
    using cons2 wit rf mo lo sc tot by auto
qed   

lemma completeness_relPerformStore:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_store a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformStore pre s1 s2 a"
proof -
  have mo: "if is_at_atomic_location (lk pre) a then 
               mo_step_atomic_write pre s1 s2 a 
            else 
               mo (incWit s2) = mo (incWit s1)"
    proof (cases "is_at_atomic_location (lk pre) a")
      assume loc: "is_at_atomic_location (lk pre) a"
      have "is_write a" using a by (cases a) auto
      thus ?thesis using loc step_mo_atomic_write[OF cons1 cons2 wit incCommitted] a by simp
    next
      assume loc: "\<not>is_at_atomic_location (lk pre) a"
      have "actions_respect_location_kinds (actions0 pre) (lk pre)"
        using cons1 unfolding exIsConsistent_op_def well_formed_threads.simps by simp
      hence "is_at_non_atomic_location (lk pre) a"
        unfolding actions_respect_location_kinds_def 
        using loc a 
        unfolding is_at_atomic_location_def is_at_non_atomic_location_def
        by (cases a) auto
      thus ?thesis using loc step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
    qed      
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have sc: "if is_seq_cst a then sc_step pre s1 s2 a else sc (incWit s2) = sc (incWit s1)"
    using step_sc[OF cons1 cons2 wit incCommitted] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformStore_def 
    using cons2 wit rf mo lo sc tot by metis
qed   

lemma completeness_relPerformRmw:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_RMW a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformRmw pre s1 s2 a"
proof -
  have "actions_respect_location_kinds (actions0 pre) (lk pre)"
    using cons1 unfolding exIsConsistent_op_def well_formed_threads.simps by simp
  hence loc: "is_at_atomic_location (lk pre) a"
    unfolding actions_respect_location_kinds_def 
    unfolding is_at_atomic_location_def is_at_non_atomic_location_def
    using a by (cases a) auto
  have "is_write a" using a by (cases a) auto
  hence mo: "mo_step_atomic_write pre s1 s2 a"
    using step_mo_atomic_write[OF cons1 cons2 wit incCommitted] loc a by simp 
  have rf: "rf_step_rmw pre s1 s2 a"
    using step_rf_rmw[OF cons1 cons2 order wit incCommitted] a by simp
  have sc: "if is_seq_cst a then sc_step pre s1 s2 a else sc (incWit s2) = sc (incWit s1)"
    using step_sc[OF cons1 cons2 wit incCommitted] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformRmw_def
    using cons2 wit rf mo lo sc tot by metis
qed   

lemma completeness_relPerformBlocked_rmw:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_blocked_rmw a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformBlocked_rmw pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have "\<not> is_seq_cst a" using a by (cases a) auto
  hence sc: "sc (incWit s2) = sc (incWit s1)"
    using step_sc_isnot_sc[OF cons1 cons2 wit incCommitted] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformBlocked_rmw_def
    using cons2 wit rf mo lo sc tot by metis
qed   

lemma completeness_relPerformLock:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_lock a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformLock pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have "\<not> is_seq_cst a" using a by (cases a) auto
  hence sc: "sc (incWit s2) = sc (incWit s1)"
    using step_sc_isnot_sc[OF cons1 cons2 wit incCommitted] a by simp  
  hence lo: "lo_step_lock_unlock pre s1 s2 a" 
    using step_lo_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformLock_def
    using cons2 wit rf mo lo sc tot by metis
qed   

lemma completeness_relPerformUnlock:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_unlock a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformUnlock pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have "\<not> is_seq_cst a" using a by (cases a) auto
  hence sc: "sc (incWit s2) = sc (incWit s1)"
    using step_sc_isnot_sc[OF cons1 cons2 wit incCommitted] a by simp  
  hence lo: "lo_step_lock_unlock pre s1 s2 a" 
    using step_lo_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformUnlock_def
    using cons2 wit rf mo lo sc tot by metis
qed 

lemma completeness_relPerformFence:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_fence a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformFence pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have sc: "if is_seq_cst a then sc_step pre s1 s2 a else sc (incWit s2) = sc (incWit s1)"
    using step_sc[OF cons1 cons2 wit incCommitted] a by simp     
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformFence_def
    using cons2 wit rf mo lo sc tot by metis
qed  

lemma completeness_relPerformAlloc:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_alloc a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformAlloc pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have "\<not> is_seq_cst a" using a by (cases a) auto
  hence sc: "sc (incWit s2) = sc (incWit s1)"
    using step_sc_isnot_sc[OF cons1 cons2 wit incCommitted] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformAlloc_def
    using cons2 wit rf mo lo sc tot by metis
qed  

lemma completeness_relPerformDealloc:
  assumes cons1:     "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and cons2:     "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
      and order:     "isInOpsemOrder_step pre s1 s2 a"
      and wit:       "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
      and committed: "incCommitted s2 = insert a (incCommitted s1)"
      and a:         "is_dealloc a \<and> a \<notin> incCommitted s1 \<and> a \<in> actions0 pre"
  shows              "relPerformDealloc pre s1 s2 a"
proof -
  have "\<not> is_write a" using a by (cases a) auto
  hence mo: "mo (incWit s2) = mo (incWit s1)" 
    using step_mo_not_atomic_write[OF cons2 wit incCommitted] a by simp
  have "\<not> is_read a" using a by (cases a) auto
  hence rf: "rf (incWit s2) = rf (incWit s1)" 
    using step_rf_non_read[OF cons1 cons2 order wit incCommitted] a by simp
  have "\<not> is_seq_cst a" using a by (cases a) auto
  hence sc: "sc (incWit s2) = sc (incWit s1)"
    using step_sc_isnot_sc[OF cons1 cons2 wit incCommitted] a by simp      
  have "\<not>is_lock a \<and> \<not>is_unlock a" using a by (cases a) auto
  hence lo: "lo (incWit s2) = lo (incWit s1)" 
    using step_lo_not_lock_unlock[OF cons1 cons2 wit incCommitted] a by simp
  have "tot_empty (pre, incWit s1, [])" "tot_empty (pre, incWit s2, [])"
    using cons1 cons2 unfolding exIsConsistent_op_def by simp_all
  hence tot: "tot (incWit s2) = tot (incWit s1)" unfolding tot_empty.simps by simp
  show ?thesis
    unfolding relPerformDealloc_def
    using cons2 wit rf mo lo sc tot by metis
qed    

lemma completeness_step:
  assumes cons:      "exIsConsistent_op (incCommitted s1) (pre, incWit s1, getRelations pre (incWit s1))"
      and step:      "minOpsemStep pre s1 s2 a"
  shows              "relOpsemStep pre s1 s2 a"
proof -
  have a: "a \<in> actions0 pre \<and> a \<notin> incCommitted s1 \<and> incCommitted s2 = insert a (incCommitted s1)"
    using step unfolding minOpsemStep_def Let_def by simp
  have order: "\<forall>b\<in>actions0 pre. (b, a) \<in> opsemOrderAlt pre (incWit s2) \<longrightarrow> b \<in> (incCommitted s1)"
    using step unfolding minOpsemStep_def Let_def by simp
  have order2: "isInOpsemOrder_step pre s1 s2 a"
    using step unfolding minOpsemStep_def isInOpsemOrder_step_def Let_def by simp
  have definedness: "stateIsDefined s2 = exIsDefined (pre, incWit s2, getRelations pre (incWit s2))"
    using step unfolding minOpsemStep_def Let_def by simp
  have cons2: "exIsConsistent_op (incCommitted s2) (pre, incWit s2, getRelations pre (incWit s2))"
    using step unfolding minOpsemStep_def Let_def by blast (* TODO: why does auto loop? *)
  have wit: "incWit s1 = incWitRestrict (incWit s2) (incCommitted s1)"
    using step unfolding minOpsemStep_def Let_def by auto
  show ?thesis
    proof (cases a)
      case Load
      hence "relPerformLoad pre s1 s2 a" 
        using completeness_relPerformLoad[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Load by auto
    next
      case Store
      hence "relPerformStore pre s1 s2 a" 
        using completeness_relPerformStore[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Store by auto
    next
      case RMW
      hence "relPerformRmw pre s1 s2 a" 
        using completeness_relPerformRmw[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness RMW by auto
    next
      case Blocked_rmw
      hence "relPerformBlocked_rmw pre s1 s2 a" 
        using completeness_relPerformBlocked_rmw[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Blocked_rmw by auto
    next
      case Lock
      hence "relPerformLock pre s1 s2 a" 
        using completeness_relPerformLock[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Lock by auto
    next
      case Unlock
      hence "relPerformUnlock pre s1 s2 a" 
        using completeness_relPerformUnlock[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Unlock by auto
    next
      case Fence
      hence "relPerformFence pre s1 s2 a" 
        using completeness_relPerformFence[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Fence by auto
    next
      case Alloc
      hence "relPerformAlloc pre s1 s2 a" 
        using completeness_relPerformAlloc[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Alloc by auto
    next
      case Dealloc
      hence "relPerformDealloc pre s1 s2 a" 
        using completeness_relPerformDealloc[OF cons cons2 order2 wit] a by auto
      thus ?thesis unfolding relOpsemStep_def using a order2 definedness Dealloc by auto
    qed
qed

lemma completenessRelTrace_aux:
  assumes "minOpsemTrace pre r s"
          "r = initialState pre"
  shows   "relOpsemTrace pre r s"
using assms
proof induct
  case (minOpsemReflexive pre s)
  hence "exIsConsistent_op {} (pre, initialWitness, getRelations pre initialWitness)"
    unfolding exIsConsistent_op_def by auto
  hence "well_formed_threads (pre, initialWitness, getRelations pre initialWitness)"
  and   "consistent_hb (pre, initialWitness, getRelations pre initialWitness)"
    unfolding exIsConsistent_op_def by auto
  thus "relOpsemTrace pre s s"
    using relOpsemReflexive minOpsemReflexive by auto
next
  case (minOpsemStep pre x y z a)
  have x: "x = initialState pre" using minOpsemStep by auto
  have minTrace: "minOpsemTrace pre x y" using minOpsemStep by auto
  have cons: "exIsConsistent_op (incCommitted y) (pre, incWit y, getRelations pre (incWit y))"
    using EquivalenceMinimalOpsem.consistencySpecTrace[OF minTrace x] .    
  have "relOpsemStep pre y z a" 
    using completeness_step[OF cons] minOpsemStep by auto
  thus "relOpsemTrace pre x z"
    using minOpsemStep relOpsemStep[where ?pre0.0=pre] by auto
qed

corollary completenessRelTrace:
  assumes "minOpsemTrace pre (initialState pre) s"
  shows   "relOpsemTrace pre (initialState pre) s"
using assms completenessRelTrace_aux by simp

(* Section X - Equivalence --------------------------------------------------------------------- *)

lemma equivalenceRelTrace:
  shows "relOpsemTrace pre (initialState pre) s = minOpsemTrace pre (initialState pre) s"
using soundnessRelTrace completenessRelTrace by fast

lemma equivalenceRelConsistent:
  shows "relOpsemConsistent = minOpsemConsistent"
using equivalenceRelTrace
apply (intro ext)
unfolding relOpsemConsistent_def minOpsemConsistent_def
by auto

lemma equivalenceRelUndefined:
  shows "relOpsemUndefined = minOpsemUndefined"
using equivalenceRelTrace
apply (intro ext)
unfolding relOpsemUndefined_def minOpsemUndefined_def
by auto

theorem equivalence_relOpsem_minOpsem:
  shows "relOpsemBehaviour = minOpsemBehaviour"
using equivalenceRelConsistent equivalenceRelUndefined
apply (intro ext)
unfolding relOpsemBehaviour_def minOpsemBehaviour_def
by auto

corollary equivalence_relOpsem_axiom:
  assumes "pre_executions_are_finite"
  shows   "relOpsemBehaviour = axiomBehaviour"
using equivalence_relOpsem_minOpsem equivalence_minOpsem_axiom[OF assms]
by metis

end
