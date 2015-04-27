theory "EquivalenceExecutableOpsem"

imports
Main
"_bin/Cmm_master"
"_bin/MinimalOpsem"
"_bin/RelationalOpsem"
"_bin/ExecutableOpsem"
"EquivalenceMinimalOpsem"
"EquivalenceRelationalOpsem"
begin

(* Simplifications and auxilary functions ------------------------------------------------------ *)

lemma bind_member [simp]:
  shows "x \<in> bind m f = (\<exists>y. y \<in> m \<and> x \<in> f y)"
unfolding bind_def
by auto

lemma bind2_empty[simp]:
  shows "(bind2 m1 m2 = {}) = (m1 = {} \<or> m2 = {})"
unfolding bind2_def
by auto

lemma bind2_member [simp]:
  shows "x \<in> bind2 m1 m2 = (m1 \<noteq> {} \<and> x \<in> m2)"
unfolding bind2_def
by auto

lemma filter_empty [simp]:
  shows "(filter b = {}) = (\<not>b)"
unfolding filter_def
by auto

lemma filter_member [simp]:
  shows "(() \<in> filter b) = b"
unfolding filter_def
by auto

lemma return_member [simp]:
  shows "x \<in> return y = (x = y)"
unfolding return_def
by auto

lemma if_member_singleton [simp]:
  shows "x \<in> (if b then {y} else {}) = (b \<and> x = y)"
by auto

lemma pair_member1 [simp]:
  shows "y\<in> (\<lambda>x. (x, c)) ` s = (fst y \<in> s \<and> snd y = c)"
by (cases y) auto

lemma pair_member2 [simp]:
  shows "y \<in> Pair c ` s = (snd y \<in> s \<and> fst y = c)"
by (cases y) auto

(* Substitutions *)

type_synonym cvalueSubstitution = "cvalue \<Rightarrow> cvalue"

definition substituteCvalueInAction :: "cvalueSubstitution \<Rightarrow> action \<Rightarrow> action"
where "substituteCvalueInAction s a = 
(case  a of 
    Load aid tid mem loc v    \<Rightarrow> Load aid tid mem loc (s v)
  | Store aid tid mem loc v   \<Rightarrow> Store aid tid mem loc (s v)
  | RMW aid tid mem loc v1 v2 \<Rightarrow> RMW aid tid mem loc (s v1) (s v2)
  | _                         \<Rightarrow> a
)"

definition substituteCvalueInRel :: "cvalueSubstitution \<Rightarrow> (action * action) set \<Rightarrow> (action * action) set"
where "substituteCvalueInRel s r = 
  (\<lambda> (a, b) \<Rightarrow> (substituteCvalueInAction s a, substituteCvalueInAction s b)) ` r"

definition substituteCvalueInPreEx :: "cvalueSubstitution \<Rightarrow> pre_execution \<Rightarrow> pre_execution"
where "substituteCvalueInPreEx s pre = 
\<lparr> actions0 = (substituteCvalueInAction s) ` (actions0 pre), 
  threads = threads pre, 
  lk = lk pre, 
  sb = substituteCvalueInRel s (sb pre), 
  asw = substituteCvalueInRel s (asw pre), 
  dd = substituteCvalueInRel s (dd pre)
\<rparr>"

definition substituteCvalueInWit :: "cvalueSubstitution \<Rightarrow> execution_witness \<Rightarrow> execution_witness"
where "substituteCvalueInWit s wit = 
\<lparr> rf = substituteCvalueInRel s (rf wit), 
  mo = substituteCvalueInRel s (mo wit), 
  sc = substituteCvalueInRel s (sc wit),
  lo = substituteCvalueInRel s (lo wit), 
  tot = substituteCvalueInRel s (tot wit)
\<rparr>"

definition subAndEqAgree :: "cvalueSubstitution \<Rightarrow> equalityCvalue \<Rightarrow> bool"
where "subAndEqAgree s eq = 
  (\<forall>c1 c2. (eq c1 c2 = TTrue  \<longrightarrow> s c1 = s c2) \<and>
           (eq c1 c2 = TFalse \<longrightarrow> s c1 \<noteq> s c2)
  )"

definition statesAgree :: "pre_execution \<Rightarrow> state \<Rightarrow> exeState \<Rightarrow> bool"
where "statesAgree pre s1 s2 = 
  (\<exists>s :: cvalueSubstitution. subAndEqAgree s (equalityCvalue s2) \<and>
                             substituteCvalueInPreEx s (preEx s2) = pre \<and>
                             substituteCvalueInWit s (exWitness0 s2) = exWitness s1 \<and>
                             (substituteCvalueInAction s) ` committed0 s2 = committed s1 \<and>
                             stateIsDefined0 s2 = stateIsDefined s1
  )"

(* Section 2 - ??? ----------------------------------------------------------------------------- *)

lemma equivalence_mo:
  assumes "statesAgree pre s1 es1 \<and> statesAgree pre s2 es2"
  shows "mo_step_atomic_write pre s1 s2 a = (mo (exWitness0 es2) \<in> addToMo a es1)"
unfolding mo_step_atomic_write_def addToMo_def
by auto

lemma soundness_rf_load:
  assumes rf:        "rf (exWitness s2) \<in> addToRf_load pre a s1"
      and a:         "is_load a \<and> a \<in> actions0 pre \<and> a \<notin> committed s1"
      and wit:       "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
      and committed: "committed s2 = insert a (committed s1)"
      and det_read:  "det_read_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
  shows              "rf_step_load pre s1 s2 a"
proof -
  have "(rf (exWitness s1) \<noteq> rf (exWitness s2))  =
        (\<exists>w'\<in>actions0 pre. (w', a) \<in> rf (exWitness s2))"
    proof (intro iffI)
      assume "rf (exWitness s1) \<noteq> rf (exWitness s2)"
      thus "\<exists>w'\<in>actions0 pre. (w', a) \<in> rf (exWitness s2)"
         using rf unfolding addToRf_load_def by auto
    next
      assume "\<exists>w'\<in>actions0 pre. (w', a) \<in> rf (exWitness s2)"
      then obtain w where w: "w \<in> actions0 pre \<and> (w, a) \<in> rf (exWitness s2)" by fast
      hence "(w, a) \<notin> rf (witnessRestrict (exWitness s2) (committed s1))" using a by auto
      hence "(w, a) \<notin> rf (exWitness s1)" using wit by auto
      thus "rf (exWitness s1) \<noteq> rf (exWitness s2)" using w by auto
    qed
  moreover have "(\<exists>w'\<in>actions0 pre. (w', a) \<in> rf (exWitness s2)) =
                 (\<exists>w\<in>actions0 pre. (w, a) \<in> getVse pre (exWitness s2))"
    using det_read a committed unfolding getRelations_def det_read_op.simps by auto
  ultimately have "(rf (exWitness s1) \<noteq> rf (exWitness s2))  =
                   (\<exists>w\<in>actions0 pre. (w, a) \<in> getVse pre (exWitness s2))" by simp
  thus ?thesis using rf unfolding rf_step_load_def addToRf_load_def by auto
qed

lemma completeness_rf_load:
  assumes "rf_step_load pre s1 s2 a"
  shows   "rf (exWitness s2) \<in> addToRf_load pre a s1"
proof (cases "\<exists>w\<in>actions0 pre. (w, a) \<in> getVse pre (exWitness s2)")
  assume "\<exists>w\<in>actions0 pre. (w, a) \<in> getVse pre (exWitness s2)"
  then obtain w where w:  "w \<in> actions0 pre \<and> w \<in> committed s1 \<and>
                           is_write w \<and> loc_of w = loc_of a \<and> 
                           value_written_by w = value_read_by a"
                and   rf: "rf (exWitness s2) = insert (w, a) (rf (exWitness s1))"
    using assms unfolding rf_step_load_def by auto
  thus ?thesis unfolding addToRf_load_def by auto
next
  assume " \<not>(\<exists>w\<in>actions0 pre. (w, a) \<in> getVse pre (exWitness s2))"
  hence "rf (exWitness s2) = rf (exWitness s1)"
    using assms unfolding rf_step_load_def by auto
  thus ?thesis unfolding addToRf_load_def by auto
qed

lemma equivalence_rf_rmw:
  shows "rf_step_rmw pre s1 s2 a = (rf (exWitness s2) \<in> addToRf_rmw pre a s1)"
unfolding rf_step_rmw_def addToRf_rmw_def Let_def 
by auto

lemma equivalence_expandsOrder:
  shows "expandsOrder domain a r1 r2 = (r2 \<in> addToTransitiveOrder domain a r1)"
unfolding expandsOrder_def addToTransitiveOrder_def
by auto

lemma equivalence_sc:
  shows "sc_step pre s1 s2 a = (sc (exWitness s2) \<in> addToSc pre a s1)"
unfolding sc_step_def addToSc_def
using equivalence_expandsOrder
by auto

lemma equivalence_lo:
  shows "lo_step_lock_unlock pre s1 s2 a = (lo (exWitness s2) \<in> addToLo pre a s1)"
unfolding lo_step_lock_unlock_def addToLo_def
using equivalence_expandsOrder
by auto

(* Equivalence performXxx *)

lemma soundness_performLoad:
  assumes exe:       "exWitness s2 \<in> exePerformLoad pre s1 a"
      and a:         "is_load a \<and> a \<in> actions0 pre \<and> a \<notin> committed s1"
      and committed: "committed s2 = insert a (committed s1)"
      and cons:      "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:       "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows              "relPerformLoad pre s1 s2 a"
proof -
  have rf_exe: "rf (exWitness s2) \<in> addToRf_load pre a s1"
    using exe unfolding exePerformLoad_def by auto
  have rf: "rf_step_load pre s1 s2 a"
    using soundness_rf_load[OF rf_exe a wit committed] cons
    unfolding exIsConsistent_op_def
    by auto
  show ?thesis
    using exe cons wit equivalence_sc rf
    unfolding exePerformLoad_def relPerformLoad_def
    by auto
qed

lemma completeness_performLoad:
  assumes rel: "relPerformLoad pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformLoad pre s1 a"
proof -
  have sc: "is_seq_cst a \<Longrightarrow> sc (exWitness s2) \<in> addToSc pre a s1"
    using rel equivalence_sc unfolding relPerformLoad_def by auto
  have rf: "rf (exWitness s2) \<in> addToRf_load pre a s1"
    using rel completeness_rf_load unfolding relPerformLoad_def by auto
  show ?thesis
    using rel sc rf
    unfolding exePerformLoad_def relPerformLoad_def
    apply auto
    apply (intro exI[where x="sc (exWitness s2)"])
    by auto
qed

lemma soundness_performStore:
  assumes exe:  "exWitness s2 \<in> exePerformStore pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformStore pre s1 s2 a"
using exe cons wit equivalence_sc equivalence_mo
unfolding exePerformStore_def relPerformStore_def
by auto

lemma completeness_performStore:
  assumes rel: "relPerformStore pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformStore pre s1 a"
proof -
  have sc: "is_seq_cst a \<Longrightarrow> sc (exWitness s2) \<in> addToSc pre a s1"
    using rel equivalence_sc unfolding relPerformStore_def by auto
  have mo: "is_at_atomic_location (lk pre) a \<Longrightarrow> mo (exWitness s2) \<in> addToMo pre a s1"
    using rel equivalence_mo unfolding relPerformStore_def by auto
  show ?thesis
    using rel sc mo
    unfolding exePerformStore_def relPerformStore_def
    apply auto
    apply (intro exI[where x="sc (exWitness s2)"])
    by auto
qed

lemma soundness_performRmw:
  assumes exe:  "exWitness s2 \<in> exePerformRmw pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformRmw pre s1 s2 a"
using exe cons wit equivalence_sc equivalence_mo equivalence_rf_rmw
unfolding exePerformRmw_def relPerformRmw_def
by auto

lemma completeness_performRmw:
  assumes rel: "relPerformRmw pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformRmw pre s1 a"
proof -
  have sc: "is_seq_cst a \<Longrightarrow> sc (exWitness s2) \<in> addToSc pre a s1"
    using rel equivalence_sc unfolding relPerformRmw_def by auto
  have mo: "mo (exWitness s2) \<in> addToMo pre a s1"
    using rel equivalence_mo unfolding relPerformRmw_def by auto
  have rf: "rf (exWitness s2) \<in> addToRf_rmw pre a s1"
    using rel equivalence_rf_rmw unfolding relPerformRmw_def by auto
  show ?thesis
    proof (cases "is_seq_cst a")
      assume "is_seq_cst a"
      thus ?thesis
        using rel sc mo rf
        unfolding exePerformRmw_def relPerformRmw_def
        apply auto
        apply (intro exI[where x="sc (exWitness s2)"])
        apply auto
        apply (intro exI[where x="rf (exWitness s2)"])
        by auto
    next
      assume "\<not>is_seq_cst a"
      thus ?thesis
        using rel sc mo rf
        unfolding exePerformRmw_def relPerformRmw_def
        apply auto
        apply (intro exI[where x="rf (exWitness s2)"])
        by auto
    qed
qed

lemma soundness_performBlocked_rmw:
  assumes exe:  "exWitness s2 \<in> exePerformBlocked_rmw pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformBlocked_rmw pre s1 s2 a"
using exe cons wit 
unfolding exePerformBlocked_rmw_def relPerformBlocked_rmw_def
by auto

lemma completeness_performBlocked_rmw:
  assumes rel: "relPerformBlocked_rmw pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformBlocked_rmw pre s1 a"
using rel 
unfolding exePerformBlocked_rmw_def relPerformBlocked_rmw_def
by auto

lemma soundness_performLock:
  assumes exe:  "exWitness s2 \<in> exePerformLock pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformLock pre s1 s2 a"
using exe cons wit equivalence_lo 
unfolding exePerformLock_def relPerformLock_def
by auto

lemma completeness_performLock:
  assumes rel: "relPerformLock pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformLock pre s1 a"
using rel equivalence_lo
unfolding exePerformLock_def relPerformLock_def
by auto

lemma soundness_performUnlock:
  assumes exe:  "exWitness s2 \<in> exePerformUnlock pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformUnlock pre s1 s2 a"
using exe cons wit equivalence_lo 
unfolding exePerformUnlock_def relPerformUnlock_def
by auto

lemma completeness_performUnlock:
  assumes rel: "relPerformUnlock pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformUnlock pre s1 a"
using rel equivalence_lo
unfolding exePerformUnlock_def relPerformUnlock_def
by auto

lemma soundness_performFence:
  assumes exe:  "exWitness s2 \<in> exePerformFence pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformFence pre s1 s2 a"
using exe cons wit equivalence_sc 
unfolding exePerformFence_def relPerformFence_def
by auto

lemma completeness_performFence:
  assumes rel: "relPerformFence pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformFence pre s1 a"
proof -
  have sc: "is_seq_cst a \<Longrightarrow> sc (exWitness s2) \<in> addToSc pre a s1"
    using rel equivalence_sc unfolding relPerformFence_def by auto
  show ?thesis
    using rel sc 
    unfolding exePerformFence_def relPerformFence_def
    by auto
qed

lemma soundness_performCreate:
  assumes exe:  "exWitness s2 \<in> exePerformCreate pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformCreate pre s1 s2 a"
using exe cons wit equivalence_lo 
unfolding exePerformCreate_def relPerformCreate_def
by auto

lemma completeness_performCreate:
  assumes rel: "relPerformCreate pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformCreate pre s1 a"
using rel equivalence_lo
unfolding exePerformCreate_def relPerformCreate_def
by auto

lemma soundness_performKill:
  assumes exe:  "exWitness s2 \<in> exePerformKill pre s1 a"
      and cons: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
      and wit:  "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
  shows         "relPerformKill pre s1 s2 a"
using exe cons wit equivalence_lo 
unfolding exePerformKill_def relPerformKill_def
by auto

lemma completeness_performKill:
  assumes rel: "relPerformKill pre s1 s2 a"
  shows        "exWitness s2 \<in> exePerformKill pre s1 a"
using rel equivalence_lo
unfolding exePerformKill_def relPerformKill_def
by auto

(* Equivalence step *)

lemma soundnessRelExeStep:
  assumes exe:  "(a, s2) \<in> exeOpsemStep pre s1"
  shows         "relOpsemStep pre s1 s2 a"
proof -
  have cons2: "exIsConsistent_op (committed s2) (pre, exWitness s2, getRelations pre (exWitness s2))"
    using exe unfolding exeOpsemStep_def Let_def by auto
  have wit: "witnessRestrict (exWitness s2) (committed s1) = exWitness s1"
    using exe unfolding exeOpsemStep_def Let_def by auto
  show ?thesis
    proof (cases a)
      case Load
      have exe_load: "exWitness s2 \<in> exePerformLoad pre s1 a"
        using exe Load unfolding exeOpsemStep_def Let_def by auto
      have a: "is_load a \<and> a \<in> actions0 pre \<and> a \<notin> committed s1"
        using exe Load unfolding exeOpsemStep_def Let_def by auto
      have committed: "committed s2 = insert a (committed s1)"
        using exe Load unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Load exe soundness_performLoad[OF exe_load a committed cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Store
      have exe_store: "exWitness s2 \<in> exePerformStore pre s1 a"
        using exe Store unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Store exe soundness_performStore[OF exe_store cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case RMW
      have exe_rmw: "exWitness s2 \<in> exePerformRmw pre s1 a"
        using exe RMW unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using RMW exe soundness_performRmw[OF exe_rmw cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Blocked_rmw
      have exe_blocked_rmw: "exWitness s2 \<in> exePerformBlocked_rmw pre s1 a"
        using exe Blocked_rmw unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Blocked_rmw exe soundness_performBlocked_rmw[OF exe_blocked_rmw cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Lock
      have exe_lock: "exWitness s2 \<in> exePerformLock pre s1 a"
        using exe Lock unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Lock exe soundness_performLock[OF exe_lock cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Unlock
      have exe_unlock: "exWitness s2 \<in> exePerformUnlock pre s1 a"
        using exe Unlock unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Unlock exe soundness_performUnlock[OF exe_unlock cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Fence
      have exe_fence: "exWitness s2 \<in> exePerformFence pre s1 a"
        using exe Fence unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Fence exe soundness_performFence[OF exe_fence cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Create
      have exe_create: "exWitness s2 \<in> exePerformCreate pre s1 a"
        using exe Create unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Create exe soundness_performCreate[OF exe_create cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    next
      case Kill
      have exe_kill: "exWitness s2 \<in> exePerformKill pre s1 a"
        using exe Kill unfolding exeOpsemStep_def Let_def by auto
      show ?thesis
        using Kill exe soundness_performKill[OF exe_kill cons2 wit]
        unfolding exeOpsemStep_def relOpsemStep_def Let_def
        by auto 
    qed
qed

lemma completenessRelExeStep:
  assumes rel:  "relOpsemStep pre s1 s2 a"
  shows         "(a, s2) \<in> exeOpsemStep pre s1"
proof (cases a)
  case Load
  show ?thesis
    using rel Load completeness_performLoad
    unfolding relOpsemStep_def exeOpsemStep_def Let_def
    apply simp
    apply (intro exI[where x=a])
    using Load
    apply simp
    apply (intro exI[where x="exWitness s2"])
    apply auto
    oops

(* Equivalence trace *)

lemma equivalenceRelExeTrace:
  assumes s_def: "s = initialState pre"
  shows         "exeOpsemTrace pre s s' = relOpsemTrace pre s s'"
proof
  assume "exeOpsemTrace pre s s'"
  thus "relOpsemTrace pre s s'"
    using s_def
    proof (induct rule: exeOpsemTrace.induct, auto)
      fix pre
      let ?s = "initialState pre"
      assume init:  "?s \<in> exeInitialStep pre"
      have "well_formed_threads (pre, initialWitness, [])"
           "consistent_hb (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
        using init unfolding exeInitialStep_def return_def
        by auto
      hence "exIsConsistent_op (committed ?s) (pre, exWitness ?s, getRelations pre (exWitness ?s))"
        unfolding exIsConsistent_op_def getRelations_def by simp
      thus "relOpsemTrace pre ?s ?s"
        using relOpsemReflexive by metis
    next
      fix pre y z a
      let ?s = "initialState pre"
      assume IH:   "relOpsemTrace pre ?s y"
         and step: "(a, z) \<in> exeOpsemStep pre y"
      have "stateIsConsistent pre y"
        unfolding stateIsConsistent_def using IH consistencySpecTrace by metis
      hence "relOpsemStep pre y z a" using step equivalenceRelExeStep by metis
      thus "relOpsemTrace pre ?s z" using IH relOpsemStep by metis
    qed
next
  assume "relOpsemTrace pre s s'"
  thus "exeOpsemTrace pre s s'"
    using s_def
    proof (induct rule: relOpsemTrace.induct, auto)
      fix pre
      let ?s = "initialState pre"
      assume init:  "exIsConsistent_op {} (pre, initialWitness, getRelations pre initialWitness)"
      have "well_formed_threads (pre, initialWitness, [])" 
           "consistent_hb (pre, initialWitness, [(''hb'', getHb pre initialWitness)])"
        using init unfolding exIsConsistent_op_def getRelations_def by simp_all
      hence "?s \<in> exeInitialStep pre"
        unfolding exeInitialStep_def return_def by simp
      thus "exeOpsemTrace pre ?s ?s"
        using exeOpsemReflexive by metis
    next
      fix pre y z a
      let ?s = "initialState pre"
      assume IH:   "exeOpsemTrace pre ?s y"
         and step: "relOpsemStep pre y z a"
         and as:   "relOpsemTrace pre ?s y"
      have "stateIsConsistent pre y"
        unfolding stateIsConsistent_def using as consistencySpecTrace by metis
      hence "(a, z) \<in> exeOpsemStep pre y" using step equivalenceRelExeStep by metis
      thus "exeOpsemTrace pre ?s z" using IH exeOpsemStep by metis
    qed
qed

end
