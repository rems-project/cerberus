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
Cmm_master_lemmas
"_bin/Cmm_master"
"_bin/MinimalOpsem"
begin

(* Section 1 - Termination proofs, simplifications and auxilary lemmas-------------------------- *)

abbreviation "sublanguage \<equiv> true_condition"
abbreviation "memory_model \<equiv> with_consume_memory_model"
abbreviation "consistent_execution \<equiv> with_consume_consistent_execution"
abbreviation "getHb \<equiv> with_consume_hb"
abbreviation "getVse \<equiv> with_consume_vse"
abbreviation "getRelations \<equiv> with_consume_relations"

lemmas sublanguage_def = true_condition_def
lemmas memory_model_def = with_consume_memory_model_def
lemmas consistent_execution_def = with_consume_consistent_execution_def
lemmas getHb_def = with_consume_hb_def
lemmas getVse_def = with_consume_vse_def
lemmas getRelations_def = with_consume_relations_simp 
                          with_consume_relations_alt_def

abbreviation "hbMinusAlt pre wit \<equiv> hbMinus (pre,wit, getRelations pre wit)"
abbreviation "opsemOrderAlt pre wit \<equiv> opsemOrder (pre,wit, getRelations pre wit)"
abbreviation "exIsConsistentAlt pre wit \<equiv> exIsConsistent (pre, wit, getRelations pre wit)"

lemmas hbMinusAlt_def = hbMinus.simps
lemmas opsemOrderAlt_def = opsemOrder.simps
lemmas exIsConsistentAlt_def = exIsConsistent_def

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
          locks_only_undefined_behaviour_def
          each_empty_def
          exIsDefined_def 
          getDefinedness_def 
          Let_def
by simp

(* Simplifications for restrictions *)

lemma relRestrict2_empty1 [simp]:
  shows "relRestrict2 x {} = {}"
unfolding relRestrict2_def
by simp

lemma relRestrict2_empty2 [simp]:
  shows "relRestrict2 {} x = {}"
unfolding relRestrict2_def
by simp

lemma relRestrict2_member [simp]:
  shows "x \<in> relRestrict2 rel s = (x \<in> rel \<and> (fst x) \<in> s)"
unfolding relRestrict2_def
by auto

lemma relRestrict2_isTransitive [simp]:
  assumes "trans x"
  shows   "trans (relRestrict2 x s)"
using assms
unfolding trans_def 
by auto 

lemma relRestrict2_irrefl [simp]:
  assumes "irrefl x"
  shows   "irrefl (relRestrict2 x s)"
using assms
unfolding irrefl_def 
by auto 

lemma relOver_relRestrict2 [simp]:
  assumes "relOver x z"
  shows   "relOver (relRestrict2 x s) z"
using assms
unfolding relOver_def 
apply auto 
apply (metis Domain.DomainI in_mono)
by (metis Range.simps in_mono)

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
  shows "consistent memory_model = consistent_execution"
        "relation_calculation memory_model = getRelations"
        "undefined0 memory_model = locks_only_undefined_behaviour"
unfolding memory_model_def
by simp_all

(* Simplifications for states *)

lemma initialState_simps [simp]:
  shows "exWitness (initialState pre) = initialWitness"
        "committed (initialState pre) = {}"
        "stateIsDefined (initialState pre) = exIsDefined (pre, initialWitness, getRelations pre initialWitness)"
unfolding initialState_def
by simp_all

(* Simplification for hbMinus *)

lemma rel_list_hbMinus [simp]:
  assumes "rel \<noteq> []"
  shows   "hbMinus (pre, wit, (''hb'', hb)#rel) = 
             hbMinus (pre, wit, (''hb'', hb)#[])"
unfolding hbMinus.simps ..

lemma rel_list_hbMinus_release_acquire_fenced:
  shows   "hbMinus (pre, wit, release_acquire_fenced_relations pre wit) = 
           hbMinus (pre, wit, [(''hb'', release_acquire_fenced_hb pre wit)])" 
unfolding release_acquire_fenced_relations_simp
          release_acquire_fenced_relations_alt_def
by simp

lemma hbMinusE [elim]:
  assumes "(a, b) \<in> hbMinusAlt pre wit"
  shows "(a, b) \<in> getHb pre wit"
        "is_na_or_non_write pre b"
using assms
unfolding hbMinusAlt_def getRelations_def
by auto

lemma hbMinusI [intro]:
  assumes "(a, b) \<in> getHb pre wit"
      and "is_na_or_non_write pre b"
  shows "(a, b) \<in> hbMinusAlt pre wit"
using assms
unfolding hbMinusAlt_def getRelations_def
by auto

(* Simplifications for relation_list in consistency predicates *)

lemma rel_list_opsemOrder [simp]:
  assumes "rel \<noteq> []"
  shows   "opsemOrder (pre, wit, (''hb'', hb)#rel) = 
             opsemOrder (pre, wit, [(''hb'', hb)])"
using assms
unfolding opsemOrder.simps
by simp

lemma rel_list_opsemOrder_release_acquire_fenced [simp]:
  shows   "opsemOrder (pre, wit, getRelations pre wit) = 
           opsemOrder (pre, wit, [(''hb'', getHb pre wit)])" 
unfolding getRelations_def
by simp

lemma rel_list_isInOpsemOrder [simp]:
  assumes "rel \<noteq> []"
  shows   "isInOpsemOrder actions (pre, wit, (''hb'', hb)#rel) = 
             isInOpsemOrder actions (pre, wit, [(''hb'', hb)])"
using assms
unfolding isInOpsemOrder_def
by simp

lemma rel_list_isInOpsemOrder_release_acquire_fenced [simp]:
  shows   "isInOpsemOrder actions (pre, wit, getRelations pre wit) = 
           isInOpsemOrder actions (pre, wit, [(''hb'', getHb pre wit)])" 
unfolding getRelations_def
by simp

lemma rel_list_consistent_mo_op [simp]:
  assumes "rel \<noteq> []"
  shows   "consistent_mo_op actions (pre, wit, rel) = consistent_mo_op actions (pre, wit, [])"
unfolding consistent_mo_op.simps ..

lemma rel_list_locks_only_consistent_locks_op [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_locks_op actions (pre, wit, rel) = 
             locks_only_consistent_locks_op actions (pre, wit, [])"
unfolding locks_only_consistent_locks_op.simps ..

lemma rel_list_rmw_atomicity_op [simp]:
  assumes "rel \<noteq> []"
  shows   "rmw_atomicity_op actions (pre, wit, rel) = rmw_atomicity_op actions (pre, wit, [])"     
unfolding rmw_atomicity_op.simps ..

lemma rel_list_well_formed_rf_op [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_rf_op actions (pre, wit, rel) = well_formed_rf_op actions (pre, wit, [])"
unfolding well_formed_rf_op.simps ..

lemma rel_list_locks_only_consistent_lo_op [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_lo_op actions (pre, wit, (''hb'', hb)#rel) = 
             locks_only_consistent_lo_op actions (pre, wit, [(''hb'', hb)])"
unfolding locks_only_consistent_lo_op.simps ..

lemma rel_list_locks_only_consistent_lo_op_release_acquire_fenced [simp]:
  shows   "locks_only_consistent_lo_op actions (pre, wit, getRelations pre wit) = 
             locks_only_consistent_lo_op actions (pre, wit, [(''hb'', getHb pre wit)])"  
unfolding getRelations_def
by simp

lemma rel_list_sc_accesses_consistent_sc_op [simp]:
  assumes "rel \<noteq> []"
  shows   "sc_accesses_consistent_sc_op actions (pre, wit, (''hb'', hb)#rel) = 
             sc_accesses_consistent_sc_op actions (pre, wit, [(''hb'', hb)])"
unfolding sc_accesses_consistent_sc_op.simps ..

lemma rel_list_sc_accesses_consistent_sc_op_release_acquire_fenced [simp]:
  shows   "sc_accesses_consistent_sc_op actions (pre, wit, getRelations pre wit) = 
             sc_accesses_consistent_sc_op actions (pre, wit, [(''hb'', getHb pre wit)])"   
unfolding getRelations_def
by simp

lemma rel_list_det_read_op [simp]:
  assumes "rel \<noteq> []"
  shows   "det_read_op actions (pre, wit, (''hb'', hb)#rel) = 
             det_read_op actions (pre, wit, [(''hb'', hb)])"          
unfolding det_read_op.simps ..

lemma rel_list_det_read_op_release_acquire_fenced [simp]:
  shows   "det_read_op actions (pre, wit, getRelations pre wit) = 
             det_read_op actions (pre, wit, [(''hb'', getHb pre wit)])"      
unfolding getRelations_def
by simp

lemma rel_list__consistent_execution [simp]:
  assumes "rel \<noteq> []"
  shows   "apply_tree consistent_execution (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             apply_tree consistent_execution (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
using assms     
unfolding consistent_execution_def
by simp

lemma rel_list_exIsConsistent [simp]:
  assumes "rel \<noteq> []"
  shows   "exIsConsistent (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             exIsConsistent (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
using assms     
unfolding exIsConsistent_def  
by simp

lemma rel_list_exIsConsistent_op [simp]:
  assumes "rel \<noteq> []"
  shows   "exIsConsistent_op actions (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) = 
             exIsConsistent_op actions (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
using assms     
unfolding exIsConsistent_op_def  
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

(* TODO: for some stupid reason, auto can't stand 
   this simplification rel_list_sublanguage, when proving stuff about 
   isConsistent_op, although
   the simplification is sensible, and does not 
   even apply in that case. *)
lemma rel_list_sublanguage:
  assumes "rel \<noteq> []"
  shows   "sublanguage {(pre, wit, rel)} = sublanguage {(pre, wit, [])}"
unfolding sublanguage_def
by simp

lemma rel_list_exIsDefined [simp]:
  assumes "rel \<noteq> []"
  shows   "exIsDefined (pre, wit, (''hb'', hb)#rel) = exIsDefined (pre, wit, [(''hb'', hb)])"
(* And for another stupid reason, simp doesn't understand rel_list_sublanguage (it does not 
   simplify sublanguage {(pre, wit, (''hb'', hb) # rel)}, nor 
   sublanguage {(pre, wit, [(''hb'', hb)])} *)
using assms
unfolding exIsDefined_simp sublanguage_def
by simp

(* Auxilary lemmas (not added to the simp-set) *)

(* This alternative definition of relOver sometimes works better. We do not include it in the simp
set, because we do not want relOver to be always expanded. *)
lemma relOver_simp:
  shows "relOver r s = (r \<subseteq> s \<times> s)"
unfolding relOver_def 
by auto


lemma transitive_simp:
  assumes "trans r"
      and "(a, b) \<in> r"
      and "(b, c) \<in> r"
  shows   "(a, c) \<in> r"
using assms
unfolding trans_def 
by fast

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

lemma trancl_mono2:
  assumes "x \<subseteq> y"
  shows   "x\<^sup>+ \<subseteq> y\<^sup>+"
using assms
by (metis subsetI trancl_mono)

lemma trancl_mono3:
  assumes "trans y"
  shows   "x\<^sup>+ \<subseteq> y = (x \<subseteq> y)"
proof -
  have "y = y\<^sup>+"
    using assms 
    by (metis trancl_id)
  hence "x \<subseteq> y \<Longrightarrow> x\<^sup>+ \<subseteq> y"
    using trancl_mono2 by blast
  thus ?thesis by auto
qed

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
          consistent_execution_def
by simp

lemma cons_tot_empty:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "tot_empty (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_well_formed_threads:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "well_formed_threads (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_well_formed_rf:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "well_formed_rf (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_locks_only_consistent_locks:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "locks_only_consistent_locks (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_locks_only_consistent_lo:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_consistent_mo:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_mo (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_sc_accesses_consistent_sc:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_sc_fenced_sc_fences_heeded:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "sc_fenced_sc_fences_heeded (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_consistent_hb:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_det_read:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "det_read (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_consistent_non_atomic_rf:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_consistent_atomic_rf:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "consistent_atomic_rf (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_coherent_memory_use:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "coherent_memory_use (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_rmw_atomicity:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "rmw_atomicity (pre, wit, [])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp

lemma cons_sc_accesses_sc_reads_restricted:
  assumes "exIsConsistent (pre, wit, getRelations pre wit)"
  shows   "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
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
  thus ?case unfolding minOpsemStep_def Let_def 
    (* TODO: auto doesn't terminate here. Find out why. *)
    by fast
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

(* The _opsem variants of the consistency predicates imply the corresponding consistency 
   predicates if all actions have been committed *)

lemma consistent_mo_resolution:
  assumes "consistent_mo_op (actions0 pre) (pre, wit, [])"
  shows   "consistent_mo (pre, wit, [])"
using assms
unfolding consistent_mo.simps consistent_mo_op.simps 
by simp

lemma det_read_resolution:
  fixes pre wit hb rel
  defines         "vse \<equiv> visible_side_effect_set (actions0 pre) hb"
  assumes conshb: "consistent_hb (pre, wit, [(''hb'', hb)])"
      and "det_read_op (actions0 pre) (pre, wit, [(''hb'', hb),(''vse'', vse)])"
  shows   "det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])"
using assms 
unfolding vse_def det_read_op.simps det_read_simp[OF conshb] det_read_alt.simps
by simp

lemma locks_only_consistent_lo_resolution:
  assumes "locks_only_consistent_lo_op (actions0 pre) (pre, wit, [(''hb'', hb)])"
  shows   "locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
using assms
unfolding locks_only_consistent_lo.simps locks_only_consistent_lo_op.simps
by simp

lemma locks_only_consistent_locks_resolution:
  assumes relOver: "relation_over (actions0 pre) (lo wit)"
      and locks:   "locks_only_consistent_locks_op (actions0 pre) (pre, wit, [])"
  shows   "locks_only_consistent_locks (pre, wit, [])"
unfolding locks_only_consistent_locks.simps
proof auto
  fix a c
  assume assms2: "is_successful_lock a"
                 "is_successful_lock c"
                 "(a, c) \<in> lo wit"
  hence "c \<in> actions0 pre" 
    using relOver 
    by (auto elim: relOverE)
  thus "\<exists>b\<in>actions0 pre. is_unlock b \<and> (a, b) \<in> lo wit \<and> (b, c) \<in> lo wit"
    using locks assms2 
    unfolding locks_only_consistent_locks_op.simps
    by auto
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
  fixes pre wit hb rel
  defines "vse \<equiv> visible_side_effect_set (actions0 pre) hb"
  assumes "exIsConsistent_op (actions0 pre) (pre, wit, [(''hb'',hb),(''vse'',vse)])"
  shows   "exIsConsistent (pre, wit, [(''hb'',hb),(''vse'',vse)])"
proof -
  have rel_lo: "relation_over (actions0 pre) (lo wit)"
    using assms
    unfolding exIsConsistent_op_def
    by (simp add: locks_only_consistent_lo_op.simps)
  show ?thesis
    using assms 
    unfolding exIsConsistent_def
              exIsConsistent_op_def
              memory_model_def
              consistent_execution_def
              vse_def
    by (auto simp add: well_formed_rf_resolution
              locks_only_consistent_locks_resolution[OF rel_lo]
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
    unfolding getRelations_def getVse_def
    using execution_resolution as4
    by simp
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
  hence axiomConsistent: "axiomConsistent opsem_t p (pre, wit, getRelations pre wit)"
    using soundnessConsistency by auto
  have "\<not> exIsDefined (pre, wit, getRelations pre wit)"
    using as1 as2 as5 by (metis isDefinedCorrespondence)
  thus "axiomUndefined opsem_t p (pre, wit, relation_calculation memory_model pre wit)"
    using axiomConsistent unfolding axiomUndefined_def by simp
qed

(* Section 3 - The execution order of the operational semantics ------------------------------- *)


(* To show completeness with respect to the axiomatic model, we execute actions of a consistent
   execution in a particular order. In this section we prove that such an order exists *)

lemma consE [elim]: 
  assumes "exIsConsistentAlt pre wit"
  shows "assumptions (pre, wit, [])"
        "tot_empty (pre, wit, [])"
        "well_formed_threads (pre, wit, [])"
        "well_formed_rf (pre, wit, [])"
        "locks_only_consistent_locks (pre, wit, [])"
        "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
        "consistent_mo (pre, wit, [])"
        "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
        "sc_fenced_sc_fences_heeded (pre, wit, [])"
        "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
        "det_read (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
        "consistent_non_atomic_rf (pre, wit, [(''hb'', getHb pre wit), (''vse'', getVse pre wit)])"
        "consistent_atomic_rf (pre, wit, [(''hb'', getHb pre wit)])"
        "coherent_memory_use (pre, wit, [(''hb'', getHb pre wit)])"
        "rmw_atomicity (pre, wit, [])"
        "sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', getHb pre wit)])"
using assms
unfolding exIsConsistent_def 
          memory_model_def
          consistent_execution_def
by simp_all

lemma not_at_writes_in_hb_minus:
  assumes cons:         "exIsConsistentAlt pre wit"
      and in_rel:       "(a, b) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit"
      and not_at_write: "is_na_or_non_write pre a"
  shows                 "(a, b) \<in> hbMinusAlt pre wit"
using in_rel
proof (elim UnE)
  assume in_rf: "(a, b) \<in> rf wit"
  hence "is_write a" "is_read b" "loc_of a = loc_of b" 
    using cons by (auto elim: rfE)
  hence "is_at_non_atomic_location (lk pre) a"
    using not_at_write unfolding is_na_or_non_write_def by simp
  hence not_at: "is_at_non_atomic_location (lk pre) b"
    using `loc_of a = loc_of b`
    unfolding is_at_non_atomic_location_def by auto
  hence "(a, b) \<in> getVse pre wit"
    using in_rf cons by (auto elim: non_atomic_rfE)
  hence in_hb: "(a, b) \<in> getHb pre wit"
    unfolding getVse_def
              visible_side_effect_set_def
    by auto
  have "is_na_or_non_write pre b"
    using not_at unfolding is_na_or_non_write_def by simp
  thus "(a, b) \<in> hbMinusAlt pre wit"
    using in_hb
    by auto
next
  assume "(a, b) \<in> mo wit"
  hence "is_write a \<and> is_at_atomic_location (lk pre) a"
    using cons by (auto elim: moE)
  hence False
    using not_at_write at_implies_not_na
    unfolding is_na_or_non_write_def
    by simp
  thus "(a, b) \<in> hbMinusAlt pre wit" 
    by contradiction auto
qed auto

lemma not_at_writes_in_hb_minus_tc:
  assumes cons:         "exIsConsistent (pre, wit, getRelations pre wit)"
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
  assumes cons:        "exIsConsistent (pre, wit, getRelations pre wit)"
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
  hence "is_read b" using cons by (auto elim: rfE)
  hence "is_RMW b" 
    using is_at_write
    unfolding is_na_or_non_write_def
    by (cases b) simp_all
  thus "(a, b) \<in> mo wit"
    using in_rf cons by (auto elim: rmw_rfE)
qed auto

lemma at_writes_in_mo_tc:
  assumes cons:        "exIsConsistent (pre, wit, getRelations pre wit)"
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
    using cons by (auto elim: moE)
  hence "\<not> is_na_or_non_write pre z" 
    unfolding is_na_or_non_write_def
    using at_implies_not_na 
    by auto
  hence "(y, z) \<in> mo wit"
    using `(y, z) \<in> hbMinusAlt pre wit \<union> rf wit \<union> mo wit`
    using at_writes_in_mo[OF cons] by auto
  thus "(y, b) \<in> (mo wit)\<^sup>+" 
    using `(z, b) \<in> (mo wit)\<^sup>+` 
    by (auto simp add: trancl_into_trancl)
qed 

lemma opsemOrder_isStrictPartialOrder:
  assumes cons: "exIsConsistent (pre, wit, getRelations pre wit)"
  shows         "isStrictPartialOrder (opsemOrderAlt pre wit)"
proof -
  have "irrefl (opsemOrderAlt pre wit)"
    unfolding irrefl_def
    proof (intro allI notI)
      fix x
      assume "(x, x) \<in> opsemOrderAlt pre wit"
      hence in_rel: "(x, x) \<in> (hbMinusAlt pre wit \<union> rf wit \<union> mo wit)\<^sup>+"
        unfolding opsemOrder.simps
        by (metis Un_assoc)
      show False
        proof (cases "is_na_or_non_write pre x")
          have cons_hb: "consistent_hb (pre, wit, [(''hb'', getHb pre wit)])"
            using cons by auto
          have "(hbMinusAlt pre wit) \<subseteq> getHb pre wit" by auto
          hence hbMinus_in_hb: "(hbMinusAlt pre wit)\<^sup>+ \<subseteq> (getHb pre wit)\<^sup>+" 
            using trancl_mono2 by auto
          hence irrefl_hbMinus: "irrefl ((hbMinusAlt pre wit)\<^sup>+)"
            using cons_hb
            unfolding consistent_hb.simps irrefl_def
            by auto
          assume "is_na_or_non_write pre x"
          hence "(x, x) \<in> (hbMinusAlt pre wit)\<^sup>+" 
            using not_at_writes_in_hb_minus_tc[OF cons in_rel] by metis
          thus False using irrefl_hbMinus unfolding irrefl_def by auto          
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
  thus "isStrictPartialOrder (opsemOrderAlt pre wit)" 
    unfolding isStrictPartialOrder_def opsemOrder.simps by simp
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

(* Section 4 - Properties of happens-before --------------------------------------------------- *)

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

definition otherThreadLoInHb :: "hbCalculation \<Rightarrow> bool" where 
  "otherThreadLoInHb hbCalc \<equiv> \<forall>a b pre wit. tid_of a \<noteq> tid_of b \<longrightarrow> 
                                             is_unlock a \<longrightarrow> 
                                             is_lock b \<longrightarrow> 
                                             a \<in> actions0 pre \<longrightarrow> 
                                             b \<in> actions0 pre \<longrightarrow> 
                                             (a, b) \<in> lo wit \<longrightarrow> 
                                             (a, b) \<in> hbCalc pre wit"

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
  shows   "locks_only_sw_set_alt pre (witnessRestrict wit actions) \<subseteq> 
           locks_only_sw_set_alt pre wit "
unfolding locks_only_sw_set_alt_def
          locks_only_sw_set_def 
by (auto simp add: locks_only_sw_def elim: relRestrictE)

lemma monotonicity_no_consume_hb:
  assumes "sw2 \<subseteq> sw"
  shows   "no_consume_hb p_sb sw2 \<subseteq> no_consume_hb p_sb sw"
using assms
unfolding no_consume_hb_def
by (metis Un_mono order_refl trancl_mono2)

lemma monotonicity_locks_only_hb:
  shows "locks_only_hb pre (witnessRestrict wit actions) \<subseteq> locks_only_hb pre wit"
unfolding locks_only_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_locks_only_sw]
by auto

(* Monotonicity hb in the rel-acq fragment *)

lemma monotonicity_release_acquire_sw:
  shows   "release_acquire_synchronizes_with_set_alt pre (witnessRestrict wit actions)  \<subseteq> 
           release_acquire_synchronizes_with_set_alt pre wit"
apply (intro subrelI, elim release_acquire_swIE)
unfolding sw_asw_def sw_lock_def sw_rel_acq_def
by (auto elim: relRestrictE)

lemma monotonicity_release_acquire_hb:
  shows "release_acquire_hb pre (witnessRestrict wit actions) \<subseteq> release_acquire_hb pre wit"
unfolding release_acquire_hb_def 
using monotonicity_no_consume_hb[OF monotonicity_release_acquire_sw]
by auto

(* Monotonicity hb in the rel-acq-rlx fragment *)

lemma monotonicity_release_sequence:
  assumes "downclosed actions (mo wit)"
          "(a, b) \<in> release_sequence_set_alt pre (witnessRestrict wit actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> release_sequence_set_alt pre wit"
using assms
unfolding release_sequence_set_alt_def 
          release_sequence_set_def
          downclosed_def
by auto

lemma monotonicity_sw_rel_acq_rs:
  assumes "downclosed actions (mo wit)"
  shows   "  sw_rel_acq_rs pre (witnessRestrict wit actions)
           \<subseteq> sw_rel_acq_rs pre wit"
(* TODO: for some reason "cases rule: sw_rel_acq_rsIE" doesn't work after the "intro subrelI". When
everything is made explicit (the fix, assume, thus) then it does do the right thing. *)
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_rel_acq_rs pre (witnessRestrict wit actions)"
  thus   "(a, b) \<in> sw_rel_acq_rs pre wit"
    proof (cases rule: sw_rel_acq_rsIE)
      case (rel_acq_rs c)
      hence "c \<in> actions" by (auto elim: relRestrictE)
      hence "(a, c) \<in> release_sequence_set_alt pre wit" 
        using monotonicity_release_sequence assms rel_acq_rs
        by metis
      thus "   a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> c \<in> actions0 pre
            \<and> (a, c) \<in> release_sequence_set_alt pre wit \<and> (c, b) \<in> rf wit "
        using rel_acq_rs by (auto elim: relRestrictE)
    qed
qed

lemma monotonicity_release_acquire_relaxed_sw:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "release_acquire_relaxed_synchronizes_with_set_alt pre (witnessRestrict wit actions) \<subseteq> 
           release_acquire_relaxed_synchronizes_with_set_alt pre wit"
using monotonicity_sw_rel_acq_rs[OF downclosed]
by (intro subrelI, elim release_acquire_relaxed_swIE)
   (auto elim!: sw_lockE sw_aswE 
         intro!: sw_aswI sw_lockI 
         elim: relRestrictE)

lemma monotonicity_release_acquire_relaxed_hb:
  assumes "downclosed actions (mo wit)"
  shows   "release_acquire_relaxed_hb pre (witnessRestrict wit actions) \<subseteq> release_acquire_relaxed_hb pre wit"
unfolding release_acquire_relaxed_hb_def 
using monotonicity_no_consume_hb monotonicity_release_acquire_relaxed_sw assms
by metis

(* Monotonicity hb in the rel-acq-rlx-fenced fragment *)

lemma monotonicity_hypothetical_release_sequence:
  assumes "downclosed actions (mo wit)"
          "(a, b) \<in> hypothetical_release_sequence_set_alt pre (witnessRestrict wit actions)"
          "b \<in> actions"          
  shows   "(a, b) \<in> hypothetical_release_sequence_set_alt pre wit"
using assms
unfolding hypothetical_release_sequence_set_alt_def 
          hypothetical_release_sequence_set_def
          downclosed_def
by auto

lemma monotonicity_sw_fence_sb_hrs_rf_sb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_sb_hrs_rf_sb pre (witnessRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre (witnessRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit"
    proof (cases rule: sw_fence_sb_hrs_rf_sbIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y z)
      hence "y \<in> actions" by (auto elim: relRestrictE)
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> z \<in> actions0 pre
            \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, z) \<in> rf wit \<and> (z, b) \<in> sb pre"
        using fence by (auto elim: relRestrictE)
    qed
qed

lemma monotonicity_sw_fence_sb_hrs_rf:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_sb_hrs_rf pre (witnessRestrict wit actions)
           \<subseteq> sw_fence_sb_hrs_rf pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_sb_hrs_rf pre (witnessRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_sb_hrs_rf pre wit"
    proof (cases rule: sw_fence_sb_hrs_rfIE)
      let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
      case (fence x y)
      hence "y \<in> actions" by (auto elim: relRestrictE)
      hence "(x, y) \<in> ?hrs"
        using monotonicity_hypothetical_release_sequence
        using downclosed fence
        by auto
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> sb pre \<and> (x, y) \<in> ?hrs \<and> (y, b) \<in> rf wit"
        using fence by (auto elim: relRestrictE)
    qed
qed

lemma monotonicity_sw_fence_rs_rf_sb:
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "  sw_fence_rs_rf_sb pre (witnessRestrict wit actions)
           \<subseteq> sw_fence_rs_rf_sb pre wit"
proof (intro subrelI)
  fix a b
  assume "(a, b) \<in> sw_fence_rs_rf_sb pre (witnessRestrict wit actions)"
  thus "(a, b) \<in> sw_fence_rs_rf_sb pre wit"
    proof (cases rule: sw_fence_rs_rf_sbIE)
      let ?rs  = "release_sequence_set_alt pre wit"
      case (fence x y)
      hence "y \<in> actions" by (auto elim: relRestrictE)
      hence "(a, x) \<in> ?rs"
        using monotonicity_release_sequence
        using downclosed fence
        by (auto elim: relRestrictE)
      thus "  a \<in> actions0 pre \<and> b \<in> actions0 pre \<and> x \<in> actions0 pre 
            \<and> y \<in> actions0 pre \<and> (a, x) \<in> ?rs \<and> (x, y) \<in> (rf wit) \<and> (y, b) \<in> (sb pre)"
        using fence by (auto elim: relRestrictE)
    qed
qed

lemma monotonicity_release_acquire_fenced_sw: 
  assumes downclosed: "downclosed actions (mo wit)"
  shows   "release_acquire_fenced_synchronizes_with_set_alt pre (witnessRestrict wit actions) \<subseteq> 
           release_acquire_fenced_synchronizes_with_set_alt pre wit"
using monotonicity_sw_fence_sb_hrs_rf_sb[OF downclosed]
using monotonicity_sw_fence_sb_hrs_rf[OF downclosed]
using monotonicity_sw_fence_rs_rf_sb[OF downclosed]
using monotonicity_sw_rel_acq_rs[OF downclosed]
apply (intro subrelI, elim release_acquire_fenced_swIE)
by (auto 8 2 elim!: sw_lockE sw_aswE 
             intro!: sw_aswI sw_lockI)

lemma monotonicity_release_acquire_fenced_hb:
  assumes "downclosed actions (mo wit)"
  shows   "release_acquire_fenced_hb pre (witnessRestrict wit actions) \<subseteq> release_acquire_fenced_hb pre wit"
unfolding release_acquire_fenced_hb_def 
using monotonicity_no_consume_hb monotonicity_release_acquire_fenced_sw assms
by metis

(* Monotonicity hb in the with_consume fragment *)

lemma monotonicity_with_consume_cad:
  shows "with_consume_cad_set_alt pre (witnessRestrict wit actions) \<subseteq> 
         with_consume_cad_set_alt pre wit"
unfolding with_consume_cad_set_alt_def
          with_consume_cad_set_def
by (intro trancl_mono2) auto

lemma monotonicity_with_consume_dob_set:
  assumes downclosed: "downclosed actions (mo wit)"
  shows "with_consume_dob_set_alt pre (witnessRestrict wit actions) \<subseteq>
         with_consume_dob_set_alt pre wit"
proof (intro subrelI)
  let ?rs   = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt pre (witnessRestrict wit actions)"
  let ?cad  = "with_consume_cad_set_alt pre wit"
  let ?cad2 = "with_consume_cad_set_alt pre (witnessRestrict wit actions)"
  fix a b
  assume in_dob: "(a, b) \<in> with_consume_dob_set_alt pre (witnessRestrict wit actions)"
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
  shows   "inter_thread_happens_before_alt pre (witnessRestrict wit actions) \<subseteq> 
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
  shows   "with_consume_hb pre (witnessRestrict wit actions) \<subseteq> with_consume_hb pre wit"
unfolding with_consume_hb_def happens_before_def
using monotonicity_ithb[OF downclosed]
by auto

(* Prefixes are final in the rel-acq-rlx fragment *)

lemma final_release_sequence:
  assumes  "downclosed actions (mo wit)"
      and  "b \<in> actions"
      and  "(a, b) \<in> release_sequence_set_alt pre wit"
  shows   "(a, b) \<in> release_sequence_set_alt pre (witnessRestrict wit actions)"
using assms
unfolding release_sequence_set_alt_def 
          release_sequence_set_def 
          downclosed_def
by auto

lemma final_sw_asw:
  assumes "(a, b) \<in> sw_asw pre wit"
  shows   "(a, b) \<in> sw_asw pre (witnessRestrict wit actions)"
using assms
unfolding sw_asw_def
by auto

lemma final_sw_lock:
  assumes "(a, b) \<in> sw_lock pre wit"
      and "a \<in> actions" 
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_lock pre (witnessRestrict wit actions)"
using assms
unfolding sw_lock_def
by auto

lemma final_sw_rel_acq_rs:
  assumes "(a, b) \<in> sw_rel_acq_rs pre wit"
      and downclosed_rf: "downclosed actions (rf wit)"
      and downclosed_mo: "downclosed actions (mo wit)"
      and "b \<in> actions"
  shows   "(a, b) \<in> sw_rel_acq_rs pre (witnessRestrict wit actions)"
using assms(1)
proof (cases rule: sw_rel_acq_rsIE, simp)
  case (rel_acq_rs c)
  hence "c \<in> actions" 
    using downclosed_rf `b \<in> actions` by (auto elim: downclosedE)
  let ?rs   = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
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
  let ?sw2 = "release_acquire_relaxed_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
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
                                     (release_acquire_relaxed_hb pre (witnessRestrict wit actions))"
    using final_no_consume_hb downclosed 
    unfolding release_acquire_relaxed_hb_def
    by metis   
qed

(* Prefixes are final in the rel-acq-rlx-fence fragment *)

lemma final_hypothetical_release_sequence:
  assumes  "downclosed actions (mo wit)"
      and  "b \<in> actions"
      and  "(a, b) \<in> hypothetical_release_sequence_set_alt pre wit"
  shows   "(a, b) \<in> hypothetical_release_sequence_set_alt pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre (witnessRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_sb_hrs_rf_sbIE, simp)
  let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
  let ?hrs2  = "hypothetical_release_sequence_set_alt pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf pre (witnessRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_sb_hrs_rfIE, simp)
  let ?hrs  = "hypothetical_release_sequence_set_alt pre wit"
  let ?hrs2  = "hypothetical_release_sequence_set_alt pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> sw_fence_rs_rf_sb pre (witnessRestrict wit actions)"
using assms(1)
proof (cases rule: sw_fence_rs_rf_sbIE, simp)
  let ?rs  = "release_sequence_set_alt pre wit"
  let ?rs2  = "release_sequence_set_alt pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
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
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
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
                                     (release_acquire_fenced_hb pre (witnessRestrict wit actions))"
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
  shows   "a \<in> actions \<and> (a, b) \<in> with_consume_cad_set_alt pre (witnessRestrict wit actions)"
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
  have "(a, b) \<in> with_consume_cad_set_alt pre (witnessRestrict wit actions)"
    using cad unfolding with_consume_cad_set_alt_def with_consume_cad_set_def
    proof (rule converse_trancl_induct)
      fix y
      assume y: "(y, b) \<in> rf wit \<inter> sb pre \<union> dd pre"
      hence "(y, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+" by fast
      hence "y \<in> actions" using downclosed_cad by fast
      hence "(y, b) \<in> relRestrict (rf wit) actions \<inter> sb pre \<union> dd pre"
        using y b by auto
      thus "(y, b) \<in> (rf (witnessRestrict wit actions) \<inter> sb pre \<union> dd pre)\<^sup>+" by auto
    next
      fix y z
      assume y:  "(y, z) \<in> rf wit \<inter> sb pre \<union> dd pre"
         and z:  "(z, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+"
         and ih: "(z, b) \<in> (rf (witnessRestrict wit actions) \<inter> sb pre \<union> dd pre)\<^sup>+"
      have "z \<in> actions" using downclosed_cad[OF z] .
      have "(y, b) \<in> (rf wit \<inter> sb pre \<union> dd pre)\<^sup>+" using y z by (rule trancl_into_trancl2)
      hence "y \<in> actions" using downclosed_cad by fast
      have "(y, z) \<in> relRestrict (rf wit) actions \<inter> sb pre \<union> dd pre"
        using y `y \<in> actions` `z \<in> actions` by auto
      thus "(y, b) \<in> (rf (witnessRestrict wit actions) \<inter> sb pre \<union> dd pre)\<^sup>+"
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
  shows   "(a, d) \<in> with_consume_dob_set_alt pre (witnessRestrict wit actions)"
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
  have cad2: "((b, d) \<in> with_consume_cad_set_alt pre (witnessRestrict wit actions) \<or> (b = d)) \<and> b \<in> actions"
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
  have rs2: "(a, e) \<in> release_sequence_set_alt pre (witnessRestrict wit actions)" 
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
  shows   "(a, b) \<in> inter_thread_happens_before_r pre (witnessRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_r_def
apply (elim UnMember_mono)
defer defer
apply (simp, elim composeMember_mono)
proof simp
  assume "(a, b) \<in> with_consume_dob_set_alt pre wit"
  thus "(a, b) \<in> with_consume_dob_set_alt pre (witnessRestrict wit actions)"
    using final_dob[OF downclosed_sb downclosed_rf downclosed_mo trans_sb dd_in_sb b]
    by auto
next
  assume "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
  thus "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
    using final_release_acquire_fenced_sw[OF downclosed_rf downclosed_mo downclosed_sb2 a b]
    by metis
next
  fix y
  assume sw: "(a, y) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
     and sb: "(y, b) \<in> sb pre"
  have "y \<in> actions"
    using sb downclosed_sb by auto
  thus "(a, y) \<in> release_acquire_fenced_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> inter_thread_happens_before_step pre (witnessRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_step_def
apply (elim UnMember_mono)
defer 
apply (simp, elim composeMember_mono)
proof simp
  assume "(a, b) \<in> inter_thread_happens_before_r pre wit"
  thus "(a, b) \<in> inter_thread_happens_before_r pre (witnessRestrict wit actions)"
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
  thus "(y, b) \<in> inter_thread_happens_before_r pre (witnessRestrict wit actions)"
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
  shows   "(a, b) \<in> inter_thread_happens_before_alt pre (witnessRestrict wit actions)"
using ithb
unfolding inter_thread_happens_before_alt_def
proof (induct rule: converse_trancl_induct)
  fix y
  assume step: "(y, b) \<in> inter_thread_happens_before_step pre wit"
  hence "y \<in> actions"
    using downclosed_ithb
    unfolding inter_thread_happens_before_alt_def
    by auto
  thus "(y, b) \<in> (inter_thread_happens_before_step pre (witnessRestrict wit actions))\<^sup>+"
    using final_ithb_step[OF downclosed_sb downclosed_sb2 downclosed_rf 
                             downclosed_mo downclosed_ithb trans_sb dd_in_sb _ b step]
    by auto
next
  fix y z
  assume yz: "(y, z) \<in> inter_thread_happens_before_step pre wit"
     and zb: "(z, b) \<in> (inter_thread_happens_before_step pre wit)\<^sup>+"
     and ih: "(z, b) \<in> (inter_thread_happens_before_step pre (witnessRestrict wit actions))\<^sup>+"
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
  hence "(y, z) \<in> (inter_thread_happens_before_step pre (witnessRestrict wit actions))\<^sup>+"
    using final_ithb_step[OF downclosed_sb1b downclosed_sb2 downclosed_rf 
                             downclosed_mo downclosed_ithb2 trans_sb dd_in_sb y z yz]
    by auto
  thus "(y, b) \<in> (inter_thread_happens_before_step pre (witnessRestrict wit actions))\<^sup>+"
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
  shows   "(a, b) \<in> with_consume_hb pre (witnessRestrict wit actions)"
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
  let ?sw2  = "release_acquire_fenced_synchronizes_with_set_alt pre (witnessRestrict wit actions)"
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
                                     (with_consume_hb pre (witnessRestrict wit actions))"
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
      show "(a, b) \<in> with_consume_hb pre (witnessRestrict wit actions)"
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
          getRelations_def 
          hbMinus.simps
by auto

lemma opsemOrderIsMonotonic:
  shows "hbCalcIsMonotonic opsemOrderAlt"
unfolding hbCalcIsMonotonic_def
proof (intro allI impI)
  fix pre
  fix wit :: execution_witness
  fix actions
  assume downclosed: "downclosed actions (mo wit)"
  have "hbMinusAlt pre (witnessRestrict wit actions) \<subseteq> hbMinusAlt pre wit"
    using downclosed hbMinusIsMonotonic
    unfolding hbCalcIsMonotonic_def by metis
  hence subset: "hbMinusAlt pre (witnessRestrict wit actions) \<union> 
                (relRestrict (rf wit) actions \<union> 
                 relRestrict2 (mo wit) actions) \<subseteq> 
                hbMinusAlt pre wit \<union> (rf wit \<union> mo wit)" 
    by auto
  show "opsemOrderAlt pre (witnessRestrict wit actions) \<subseteq> opsemOrderAlt pre wit"
    unfolding opsemOrder.simps apply simp
    using subset trancl_mono2 by metis
qed

(* Section 5 - Invariance of consistency predicates under prefixes ---------------------------- *)

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
  shows   "assumptions (pre, witnessRestrict wit actions, [])"
using assms
unfolding assumptions.simps finite_prefixes_def
by auto

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
proof auto
  assume "irrefl (hb\<^sup>+)" 
     and "hb2 \<subseteq> hb"
  hence "hb2\<^sup>+ \<subseteq> hb\<^sup>+" using trancl_mono2 by metis
  thus "irrefl (hb2\<^sup>+)" using `irrefl (hb\<^sup>+)` 
    unfolding irrefl_def by auto
next
  assume "finite_prefixes hb (actions0 pre)"
     and "hb2 \<subseteq> hb"
  thus "finite_prefixes hb2 (actions0 pre)"
    using finite_prefix_subset
    using `hb2 \<subseteq> hb`
    by auto
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
    using final_vse[OF final `hb2 \<subseteq> hb` non_write_b `b \<in> actions`] 
    unfolding vse_def vse2_def by blast
qed

lemma det_read_restriction:
  fixes pre wit hb hb2 
  defines "vse  \<equiv>  visible_side_effect_set (actions0 pre) hb"
      and "vse2 \<equiv>  visible_side_effect_set (actions0 pre) hb2"
  assumes det_read:      "det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])"
      and conshb:        "consistent_hb (pre, wit, [(''hb'', hb)])"
      and downclosed_rf: "downclosed actions (rf wit)"
      and final:         "selective_prefixes_are_final (is_na_or_non_write pre) actions hb hb2"
      and                "hb2 \<subseteq> hb"
  shows   "det_read_op actions (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
unfolding det_read_op.simps
proof (clarsimp)
  fix r 
  assume "r \<in> actions0 pre" 
         "is_load r" 
         "r \<in> actions" 
  hence non_write_r: "is_na_or_non_write pre r"
    unfolding is_na_or_non_write_def by (cases r) auto
  hence "\<And>w. ((w, r) \<in> hb2) = ((w, r) \<in> hb)"
    using `hb2 \<subseteq> hb` final `r \<in> actions`
    unfolding selective_prefixes_are_final_def 
    by auto  
  hence "  (\<exists>w\<in>actions0 pre. (w, r) \<in> hb2 \<and> is_write w \<and> loc_of w = loc_of r)
         = (\<exists>w\<in>actions0 pre. (w, r) \<in> hb \<and> is_write w \<and> loc_of w = loc_of r)"
    by auto
  also have "... = (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit)"
    using det_read `is_load r` `r \<in> actions0 pre` 
    unfolding vse_def det_read_simp[OF conshb] det_read_alt.simps
    by simp
  also have "... = (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit \<and> w' \<in> actions)"
    using downclosed_rf `r \<in> actions` unfolding downclosed_def by auto
  finally show "  (\<exists>w\<in>actions0 pre. (w, r) \<in> hb2 \<and> is_write w \<and> loc_of w = loc_of r)  
                = (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit \<and> w' \<in> actions)" .
qed

lemma locks_only_consistent_lo_restriction:
  assumes "locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
          "hb2 \<subseteq> hb"
  shows   "locks_only_consistent_lo_op actions (pre, witnessRestrict wit actions, [(''hb'', hb2)])"
proof -
  obtain hb3 where [simp]: "hb = hb2 \<union> hb3" using `hb2 \<subseteq> hb` by auto
  show ?thesis 
    using assms relRestrict_relOver relRestrict_isTransitive relRestrict_isIrreflexive
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
    using assms relRestrict_relOver relRestrict_isTransitive relRestrict_isIrreflexive
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
      and downclosed: "downclosed actions (opsemOrderAlt pre wit)"
  shows   "exIsConsistent_op actions (pre, wit', getRelations pre wit')"
proof -

  have downclosed_hbMinus: "downclosed actions (hbMinusAlt pre wit)"
   and downclosed_rf:      "downclosed actions (rf wit)"
   and downclosed_mo:      "downclosed actions (mo wit)"
    using downclosed unfolding opsemOrder.simps by simp_all
  have "sbMinus pre (sb pre) \<subseteq> hbMinusAlt pre wit" 
    using sbInHb unfolding sbMinus_def hbMinus.simps by auto
  hence downclosed_sbMinus: "downclosed actions (sbMinus pre (sb pre))"
    using downclosed_hbMinus downclosed_subset by metis
  have selective_downclosed: "selective_downclosed (is_na_or_non_write pre) actions (getHb pre wit)"
    using downclosed_hbMinus
    (* TODO: make a simp for hbMinus. *)
    unfolding getRelations_def 
              hbMinus.simps
    by auto
  have trans_sb: "trans (sb pre)"
    using cons_well_formed_threads[OF cons]
    unfolding well_formed_threads.simps isStrictPartialOrder_def
    by auto
  have dd_subset_sb: "dd pre \<subseteq> sb pre"
    using cons_well_formed_threads[OF cons]
    unfolding well_formed_threads.simps 
    by auto
  have prefixes_final: "selective_prefixes_are_final (is_na_or_non_write pre) actions (getHb pre wit) (getHb pre wit')"
    using hbCalcIsFinalForPrefixes downclosed_rf downclosed_mo 
          downclosed_sbMinus selective_downclosed trans_sb dd_subset_sb
    unfolding hbCalcIsFinalForPrefixes_def hbMinus_def wit'_def
    by auto

  have hbSubset: "getHb pre wit' \<subseteq> getHb pre wit"
    using hbCalcIsMonotonic downclosed_mo unfolding hbCalcIsMonotonic_def wit'_def by simp

  show ?thesis
    unfolding exIsConsistent_def
              exIsConsistent_op_def              
              consistent_execution_def
              release_acquire_fenced_relations_simp
              release_acquire_fenced_relations_alt_def
    proof auto
      show "assumptions (pre, wit', [])"
        using cons cons_assumptions assumptions_restriction wit'_def by metis
    next
      show "det_read_op actions (pre, wit', [(''hb'', getHb pre wit')])"
        using cons cons_det_read cons_consistent_hb 
              det_read_restriction downclosed_rf prefixes_final hbSubset
        unfolding getVse_def wit'_def        
        by metis
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
      and downclosed: "downclosed actions (opsemOrderAlt pre wit)"
  shows   "\<exists> s. minOpsemTrace pre (initialState pre) s \<and> 
                exWitness s = witnessRestrict wit actions \<and> 
                committed s = actions"
proof (rule finite_downclosedsubset_induct[where R="(opsemOrderAlt pre wit)" and B="actions0 pre"])
  show "finite actions" using finite .
next
  show "actions \<subseteq> actions0 pre" using universe .
next
  show "downclosed actions (opsemOrderAlt pre wit)" using downclosed .
next
  show "acyclic (opsemOrderAlt pre wit)"
    using opsemOrder_isStrictPartialOrder[OF cons]
    unfolding isStrictPartialOrder_def acyclic_def irrefl_def
    by auto
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
     and downclosed': "downclosed (insert a actions) (opsemOrderAlt pre wit)"
     and max:         "\<forall>b\<in>actions. (a, b) \<notin> opsemOrderAlt pre wit"
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
    using downclosed' unfolding opsemOrder.simps by auto
  have inOpsemOrder: "\<forall>b\<in>actions0 pre. ((b, a) \<in> opsemOrderAlt pre (exWitness ?s') \<longrightarrow> b \<in> actions) \<and>
                                       (b \<in> actions \<longrightarrow> (a, b) \<notin> opsemOrderAlt pre (exWitness ?s'))"
    proof auto
      fix b
      (* TODO: fix opsemOrder *)
      assume "b \<in> actions0 pre"
             "(b, a) \<in> opsemOrder (pre, ?wit', [(''hb'', getHb pre ?wit')])"
      hence ba_in_rel: "(b, a) \<in> opsemOrderAlt pre wit"
        using opsemOrderIsMonotonic downclosed_mo
        unfolding hbCalcIsMonotonic_def
        by auto
      hence "b \<noteq> a"
        using opsemOrder_isStrictPartialOrder[OF cons]
        unfolding isStrictPartialOrder_def irrefl_def
        by auto
      thus "b \<in> actions"
        using downclosed' ba_in_rel unfolding downclosed_def by auto
    next
      fix b
      (* TODO: fix opsemOrder *)
      assume "b \<in> actions0 pre"
             "b \<in> actions"
             "(a, b) \<in> opsemOrder (pre, ?wit', [(''hb'', getHb pre ?wit')])"
      hence ba_in_rel: "(a, b) \<in> opsemOrderAlt pre wit"
        using opsemOrderIsMonotonic downclosed_mo
        unfolding hbCalcIsMonotonic_def
        by auto
      thus False using max `b \<in> actions` by metis 
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
unfolding relOver_def relRestrict_def
by auto

lemma relRestrict2_relOver:
  assumes "relOver r a"
  shows   "relRestrict2 r a = r"
using assms
unfolding relOver_def 
by auto

lemma downclosed_relOver:
  assumes "relOver r a"
  shows   "downclosed a r"
using assms
unfolding relOver_def downclosed_def by auto

lemma completenessConsistency:
  assumes axiomCons: "axiomConsistent opsem_t p (pre, wit, rl)"
      and finite:    "finite (actions0 pre)"
  shows   "minOpsemConsistent opsem_t p (pre, wit)"
proof -

  have opsem_t: "opsem_t p pre" using axiomCons unfolding axiomConsistent.simps by simp

  have "consistent memory_model = consistent_execution"
    by simp
  hence consistent: "exIsConsistent (pre, wit, getRelations pre wit)"
    using axiomCons 
    unfolding axiomConsistent.simps exIsConsistent_def 
    by auto

  have relOverSb: "relOver (sb pre) (actions0 pre)"
    using consistent cons_well_formed_threads
    unfolding well_formed_threads.simps
    by auto

  have "well_formed_rf (pre, wit, [])" 
    using consistent cons_well_formed_rf by simp
  hence relOverRf: "relOver (rf wit) (actions0 pre)"
    unfolding well_formed_rf.simps relOver_def image_def fst_def snd_def 
    by auto

  have "consistent_mo (pre, wit, [])"
    using consistent cons_consistent_mo by simp
  hence relOverMo: "relOver (mo wit) (actions0 pre)"
    unfolding consistent_mo.simps by simp

  have "sc_accesses_consistent_sc (pre, wit, [(''hb'', getHb pre wit)])"
    using consistent cons_sc_accesses_consistent_sc by simp
  hence relOverSc: "relOver (sc wit) (actions0 pre)"
    unfolding sc_accesses_consistent_sc.simps by simp

  have "locks_only_consistent_lo (pre, wit, [(''hb'', getHb pre wit)])"
    using consistent cons_locks_only_consistent_lo by simp
  hence relOverLo: "relOver (lo wit) (actions0 pre)"
    unfolding locks_only_consistent_lo.simps by simp

  have "tot_empty (pre, wit, [])"
    using consistent cons_tot_empty by simp
  hence relOverTot: "relOver (tot wit) (actions0 pre)"
    unfolding tot_empty.simps by simp

  have wit_restrict: "witnessRestrict wit (actions0 pre) = wit" 
    using relOverRf relOverMo relOverSc relOverLo relOverTot
    unfolding witnessRestrict_def 
    by (simp add: relRestrict_relOver relRestrict2_relOver)

  have "relOver (getHb pre wit) (actions0 pre)" 
    using relOverSb hbRelOver by auto
  hence relOverHbMinus: "relOver (hbMinusAlt pre wit) (actions0 pre)"
    unfolding hbMinus.simps 
              relOver_def 
              getRelations_def
    by auto

  have downclosed: "downclosed (actions0 pre) (opsemOrderAlt pre wit)" 
    unfolding opsemOrder.simps
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
  have memModel: "consistent memory_model = consistent_execution"
    by simp
  have "axiomConsistent opsem_t p (pre, wit, rl)"
    using axiomUndef unfolding axiomUndefined_def by simp
  hence "minOpsemConsistent opsem_t p (pre, wit)"
    using finite completenessConsistency by simp
  from this obtain s where assms2: "opsem_t p pre"
                                   "minOpsemTrace pre (initialState pre) s"
                                   "exWitness s = wit"
                                   "committed s = actions0 pre"
    unfolding minOpsemConsistent_def by auto
  have "\<not>exIsDefined (pre, wit, getRelations pre wit)"
    using axiomUndef
    unfolding axiomUndefined_def axiomConsistent.simps 
    by auto
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
    unfolding sublanguage_def
    apply auto
    unfolding observable_filter_def
    by auto

  show "minOpsemBehaviour opsem_t p = axiomBehaviour opsem_t p"
    using opsemIsAxiomAux axiomIsAxiomAux by simp

qed
  
end
