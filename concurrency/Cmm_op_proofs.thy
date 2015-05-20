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
abbreviation "axConsistent ex \<equiv> apply_tree standard_consistent_execution ex"

lemmas sublanguage_def = true_condition_def
lemmas memory_model_def = with_consume_memory_model_def
lemmas axBehaviour_def = standard_behaviour_def
lemmas axUndefined_def = locks_only_undefined_behaviour_alt_def
lemmas getRelations_def = standard_relations_def
lemmas axConsistent_def = standard_consistent_execution_def

lemmas getRelations_simp = standard_relations_simp
                           standard_relations_alt_def



(* The simplified axiomatic model ------------------------------------- *)

abbreviation "axsimpConsistent ex \<equiv> apply_tree axsimpConsistentExecution ex"

lemmas axsimpConsistent_def = axsimpConsistentExecution_def

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

lemma axBehaviourEq:
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

end
