theory "Cmm_master_lemmas"

imports 
Main
"_bin/Cmm_csem"
begin

section {* Auxiliaries *}

lemma defToElim:
  assumes "left = right"
      and "left"
  obtains "right"
using assms
by auto

lemma relToElim:
  assumes "left = right"
      and "(a, b) \<in> left"
  obtains "(a, b) \<in> right"
using assms
by auto

lemmas defToIntro = iffD2

lemma relToIntro:
  assumes "left = right"
      and "(a, b) \<in> right"
  shows   "(a, b) \<in> left"
using assms
by (rule ssubst)

(* 
lemmas I [intro?] = defToIntro[OF _def]
lemmas E [elim?] = defToElim[OF _def]
*)

section {* Lemmas for relation.lem *}

subsubsection {* isIrreflexive *}

lemmas irreflI [intro?] = defToIntro[OF irrefl_def]

lemma irreflE [elim?]:
  assumes "irrefl r"
      and "(a, b) \<in> r"
  obtains "a \<noteq> b"
using assms
unfolding irrefl_def
by auto

lemma irreflTranclE [elim?]:
  assumes "irrefl (r\<^sup>+)"
      and "(a, b) \<in> r"
  obtains "(b, a) \<notin> r"
proof (intro that notI)
  assume "(b, a) \<in> r"
  hence "(a, a) \<in> r\<^sup>+"
    using assms
    by auto
  thus False
    using assms
    unfolding irrefl_def
    by auto
qed

lemma irreflTransE [elim?]:
  assumes "irrefl r"
      and "trans r"
      and "(a, b) \<in> r"
  obtains "(b, a) \<notin> r"
proof -
  have "irrefl (r\<^sup>+)"
    using assms by auto
  thus ?thesis
    using irreflTranclE assms that
    by metis
qed

lemma isIrreflexive_empty [simp]:
  shows "irrefl {}"
unfolding irrefl_def
by simp

lemma isIrreflexive_union [simp]:
  shows "irrefl (r \<union> r') = (irrefl r \<and> irrefl r')"
unfolding irrefl_def
by auto

lemma isIrreflexive_subset:
  assumes "irrefl r"
      and "r' \<subseteq> r"
  shows   "irrefl r'"
using assms
unfolding irrefl_def
by auto

subsubsection {* acyclic *}

lemmas acyclicI [intro?] = defToIntro[OF acyclic_def]

lemma acyclicE [elim?]:
  assumes "acyclic r"
      and "(a, b) \<in> r"
  obtains "(b, a) \<notin> r"
proof (intro that notI)
  assume "(b, a) \<in> r"
  hence "(a, a) \<in> r\<^sup>+"
    using assms
    by auto
  thus False
    using assms
    unfolding acyclic_def
    by auto
qed

lemma acyclic_empty [simp]:
  shows "acyclic {}"
unfolding acyclic_def
by simp

subsubsection {* isTransitive *}

lemmas transI [intro?] = defToIntro[OF trans_def]

(* transE already exists *)
lemmas transE [elim?]

lemma isTransitive_empty [simp]:
  shows "trans {}"
by (rule transI) simp

lemma isTransitive_cross [simp]:
  shows "trans (s \<times> s)"
by (rule transI) simp

lemma isTransitive_closure_equals_id:
  shows "(r\<^sup>+ = r) \<longleftrightarrow> trans r"
proof 
  assume "r\<^sup>+ = r"
  thus "trans r"
    unfolding trans_def
    proof (intro allI impI)
      fix x y z
      assume "(x, y) \<in> r" "(y, z) \<in> r"
      hence "(x, z) \<in> r\<^sup>+" by simp
      thus "(x, z) \<in> r" using `r\<^sup>+ = r` by simp
    qed
qed auto

subsubsection {* Trancl *}

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

subsubsection {* isStrictPartialOrder *}

lemmas isStrictPartialOrderI [intro?] = defToIntro[OF isStrictPartialOrder_def]

lemma isStrictPartialOrderE [elim]:
  assumes "isStrictPartialOrder r"
  obtains "irrefl r"
      and "trans r"
using assms
unfolding isStrictPartialOrder_def
by simp

lemma isStrictPartialOrder_empty [simp]:
  shows "isStrictPartialOrder {}"
unfolding isStrictPartialOrder_def
by simp

subsubsection {* relDomain *}

lemma relDomain_cross_id [simp]:
  shows "Domain (s \<times> s) = s"
unfolding Domain_def
by auto

declare Domain_Un_eq [simp]
thm Domain_Un_eq

subsubsection {* relRange *}

lemma relRange_cross_id [simp]:
  shows "Range (s \<times> s) = s"
unfolding Range_def
by auto

declare Range_Un_eq [simp]
thm Range_Un_eq

subsubsection {* relOver *}

lemma relOverI [intro?]:
  assumes "\<And>a b. (a, b) \<in> r \<Longrightarrow> a \<in> s \<and> b \<in> s"
  shows "relOver r s"
using assms
unfolding relOver_def
by auto

lemma relOverE [elim?]:
  assumes "relOver r s"
      and "(a, b) \<in> r"
  obtains "a \<in> s" "b \<in> s"
using assms
unfolding relOver_def
by auto

lemma relOver_empty_relation [simp]:
  shows "relOver {} s"
unfolding relOver_def
by simp

lemma relOver_empty_carrier [simp]:
  shows "relOver r {} = (r = {})"
unfolding relOver_def 
by auto

lemma relOver_cross_id [simp]:
  shows "relOver (s \<times> s) s' = (s \<subseteq> s')"
unfolding relOver_def
by simp

lemma relOver_union [simp]:
  shows "relOver (r \<union> r') s = (relOver r s \<and> relOver r' s)"
unfolding relOver_def 
by auto

lemma relOver_trancl [simp]:
  shows "relOver (r\<^sup>+) s = relOver r s"
unfolding relOver_def 
by auto

(* We do not add this lemma to the simp set, because it has assumptions that are not always met when
the conclusion holds. *)
lemma relOver_relComp:
  assumes "relOver r s"
          "relOver r' s"
  shows "relOver (relcomp r r') s"
using assms
unfolding relOver_def
by auto

lemma relOver_subset:
  assumes "relOver r s"
      and "r' \<subseteq> r"
  shows   "relOver r' s"
using assms
unfolding relOver_def
by auto

subsubsection {* relRestrict *}

lemmas relRestrictI [intro?] = relToIntro[OF relRestrict_def]

lemma relRestrictE [elim]:
  assumes "(a, b) \<in> relRestrict r s"
  obtains "(a, b) \<in> r"
      and "a \<in> s"
      and "b \<in> s"
using assms
unfolding relRestrict_def
by simp

(* TODO: this simp is redundant (given the elim and intro of relRestrict), but removing it 
makes the proof fail *)
lemma relRestrict_member [simp]:
  shows "(a, b) \<in> relRestrict rel s = ((a, b) \<in> rel \<and> a \<in> s \<and> b \<in> s)"
unfolding relRestrict_def
by auto

lemma relRestrict_empty_restriction [simp]:
  shows "relRestrict r {} = {}"
unfolding relRestrict_def
by simp

lemma relRestrict_empty_relation [simp]:
  shows "relRestrict {} s = {}"
unfolding relRestrict_def
by simp

lemma relRestrict_subset [simp]:
  shows "relRestrict r s \<subseteq> r"
unfolding relRestrict_def
by auto

lemma relRestrict_union [simp]:
  shows "relRestrict (r \<union> r') s = (relRestrict r s \<union> relRestrict r' s)"
unfolding relRestrict_def
by auto

lemma relRestrict_relRestrict [simp]:
  shows "relRestrict (relRestrict r s) s' = relRestrict r (s \<inter> s')"
unfolding relRestrict_def
by auto

lemma relRestrict_id:
  assumes "relOver r a"
  shows   "relRestrict r a = r"
using assms
unfolding relOver_def relRestrict_def
by auto

lemma relRestrict_isTransitive [elim]:
  assumes "trans r"
  shows   "trans (relRestrict r s)"
using assms
unfolding trans_def relRestrict_def
by blast

lemma relRestrict_trancl_subset:
  shows "(relRestrict r s)\<^sup>+ \<subseteq> relRestrict (r\<^sup>+) s"
apply (intro subrelI)
apply (erule trancl_induct)
by auto

lemma relRestrict_isIrreflexive [elim]:
  assumes "irrefl r"
  shows   "irrefl (relRestrict r s)"
using assms
unfolding irrefl_def relRestrict_def
by auto

lemma relRestrict_relOver [elim]:
  assumes "relOver r s'"
  shows   "relOver (relRestrict r s) s'"
using assms
unfolding relOver_def relRestrict_def
by auto

lemma relRestrict_relOver2 [elim]:
  assumes "relOver r s'"
  shows   "relOver (relRestrict r s) (s' \<inter> s)"
using assms
unfolding relOver_def relRestrict_def
by auto

lemma relRestrict_finite_prefixes [elim]:
  assumes "finite_prefixes r s'"
  shows   "finite_prefixes (relRestrict r s) s'"
using assms
unfolding finite_prefixes_def relRestrict_def
by auto

subsubsection {* Supremum *}

lemma supremum_partial_order:
  assumes finite:    "finite A"
      and non_empty: "A \<noteq> {}"
      and order:     "isStrictPartialOrder R"
  obtains x where "x \<in> A" "\<forall>y. y \<in> A \<longrightarrow> (x, y) \<notin> R"
using finite non_empty
proof (induct rule: finite_ne_induct)
  case (singleton x)
  have "(x, x) \<notin> R"
    using order 
    unfolding isStrictPartialOrder_def irrefl_def
    by auto
  thus ?case
    using singleton by auto
next
  case (insert a F)
  have "\<And>x. x \<in> F \<Longrightarrow> \<forall>y. y \<in> F \<longrightarrow> (x, y) \<notin> R \<Longrightarrow> thesis"
    proof -
      fix x
      assume x: "x \<in> F" 
         and sup: "\<forall>y. y \<in> F \<longrightarrow> (x, y) \<notin> R"
      show "thesis"
        proof (cases "(x, a) \<in> R")
          assume "(x, a) \<in> R"
          have "\<forall>y. y \<in> insert a F \<longrightarrow> (a, y) \<notin> R"
            proof auto
              assume "(a, a) \<in> R"
              thus False 
                using order 
                unfolding isStrictPartialOrder_def irrefl_def
                by auto
            next
              fix y
              assume "y \<in> F" "(a, y) \<in> R"
              hence "(x, y) \<in> R"
                using `(x, a) \<in> R` order
                unfolding isStrictPartialOrder_def trans_def
                by blast
              thus False using sup `y \<in> F` by auto
            qed
          thus ?thesis
            using insert by auto
        next
          assume "(x, a) \<notin> R"
          have "\<forall>y. y \<in> insert a F \<longrightarrow> (x, y) \<notin> R"
            using `(x, a) \<notin> R` sup
            by auto
          thus ?thesis
            using insert `x \<in> F` by auto
        qed
    qed
  thus ?case
    using insert by metis
qed

lemma supremum:
  assumes finite:    "finite A"
      and non_empty: "A \<noteq> {}"
      and acyclic:   "acyclic R"
  obtains x where "x \<in> A" "\<forall>y. y \<in> A \<longrightarrow> (x, y) \<notin> R"
proof -
  have "isStrictPartialOrder (R\<^sup>+)"
    using acyclic
    unfolding acyclic_def isStrictPartialOrder_def irrefl_def
    by auto
  then obtain x where x: "x \<in> A" "\<forall>y. y \<in> A \<longrightarrow> (x, y) \<notin> R\<^sup>+"
    using supremum_partial_order[OF finite non_empty] by auto
  thus ?thesis
    using x that by auto
qed

section {* Cmm: 1 - Relational definitions *}

subsubsection {* relation_over *}

(* We simplify relation_over_def to its official Lem counterpart. *)

declare relation_over_def [simp]
thm relation_over_def

subsubsection {* inj_on *}

lemma inj_on_empty [simp]:
  shows "inj_on f {}"
unfolding inj_on_def
by simp

subsubsection {* adjacent_less_than *}

lemmas adjacent_less_thanI [intro?] = defToIntro[OF adjacent_less_than_def]

(* TODO: perhaps the negative conjuct should be phrased differently. For example by assuming a z
with the properties, obtaining False. *)

lemma adjacent_less_thanE [elim]:
  assumes "adjacent_less_than ord s x y"
  obtains "(x, y) \<in> ord"
      and "\<not>(\<exists>z\<in>s. (x, z) \<in> ord \<and> (z, y) \<in> ord)"
using assms
unfolding adjacent_less_than_def
by simp

subsubsection {* finite_prefixes *}

lemmas finite_prefixesI [intro?] = defToIntro[OF finite_prefixes_def]

lemma finite_prefixesE [elim?]:
  assumes "finite_prefixes r s"
      and "b \<in> s"
  obtains "finite {a. (a, b) \<in> r}"
using assms
unfolding finite_prefixes_def
by simp

lemma finite_prefixes_empty [simp]:
  shows "finite_prefixes {} x"
unfolding finite_prefixes_def
by simp

lemma finite_prefixes_union [simp]:
  shows "finite_prefixes (r \<union> r') s = (finite_prefixes r s \<and> finite_prefixes r' s)"
unfolding finite_prefixes_def
by auto

lemma finite_prefixes_relComp:
  assumes "finite_prefixes r s"
          "finite_prefixes r' s"
          "relOver r' s"
  shows "finite_prefixes (relcomp r r') s"
unfolding finite_prefixes_def 
proof (intro ballI)
  fix c
  assume "c \<in> s"
  let ?S = "\<Union>b\<in>{b. (b, c) \<in> r'}. {a. (a, b) \<in> r}"
  have subset: "{a. (a, c) \<in> relcomp r r'} = ?S"
    unfolding relcomp_def by auto
  have "finite {b. (b, c) \<in> r'}" 
    using assms `c \<in> s` unfolding finite_prefixes_def by auto
  hence "finite ?S"
    proof (rule finite_UN_I, clarify)
      fix b
      assume "(b, c) \<in> r'"
      hence "b \<in> s" using `relOver r' s` unfolding relOver_def by auto
      thus "finite {a. (a, b) \<in> r}" using assms unfolding finite_prefixes_def by simp
    qed
  thus "finite {a. (a, c) \<in> relcomp r r'}"
    using subset by metis
qed

lemma finite_prefix_subset:
  assumes "finite_prefixes r s"
      and "r' \<subseteq> r"
      and "s' \<subseteq> s"
  shows   "finite_prefixes r' s'"
unfolding finite_prefixes_def
proof
  fix b
  assume "b \<in> s'"
  hence "b \<in> s"
    using assms by auto
  hence "finite {a. (a, b) \<in> r}"
    using assms unfolding finite_prefixes_def by simp
  have "{a. (a, b) \<in> r'} \<subseteq> {a. (a, b) \<in> r}"
    using `r' \<subseteq> r` by auto
  thus "finite {a. (a, b) \<in> r'}"
    using `finite {a. (a, b) \<in> r}` by (metis rev_finite_subset)
qed

section {* Cmm: 2 - Type definitions and projections *}

subsubsection {* apply_tree *}

termination apply_tree by lexicographic_order

subsubsection {* empty_witness *}

lemma empty_witness_simps [simp]:
  shows "rf empty_witness = {}"
        "mo empty_witness = {}"
        "sc empty_witness = {}"
        "lo empty_witness = {}"
        "tot empty_witness = {}"
unfolding empty_witness_def
by simp_all

subsubsection {* behaviour *}

lemma behaviour_memory_model_eq [case_names Consistency Undef Sublanguage]:
  fixes m1 m2 opsem_t p cons1 rel1 cons2 rel2
  defines "cons1 \<equiv> apply_tree (consistent m1)"
      and "cons2 \<equiv> apply_tree (consistent m2)"
      and "undef1 \<equiv> each_empty (undefined0 m1)"
      and "undef2 \<equiv> each_empty (undefined0 m2)"
      and "rel1 \<equiv> relation_calculation m1"
      and "rel2 \<equiv> relation_calculation m2"
      and "consEx1 \<equiv> {(Xo, Xw, rl). opsem_t p Xo \<and> cons1 (Xo, Xw, rl) \<and> rl = rel1 Xo Xw}"
      and "consEx2 \<equiv> {(Xo, Xw, rl). opsem_t p Xo \<and> cons2 (Xo, Xw, rl) \<and> rl = rel2 Xo Xw}"
  assumes cons:    "\<And>pre wit. cons1 (pre, wit, rel1 pre wit) = cons2 (pre, wit, rel2 pre wit)"
      and undef:   "\<And>pre wit. undef1 (pre, wit, rel1 pre wit) = undef2 (pre, wit, rel2 pre wit)"
      and sublang: "c1 consEx1 = c2 consEx2"
  shows            "behaviour m1 c1 opsem_t p = behaviour m2 c2 opsem_t p"
proof -
  have consEx: "observable_filter consEx1 = observable_filter consEx2"
    using cons
    unfolding observable_filter_def
              consEx1_def consEx2_def
    by auto
  have undefEq: "  Ball consEx1 (each_empty (undefined0 m1))
                 = Ball consEx2 (each_empty (undefined0 m2))"
    using undef cons
    unfolding undef1_def undef2_def rel1_def rel2_def
              consEx1_def consEx2_def
    by auto
  thus ?thesis
    using consEx sublang
    unfolding behaviour_def Let_def
              cons1_def cons2_def 
              undef1_def undef2_def
              rel1_def rel2_def
              consEx1_def consEx2_def
    by simp
qed

subsubsection {* Simplifications for projection functions *}

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
declare is_alloc.simps [simp]
declare is_dealloc.simps [simp]
declare is_atomic_action.simps [simp]
declare is_read.simps [simp]
declare is_write.simps [simp]
declare is_acquire.simps [simp]
declare is_release.simps [simp]
declare is_consume.simps [simp]
declare is_seq_cst.simps [simp]

lemma value_read_byE [elim]:
  assumes "x = value_read_by a"
      and "is_read a"
  obtains v where "x = Some v"
using assms
by (cases a) auto

lemma value_written_byE [elim]:
  assumes "x = value_written_by a"
      and "is_write a"
  obtains v where "x = Some v"
using assms
by (cases a) auto

lemma is_RMWI [intro?]:
  assumes "is_read a"
          "is_write a"
  shows   "is_RMW a"
using assms 
by (cases a) auto

lemma is_RMWE [elim]:
  assumes "is_RMW a"
  obtains  "is_read a"
      and  "is_write a"
using assms by (cases a) auto

lemma is_readI [intro?]:
  assumes "is_load a"
  shows   "is_read a"
using assms by (cases a) auto

lemma is_RMWE_location_kind [elim?]:
  assumes "is_RMW a" "a \<in> actions0 pre"
      and "actions_respect_location_kinds (actions0 pre) (lk pre)"
  obtains "is_at_atomic_location (lk pre) a"
using assms
unfolding actions_respect_location_kinds_def
          is_at_atomic_location_def
by (cases a) auto

subsubsection {* threadwise *}

lemmas threadwiseI [intro?] = defToIntro[OF threadwise_def]

lemma threadwiseE [elim?]:
  assumes "threadwise s rel"
      and "(a, b) \<in> rel"
  obtains "tid_of a = tid_of b"
using assms
unfolding threadwise_def
by auto

lemma threadwise_empty [simp]:
  shows "threadwise s {}"
unfolding threadwise_def
by simp

subsubsection {* interthread *}

lemmas interthreadI [intro?] = defToIntro[OF interthread_def]

lemma interthreadE [elim?]:
  assumes "interthread s rel"
      and "(a, b) \<in> rel"
  obtains "tid_of a \<noteq> tid_of b"
using assms
unfolding interthread_def
by auto

lemma interthread_empty [simp]:
  shows "interthread s {}"
unfolding interthread_def
by simp

subsubsection {* locationwise *}

lemmas locationwiseI [intro?] = defToIntro[OF locationwise_def]

lemma locationwiseE [elim?]:
  assumes "locationwise s rel"
      and "(a, b) \<in> rel"
  obtains "loc_of a = loc_of b"
using assms
unfolding locationwise_def
by auto

lemma locationwise_empty [simp]:
  shows "locationwise s {}"
unfolding locationwise_def
by simp

subsubsection {* actions_respect_location_kinds *}

declare action_respects_location_kinds.simps [simp]

lemmas actions_respect_location_kindsI [intro?] = defToIntro[OF actions_respect_location_kinds_def]
lemmas actions_respect_location_kindsE [elim?] = defToElim[OF actions_respect_location_kinds_def]

lemma actions_respect_location_kinds_empty [simp]:
  shows "actions_respect_location_kinds {} p_lk"
unfolding actions_respect_location_kinds_def
by simp

subsubsection {* is_at_xxx_location *}

lemma same_loc_atomic_location:
  assumes "is_at_atomic_location lk1 a"
      and "loc_of a = loc_of b"
  obtains "is_at_atomic_location lk1 b"
using assms
unfolding is_at_atomic_location_def
by auto

lemma is_at_mutex_locationE [elim]:
  assumes "is_at_mutex_location lk1 a"
  obtains l where "loc_of a = Some l" "lk1 l = Mutex"
using assms
unfolding is_at_mutex_location_def
by (cases "loc_of a") auto

lemma is_at_non_atomic_locationE [elim]:
  assumes "is_at_non_atomic_location lk1 a"
  obtains l where "loc_of a = Some l" "lk1 l = Non_Atomic"
using assms
unfolding is_at_non_atomic_location_def
by (cases "loc_of a") auto

lemma is_at_atomic_locationE [elim]:
  assumes "is_at_atomic_location lk1 a"
  obtains l where "loc_of a = Some l" "lk1 l = Atomic"
using assms
unfolding is_at_atomic_location_def
by (cases "loc_of a") auto

lemma mutual_exclusive_location_mutex_non_atomic [elim]:
  assumes "is_at_mutex_location lk1 a"
      and "is_at_non_atomic_location lk1 a"
  shows "False"
using assms
by (elim is_at_mutex_locationE is_at_non_atomic_locationE) auto

lemma mutual_exclusive_location_non_atomic_atomic [elim]:
  assumes "is_at_non_atomic_location lk1 a"
      and "is_at_atomic_location lk1 a"
  shows "False"
using assms
by (elim is_at_non_atomic_locationE is_at_atomic_locationE) auto

lemma mutual_exclusive_location_atomic_mutex [elim]:
  assumes "is_at_atomic_location lk1 a"
      and "is_at_mutex_location lk1 a"
  shows "False"
using assms
by (elim is_at_atomic_locationE is_at_mutex_locationE) auto

declare well_formed_action.simps [simp]

subsubsection {* assumptions *}

lemma assumptionsI [intro?]:
  assumes "finite_prefixes (rf wit) (actions0 pre)"
          "finite_prefixes (mo wit) (actions0 pre)"
          "finite_prefixes (sc wit) (actions0 pre)"
          "finite_prefixes (lo wit) (actions0 pre)"
  shows   "assumptions (pre, wit, rel)"
using assms
unfolding assumptions.simps
by simp

lemma assumptionsE [elim]:
  assumes "assumptions (pre, wit, rel)"
  obtains "finite_prefixes (rf wit) (actions0 pre)"  
      and "finite_prefixes (mo wit) (actions0 pre)"  
      and "finite_prefixes (sc wit) (actions0 pre)"  
      and "finite_prefixes (lo wit) (actions0 pre)"
using assms
unfolding assumptions.simps
by auto

lemma rel_list_assumptions [simp]:
  assumes "rel \<noteq> []"
  shows   "assumptions (pre, wit, rel) = assumptions (pre, wit,[])"
unfolding assumptions.simps ..

subsubsection {* blocking_observed *}

lemma blocking_observed_empty [simp]:
  shows "blocking_observed {} r"
        "blocking_observed s {}"
unfolding blocking_observed_def
by simp_all

subsubsection {* indeterminate_sequencing *}

lemmas indeterminate_sequencingI [intro?] = defToIntro[OF indeterminate_sequencing_def]

lemma indeterminate_sequencingE [elim?]:
  assumes "indeterminate_sequencing pre"
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "tid_of a = tid_of b"
      and "a \<noteq> b"
      and " \<not>(is_at_non_atomic_location (lk pre) a \<and> is_at_non_atomic_location (lk pre) b)"
  obtains "(a, b) \<in> sb pre"
        | "(b, a) \<in> sb pre"
using assms
unfolding indeterminate_sequencing_def
by auto

subsubsection {* disjoint_allocs *}

lemma disjoint_allocs_empty [simp]:
  shows "disjoint_allocs {}"
unfolding disjoint_allocs_def
by simp

subsubsection {* well_formed_threads *}

lemma well_formed_threadsI [intro?]:
  assumes "actions_respect_location_kinds (actions0 pre) (lk pre)"  
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
      and "\<And>a. a \<in> actions0 pre \<Longrightarrow> well_formed_action a"
  shows   "well_formed_threads (pre, wit, rel)"
using assms
unfolding well_formed_threads.simps
by auto

lemma  well_formed_threadsE [elim]:
  assumes "well_formed_threads (pre, wit, rel)"
  obtains "actions_respect_location_kinds (actions0 pre) (lk pre)"  
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
unfolding well_formed_threads.simps
by simp

lemma  well_formed_threadsE_well_formed_action [elim]:
  assumes "well_formed_threads (pre, wit, rel)"
      and "a \<in> actions0 pre"
  obtains "well_formed_action a"
using assms
unfolding well_formed_threads.simps
by simp

lemma rel_list_well_formed_threads [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_threads (pre, wit, rel) = well_formed_threads (pre, wit, [])"
unfolding well_formed_threads.simps ..

lemma witness_well_formed_threads [simp]:
  assumes "wit \<noteq> empty_witness"
  shows   "well_formed_threads (pre, wit, []) = well_formed_threads (pre, empty_witness, [])"
unfolding well_formed_threads.simps ..

subsubsection {* downclosed *}

lemmas downclosedI [intro?] = defToIntro[OF downclosed_def]

lemma downclosedE [elim?]:
  assumes "downclosed A R"
      and "(a, b) \<in> R"
      and "b \<in> A"
  obtains "a \<in> A"
using assms
unfolding downclosed_def
by simp

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
  assume as: "\<forall>p. (\<exists>q. q \<in> a \<and> (p, q) \<in> x) \<longrightarrow> p \<in> a"
     and     "q \<in> a" "(p, q) \<in> x\<^sup>+"
  show "p \<in> a"
    using `(p, q) \<in> x\<^sup>+` `q \<in> a` 
    proof induct
      fix y
      assume "(p, y) \<in> x" "y \<in> a"
      thus "p \<in> a" using as by auto
    next
      fix y z
      assume "(y, z) \<in> x" "y \<in> a \<Longrightarrow> p \<in> a" "z \<in> a"
      thus "p \<in> a" using as by auto
    qed
qed

lemma downclosed_relOver:
  assumes "relOver r a"
  shows   "downclosed a r"
using assms
unfolding relOver_def downclosed_def by auto

lemma downclosed_subset:
  assumes "r \<subseteq> r'"
          "downclosed a r'"
  shows   "downclosed a r"
using assms
unfolding downclosed_def
by auto

section {* Cmm: 3 - Single thread, no atomics *}

subsubsection {* visible_side_effect_set *}

lemmas visible_side_effect_setI [intro?] = relToIntro[OF visible_side_effect_set_def]

lemma visible_side_effect_setE1 [elim]:
  assumes "(a, b) \<in> visible_side_effect_set actions hb"
  obtains "(a, b) \<in> hb" 
      and "is_write a" 
      and "is_read b" 
      and "loc_of a = loc_of b"
using assms
unfolding visible_side_effect_set_def
by auto

lemma visible_side_effect_setE2 [elim?]:
  assumes "(a, b) \<in> visible_side_effect_set actions hb"
      and "c \<in> actions" 
          "c \<noteq> a" 
          "c \<noteq> b" 
          "is_write c" 
          "loc_of c = loc_of b"
          "(a, c) \<in> hb"
          "(c, b) \<in> hb"
  obtains "False"
using assms
unfolding visible_side_effect_set_def
by auto

lemma visible_side_effect_set_empty [simp]:
  shows "visible_side_effect_set s {} = {}"
unfolding visible_side_effect_set_def
by simp

lemma exists_vse_hb:
  assumes cons:  "consistent_hb (pre, wit, (''hb'', hb)#rel)"
      and r:     "r \<in> actions0 pre" "is_read r"
  shows   "  (\<exists>w\<in>actions0 pre. (w, r) \<in> visible_side_effect_set (actions0 pre) hb)
           = (\<exists>w\<in>actions0 pre. (w, r) \<in> hb \<and> is_write w \<and> loc_of w = loc_of r)" 
proof auto
  let ?S = "{w | w. w \<in> actions0 pre \<and> (w, r) \<in> hb \<and> is_write w \<and> loc_of w = loc_of r}"
  fix w
  assume w: "w \<in> actions0 pre" "(w, r) \<in> hb" "is_write w" "loc_of w = loc_of r"
  hence ne: "?S \<noteq> {}" by auto
  have finite: "finite ?S"
    using cons r
    unfolding consistent_hb.simps finite_prefixes_def
    by auto
  have acyclic: "acyclic hb"
    using cons
    unfolding acyclic_def consistent_hb.simps irrefl_def
    by auto
  obtain v where v: "v \<in> ?S" "\<forall>y. y \<in> ?S \<longrightarrow> (v, y) \<notin> hb"
    using supremum[OF finite ne acyclic] by auto
  hence "(v, r) \<in> visible_side_effect_set (actions0 pre) hb"
    unfolding visible_side_effect_set_def
    using r
    by auto
  thus "\<exists>w\<in>actions0 pre. (w, r) \<in> visible_side_effect_set (actions0 pre) hb"
    using v by auto
qed

subsubsection {* det_read *}

lemma det_readI [intro?]:
  assumes "\<And>r.    r \<in> actions0 pre
               \<Longrightarrow> is_load r 
               \<Longrightarrow>   (\<exists>w \<in>actions0 pre. (w,  r) \<in> vse) 
                   = (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit)"
  shows "det_read (pre, wit, (''hb'', hb)#(''vse'', vse)#rel)"
using assms
unfolding det_read.simps
by auto
  
lemma det_readE_vse [elim]:
  assumes "det_read (pre, wit, (''hb'', hb)#(''vse'', vse)#rel)"
      and "r \<in> actions0 pre"
      and "is_load r"
      and "w \<in> actions0 pre"
      and "(w, r) \<in> vse"
  obtains w' where "w' \<in> actions0 pre" "(w', r) \<in> rf wit"
using assms
unfolding det_read.simps
by auto

lemma det_readE_rf [elim]:
  assumes "det_read (pre, wit, (''hb'', hb)#(''vse'', vse)#rel)"
      and "r \<in> actions0 pre"
      and "is_load r"
      and "w \<in> actions0 pre"
      and "(w, r) \<in> rf wit"
  obtains w' where "w' \<in> actions0 pre" "(w', r) \<in> vse"
using assms
unfolding det_read.simps
by auto

lemma rel_list_det_read [simp]:
  assumes "rel \<noteq> []"
  shows   "  det_read (pre, wit, (''hb'', hb)#(''vse'', vse)#rel) 
           = det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])"     
unfolding det_read.simps ..

subsubsection {* det_read_alt *}

lemma det_read_altI [intro?]:
  assumes "\<And>r.    r \<in> actions0 pre
               \<Longrightarrow> is_load r 
               \<Longrightarrow>   (\<exists>w \<in>actions0 pre. (w, r) \<in> hb \<and> is_write w \<and> loc_of w = loc_of r) 
                   = (\<exists>w'\<in>actions0 pre. (w', r) \<in> rf wit)"
  shows "det_read_alt (pre, wit, (''hb'', hb)#rel)"
using assms
unfolding det_read_alt.simps
by auto
  
lemma det_read_altE_vse [elim]:
  assumes "det_read_alt (pre, wit, (''hb'', hb)#rel)"
      and "r \<in> actions0 pre"
      and "is_load r"
      and "w \<in> actions0 pre"
      and "(w, r) \<in> hb"
      and "is_write w"
      and "loc_of w = loc_of r"
  obtains w' where "w' \<in> actions0 pre" 
               and "(w', r) \<in> rf wit"
using assms
unfolding det_read_alt.simps
by auto

lemma det_read_altE_rf [elim]:
  assumes "det_read_alt (pre, wit, (''hb'', hb)#rel)"
      and "r \<in> actions0 pre"
      and "is_load r"
      and "w \<in> actions0 pre"
      and "(w, r) \<in> rf wit"
  obtains w' where "w' \<in> actions0 pre" 
               and "(w', r) \<in> hb"
               and "is_write w'"
               and "loc_of w' = loc_of r"
using assms
unfolding det_read_alt.simps
by auto

lemma rel_list_det_read_alt [simp]:
  assumes "rel \<noteq> []"
  shows   "  det_read_alt (pre, wit, (''hb'', hb)#rel) 
           = det_read_alt (pre, wit, [(''hb'', hb)])"     
unfolding det_read_alt.simps ..

lemma det_read_simp:
  fixes pre wit hb rel
  defines         "vse \<equiv> visible_side_effect_set (actions0 pre) hb"
  assumes conshb: "consistent_hb (pre, wit, [(''hb'', hb)])"
  shows   "  det_read (pre, wit, [(''hb'', hb),(''vse'', vse)])
           = det_read_alt (pre, wit, [(''hb'', hb)])"
proof -
  have "\<And>r.    r \<in> actions0 pre
            \<Longrightarrow> is_load r
            \<Longrightarrow>   (\<exists>w\<in>actions0 pre. (w, r) \<in> visible_side_effect_set (actions0 pre) hb) 
                = (\<exists>w\<in>actions0 pre. (w, r) \<in> hb \<and> is_write w \<and> loc_of w = loc_of r)"
    using exists_vse_hb[OF conshb] is_readI
    by auto
  thus ?thesis
    unfolding det_read.simps det_read_alt.simps vse_def
    by auto
qed

subsubsection {* consistent_non_atomic_rf *}

lemmas consistent_non_atomic_rfI [intro?] = defToIntro[OF consistent_non_atomic_rf.simps(3)]

lemma consistent_non_atomic_rfE [elim]:
  assumes "consistent_non_atomic_rf (pre, wit, (''hb'', hb)#(''vse'', vse)#rel)"
      and "(a, b) \<in> rf wit"
      and "is_at_non_atomic_location (lk pre) b"
  obtains "(a, b) \<in> vse"
using assms
unfolding consistent_non_atomic_rf.simps
by auto

lemma rel_list_consistent_non_atomic_rf [simp]:
  assumes "rel \<noteq> []"
  shows    "  consistent_non_atomic_rf (pre, wit, (''hb'', hb)#(''vse'', vse)#rel)  
            = consistent_non_atomic_rf (pre, wit, [(''hb'', hb),(''vse'', vse)])"    
unfolding consistent_non_atomic_rf.simps ..

subsubsection {* well_formed_rf *}

lemma well_formed_rfI [intro?]:
  assumes "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> a \<in> actions0 pre"
      and "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> b \<in> actions0 pre"
      and "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> loc_of a = loc_of b"
      and "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> is_write a"
      and "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> is_read b "
      and "\<And>a b. (a, b) \<in> rf wit \<Longrightarrow> value_read_by b = value_written_by a"
      and "\<And>a a' b. (a, b) \<in> rf wit \<Longrightarrow> (a', b) \<in> rf wit \<Longrightarrow> a = a'"
  shows "well_formed_rf (pre, wit, rel)"
using assms
unfolding well_formed_rf.simps 
by auto

lemma well_formed_rfE [elim]:
  assumes "well_formed_rf (pre, wit, rel)"
      and "(a, b) \<in> rf wit"
  obtains "a \<in> actions0 pre"
          "b \<in> actions0 pre" 
          "loc_of a = loc_of b" 
          "is_write a"
          "is_read b"
          "value_read_by b = value_written_by a" 
using assms
unfolding well_formed_rf.simps 
by auto

lemma well_formed_rfE2 [elim]:
  assumes "well_formed_rf (pre, wit, rel)"
      and "(a, c) \<in> rf wit"
      and "(b, c) \<in> rf wit"
  obtains "a = b"
proof -
  have "a \<in> actions0 pre" "b \<in> actions0 pre"
    using assms by auto
  hence "a = b"
    using assms
    unfolding well_formed_rf.simps 
    by auto
  thus ?thesis using that by simp
qed

lemma rel_list_well_formed_rf [simp]:
  assumes "rel \<noteq> []"
  shows   "well_formed_rf (pre, wit, rel) = well_formed_rf (pre, wit, [])"
unfolding well_formed_rf.simps ..

subsubsection {* tot_empty *}

lemmas tot_emptyI [intro?] = defToIntro[OF tot_empty.simps]
lemmas tot_emptyE [elim] = defToElim[OF tot_empty.simps]

lemma rel_list_tot_empty [simp]:
  assumes "rel \<noteq> []"
  shows   "tot_empty (pre, wit, rel) = tot_empty (pre, wit,[])"
unfolding tot_empty.simps ..

section {* Cmm: 4 - Locks, multi-thread, no atomics *}

subsubsection {* locks_only_relations *}

lemma locks_only_relations_simp:
  shows "locks_only_relations = locks_only_relations_alt"
apply (rule ext)+
unfolding locks_only_relations_def 
          locks_only_relations_alt_def
          Let_def
unfolding locks_only_hb_def
          locks_only_vse_def
          locks_only_sw_set_alt_def
by auto

lemma locks_only_relations_non_empty [simp]:
  shows "locks_only_relations pre wit \<noteq> []"
unfolding locks_only_relations_def Let_def by simp

subsubsection {* locks_only_consistent_lo *}

lemmas locks_only_consistent_loI [intro?] = defToIntro[OF locks_only_consistent_lo.simps(2)]

lemma locks_only_consistent_loE1 [elim]:
  assumes "locks_only_consistent_lo (pre, wit, (''hb'', hb)#rel)"
  obtains "relOver (lo wit) (actions0 pre)"
          "trans (lo wit)"
          "irrefl (lo wit)"
using assms
unfolding locks_only_consistent_lo.simps
by auto

(* Original elim. *)
(*
lemma locks_only_consistent_loE2 [elim]:
  assumes "locks_only_consistent_lo (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> lo wit" 
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
  obtains "(b, a) \<notin> hb"
      and "a \<noteq> b"
      and "loc_of a = loc_of b" 
      and "is_lock a \<or> is_unlock a"
      and "is_lock b \<or> is_unlock b"
      and "is_at_mutex_location (lk pre) a"
      and "is_at_mutex_location (lk pre) b" 
using assms
unfolding locks_only_consistent_lo.simps
(* TODO: auto doesn't work here if both irreflE and transE are added to the elim-set. *)
by auto
*)

lemma locks_only_consistent_loE2 [elim]:
  assumes "locks_only_consistent_lo (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> lo wit" 
  obtains "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "a \<noteq> b"
      and "loc_of a = loc_of b" 
      and "is_lock a \<or> is_unlock a"
      and "is_lock b \<or> is_unlock b"
      and "is_at_mutex_location (lk pre) a"
      and "is_at_mutex_location (lk pre) b" 
      and "(b, a) \<notin> hb"
      and "(b, a) \<notin> lo wit"
proof -
  have "(b, a) \<notin> lo wit"
    using assms
    by (auto elim: irreflTransE)
  moreover have "a \<in> actions0 pre" "b \<in> actions0 pre"
    using assms
    by (auto elim: relOverE)
  ultimately show ?thesis
    using assms that
    unfolding locks_only_consistent_lo.simps
    by auto
qed

lemma locks_only_consistent_loE2_inv [elim]:
  assumes "locks_only_consistent_lo (pre, wit, (''hb'', hb)#rel)"
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "a \<noteq> b"
      and "loc_of a = loc_of b" 
      and "is_lock a \<or> is_unlock a"
      and "is_lock b \<or> is_unlock b"
      and "is_at_mutex_location (lk pre) a"
      and "(b, a) \<notin> lo wit"
  obtains "(a, b) \<in> lo wit" 
proof -
  show ?thesis
    using assms that
    unfolding locks_only_consistent_lo.simps
    by auto
qed

lemma rel_list_locks_only_consistent_lo [simp]:
  assumes "rel \<noteq> []"
  shows   "  locks_only_consistent_lo (pre, wit, (''hb'', hb)#rel) 
           = locks_only_consistent_lo (pre, wit, [(''hb'', hb)])"
unfolding locks_only_consistent_lo.simps ..

subsubsection {* locks_only_consistent_locks *}

lemmas locks_only_consistent_locksI [intro?] = defToIntro[OF locks_only_consistent_locks.simps]

lemma locks_only_consistent_locksE [elim]:
  assumes "locks_only_consistent_locks (pre, wit, rel)"
      and "(a, c) \<in> lo wit"
      and "is_successful_lock a"
      and "is_successful_lock c"
  obtains b where "b \<in> actions0 pre" 
              and "is_unlock b" 
              and "(a, b) \<in> lo wit" 
              and "(b, c) \<in> lo wit"
using assms
unfolding locks_only_consistent_locks.simps
by auto

lemma rel_list_locks_only_consistent_locks [simp]:
  assumes "rel \<noteq> []"
  shows   "locks_only_consistent_locks (pre, wit, rel) = locks_only_consistent_locks (pre, wit, [])"
unfolding locks_only_consistent_locks.simps ..

subsubsection {* consistent_hb *}

lemmas consistent_hbI [intro?] = defToIntro[OF consistent_hb.simps(2)]

lemma consistent_hbE [elim]:
  assumes "consistent_hb (pre, wit, (''hb'', hb)#rel)"
  obtains "irrefl (trancl hb)"
      and "finite_prefixes hb (actions0 pre)"
using assms
unfolding consistent_hb.simps
by auto

(* We don't add irreflE and transE to the elim-set (see notes08-2015-05-12) so we give an extra elim
for the consistency predicate that unfolds them. *)

lemma consistent_hbE2 [elim]:
  assumes "consistent_hb (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> hb"
  obtains "(b, a) \<notin> hb"
using assms
unfolding consistent_hb.simps 
by (auto elim: irreflTranclE)

lemma rel_list_consistent_hb [simp]:
  assumes "rel \<noteq> []"
  shows    "  consistent_hb (pre, wit, (''hb'', hb)#rel) 
            = consistent_hb (pre, wit, [(''hb'', hb)])"      
unfolding consistent_hb.simps ..

subsubsection {* locks_only_undefined_behaviour *}

lemma locks_only_undefined_behaviour_simp:
  shows "  (locks_only_undefined_behaviour_alt ex = []) 
         = (each_empty locks_only_undefined_behaviour ex)"
unfolding locks_only_undefined_behaviour_alt_def
          locks_only_undefined_behaviour_def
          each_empty_def
          Let_def
by simp

section {* Cmm: 5 - relaxed - no sc, consumes, release or acquire *}

subsubsection {* consistent_atomic_rf *}

lemmas consistent_atomic_rfI [intro?] = defToIntro[OF consistent_atomic_rf.simps(2)]

lemma consistent_atomic_rfE [elim]:
  assumes "consistent_atomic_rf (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> rf wit"
      and "is_load b"
      and "is_at_atomic_location (lk pre) b"
  obtains "(b, a) \<notin> hb"
using assms
unfolding consistent_atomic_rf.simps
by auto

lemma rel_list_consistent_atomic_rf [simp]:
  assumes "rel \<noteq> []"
  shows   "  consistent_atomic_rf (pre, wit, (''hb'', hb)#rel)
           = consistent_atomic_rf (pre, wit, [(''hb'', hb)])"      
unfolding consistent_atomic_rf.simps ..

subsubsection {* rmw_atomicity *}

lemma rmw_atomicityI [intro?]:
  assumes "\<And>a b.    a \<in> actions0 pre
                 \<Longrightarrow> b \<in> actions0 pre
                 \<Longrightarrow> is_RMW b
                 \<Longrightarrow>   adjacent_less_than (mo wit) (actions0 pre) a b
                     = ((a, b) \<in> rf wit)"
  shows "rmw_atomicity (pre, wit, rel)"
using assms
unfolding rmw_atomicity.simps
by auto

lemma rmw_atomicityE1 [elim]:
  assumes "rmw_atomicity (pre, wit, rel)"
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "is_RMW b"
      and "adjacent_less_than (mo wit) (actions0 pre) a b"
  obtains "(a, b) \<in> rf wit"
using assms
unfolding rmw_atomicity.simps
by auto

lemma rmw_atomicityE2 [elim]:
  assumes "rmw_atomicity (pre, wit, rel)"
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "is_RMW b"
      and "(a, b) \<in> rf wit"
  obtains "adjacent_less_than (mo wit) (actions0 pre) a b"
using assms
unfolding rmw_atomicity.simps
by auto

lemma rel_list_rmw_atomicity [simp]:
  assumes "rel \<noteq> []"
  shows   "rmw_atomicity (pre, wit, rel) = rmw_atomicity (pre, wit, [])"     
unfolding rmw_atomicity.simps ..

subsubsection {* coherent_memory_use *}

lemmas coherent_memory_useI [intro?] = defToIntro[OF coherent_memory_use.simps(2)]

lemma coherent_memory_useE_CoRR [elim]:
  assumes "coherent_memory_use (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> rf wit"
      and "(c, d) \<in> rf wit"
      and "(b, d) \<in> hb"
      and "(c, a) \<in> mo wit"
  obtains False
using assms
unfolding coherent_memory_use.simps
by auto

lemma coherent_memory_useE_CoWR [elim]:
  assumes "coherent_memory_use (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> rf wit"
      and "c \<in> actions0 pre"
      and "(c, b) \<in> hb"
      and "(a, c) \<in> mo wit"
  obtains False
using assms
unfolding coherent_memory_use.simps
by auto

lemma coherent_memory_useE_CoRW [elim]:
  assumes "coherent_memory_use (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> rf wit"
      and "c \<in> actions0 pre"
      and "(b, c) \<in> hb"
      and "(c, a) \<in> mo wit"
  obtains False
using assms
unfolding coherent_memory_use.simps
by auto

lemma coherent_memory_useE_CoWW [elim]:
  assumes "coherent_memory_use (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> hb"
      and "(b, a) \<in> mo wit"
  obtains False
using assms
unfolding coherent_memory_use.simps
by auto

lemma rel_list_coherent_memory_use [simp]:
  assumes "rel \<noteq> []"
  shows   "coherent_memory_use (pre, wit, (''hb'', hb)#rel) = 
             coherent_memory_use (pre, wit, [(''hb'', hb)])"      
unfolding coherent_memory_use.simps ..

subsubsection {* consistent_mo *}

definition sameLocAtWrites :: "pre_execution \<Rightarrow> action \<Rightarrow> action \<Rightarrow> bool" where
  "sameLocAtWrites pre a b \<equiv>   a \<in> actions0 pre
                              \<and> b \<in> actions0 pre
                              \<and> a \<noteq> b
                              \<and> loc_of a = loc_of b
                              \<and> is_write a
                              \<and> is_write b
                              \<and> (   is_at_atomic_location (lk pre) a 
                                  \<or> is_at_atomic_location (lk pre) b)"

lemma consistent_moI [intro?]:
  assumes at_writes: "\<And>a b. (a, b) \<in> mo wit \<Longrightarrow> sameLocAtWrites pre a b"
      and trans:     "\<And>a b c.    (a, b) \<in> mo wit
                              \<Longrightarrow> (b, c) \<in> mo wit
                              \<Longrightarrow> (a, c) \<in> mo wit"
      and in_mo:     "\<And>a b.    a \<in> actions0 pre
                            \<Longrightarrow> b \<in> actions0 pre
                            \<Longrightarrow> a \<noteq> b
                            \<Longrightarrow> loc_of a = loc_of b
                            \<Longrightarrow> is_write a
                            \<Longrightarrow> is_write b
                            \<Longrightarrow> is_at_atomic_location (lk pre) a
                            \<Longrightarrow> is_at_atomic_location (lk pre) b
                            \<Longrightarrow> ((a, b) \<in> mo wit \<or> (b, a) \<in> mo wit)"
  shows "consistent_mo (pre, wit, rel)"
proof -
  have at_loc2: "\<And>a b.     (a, b) \<in> mo wit
                        \<Longrightarrow>   is_at_atomic_location (lk pre) b
                            \<and> is_at_atomic_location (lk pre) a"
    using at_writes same_loc_atomic_location
    unfolding sameLocAtWrites_def
    by metis
  have "relOver (mo wit) (actions0 pre)"
    using at_writes unfolding sameLocAtWrites_def relOver_def by auto
  moreover have "trans (mo wit)"
    using trans unfolding trans_def by metis
  moreover have "irrefl (mo wit)"
    using at_writes unfolding sameLocAtWrites_def irrefl_def by auto
  moreover have "\<forall>a\<in>actions0 pre. \<forall>b\<in>actions0 pre. 
                      ((a, b) \<in> mo wit \<or> (b, a) \<in> mo wit) 
                    = (   a \<noteq> b \<and> is_write a \<and> is_write b 
                        \<and> loc_of a = loc_of b 
                        \<and> is_at_atomic_location (lk pre) a)"
    using at_writes at_loc2 in_mo same_loc_atomic_location
    unfolding sameLocAtWrites_def 
    by auto blast
  ultimately show ?thesis
    unfolding consistent_mo.simps
    by simp
qed

lemma consistent_moE_rel [elim]:
  assumes "consistent_mo (pre, wit, rel)"
  obtains "relOver (mo wit) (actions0 pre)"
          "trans (mo wit)"
          "irrefl (mo wit)"
using assms
unfolding consistent_mo.simps
by auto

(* Original elim *)
(*
lemma consistent_moE_mem [elim]:
  assumes "consistent_mo (pre, wit, rel)"
      and "(a, b) \<in> mo wit"
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
  obtains "a \<noteq> b"
          "loc_of a = loc_of b"
          "is_write a"
          "is_write b"
          "is_at_atomic_location (lk pre) a"
          "is_at_atomic_location (lk pre) b"
using assms
unfolding consistent_mo.simps
by auto
*)

lemma consistent_moE_mem [elim]:
  assumes "consistent_mo (pre, wit, rel)"
      and "(a, b) \<in> mo wit"
  obtains "a \<in> actions0 pre" 
      and "b \<in> actions0 pre"
      and "a \<noteq> b"
      and "loc_of a = loc_of b"
      and "is_write a"
      and "is_write b"
      and "is_at_atomic_location (lk pre) a"
      and "is_at_atomic_location (lk pre) b"
      and "(b, a) \<notin> mo wit" 
proof -
  have "(b, a) \<notin> mo wit"
    using assms
    by (auto elim: irreflTransE)
  moreover have "a \<in> actions0 pre" "b \<in> actions0 pre"
    using assms
    by (auto elim: relOverE)
  ultimately show ?thesis
    using assms that
    unfolding consistent_mo.simps
    by auto
qed

lemma consistent_moE_inv:
  assumes "consistent_mo (pre, wit, rel)"
      and "a \<in> actions0 pre" 
      and "b \<in> actions0 pre"
      and "a \<noteq> b"
      and "loc_of a = loc_of b"
      and "is_write a"
      and "is_write b"
      and "is_at_atomic_location (lk pre) a \<or> is_at_atomic_location (lk pre) b"
      and "(b, a) \<notin> mo wit"
  obtains "(a, b) \<in> mo wit"
proof -
  have "is_at_atomic_location (lk pre) a" 
    using assms same_loc_atomic_location by metis
  thus ?thesis
    using assms that
    unfolding consistent_mo.simps
    by auto
qed

lemma rel_list_consistent_mo [simp]:
  assumes "rel \<noteq> []"
  shows   "consistent_mo (pre, wit, rel) = consistent_mo (pre, wit, [])"
unfolding consistent_mo.simps ..

section {* Cmm: 6 - release, acquire; no sc, consume or relaxed *}

subsubsection {* sw_asw *}

lemmas sw_aswI = relToIntro[OF sw_asw_def]

lemma sw_aswE [elim]:
  assumes "(a, b) \<in> sw_asw pre"
  obtains "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "tid_of a \<noteq> tid_of b"
      and "(a, b) \<in> asw pre"
using assms
unfolding sw_asw_def
by simp

subsubsection {* sw_lock *}

lemmas sw_lockI = relToIntro[OF sw_lock_def]

lemma sw_lockE [elim]:
  assumes "(a, b) \<in> sw_lock pre wit"
  obtains "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "tid_of a \<noteq> tid_of b"
      and "is_unlock a"
      and "is_lock b "
      and "(a, b) \<in> lo wit"
using assms
unfolding sw_lock_def
by simp

subsubsection {* sw_rel_acq *}

lemmas sw_rel_acqI = relToIntro[OF sw_rel_acq_def]

lemma sw_rel_acqE [elim]:
  assumes "(a, b) \<in> sw_rel_acq pre wit"
  obtains "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "tid_of a \<noteq> tid_of b"
      and "is_release a"
      and "is_acquire b"
      and "(a, b) \<in> rf wit"
using assms
unfolding sw_rel_acq_def
by simp

subsubsection {* release_acquire_synchronizes_with_set *}

(* This is an unsafe elim, since the extra assumptions might not be provable when the conclusion is
provable. *)
lemma release_acquire_swIE:
  assumes "(a, b) \<in> release_acquire_synchronizes_with_set_alt pre wit"
      and "(a, b) \<in> sw_asw pre \<Longrightarrow> (a, b) \<in> sw_asw pre2"
      and "(a, b) \<in> sw_lock pre wit \<Longrightarrow> (a, b) \<in> sw_lock pre2 wit2"
      and "(a, b) \<in> sw_rel_acq pre wit \<Longrightarrow> (a, b) \<in> sw_rel_acq pre2 wit2"
  shows   "(a, b) \<in> release_acquire_synchronizes_with_set_alt pre2 wit2"
using assms
unfolding release_acquire_synchronizes_with_set_alt_def
by auto

lemma release_acquire_sw_simp:
  shows "  release_acquire_synchronizes_with_set (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit)
         = release_acquire_synchronizes_with_set_alt pre wit"
unfolding release_acquire_synchronizes_with_set_def
          release_acquire_synchronizes_with_set_alt_def
          sw_asw_def
          sw_lock_def
          sw_rel_acq_def
by (auto simp add: release_acquire_synchronizes_with_def)

subsubsection {* release_acquire_relations *}

lemma release_acquire_relations_simp:
  shows "release_acquire_relations = release_acquire_relations_alt"
apply (rule ext)+
unfolding release_acquire_relations_def 
          release_acquire_relations_alt_def
          Let_def
unfolding release_acquire_hb_def
          release_acquire_vse_def
using release_acquire_sw_simp
by auto

lemma release_acquire_relations_non_empty [simp]:
  shows "release_acquire_relations pre wit \<noteq> []"
unfolding release_acquire_relations_def Let_def by simp

section {* Cmm: 7 - release, acquire, relaxed; no sc or consume *}

subsubsection {* sw_rel_acq_rs *}

lemmas sw_rel_acq_rsI = relToIntro[OF sw_rel_acq_rs_def]

lemma sw_rel_acq_rsE [elim]:
  assumes "(a, b) \<in> sw_rel_acq_rs pre wit"
  obtains c 
    where "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "c \<in> actions0 pre"
      and "tid_of a \<noteq> tid_of b"
      and "is_release a"
      and "is_acquire b"
      and "(a, c) \<in> release_sequence_set_alt pre wit"
      and "(c, b) \<in> rf wit"
using assms
unfolding sw_rel_acq_rs_def
by auto

lemma sw_rel_acq_rsIE [consumes 1, case_names rel_acq_rs]:
  assumes "(a, b) \<in> sw_rel_acq_rs pre wit"
      and " \<And>c.     a \<in> actions0 pre 
                 \<Longrightarrow> b \<in> actions0 pre 
                 \<Longrightarrow> tid_of a \<noteq> tid_of b 
                 \<Longrightarrow> is_release a 
                 \<Longrightarrow> is_acquire b 
                 \<Longrightarrow> c \<in> actions0 pre 
                 \<Longrightarrow> (a, c) \<in> release_sequence_set_alt pre wit
                 \<Longrightarrow> (c, b) \<in> rf wit
                 \<Longrightarrow>   a \<in> actions0 pre2 
                     \<and> b \<in> actions0 pre2 
                     \<and> c \<in> actions0 pre2 
                     \<and> (a, c) \<in> release_sequence_set_alt pre2 wit2
                     \<and> (c, b) \<in> rf wit2"
  shows   "(a, b) \<in> sw_rel_acq_rs pre2 wit2"
using assms
unfolding sw_rel_acq_rs_def
by auto

subsubsection {* release_acquire_relaxed_synchronizes_with_set *}

(* This is an unsafe elim, since the extra assumptions might not be provable when the conclusion is
provable. *)
lemma release_acquire_relaxed_swIE [consumes, case_names asw lock rel_acq_rs]:
  assumes "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt pre wit"
      and "(a, b) \<in> sw_asw pre \<Longrightarrow> (a, b) \<in> sw_asw pre2"
      and "(a, b) \<in> sw_lock pre wit \<Longrightarrow> (a, b) \<in> sw_lock pre2 wit2"
      and "(a, b) \<in> sw_rel_acq_rs pre wit \<Longrightarrow> (a, b) \<in> sw_rel_acq_rs pre2 wit2"
  shows   "(a, b) \<in> release_acquire_relaxed_synchronizes_with_set_alt pre2 wit2"
using assms
unfolding release_acquire_relaxed_synchronizes_with_set_alt_def
by auto

lemma release_acquire_relaxed_sw_simp:
  shows "release_acquire_relaxed_synchronizes_with_set 
           (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit) 
           (release_sequence_set (actions0 pre) (lk pre) (mo wit)) =
         release_acquire_relaxed_synchronizes_with_set_alt pre wit"
unfolding release_acquire_relaxed_synchronizes_with_set_def
          release_acquire_relaxed_synchronizes_with_set_alt_def
          sw_asw_def
          sw_lock_def
          sw_rel_acq_def
          sw_rel_acq_rs_def
          release_sequence_set_alt_def
by (auto simp add: release_acquire_relaxed_synchronizes_with_def)  

subsubsection {* release_acquire_relaxed_relations *}

lemma release_acquire_relaxed_relations_simp:
  shows "release_acquire_relaxed_relations = release_acquire_relaxed_relations_alt"
apply (rule ext)+
unfolding release_acquire_relaxed_relations_def 
          release_acquire_relaxed_relations_alt_def
          Let_def
unfolding release_acquire_relaxed_hb_def
          release_acquire_relaxed_vse_def
          release_sequence_set_alt_def
using release_acquire_relaxed_sw_simp
by auto

lemma release_acquire_relaxed_relations_non_empty [simp]:
  shows "release_acquire_relaxed_relations pre wit \<noteq> []"
unfolding release_acquire_relaxed_relations_def Let_def by simp

section {* Cmm: 8 - release, acquire, fenced; no sc or consume *}

subsubsection {* sw_fence_sb_hrs_rf_sb *}

lemma sw_fence_sb_hrs_rf_sbIE [consumes 1, case_names fence]:
  assumes "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit"
      and "\<And>x y z.     a \<in> actions0 pre
                    \<Longrightarrow> b \<in> actions0 pre
                    \<Longrightarrow> tid_of a \<noteq> tid_of b
                    \<Longrightarrow> is_fence a
                    \<Longrightarrow> is_release a
                    \<Longrightarrow> is_fence b
                    \<Longrightarrow> is_acquire b
                    \<Longrightarrow> x \<in> actions0 pre
                    \<Longrightarrow> y \<in> actions0 pre
                    \<Longrightarrow> z \<in> actions0 pre
                    \<Longrightarrow> (a, x) \<in> sb pre
                    \<Longrightarrow> (x, y) \<in> hypothetical_release_sequence_set_alt pre wit
                    \<Longrightarrow> (y, z) \<in> rf wit
                    \<Longrightarrow> (z, b) \<in> sb pre
                    \<Longrightarrow>    a \<in> actions0 pre2
                         \<and> b \<in> actions0 pre2
                         \<and> x \<in> actions0 pre2
                         \<and> y \<in> actions0 pre2
                         \<and> z \<in> actions0 pre2 
                         \<and> (a, x) \<in> sb pre2 
                         \<and> (x, y) \<in> hypothetical_release_sequence_set_alt pre2 wit2 
                         \<and> (y, z) \<in> rf wit2
                         \<and> (z, b) \<in> sb pre2"
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre2 wit2"
using assms
unfolding sw_fence_sb_hrs_rf_sb_def
by blast

subsubsection {* sw_fence_sb_hrs_rf *}

lemma sw_fence_sb_hrs_rfIE [consumes 1, case_names fence]:
  assumes "(a, b) \<in> sw_fence_sb_hrs_rf pre wit"
      and "\<And>x y.     a \<in> actions0 pre
                  \<Longrightarrow> b \<in> actions0 pre
                  \<Longrightarrow> tid_of a \<noteq> tid_of b
                  \<Longrightarrow> is_fence a
                  \<Longrightarrow> is_release a
                  \<Longrightarrow> is_acquire b
                  \<Longrightarrow> x \<in> actions0 pre
                  \<Longrightarrow> y \<in> actions0 pre
                  \<Longrightarrow> (a, x) \<in> sb pre
                  \<Longrightarrow> (x, y) \<in> hypothetical_release_sequence_set_alt pre wit
                  \<Longrightarrow> (y, b) \<in> rf wit
                  \<Longrightarrow>    a \<in> actions0 pre2
                       \<and> b \<in> actions0 pre2
                       \<and> x \<in> actions0 pre2
                       \<and> y \<in> actions0 pre2
                       \<and> (a, x) \<in> sb pre2 
                       \<and> (x, y) \<in> hypothetical_release_sequence_set_alt pre2 wit2 
                       \<and> (y, b) \<in> rf wit2"
  shows   "(a, b) \<in> sw_fence_sb_hrs_rf pre2 wit2"
using assms
unfolding sw_fence_sb_hrs_rf_def
by auto

subsubsection {* sw_fence_rs_rf_sb *}

lemma sw_fence_rs_rf_sbIE [consumes 1, case_names fence]:
  assumes "(a, b) \<in> sw_fence_rs_rf_sb pre wit"
      and "\<And>x y.     a \<in> actions0 pre
                  \<Longrightarrow> b \<in> actions0 pre
                  \<Longrightarrow> tid_of a \<noteq> tid_of b
                  \<Longrightarrow> is_release a
                  \<Longrightarrow> is_fence b
                  \<Longrightarrow> is_acquire b
                  \<Longrightarrow> x \<in> actions0 pre
                  \<Longrightarrow> y \<in> actions0 pre
                  \<Longrightarrow> (a, x) \<in> release_sequence_set_alt pre wit
                  \<Longrightarrow> (x, y) \<in> rf wit
                  \<Longrightarrow> (y, b) \<in> sb pre
                  \<Longrightarrow>    a \<in> actions0 pre2
                       \<and> b \<in> actions0 pre2
                       \<and> x \<in> actions0 pre2
                       \<and> y \<in> actions0 pre2
                       \<and> (a, x) \<in> release_sequence_set_alt pre2 wit2
                       \<and> (x, y) \<in> rf wit2
                       \<and> (y, b) \<in> sb pre2"
  shows   "(a, b) \<in> sw_fence_rs_rf_sb pre2 wit2"
using assms
unfolding sw_fence_rs_rf_sb_def
by auto

subsubsection {* release_acquire_fenced_synchronizes_with_set *}

(* This is an unsafe elim, since the extra assumptions might not be provable when the conclusion is
provable. *)
lemma release_acquire_fenced_swIE [consumes 1, case_names asw lock rel_acq fence1 fence2 fence3]:
  assumes "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre wit"
      and "(a, b) \<in> sw_asw pre \<Longrightarrow> (a, b) \<in> sw_asw pre2"
      and "(a, b) \<in> sw_lock pre wit \<Longrightarrow> (a, b) \<in> sw_lock pre2 wit2"
      and "(a, b) \<in> sw_rel_acq_rs pre wit \<Longrightarrow> (a, b) \<in> sw_rel_acq_rs pre2 wit2"
      and "(a, b) \<in> sw_fence_sb_hrs_rf_sb pre wit \<Longrightarrow> (a, b) \<in> sw_fence_sb_hrs_rf_sb pre2 wit2"
      and "(a, b) \<in> sw_fence_sb_hrs_rf pre wit \<Longrightarrow> (a, b) \<in> sw_fence_sb_hrs_rf pre2 wit2"
      and "(a, b) \<in> sw_fence_rs_rf_sb pre wit \<Longrightarrow> (a, b) \<in> sw_fence_rs_rf_sb pre2 wit2"
  shows   "(a, b) \<in> release_acquire_fenced_synchronizes_with_set_alt pre2 wit2"
using assms
unfolding release_acquire_fenced_synchronizes_with_set_alt_def
by auto

lemma release_acquire_fenced_sw_simp:
  shows "  release_acquire_fenced_synchronizes_with_set 
             (actions0 pre) (sb pre) (asw pre) (rf wit) (lo wit) 
             (release_sequence_set (actions0 pre) (lk pre) (mo wit))
             (hypothetical_release_sequence_set (actions0 pre) (lk pre) (mo wit))
         = release_acquire_fenced_synchronizes_with_set_alt pre wit" (is "?left = ?right")
(* If we prove both directions at once, auto doesn't terminate. *)  
proof (intro equalityI subrelI)
  fix a b
  assume "(a, b) \<in> ?left"
  thus "(a, b) \<in> ?right"
    unfolding release_acquire_fenced_synchronizes_with_set_def
          release_acquire_fenced_synchronizes_with_set_alt_def
          sw_asw_def
          sw_lock_def
          sw_rel_acq_def
          sw_rel_acq_rs_def
          sw_fence_sb_hrs_rf_sb_def
          sw_fence_sb_hrs_rf_def
          sw_fence_rs_rf_sb_def
          release_sequence_set_alt_def
          hypothetical_release_sequence_set_alt_def
    by (auto simp add: release_acquire_fenced_synchronizes_with_def)
next
  fix a b
  assume "(a, b) \<in> ?right"
  thus "(a, b) \<in> ?left"
    unfolding release_acquire_fenced_synchronizes_with_set_def
          release_acquire_fenced_synchronizes_with_set_alt_def
          sw_asw_def
          sw_lock_def
          sw_rel_acq_def
          sw_rel_acq_rs_def
          sw_fence_sb_hrs_rf_sb_def
          sw_fence_sb_hrs_rf_def
          sw_fence_rs_rf_sb_def
          release_sequence_set_alt_def
          hypothetical_release_sequence_set_alt_def
    by (auto simp add: release_acquire_fenced_synchronizes_with_def)
qed

subsubsection {* release_acquire_fenced_relations *}

lemma release_acquire_fenced_relations_simp:
  shows "release_acquire_fenced_relations = release_acquire_fenced_relations_alt"
apply (rule ext)+
unfolding release_acquire_fenced_relations_def 
          release_acquire_fenced_relations_alt_def
          Let_def
unfolding release_acquire_fenced_hb_def
          release_acquire_fenced_vse_def
          release_sequence_set_alt_def
          hypothetical_release_sequence_set_alt_def
using release_acquire_fenced_sw_simp
by auto

lemma release_acquire_fenced_relations_non_empty [simp]:
  shows "release_acquire_fenced_relations pre wit \<noteq> []"
unfolding release_acquire_fenced_relations_def Let_def by simp

section {* Cmm: 9 - sc, no sc fences *}

subsubsection {* sc_accesses_consistent_sc *}

lemmas sc_accesses_consistent_scI [intro?] = defToIntro[OF sc_accesses_consistent_sc.simps(2)]

lemma sc_accesses_consistent_scE1 [elim]:
  assumes "sc_accesses_consistent_sc (pre, wit, (''hb'', hb)#rel)"
  obtains "relOver (sc wit) (actions0 pre)"
          "trans (sc wit)"
          "irrefl (sc wit)"
using assms
unfolding sc_accesses_consistent_sc.simps
by auto

(* Original elim. *)
(*
lemma sc_accesses_consistent_scE2 [elim]:
  assumes "sc_accesses_consistent_sc (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> sc wit" 
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
  obtains "(b, a) \<notin> hb"
          "(b, a) \<notin> mo wit"
          "a \<noteq> b"
          "is_seq_cst a"
          "is_seq_cst b"
using assms
unfolding sc_accesses_consistent_sc.simps
by auto
*)

lemma sc_accesses_consistent_scE2 [elim]:
  assumes "sc_accesses_consistent_sc (pre, wit, (''hb'', hb)#rel)"
      and "(a, b) \<in> sc wit" 
  obtains "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "a \<noteq> b"
      and "is_seq_cst a"
      and "is_seq_cst b"
      and "(b, a) \<notin> hb"
      and "(b, a) \<notin> mo wit"
      and "(b, a) \<notin> sc wit"
proof -
  have "(b, a) \<notin> sc wit"
    using assms
    by (auto elim: irreflTransE)
  moreover have "a \<in> actions0 pre" "b \<in> actions0 pre"
    using assms
    by (auto elim: relOverE)
  ultimately show ?thesis
    using assms that
    unfolding sc_accesses_consistent_sc.simps
    by auto
qed

lemma sc_accesses_consistent_scE2_inv [elim]:
  assumes "sc_accesses_consistent_sc (pre, wit, (''hb'', hb)#rel)"
      and "a \<in> actions0 pre"
      and "b \<in> actions0 pre"
      and "a \<noteq> b"
      and "is_seq_cst a"
      and "is_seq_cst b"
      and "(b, a) \<notin> sc wit"
  obtains "(a, b) \<in> sc wit" 
proof -
  show ?thesis
    using assms that
    unfolding sc_accesses_consistent_sc.simps
    by auto
qed

lemma rel_list_sc_accesses_consistent_sc [simp]:
  assumes "rel \<noteq> []"
  shows   "  sc_accesses_consistent_sc (pre, wit, (''hb'', hb)#rel) 
           = sc_accesses_consistent_sc (pre, wit, [(''hb'', hb)])"
unfolding sc_accesses_consistent_sc.simps ..

subsubsection {* sc_accesses_sc_reads_restricted *}

lemmas sc_accesses_sc_reads_restrictedI [intro?] 
       = defToIntro[OF sc_accesses_sc_reads_restricted.simps(2)]

lemmas sc_accesses_sc_reads_restrictedE [elim] 
       = defToElim[OF sc_accesses_sc_reads_restricted.simps(2)]

lemma rel_list_sc_accesses_sc_reads_restricted [simp]:
  assumes "rel \<noteq> []"
  shows   "  sc_accesses_sc_reads_restricted (pre, wit, (''hb'', hb)#rel)
           = sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', hb)])"  
unfolding sc_accesses_sc_reads_restricted.simps ..

section {* Cmm: 10 - sc_fences, no consume *}

subsubsection {* sc_fenced_sc_fences_heeded *}

lemmas sc_fenced_sc_fences_heededI [intro?] = defToIntro[OF sc_fenced_sc_fences_heeded.simps]
lemmas sc_fenced_sc_fences_heededE [elim] = defToElim[OF sc_fenced_sc_fences_heeded.simps]

lemma rel_list_sc_fenced_sc_fences_heeded [simp]:
  assumes "rel \<noteq> []"
  shows   "sc_fenced_sc_fences_heeded (pre, wit, rel) = sc_fenced_sc_fences_heeded (pre, wit, [])"  
unfolding sc_fenced_sc_fences_heeded.simps ..

section {* Cmm: 11 - with consume *}

subsubsection {* compose *}

(* We simplify compose0 to its official counterpart in the LEM library *)
lemma compose_simp [simp]:
  shows "compose0 a b = relcomp a b"
unfolding compose0_def relcomp_def 
by force

subsubsection {* inter_thread_happens_before *}

lemma inter_thread_happens_before_simp:
  shows "  inter_thread_happens_before 
             (actions0 pre) 
             (sb pre) 
             (release_acquire_fenced_synchronizes_with_set_alt pre wit)
             (with_consume_dob_set (actions0 pre) 
                                   (rf wit) 
                                   (release_sequence_set (actions0 pre) (lk pre) (mo wit)) 
                                   (with_consume_cad_set (actions0 pre) (sb pre) (dd pre) (rf wit))) 
         = inter_thread_happens_before_alt pre wit"
unfolding inter_thread_happens_before_alt_def
          inter_thread_happens_before_step_def
          inter_thread_happens_before_r_def
          inter_thread_happens_before_def
          Let_def
          release_sequence_set_alt_def
          with_consume_dob_set_alt_def
          with_consume_cad_set_alt_def
by auto

subsubsection {* with_consume_relations *}

lemma with_consume_relations_simp:
  shows "with_consume_relations = with_consume_relations_alt"
apply (rule ext)+
unfolding with_consume_relations_def 
          with_consume_relations_alt_def
          Let_def
unfolding with_consume_hb_def
          with_consume_vse_def
          release_sequence_set_alt_def
          hypothetical_release_sequence_set_alt_def
          with_consume_dob_set_alt_def
          with_consume_cad_set_alt_def
using release_acquire_fenced_sw_simp
      inter_thread_happens_before_simp
by auto

lemma with_consume_relations_non_empty [simp]:
  shows "with_consume_relations pre wit \<noteq> []"
unfolding with_consume_relations_def Let_def by simp

section {* Cmm: 12 - the standard model *}

subsubsection {* standard_vsses *}

lemma standard_vssesE [elim]:
  assumes "(a, b) \<in> standard_vsses_alt pre wit"
  obtains (immediate) 
          "a \<in> actions0 pre"
          "b \<in> actions0 pre"
          "is_at_atomic_location (lk pre) b"
          "(a, b) \<in> with_consume_vse pre wit"
          "\<forall>v'\<in>actions0 pre. (v', b) \<in> with_consume_vse pre wit \<longrightarrow> (a, v') \<notin> mo wit"
        | (head) head where 
          "a \<in> actions0 pre"
          "b \<in> actions0 pre"
          "head \<in> actions0 pre"
          "is_at_atomic_location (lk pre) b"
          "(head, b) \<in> with_consume_vse pre wit"
          "\<forall>v'\<in>actions0 pre. (v', b) \<in> with_consume_vse pre wit \<longrightarrow> (head, v') \<notin> mo wit"
          "(head, a) \<in> mo wit"
          "(b, a) \<notin> with_consume_hb pre wit"
          "\<forall>w\<in>actions0 pre. (head, w) \<in> mo wit \<and> (w, a) \<in> mo wit \<longrightarrow> (b, w) \<notin> with_consume_hb pre wit"
using assms
unfolding standard_vsses_alt_def
          standard_vsses_def
by auto

subsubsection {* standard_relations *}

lemma standard_relations_simp:
  shows "standard_relations = standard_relations_alt"
apply (rule ext)+
unfolding standard_relations_def 
          standard_relations_alt_def
          Let_def
unfolding with_consume_hb_def
          with_consume_vse_def
          release_sequence_set_alt_def
          hypothetical_release_sequence_set_alt_def
          with_consume_dob_set_alt_def
          with_consume_cad_set_alt_def
          standard_vsses_alt_def
using release_acquire_fenced_sw_simp
      inter_thread_happens_before_simp
by auto

lemma standard_relations_non_empty [simp]:
  shows "standard_relations pre wit \<noteq> []"
unfolding standard_relations_def Let_def by simp

subsubsection {* standard_consistent_atomic_rf *}

lemma standard_consistent_atomic_rf_simp:
  fixes pre wit
  defines "ex \<equiv> (pre, wit, standard_relations_alt pre wit)"
  assumes det_read:  "det_read ex"
      and coherency: "coherent_memory_use ex"
      and cons_hb:   "consistent_hb ex"
      and cons_mo:   "consistent_mo ex"
      and well_rf:   "well_formed_rf ex"
  shows   "standard_consistent_atomic_rf ex = consistent_atomic_rf ex"
proof
  assume std_cons_rf: "standard_consistent_atomic_rf ex"
  show "consistent_atomic_rf ex"
    unfolding ex_def standard_relations_alt_def
              consistent_atomic_rf.simps
    proof auto
      fix a b
      assume "(a, b) \<in> rf wit"
             "is_at_atomic_location (lk pre) b"
             "is_load b"
      hence "(a, b) \<in> standard_vsses_alt pre wit"
        using std_cons_rf
        unfolding ex_def standard_relations_alt_def
                  standard_consistent_atomic_rf.simps
        by auto
      hence not_hb: "(b, a) \<notin> with_consume_hb pre wit"
        proof (cases rule: standard_vssesE)
          case head
          thus ?thesis by auto
        next
          case immediate
          hence hb: "(a, b) \<in> with_consume_hb pre wit"
            unfolding with_consume_vse_def by auto
          show ?thesis
            using hb cons_hb 
            unfolding ex_def standard_relations_alt_def 
            by auto
            (*
            proof
              assume "(b, a) \<in> with_consume_hb pre wit"
              hence "(a, a) \<in> (with_consume_hb pre wit)\<^sup>+"
                using hb by auto
              thus False
                using cons_hb
                unfolding ex_def standard_relations_alt_def 
                by (auto elim: consistent_hbE irreflE)
            qed *)
        qed
      assume hb: "(b, a) \<in> with_consume_hb pre wit"
      thus False using not_hb by auto
    qed
next
  assume cons_rf: "consistent_atomic_rf ex"
  show "standard_consistent_atomic_rf ex"
    unfolding ex_def standard_relations_alt_def
              standard_consistent_atomic_rf.simps
    proof auto
      fix a b
      assume "(a, b) \<in> rf wit"
             "is_at_atomic_location (lk pre) b"
             "is_load b"
      hence not_hb: "(b, a) \<notin> with_consume_hb pre wit"
        using cons_rf
        unfolding ex_def standard_relations_alt_def
                  consistent_atomic_rf.simps
        by auto
      have "a \<in> actions0 pre" 
           "b \<in> actions0 pre" 
           "loc_of a = loc_of b"
           "is_write a"
        using well_rf `(a, b) \<in> rf wit`
        unfolding ex_def standard_relations_alt_def
        (* by (auto elim: well_formed_rfE) *)
        by auto
      hence "is_at_atomic_location (lk pre) a"
        using `is_at_atomic_location (lk pre) b`
              same_loc_atomic_location
        by metis
      let ?S = "{w | w. w \<in> actions0 pre \<and> (w, b) \<in> with_consume_vse pre wit}"
      have non_empty: "?S \<noteq> {}"
        using `(a, b) \<in> rf wit` 
              `a \<in> actions0 pre` 
              `b \<in> actions0 pre` 
              `is_load b`
        using det_read 
        unfolding ex_def standard_relations_alt_def
        (* by (auto elim: det_readE_rf) *)
        by auto
      have subset: "?S \<subseteq> {w. (w, b) \<in> with_consume_hb pre wit}"
        unfolding with_consume_vse_def
                  visible_side_effect_set_def
        by auto
      have "finite {w. (w, b) \<in> with_consume_hb pre wit}"
        using cons_hb `b \<in> actions0 pre`
        unfolding ex_def standard_relations_alt_def
        (* by (auto elim!: consistent_hbE finite_prefixesE) *)
        by (auto elim: finite_prefixesE)
      hence finite: "finite ?S"
        using finite_subset[OF subset] by metis
      have order: "isStrictPartialOrder (mo wit)"
        unfolding isStrictPartialOrder_def
        using cons_mo
        unfolding ex_def standard_relations_alt_def
        (* by (auto elim: consistent_moE_rel) *)
        by auto
      obtain head where head: "head \<in> ?S"
                    and sup:  "\<forall>y. y \<in> ?S \<longrightarrow> (head, y) \<notin> mo wit"
        using supremum_partial_order[OF finite non_empty order]
        by auto
      show "(a, b) \<in> standard_vsses_alt pre wit"
        proof (cases "a = head")
          assume "a = head"
          thus ?thesis
            unfolding standard_vsses_alt_def
                      standard_vsses_def
            using `a \<in> actions0 pre`
                  `b \<in> actions0 pre`
                  `is_at_atomic_location (lk pre) b`
                  head sup
            by auto
        next
          assume "a \<noteq> head"
          have "loc_of a = loc_of head"
            using head
            unfolding with_consume_vse_def
                      visible_side_effect_set_def
            using `loc_of a = loc_of b`
            by auto
          have "(head, b) \<in> with_consume_hb pre wit"
               "is_write head"
            using head
            unfolding with_consume_vse_def
                      visible_side_effect_set_def
            by auto
          hence "(a, head) \<notin> mo wit"
            using `(a, b) \<in> rf wit` coherency head
            unfolding ex_def standard_relations_alt_def
                      coherent_memory_use.simps
            by auto
          hence "(head, a) \<in> mo wit"
            using cons_mo head
                  `a \<in> actions0 pre`
                  `is_at_atomic_location (lk pre) a`
                  `a \<noteq> head`
                  `loc_of a = loc_of head`
                  `is_write a`
                  `is_write head`
            unfolding ex_def standard_relations_alt_def
                      consistent_mo.simps
            by auto
          have "(\<forall>w\<in>actions0 pre.      (head, w) \<in> mo wit \<and> (w, a) \<in> mo wit
                                   \<longrightarrow> (b, w) \<notin> with_consume_hb pre wit)"
            proof auto
              fix w
              assume "w \<in> actions0 pre"
                     "(w, a) \<in> mo wit"
                     "(b, w) \<in> with_consume_hb pre wit"
              thus False
                using `(a, b) \<in> rf wit` coherency head
                unfolding ex_def standard_relations_alt_def
                          coherent_memory_use.simps
                by auto
            qed
          thus ?thesis
            using `a \<in> actions0 pre`
                  `b \<in> actions0 pre`
                  `is_at_atomic_location (lk pre) b`
                  `(head, a) \<in> mo wit`
            unfolding standard_vsses_alt_def
                      standard_vsses_def
            using head sup not_hb
            by auto
        qed      
    qed
qed

subsubsection {* standard_memory_model *}

lemma standard_memory_model_simps [simp]:
  shows "consistent standard_memory_model = standard_consistent_execution"
        "relation_calculation standard_memory_model = standard_relations"
        "undefined0 standard_memory_model = locks_only_undefined_behaviour"
unfolding standard_memory_model_def
by simp_all

section {* Composite elims *}

lemma rmw_atomicityE1_consistent_mo [elim]:
  assumes rmw_at:  "rmw_atomicity (pre, wit, rel)"
      and cons_mo: "consistent_mo (pre, wit, rel)"
      and is_rmw:  "is_RMW b"
      and in_mo:   "adjacent_less_than (mo wit) (actions0 pre) a b"
  obtains "(a, b) \<in> rf wit"
proof -
  have "a \<in> actions0 pre" "b \<in> actions0 pre"
    using cons_mo in_mo by auto
  thus ?thesis
    using rmw_at is_rmw in_mo that
    by auto
qed

lemma rmw_atomicityE2_well_formed_rf [elim]:
  assumes rmw_at:  "rmw_atomicity (pre, wit, rel)"
      and well_rf: "well_formed_rf (pre, wit, rel)"
      and is_rmw:  "is_RMW b"
      and in_rf:   "(a, b) \<in> rf wit"
  obtains "adjacent_less_than (mo wit) (actions0 pre) a b"
      and "(a, b) \<in> mo wit"
proof -
  have "a \<in> actions0 pre" "b \<in> actions0 pre"
    using well_rf in_rf by auto
  thus ?thesis
    using rmw_at is_rmw in_rf that
    by auto
qed

lemma irreflRf [elim]:
  assumes in_rf:    "(a, b) \<in> rf wit"
      and well_rf:  "well_formed_rf (pre, wit, rel)"
      and cons_rmw: "rmw_atomicity (pre, wit, rel)"
      and cons_mo:  "consistent_mo (pre, wit, rel)"
  shows             "a \<noteq> b"
proof
  assume "a = b"
  have ab: "is_write a" "is_read b" "a \<in> actions0 pre"
    using in_rf well_rf by auto
  hence "is_RMW a" 
    using `a = b` by (auto intro: is_RMWI)
  hence "(a, a) \<in> mo wit" 
    using cons_rmw ab `a = b` in_rf by auto
  thus False using cons_mo by auto
qed

(*
lemma non_atomic_rfE:
  assumes in_rf:   "(a, b) \<in> rf wit"
      and not_at:  "is_at_non_atomic_location (lk pre) b"
      and cons_rf: "consistent_non_atomic_rf (pre, wit, [(''hb'', with_consume_hb pre wit), 
                                                         (''vse'', with_consume_vse pre wit)])"
  shows            "(a, b) \<in> with_consume_vse pre wit"
                   "(a, b) \<in> with_consume_hb pre wit"
proof -
  show "(a, b) \<in> with_consume_vse pre wit"
    using cons_rf in_rf not_at
    unfolding consistent_non_atomic_rf.simps 
    by auto
  thus "(a, b) \<in> with_consume_hb pre wit"
    unfolding with_consume_vse_def
    by (auto elim: visible_side_effect_setE1)
qed

thm consistent_non_atomic_rfE
*)

section {* Extra lemmas for standard-relations *}

subsubsection {* with_consume_vse *}

lemma with_consume_vseE [elim]:
  assumes "(a, b) \<in> with_consume_vse pre wit"
  obtains "(a, b) \<in> with_consume_hb pre wit"
using assms
unfolding with_consume_vse_def
by auto

subsubsection {* Simplification of the relation_calculation *}

lemma rel_list_coherent_memory_use_standard [simp]:
  shows   "  coherent_memory_use (pre, wit, standard_relations pre wit) 
           = coherent_memory_use (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_consistent_atomic_rf_standard [simp]:
  shows   "  consistent_atomic_rf (pre, wit, standard_relations pre wit) 
           = consistent_atomic_rf (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_consistent_hb_standard [simp]:
  shows   "  consistent_hb (pre, wit, standard_relations pre wit) 
           = consistent_hb (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_locks_only_consistent_lo_standard [simp]:
  shows   "  locks_only_consistent_lo (pre, wit, standard_relations pre wit) 
           = locks_only_consistent_lo (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_sc_accesses_consistent_sc_standard [simp]:
  shows   "  sc_accesses_consistent_sc (pre, wit, standard_relations pre wit) 
           = sc_accesses_consistent_sc (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_sc_accesses_sc_reads_restricted_standard [simp]:
  shows   "  sc_accesses_sc_reads_restricted (pre, wit, standard_relations pre wit) 
           = sc_accesses_sc_reads_restricted (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_consistent_non_atomic_rf_standard [simp]:
  shows   "  consistent_non_atomic_rf (pre, wit, standard_relations pre wit) 
           = consistent_non_atomic_rf (pre, wit, [(''hb'', with_consume_hb pre wit), 
                                                  (''vse'', with_consume_vse pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_det_read_standard [simp]:
  shows   "  det_read (pre, wit, standard_relations pre wit) 
           = det_read (pre, wit, [(''hb'', with_consume_hb pre wit), 
                                  (''vse'', with_consume_vse pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

lemma rel_list_det_read_alt_standard [simp]:
  shows   "  det_read_alt (pre, wit, standard_relations pre wit) 
           = det_read_alt (pre, wit, [(''hb'', with_consume_hb pre wit)])"      
unfolding standard_relations_simp
          standard_relations_alt_def
by simp

end
