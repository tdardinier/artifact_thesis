theory Chapter4_Wands
  imports
    "Wands/CombinableWands"
begin

text \<open>The following Isabelle theory file contains references to all the formalised results explicitly
mentioned in chapter 4 of the thesis. The theory file is structured using Isabelle sections and subsections,
which match those from the thesis. \<close>



section \<open>4.3: Specialized Package Logic\<close>

text \<open>Note that the definitions presented here are already from the generalized package logic, which
is the only one formalized. The specialized package logic is simply a concrete instantiation of it,
which allows us to simplify the presentation of the key ideas.\<close>


subsection \<open>4.3.2: Package Logic: Preliminaries\<close>


text \<open>As described in the thesis, we reuse the IDF algebra \<^class>\<open>sep_algebra\<close> from @{file "CoreIVL/SepAlgebra.thy"}:
\<^item> \<^term>\<open>\<sigma> \<oplus> \<sigma>'\<close>: addition of states \<sigma> and \<sigma>'.
\<^item> \<^term>\<open>\<sigma> ## \<sigma>'\<close>: the addition \<^term>\<open>\<sigma> \<oplus> \<sigma>'\<close> is defined.
\<^item> \<^term>\<open>\<sigma>' \<succeq> \<sigma>\<close>: \<sigma>' is greater than \<sigma>.
\<^item> \<^term>\<open>\<sigma>' \<ominus> \<sigma>\<close>: subtraction (well-defined only if \<^term>\<open>\<sigma>' \<succeq> \<sigma>\<close>.\<close>


paragraph \<open>Assertion language\<close>

text \<open>The assertion language described at the start of Section 4.3.2 corresponds to the type \<^typ>\<open>'a aassertion\<close>,
where the type parameter 'a is the type of states from the IDF algebra.
The semantics of this small assertion language is defined via \<^term>\<open>sat A \<omega>\<close> (where A is an assertion and \<omega> a state.)\<close>



subsection \<open>4.3.3: The Package Logic\<close>



paragraph \<open>Definition 4.3.1: Witness sets and contexts.\<close>

text \<open>Witness sets are represented by the type \<^typ>\<open>'a ext_state set\<close>. The type \<^typ>\<open>'a ext_state\<close>
represents a pair of state (with the relevant transformer from the generalized version).\<close>

text \<open>The context is not represented as a specific type. Instead, our judgment takes more arguments.\<close>


paragraph \<open>Definition 4.3.2: Configurations and reductions.\<close>

text \<open>A reduction \<langle>B, pc, (\<sigma>0 , S0)\<rangle> --> (\<sigma>1, S1) is represented as \<^term>\<open>package_rhs \<sigma>0 \<sigma>F S0 pc B \<sigma>1 \<sigma>F' S1\<close>.
As can be seen, configurations are not represented as a specific type, but simply as multiple arguments.
The terms \<sigma>F and \<sigma>F' can be ignored for now, as they become relevant for the generalized version.\<close>



paragraph \<open>Figure 4.2: Rules of the package logic.\<close>

text \<open>The rules of the package logic can be seen as part of the definition of \<^term>\<open>package_rhs\<close>:
\<^item> Star: Rule @{thm AStar}
\<^item> Implication: Rule @{thm AImp}
\<^item> AtomS: Rule @{thm ASem}
\<^item> ExtractS: Rule @{thm AddFromOutside} (the function choice is represented by the Isabelle function witness).
\<close>



subsection \<open>4.3.4: Soundness and Completeness\<close>

paragraph \<open>Theorem 4.3.1 Soundness of the package logic.\<close>

definition wand_set where
  "wand_set A B = Collect (sat A) --\<otimes> Collect (sat B)"

abbreviation initial_witness_set where
  "initial_witness_set \<sigma> A \<equiv> { (a, stabilize |a|, id) |a. sat A a \<and> a ## stabilize |\<sigma>| }"

theorem specialized_soundness:
  assumes "wf_assertion B"
      and "package_rhs \<sigma> (stabilize |\<sigma>| ) (initial_witness_set \<sigma> A) (\<lambda>_. True) B \<sigma>' f S'"
      and "intuitionistic (sat B) \<or> pure_remains S'"
    shows "\<exists>\<sigma>w. stable \<sigma>w \<and> Some \<sigma> = \<sigma>' \<oplus> \<sigma>w \<and> \<sigma>w \<in> wand_set A B"
proof -
  have r: "Some \<sigma> = \<sigma>' \<oplus> f \<and> stable f \<and> (\<forall>(a, T)\<in>{(a, id) |a. sat A a}. a ## T f \<longrightarrow> sat B (the (a \<oplus> T f)))"
    apply (rule general_soundness[OF _ _ assms(1) assms(3), of \<sigma> _ \<sigma>' f])
    using assms(2) unfolding mono_transformer_def by simp_all
  then have "f \<in> wand_set A B"
    unfolding wand_set_def wand_def apply simp
    by (metis defined_def not_None_eq option.sel)
  then show ?thesis using r by blast
qed


paragraph \<open>Theorem 4.3.2: Completeness of the package logic.\<close>

theorem specialized_completeness:
  assumes "wf_assertion B"
      and "stable \<sigma>w"
      and "\<sigma>w \<in> wand_set A B"
      and "Some \<sigma> = \<sigma>' \<oplus> \<sigma>w"
    shows "\<exists>S'. package_rhs \<sigma> (stabilize |\<sigma>| ) (initial_witness_set \<sigma> A) (\<lambda>_. True) B \<sigma>' \<sigma>w S'"
  apply (rule completeness[OF _ assms(4) assms(2) _ assms(1)])
  using assms(3) unfolding valid_package_set_def wand_set_def wand_def mono_transformer_def
  by simp_all blast





section \<open>4.4: Generalized Package Logic\<close>


subsection \<open>4.4.1: Generalizing the Logic\<close>

paragraph \<open>Definition 4.4.1: Parametric magic wands.\<close>

text \<open>A transformer T is monotonic if \<^term>\<open>mono_transformer T\<close> holds.\<close>

definition parametric_wand where
  "parametric_wand A \<tau> B \<sigma>F \<longleftrightarrow> (\<forall>\<sigma> \<sigma>B. sat A \<sigma> \<and> Some \<sigma>B = \<sigma> \<oplus> \<tau> \<sigma> \<sigma>F \<longrightarrow> sat B \<sigma>B)"


paragraph \<open>Example 4.4.1: The standard wand is a parametric wand.\<close>

lemma standard_wand_is_parametric:
  "\<sigma>F \<in> wand_set A B \<longleftrightarrow> parametric_wand A (\<lambda>_. id) B \<sigma>F"
  unfolding wand_set_def parametric_wand_def wand_def apply simp
  by blast



paragraph \<open>Definition 4.4.2: Generalized witness sets and contexts.\<close>

text \<open>Generalized witness sets are represented by the type \<^typ>\<open>'a ext_state set\<close>.
 The type \<^typ>\<open>'a ext_state\<close> represents a triple of two states and a transformer.\<close>

text \<open>The generalized context is not represented as a specific type. Instead, our judgment,
\<^term>\<open>package_rhs \<sigma>0 f0 S0 pc B \<sigma>1 f1 S1\<close>, takes more arguments:
The initial witness set is S0, and the initial configuration is <B, pc, (\<sigma>0, f0, S0)>.\<close>



paragraph \<open>Figure 4.4: Rules of the generalized package logic.\<close>

text \<open>The rules of the generalized package logic can be seen as part of the definition of \<^term>\<open>package_rhs\<close>:
\<^item> Star: Rule @{thm AStar}
\<^item> Implication: Rule @{thm AImp}
\<^item> AtomS: Rule @{thm ASem}
\<^item> ExtractS: Rule @{thm AddFromOutside} (the function choice is represented by the Isabelle function witness).
\<close>



paragraph \<open>Theorem 4.4.1: Soundness of the generalized package logic.\<close>

abbreviation generalized_init_witness_set where
  "generalized_init_witness_set \<tau> \<sigma> A \<equiv> { (a, stabilize |a|, \<tau> a) |a. sat A a \<and> a ## stabilize |\<sigma>| }"

theorem general_soundness:
  assumes "wf_assertion B"
      and "\<And>\<sigma>. mono_transformer (\<tau> \<sigma>)"
      and "package_rhs \<sigma>0 (stabilize |\<sigma>0| ) (generalized_init_witness_set \<tau> \<sigma>0 A) (\<lambda>_. True) B \<sigma>1 \<sigma>F S1"
      and "intuitionistic (sat B) \<or> pure_remains S1"
    shows "Some \<sigma>0 = \<sigma>1 \<oplus> \<sigma>F \<and> stable \<sigma>F \<and> parametric_wand A \<tau> B \<sigma>F"
proof -
  have r: "Some \<sigma>0 = \<sigma>1 \<oplus> \<sigma>F \<and>
sep_algebra_class.stable \<sigma>F \<and> (\<forall>(a, T)\<in>{(a, \<tau> a) |a. sat A a \<and> a ## stabilize |\<sigma>0|}. a ## T \<sigma>F \<longrightarrow> sat B (the (a \<oplus> T \<sigma>F)))"
    apply (rule general_soundness[OF _ _ assms(1) assms(4), of \<sigma>0 "{ (a, \<tau> a) |a. sat A a \<and> a ## stabilize |\<sigma>0| }" \<sigma>1 \<sigma>F])
    using assms(3) apply simp
    using assms(2) by blast
  then have "parametric_wand A \<tau> B \<sigma>F"
    unfolding parametric_wand_def
    apply (intro allI impI; elim conjE)
    apply simp
    apply (subgoal_tac "\<sigma> ## stabilize |\<sigma>0|")
    apply (metis defined_def option.sel option.simps(3))
  proof -
    fix \<sigma> \<sigma>B
    assume asm0: "Some \<sigma>B = \<sigma> \<oplus> \<tau> \<sigma> \<sigma>F" "Some \<sigma>0 = \<sigma>1 \<oplus> \<sigma>F"
       "sep_algebra_class.stable \<sigma>F"
    then have "\<sigma> ## stabilize |\<tau> \<sigma> \<sigma>F|"
      using asso3 defined_def property_needed_one by fastforce
    then have "\<sigma> ## stabilize |\<sigma>F|"
      using mono_transformer_def[of "\<tau> \<sigma>"] assms(2)
      by (smt (verit, ccfv_threshold) compatible_with_stab_pure_larger defined_comm defined_def option.distinct(1) smaller_compatible
          stabilize_core_right_id)
    then show "\<sigma> ## stabilize |\<sigma>0|"
      by (metis asm0(2) pcm_with_core_class.core_sum plus_pure_stabilize_eq pre_pcm_class.commutative)
  qed
  then show ?thesis using r by blast
qed



paragraph \<open>Theorem 4.4.2: Completeness of the generalized package logic.\<close>

theorem general_completeness:
  assumes "wf_assertion B"
      and "\<And>\<sigma>. mono_transformer (\<tau> \<sigma>)"
      and "stable \<sigma>F"
      and "parametric_wand A \<tau> B \<sigma>F"
      and "Some \<sigma>0 = \<sigma>1 \<oplus> \<sigma>F"
    shows "\<exists>S1. package_rhs \<sigma>0 (stabilize |\<sigma>0| ) (generalized_init_witness_set \<tau> \<sigma>0 A) (\<lambda>_. True) B \<sigma>1 \<sigma>F S1"
    apply (rule completeness[OF _ assms(5) assms(3) _ assms(1)])
    using assms(4) unfolding parametric_wand_def apply blast
    using assms(2) by blast




subsection \<open>4.4.2: Using the Generalized Package Logic with Combinable Wands\<close>


paragraph \<open>Definition 4.4.3: Scalable footprints.\<close>


text \<open>scaled(\<sigma>) is represented as \<^term>\<open>scaled \<sigma>\<close>\<close>

definition scalable where
  "scalable \<sigma>E \<sigma>A \<longleftrightarrow> (\<forall>\<sigma> \<in> scaled \<sigma>E. \<sigma>A ## \<sigma>) \<or> (\<forall>\<sigma> \<in> scaled \<sigma>E. \<not> \<sigma>A ## \<sigma>)"

definition scalable_for_wand where
  "scalable_for_wand \<sigma>F A \<longleftrightarrow> (\<forall>\<sigma>A. sat A \<sigma>A \<longrightarrow> scalable \<sigma>F \<sigma>A)"




paragraph \<open>Definition 4.4.4: Combinable wands.\<close>


text \<open>The family of monotonic transformers R is defined as \<^term>\<open>R\<close>.\<close>

text \<open>We define the combinable wand as \<^term>\<open>cwand A B\<close>.
As the following lemma shows, it corresponds to a parametric magic wand with family of transformers R.\<close>

lemma cwand_is_parametric:
  "\<sigma>F \<in> cwand (Collect (sat A)) (Collect (sat B)) \<longleftrightarrow> parametric_wand A R B \<sigma>F"
  unfolding cwand_def parametric_wand_def R_def
   using PartialHeapSA.commutative by auto



paragraph \<open>Proposition 4.4.3: Key properties of combinable wands.\<close>


theorem properties_of_combinable_wands:
  assumes "up_closed B"
    shows "combinable B \<Longrightarrow> combinable (cwand A B)"
      and "cwand A B \<subseteq> wand A B"
      and "binary A \<Longrightarrow> cwand A B = wand A B"
  by (simp_all add: assms combinable_cwand cwand_stronger binary_same dual_order.eq_iff)


end
