theory Chapters56_HHL_Hypra
  imports "HyperHoareLogic/ExamplesCompositionality" "HyperHoareLogic/AutomatingHHL"
begin

text \<open>This file contains the formal results mentioned in chapters 5 and 6 of the thesis.
It is organized in the same order and with the same structure as the thesis.\<close>


text \<open>Navigating the Isabelle formalization:
\<^item> You can use the panel "Sidekick" on the right to see and navigate the structure of the file, via sections and subsections.
\<^item> You can ctrl+click on terms to jump to their definition.
\<^item> After jumping to another location, you can come back to the previous location by clicking the
  green left arrow, on the right side of the menu above.\<close>


section \<open>5.3: Hyper Hoare Logic\<close>

subsection \<open>5.3.1: Language and Semantics\<close>

paragraph \<open>Definition 5.3.1: Program states and programming language.\<close>

text \<open>The programming language is defined in the file @{file "HyperHoareLogic/Language.thy"}:
\<^item> The type of program state is \<^typ>\<open>('pvar, 'pval) pstate\<close>
  (<-- you can ctrl+click on the name \<open>pstate\<close> above to jump to its definition).
\<^item> Program commands are defined via the type \<^typ>\<open>('var, 'val) stmt\<close>.\<close>


paragraph \<open>Figure 5.1: Big-step semantics.\<close>

text \<open>The big-step semantics is defined as \<^const>\<open>single_sem\<close>. We also use the notation \<^term>\<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>.\<close>



subsection \<open>5.3.2: Hyper-Triples, Formally\<close>


paragraph \<open>Definition 5.3.2: Extended states.\<close>

text \<open>Extended states (definition 2) are defined as \<^typ>\<open>('lvar, 'lval, 'pvar, 'pval) state\<close> (file Language.thy).\<close>


paragraph \<open>Definition 5.3.3: Hyper-assertions.\<close>

text \<open>In the file @{file "HyperHoareLogic/Logic.thy"}:
\<^item> Hyper-assertions are defined as \<^typ>\<open>('lvar, 'lval, 'pvar, 'pval) state hyperassertion\<close>
\<^item> Entailment between hyper-assertions P and Q is defined as \<^term>\<open>entails P Q\<close>
\<close>


paragraph \<open>Definition 5.3.4: Extended semantics.\<close>

text \<open>The extended semantics is defined as \<^term>\<open>sem C S\<close> (file Language.thy).\<close>


paragraph \<open>Lemma 5.3.1: Properties of the extended semantics.\<close>

lemma properties_extended_semantics:
  "sem C (S1 \<union> S2) = sem C S1 \<union> sem C S2"
  "S \<subseteq> S' \<Longrightarrow> sem C S \<subseteq> sem C S'"
  "sem C (\<Union>x. f x) = (\<Union>x. sem C (f x))"
  "sem Skip S = S"
  "sem (C1;; C2) S = sem C2 (sem C1 S)"
  "sem (If C1 C2) S = sem C1 S \<union> sem C2 S"
  "sem (While C) S = (\<Union>n. iterate_sem n C S)"
  using sem_if sem_seq sem_union sem_skip sem_union_general sem_monotonic sem_while by metis+



paragraph \<open>Definition 5.3.5: Hyper-triples.\<close>

text \<open>Hyper-triples are defined as \<^const>\<open>hyper_hoare_triple\<close> (file Logic.thy).
We also use the notation \<^term>\<open>\<Turnstile> {P} C {Q}\<close>.\<close>


paragraph \<open>Blue box: Terminating hyper-triples\<close>

text \<open>Terminating hyper-triples are defined as \<^const>\<open>total_hyper_triple\<close>, and usually
written \<^term>\<open>\<Turnstile>TERM {P} C {Q}\<close>.\<close>





subsection \<open>5.3.3: Expressiveness of Hyper-Triples\<close>


paragraph \<open>Definition 5.3.6: Program hyperproperties.\<close>

text \<open>Program hyperproperties are defined in the file ProgramHyperproperties as
the type \<^typ>\<open>('pvar, 'pval) program_hyperproperty\<close>, which is syntactic sugar for the type
\<^typ>\<open>(('pvar, 'pval) pstate \<times> ('pvar, 'pval) pstate) set \<Rightarrow> bool\<close>. As written in the thesis (after the definition),
this type is equivalent to the type \<^typ>\<open>((('pvar, 'pval) pstate \<times> ('pvar, 'pval) pstate) set) set\<close>.
The satisfiability of program hyperproperties is defined via the function \<^const>\<open>hypersat\<close>.\<close>



paragraph \<open>Theorem 5.3.2: Expressing hyperproperties as hyper-triples\<close>

theorem expressing_hyperproperties_as_hyper_triples:
  fixes to_lvar :: "'pvar \<Rightarrow> 'lvar"
  fixes to_lval :: "'pval \<Rightarrow> 'lval"
  fixes H :: "('pvar, 'pval) program_hyperproperty"
  assumes "injective to_lvar" \<comment>\<open>The cardinality of \<^typ>\<open>'lvar\<close> is at least the cardinality of \<^typ>\<open>'pvar\<close>.\<close>
      and "injective to_lval" \<comment>\<open>The cardinality of \<^typ>\<open>'lval\<close> is at least the cardinality of \<^typ>\<open>'pval\<close>.\<close>
    shows "\<exists>P Q::('lvar, 'lval, 'pvar, 'pval) state hyperassertion. (\<forall>C. hypersat C H \<longleftrightarrow> \<Turnstile> {P} C {Q})"
  using assms proving_hyperproperties
  by blast


paragraph \<open>Theorem 5.3.3: Expressing hyper-triples as hyperproperties\<close>

theorem expressing_hyper_triples_as_hyperproperties:
  "\<Turnstile> {P} C {Q} \<longleftrightarrow> hypersat C (hyperprop_hht P Q)"
  by (simp add: any_hht_hyperprop)


paragraph \<open>Theorem 5.3.4: Disproving hyper-triples\<close>

theorem disproving_triples:
  "\<not> \<Turnstile> {P} C {Q} \<longleftrightarrow> (\<exists>P'. sat P' \<and> entails P' P \<and> \<Turnstile> {P'} C {\<lambda>S. \<not> Q S})"
  using disproving_triple by auto




section \<open>5.4: Core Rules\<close>


paragraph \<open>Figure 5.2.: Core rules of Hyper Hoare Logic.\<close>

text \<open>The core rules are defined in the file Logic.thy as \<^const>\<open>syntactic_HHT\<close>.
We also use the notation \<^term>\<open>\<turnstile> {P} C {Q}\<close>.\<close>


paragraph \<open>Definitions 5.4.1 and 5.4.2: (Indexed) unions of hyper-assertions.\<close>

text \<open>The operators \<open>\<otimes>\<close> and \<open>\<Otimes>\<close> are defined as \<^const>\<open>join\<close> and \<^const>\<open>natural_partition\<close>, respectively.\<close>


paragraph \<open>Blue box: Rules for terminating hyper-triples\<close>

fun no_assume where
  "no_assume (Assume _) \<longleftrightarrow> False"
| "no_assume (Seq C1 C2) \<longleftrightarrow> no_assume C1 \<and> no_assume C2"
| "no_assume (If C1 C2) \<longleftrightarrow> no_assume C1 \<and> no_assume C2"
| "no_assume _ \<longleftrightarrow> True"

lemma no_assume_terminates:
  assumes "no_assume C"
  shows "terminates C"
  using assms by (induct C)
  (simp_all add: terminates_assign terminates_havoc terminates_if terminates_seq terminates_while terminates_skip)

lemma no_assume_then_term_same:
  assumes "no_assume C"
  shows "\<Turnstile>TERM {P} C {Q} \<longleftrightarrow> \<Turnstile> {P} C {Q}"
  using assms no_assume_terminates terminates_implies_total total_hyper_triple_equiv by blast


lemma IfTot:
  assumes "\<Turnstile> {P} Assume b {PT}"
      and "\<Turnstile> {P} Assume (lnot b) {PF}"
      and "\<Turnstile>TERM {PT} C1 {Q1}"
      and "\<Turnstile>TERM {PF} C2 {Q2}"
    shows "\<Turnstile>TERM {P} if_then_else b C1 C2 {join Q1 Q2}"
  using assms terminating_if by blast


theorem WhileDesugaredTot:
  assumes "\<And>n. \<Turnstile> {P n} Assume b {Q n}"
      and "\<And>n. \<Turnstile>TERM {conj (Q n) (e_recorded_in_t e t)} C {conj (P (Suc n)) (e_smaller_than_t e t lt)}"
      and "\<Turnstile> {natural_partition P} Assume (lnot b) {R}"
      and "wfP lt"
      and "\<And>n. not_fv_hyper t (P n)"
      and "\<And>n. not_fv_hyper t (Q n)"
    shows "\<Turnstile>TERM {P 0} while_cond b C {R}"
  using normal_while_tot assms by metis




subsection \<open>5.4.2. Soundness and Completeness\<close>


paragraph \<open>Theorem 5.4.1 Soundness of the core rules.\<close>

theorem soundness_core_rules:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<Turnstile> {P} C {Q}"
  using assms soundness by auto

paragraph \<open>Theorem 5.4.2: Completeness of the core rules.\<close>

theorem completeness_core_rules:
  assumes "\<Turnstile> {P} C {Q}"
  shows "\<turnstile> {P} C {Q}"
  using assms completeness by auto





section \<open>5.5: Syntactic Rules\<close>


subsection \<open>5.5.1: Syntactic Hyper-Assertions\<close>


paragraph \<open>Definition 5.5.1: Syntactic hyper-expressions and hyper-assertions.\<close>

text \<open>Syntactic hyper-expressions and hyper-assertions are defined in the file
SyntacticAssertions.thy as \<^typ>\<open>'val exp\<close> and \<^typ>\<open>'val assertion\<close> respectively, where 'val is the
type of both logical and program values. Note that we use de Bruijn indices (i.e, natural numbers)
for states and variables bound by quantifiers.\<close>


paragraph \<open>Definition 5.5.2 Evaluation of syntactic hyper-expressions and satisfiability of hyper-assertions.\<close>

text \<open>
\<^item> Evaluation of syntactic hyper-expressions: \<^term>\<open>interp_exp \<Delta> \<Sigma> e\<close>
\<^item> Satisfiability of hyper-assertions: \<^term>\<open>interp_assert A\<close> (via \<^term>\<open>sat_assertion \<Delta> \<Sigma> A S\<close>)
\<close>



subsection \<open>5.5.2: Syntactic Rules for Deterministic and Non-Deterministic Assignments.\<close>

paragraph \<open>Definitions 5.5.3 and 5.5.4: Syntactic transformation for assignments.\<close>

text \<open>\<^term>\<open>transform_assign x e P\<close> and \<^term>\<open>transform_havoc x P\<close> correspond to \<open>A\<^sup>e\<^sub>x\<close> and \<open>H\<^sub>x\<close>.\<close>


paragraph \<open>Rule AssignS from Figure 5.3\<close>

text \<open>We prove semantic versions of the syntactic rules from.
We use \<^const>\<open>interp_assert\<close> to convert a syntactic hyper-assertion into a semantic one, because
our hyper-triples require semantic hyper-assertions. Similarly, we use \<^const>\<open>interp_pexp\<close> to convert
a syntactic program expression into a semantic one.\<close>

proposition AssignS:
  "\<turnstile> { interp_assert (transform_assign x e P) } Assign x (interp_pexp e) {interp_assert P}"
  using completeness rule_assign_syntactic by blast


paragraph \<open>Rule HavocS from Figure 5.3\<close>

proposition HavocS:
  "\<turnstile> { interp_assert (transform_havoc x P) } Havoc x {interp_assert P}"
  using completeness rule_havoc_syntactic by blast



subsection \<open>5.5.3: Syntactic Rules for Assume Statements\<close>

paragraph \<open>Definition 5.5.5: Syntactic transformation for assume statements.\<close>

text \<open>\<^const>\<open>transform_assume\<close> corresponds to \<open>\<Pi>\<^sub>b\<close>.\<close>

paragraph \<open>Rule AssumeS from Figure 5.3\<close>

proposition AssumeS:
  "\<turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 b) P) } Assume (interp_pbexp b) {interp_assert P}"
  using completeness rule_assume_syntactic by blast


text \<open>As before, we use \<^const>\<open>interp_pbexp\<close> to convert the syntactic program Boolean expression b into
a semantic one. Similarly, \<^term>\<open>pbexp_to_assertion 0 b\<close> converts the syntactic program Boolean expression
p into a syntactic hyper-assertion. The number 0 is a de Bruijn index, which corresponds to the closest
quantified state. For example, the hyper-assertion \<open>\<forall><\<phi>>. \<phi>(a)=\<phi>(b) \<and> (\<exists><\<phi>'>. \<phi>(x) \<succeq> \<phi>'(y))\<close> would
be written as \<open>\<forall>. 0(a)=0(b) \<and> (\<exists>. 1(x) \<succeq> 0(y))\<close> with de Bruijn indices. Thus, one can think of
\<open>pbexp_to_assertion 0 b\<close> as \<open>b(\<phi>)\<close>, where \<open>\<phi>\<close> is simply the innermost quantified state.\<close>




section \<open>5.6: Loop Rules\<close>


paragraph \<open>Rule WhileDesugared from Figure 5.5.\<close>

theorem while_desugared:
  assumes "\<And>n. \<turnstile> {I n} Assume b;; C {I (Suc n)}"
      and "\<turnstile> { natural_partition I } Assume (lnot b) { Q }"
    shows "\<turnstile> {I 0} while_cond b C { Q }"
  by (metis completeness soundness assms(1) assms(2) seq_rule while_cond_def while_rule)

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>natural_partition I\<close> corresponds to the \<open>\<Otimes>\<close> operator from definition 7.
\<^item> \<^term>\<open>lnot b\<close> negates b.
\<^item> \<^term>\<open>while_cond b C\<close> is defined as \<^term>\<open>While (Assume b;; C);; Assume (lnot b)\<close>.\<close>


subsection \<open>5.6.1: Synchronized Control Flow\<close>

paragraph \<open>Rule WhileSync from Figure 5.5\<close>

lemma WhileSync:
  assumes "entails I (low_exp b)"
      and "\<turnstile> {conj I (holds_forall b)} C {I}"
    shows "\<turnstile> {conj I (low_exp b)} while_cond b C {conj (disj I emp) (holds_forall (lnot b))}"
  using WhileSync_simpler entail_conj completeness soundness assms(1) assms(2) entails_refl 
  consequence_rule[of "conj I (holds_forall b)" "conj I (holds_forall b)" I "conj I (low_exp b)"] by blast

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>conj A B\<close> corresponds to the hyper-assertion \<open>A \<and> B\<close>.
\<^item> \<^term>\<open>holds_forall b\<close> corresponds to \<open>box(b)\<close>.
\<^item> \<^term>\<open>low_exp b\<close> corresponds to \<open>low(b)\<close>.
\<^item> \<^term>\<open>disj A B\<close> corresponds to the hyper-assertion \<open>A \<or> B\<close>.
\<^item> \<^term>\<open>emp\<close> checks whether the set of states is empty.\<close>



paragraph \<open>Blue box: Synchronized loop rule for terminating hyper-triples\<close>

theorem WhileSyncTot:
  assumes "\<Turnstile>TERM {conj I (\<lambda>S. \<forall>\<phi>\<in>S. b (snd \<phi>) \<and> fst \<phi> t = e (snd \<phi>))} C {conj (conj I (low_exp b)) (e_smaller_than_t e t lt)}"
      and "wfP lt"
      and "not_fv_hyper t I"
    shows "\<Turnstile>TERM {conj I (low_exp b)} while_cond b C {conj I (holds_forall (lnot b))}"
  by (meson WhileSyncTot assms(1) assms(2) assms(3))




paragraph \<open>Rule IfSync from Figure 5.5\<close>

theorem IfSync:
  assumes "entails P (low_exp b)"
      and "\<turnstile> {conj P (holds_forall b)} C1 {Q}"
      and "\<turnstile> {conj P (holds_forall (lnot b))} C2 {Q}"
    shows "\<turnstile> {P} if_then_else b C1 C2 {Q}"
  using completeness soundness consequence_rule[of _ "conj P (low_exp b)" Q] assms(1) entail_conj entails_refl assms if_synchronized by metis

text \<open>This result uses the following construct:
\<^item> \<^term>\<open>if_then_else b C1 C2\<close> is syntactic sugar for \<^term>\<open>If (Assume b;; C1) (Assume (lnot b);; C2)\<close>.\<close>




subsection \<open>5.6.2: \<open>\<forall>*\<exists>*\<close>-Hyperproperties\<close>


paragraph \<open>Rule \<open>While-\<forall>*\<exists>*\<close> from Figure 5.5\<close>

theorem while_forall_exists:
  assumes "\<turnstile> {I} if_then b C {I}"
      and "\<turnstile> {I} Assume (lnot b) {interp_assert Q}"
      and "no_forall_state_after_existential Q"
    shows "\<turnstile> {I} while_cond b C {interp_assert Q}"
  using consequence_rule[of I I "conj (interp_assert Q) (holds_forall (lnot b))" "interp_assert Q"]
  using completeness soundness while_forall_exists_simpler assms entail_conj_weaken entails_refl by metis

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>if_then b C\<close> is syntactic sugar for \<^term>\<open>If (Assume b;; C) (Assume (lnot b))\<close>.
\<^item> \<^term>\<open>no_forall_state_after_existential Q\<close> holds iff there is no universal state quantifier \<open>\<forall>\<langle>_\<rangle>\<close> after any \<open>\<exists>\<close> in Q.\<close>




subsection \<open>5.6.3: \<open>\<exists>*\<forall>*\<close>-Hyperproperties\<close>


paragraph \<open>Rule \<open>While-\<exists>\<close> from Figure 5.5\<close>

theorem while_loop_exists:
  assumes "wfP lt"
      and "\<And>v. \<turnstile> { (\<lambda>S. (\<exists>\<phi>\<in>S. e (snd \<phi>) = v \<and> b (snd \<phi>) \<and> P \<phi> S) \<and> F S) } if_then b C { (\<lambda>S. (\<exists>\<phi>\<in>S. lt (e (snd \<phi>)) v \<and> P \<phi> S) \<and> F S) }"
      and "\<And>\<phi>. \<turnstile> { conj (P \<phi>) F } while_cond b C { Q \<phi> }"
    shows "\<turnstile> { (\<lambda>S. (\<exists>\<phi>\<in>S. P \<phi> S) \<and> F S) } while_cond b C { (\<lambda>S. \<exists>\<phi>\<in>S. Q \<phi> S) }"
  apply (rule completeness)
  apply (rule exists_terminates_loop[OF assms(1)])
   apply (rule soundness)
  using assms(2) apply fast
   apply (rule soundness)
  using assms(3) by blast


text \<open>\<^term>\<open>wfP lt\<close> in this result ensures that the binary operator \<open>lt\<close> is well-founded.
\<open>e\<close> is a function of a program state, which must decrease after each iteration.
Note that this version is stronger than the one presented in the thesis, as it also allows to frame
some arbitrary hyperproperty F, which Hypra leverages. One can obtain the weaker version from the thesis
by setting F to true.\<close>






section \<open>5.7: Compositionality Rules\<close>



subsection \<open>5.7.1: Compositionality Rules\<close>


paragraph \<open>Figure 5.8: Compositionality rules of Hyper Hoare Logic.\<close>

proposition rule_Forall:
  assumes "\<And>x. \<turnstile> {P x} C {Q x}"
  shows "\<turnstile> {forall P} C {forall Q}"
  using assms soundness completeness rule_Forall by metis

proposition rule_Linking:
  assumes "\<And>\<phi>1 (\<phi>2 :: ('a, 'b, 'c, 'd) state). fst \<phi>1 = fst \<phi>2 \<and> ( \<turnstile> { (in_set \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { in_set \<phi>2 } )
  \<Longrightarrow> ( \<turnstile> { (P \<phi>1 :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { Q \<phi>2 } )"
  shows "\<turnstile> { ((\<lambda>S. \<forall>\<phi>1 \<in> S. P \<phi>1 S) :: (('a, 'b, 'c, 'd) state) hyperassertion) } C { (\<lambda>S. \<forall>\<phi>2 \<in> S. Q \<phi>2 S) }"
  using assms soundness completeness rule_linking by blast

proposition rule_IndexedUnion:
  assumes "\<And>x. \<turnstile> {P x} C {Q x}"
  shows "\<turnstile> {general_join P} C {general_join Q}"
  using assms soundness completeness rule_IndexedUnion by metis

proposition rule_Union:
  assumes "\<turnstile> {P} C {Q}"
      and "\<turnstile> {P'} C {Q'}"
    shows "\<turnstile> {join P P'} C {join Q Q'}"
  using assms soundness completeness rule_Union by metis

proposition rule_BigUnion:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  assumes "\<turnstile>  {P} C {Q}"
  shows "\<turnstile> {general_union P} C {general_union Q}"
  using assms soundness completeness rule_BigUnion by blast

proposition rule_And:
  assumes "\<turnstile> {P} C {Q}"
      and "\<turnstile> {P'} C {Q'}"
    shows "\<turnstile> {conj P P'} C {conj Q Q'}"
  using assms soundness completeness rule_And by metis

proposition rule_Or:
  assumes "\<turnstile> {P} C {Q}"
      and "\<turnstile> {P'} C {Q'}"
    shows "\<turnstile> {disj P P'} C {disj Q Q'}"
  using assms soundness completeness rule_Or by metis

proposition rule_AtMost:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<turnstile> {has_superset P} C {has_superset Q}"
  using assms soundness completeness rule_AtMost by blast

proposition rule_AtLeast:
  assumes "\<turnstile> {P} C {Q}"
  shows "\<turnstile> {has_subset P} C {has_subset Q}"
  using assms soundness completeness rule_AtLeast by blast

proposition rule_LUpdateSyntactic:
  assumes "\<turnstile> { (\<lambda>S. P S \<and> e_recorded_in_t e t S) } C { Q }"
      and "not_fv_hyper t P"
      and "not_fv_hyper t Q"
    shows "\<turnstile> { P } C { Q }"
  using LUpdateS soundness completeness assms by fast

text \<open>In the following, \<^term>\<open>entails_with_updates vars P P'\<close> and \<^term>\<open>invariant_on_updates vars Q\<close>
respectively correspond to the notions of entailments modulo logical variables and invariance with
respect to logical updates, as described in definition 5.7.1.\<close>

proposition rule_LUpdate:
  assumes "\<turnstile> {P'} C {Q}"
      and "entails_with_updates vars P P'"
      and "invariant_on_updates vars Q"
    shows "\<turnstile> {P} C {Q}"
  using assms soundness completeness rule_LUpdate by blast

proposition rule_True:
  "\<turnstile> {P} C {\<lambda>_. True}"
  using rule_True completeness by blast

proposition rule_False:
  "\<turnstile> { (\<lambda>_. False) } C {Q}"
  using rule_False completeness by blast

proposition rule_FrameSafe:
  assumes "wr C \<inter> fv F = {}"
      and "wf_assertion F"
      and "no_exists_state F"
    shows "\<turnstile> {interp_assert F} C {interp_assert F}"
  using safe_frame_rule_syntactic assms completeness by metis

proposition rule_Specialize:
  assumes "\<turnstile> {interp_assert P} C {interp_assert Q}"
      and "indep_of_set b"
      and "wf_assertion_aux 0 1 b"
      and "wr C \<inter> fv b = {}"
    shows "\<turnstile> { interp_assert (transform_assume b P) } C { interp_assert (transform_assume b Q) }"
  using filter_rule_syntactic assms soundness completeness by blast

proposition rule_Empty:
  "\<turnstile> { (\<lambda>S. S = {}) } C { (\<lambda>S. S = {}) }"
  using completeness rule_Empty by blast



paragraph \<open>Blue box: Framing for terminating hyper-triples\<close>

theorem rule_Frame:
  assumes "\<Turnstile>TERM {P} C {Q}"
      and "wr C \<inter> fv F = {}" (* free *program* variables *)
      and "wf_assertion F" (* No unbound free variable *)
    shows "\<Turnstile>TERM {conj P (interp_assert F)} C {conj Q (interp_assert F)}"
  using assms frame_rule_syntactic by blast



paragraph \<open>Definition 5.7.1: Logical updates.\<close>

text \<open>
\<^item> Two sets S1 and S2 are equivalent up to logical variables V: \<^term>\<open>same_mod_updates V S1 S2\<close>
\<^item> P entails P' modulo logical variables V: \<^term>\<open>entails_with_updates vars P P'\<close>
\<^item> P is invariant with respect to logical updates in V: \<^term>\<open>invariant_on_updates vars Q\<close>
\<close>




subsection \<open>5.7.2: Examples\<close>

paragraph \<open>Example 5.7.4 (Figure 5.9): Composing minimality and monotonicity.\<close>

text \<open>To see the actual proof, ctrl+click on @{thm composing_monotonicity_and_minimum}.\<close>

proposition composing_monotonicity_and_minimum:
  fixes P :: "((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)"
  fixes i :: 'a
  fixes x y :: 'c
  fixes leq :: "'d \<Rightarrow> 'd \<Rightarrow> bool"
  fixes one two :: 'b
  assumes "\<turnstile> { P } C1 { has_minimum x leq }"
      and "\<turnstile> { is_monotonic i x one two leq } C2 { is_monotonic i y one two leq }"
      and "\<turnstile> { (is_singleton :: ((('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set \<Rightarrow> bool)) } C2 { is_singleton }"
      and "one \<noteq> two" \<comment>\<open>We use distinct logical values \<open>one\<close> and \<open>two\<close> to represent 1 and 2.\<close>
      and "\<And>x. leq x x" \<comment>\<open>We assume that \<open>leq\<close> is a partial order, and thus that it satisfies reflexivity.\<close>
    shows "\<turnstile> { P } C1 ;; C2 { has_minimum y leq }"
  using assms soundness completeness composing_monotonicity_and_minimum by metis

paragraph \<open>Example 5.7.5 (Figure 5.10): Composing non-interference with generalized non-interference.\<close>

text \<open>To see the actual proof, ctrl+click on @{thm composing_GNI_with_SNI}.\<close>

proposition composing_GNI_with_SNI:
  fixes h :: 'lvar
  fixes l :: 'pvar
  assumes "\<turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { low l }"
      and "\<turnstile> { (not_empty :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C2 { not_empty }"
      and "\<turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1 { lGNI l h }"
    shows "\<turnstile> { (low l :: (('lvar, 'lval, 'pvar, 'pval) state) hyperassertion) } C1;; C2 { lGNI l h }"
  using assms soundness completeness composing_GNI_with_SNI by metis





section \<open>Chapter 6: Hypra\<close>


paragraph \<open>Theorem 6.4.1: Soundness of the novel loop rule for \<open>\<forall>*\<exists>*\<close>-hyperproperties\<close>

text \<open>This result uses the following constructs:
\<^item> \<^term>\<open>conj A B\<close> corresponds to the hyper-assertion \<open>A \<and> B\<close>.
\<^item> \<^term>\<open>sp_assume (lnot b \<circ> snd) [] [] I\<close> corresponds to \<open>\<Theta>\<^sub>\<not>\<^sub>b(I)\<close>.
\<^item> \<^term>\<open>holds_forall b\<close> corresponds to \<open>box(b)\<close>.\<close>

theorem WhileAutoForallExists:
  assumes "\<Turnstile> {interp_assert I} if_then b C {interp_assert I}"
      and "no_forall_state_after_existential I"
    shows "\<Turnstile> {interp_assert I} while_cond b C { conj (sp_assume (lnot b \<circ> snd) [] [] I) (holds_forall (lnot b)) }"
  using while_general_auto assms by auto

paragraph \<open>Lemma 6.4.2: Soundness of the framing encoding.\<close>

text \<open>In the formalization, states have a logical part (omitted in the paper) as well as a program part.
Our lemma below expresses equality of the logical parts (\<^term>\<open>fst \<sigma>\<close>), and equality of non-modified variables
for the program part (\<^term>\<open>snd \<sigma>\<close>).\<close>

lemma sound_framing_over:
  "\<forall>\<sigma>' \<in> sem C S. \<exists>\<sigma> \<in> S. (\<forall>x. x \<notin> wr C \<longrightarrow> snd \<sigma> x = snd \<sigma>' x) \<and> fst \<sigma> = fst \<sigma>'"
  using sound_framing_over by blast





section \<open>A.3: Expressiveness of Hyper Triples\<close>

text \<open>The results for expressiveness are in the file @{file "HyperHoareLogic/Expressivity.thy"}}\<close>

subsection \<open>A.3.1: Overapproximate Hoare Logics\<close>



paragraph \<open>Definition A.3.1: Hoare Logic (HL) - \<^term>\<open>HL P C Q\<close>\<close>


paragraph \<open>Proposition A.3.1: HL triples express hyperproperties\<close>

proposition HL_expresses_hyperproperties:
  "\<exists>H. (\<forall>C. hypersat C H \<longleftrightarrow> HL P C Q)"
  using HL_expresses_hyperproperties by blast


paragraph \<open>Proposition A.3.2: Expressing HL in Hyper Hoare Logic\<close>

proposition expressing_HL_in_HHL:
  "HL P C Q \<longleftrightarrow> (hyper_hoare_triple (over_approx P) C (over_approx Q))"
  using encoding_HL by auto


paragraph \<open>Definition A.3.2: Big-step semantics for k executions - \<^term>\<open>k_sem C \<sigma>s \<sigma>s'\<close>\<close>


paragraph \<open>Definition A.3.3: Cartesian Hoare Logic (CHL) - \<^term>\<open>CHL P C Q\<close>\<close>


paragraph \<open>Proposition A.3.3: CHL triples express hyperproperties\<close>

proposition CHL_is_hyperproperty:
  "hypersat C (CHL_hyperprop P Q) \<longleftrightarrow> CHL P C Q"
  using CHL_hyperproperty by fast

paragraph \<open>Proposition A.3.4: Expressing CHL in Hyper Hoare Logic\<close>

proposition encoding_CHL_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "CHL P C Q \<longleftrightarrow> \<Turnstile> {encode_CHL from_nat x P} C {encode_CHL from_nat x Q}"
  using encoding_CHL assms by fast

text \<open>The function \<open>from_nat\<close> gives us a way to encode numbers from 1 to k as logical values.
Moreover, note that we represent k-tuples implicitly, as mappings of type \<^typ>\<open>'a \<Rightarrow> 'b\<close>: When the type
\<open>'a\<close> has k elements, a function of type \<^typ>\<open>'a \<Rightarrow> 'b\<close> corresponds to a k-tuple of elements of type 'b.
This representation is more convenient to work with, and more general, since it also captures infinite sequences.\<close>



subsection \<open>Appendix C.2: Underapproximate Hoare Logics\<close>



paragraph \<open>Definition A.3.4 (Incorrectness Logic): \<^term>\<open>IL P C Q\<close>.\<close>


paragraph \<open>Proposition A.3.5: IL triples express hyperproperties\<close>

proposition IL_hyperproperties:
  "IL P C Q \<longleftrightarrow> IL_hyperprop P Q (set_of_traces C)"
  using IL_expresses_hyperproperties by fast

paragraph \<open>Proposition A.3.6: Expressing IL in Hyper Hoare Logic\<close>

proposition expressing_IL_in_HHL:
  "IL P C Q \<longleftrightarrow> (hyper_hoare_triple (under_approx P) C (under_approx Q))"
  using encoding_IL by fast



paragraph \<open>Definition A.3.5 (k-Incorrectness Logic): \<^term>\<open>RIL P C Q\<close>.\<close>

text \<open>RIL is the old name of k-IL.\<close>


paragraph \<open>Proposition A.3.7: k-IL triples express hyperproperties\<close>

proposition kIL_hyperproperties:
  "hypersat C (RIL_hyperprop P Q) \<longleftrightarrow> RIL P C Q"
  using RIL_expresses_hyperproperties by fast

paragraph \<open>Proposition A.3.8: Expressing k-IL in Hyper Hoare Logic\<close>

proposition expressing_kIL_in_HHL:
  fixes x :: "'lvar"
  assumes "\<And>l l' \<sigma>. (\<lambda>i. (l i, \<sigma> i)) \<in> P \<longleftrightarrow> (\<lambda>i. (l' i, \<sigma> i)) \<in> P"  (* P does not depend on logical variables *)
      and "injective (indexify :: (('a \<Rightarrow> ('pvar \<Rightarrow> 'pval)) \<Rightarrow> 'lval))" (* |lval| \<ge> |PStates^k| *)
      and "c \<noteq> x"
      and "injective from_nat"
      and "not_free_var_of (P :: ('a \<Rightarrow> ('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set) x \<and> not_free_var_of P c"
      and "not_free_var_of Q x \<and> not_free_var_of Q c"
    shows "RIL P C Q \<longleftrightarrow> \<Turnstile> {pre_insec from_nat x c P} C {post_insec from_nat x c Q}"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by (rule encoding_RIL)




paragraph \<open>Definition A.3.6 (Sufficient Incorrectness Logic): \<^term>\<open>FU P C Q\<close>.\<close>

proposition FU_hyperproperties:
  "hypersat C (hyperprop_FU P Q) \<longleftrightarrow> FU P C Q"
  by (rule FU_expresses_hyperproperties)

paragraph \<open>Proposition A.3.9: Expressing SIL in Hyper Hoare Logic\<close>


proposition expressing_SIL_in_HHL:
  "FU P C Q \<longleftrightarrow> \<Turnstile> {encode_FU P} C {encode_FU Q}"
  by (rule encoding_FU)



paragraph \<open>Definition A.3.7 (k-Forward Underapproximation): \<^term>\<open>RFU P C Q\<close>.\<close>

text \<open>RFU is the old name of k-FU.\<close>

paragraph \<open>Proposition A.3.10: k-FU triples express hyperproperties\<close>

proposition kFU_expresses_hyperproperties:
  "hypersat C (RFU_hyperprop P Q) \<longleftrightarrow> RFU P C Q"
  by (rule RFU_captures_hyperproperties)



paragraph \<open>Proposition A.3.11: Expressing k-FU in Hyper Hoare Logic\<close>

proposition encode_kFU_in_HHL:
  assumes "not_free_var_of P x"
      and "not_free_var_of Q x"
      and "injective from_nat"
    shows "RFU P C Q \<longleftrightarrow> \<Turnstile> {encode_RFU from_nat x P} C {encode_RFU from_nat x Q}"
  using assms
  by (rule encode_RFU)



subsection \<open>Appendix C.3: Beyond Over- and Underapproximation\<close>


paragraph \<open>Definition A.3.8 (k-Universal Existential): \<^term>\<open>RUE P C Q\<close>.\<close>

text \<open>Note that RUE is the old name of k-UE.\<close>


paragraph \<open>Proposition A.3.12: k-UE triples express hyperproperties\<close>

proposition kUE_expresses_hyperproperty:
  "RUE P C Q \<longleftrightarrow> hypersat C (hyperprop_RUE P Q)"
  by (rule RUE_express_hyperproperties)



paragraph \<open>Proposition A.3.13: Expressing k-UE in Hyper Hoare Logic\<close>

proposition expressing_kUE_in_HHL:
  assumes "injective fn \<and> injective fn1 \<and> injective fn2"
      and "t \<noteq> x"
      and "injective (fn :: nat \<Rightarrow> 'a)"
      and "injective fn1"
      and "injective fn2"
      and "not_in_free_vars_double {x, t} P"
      and "not_in_free_vars_double {x, t} Q"
  shows "RUE P C Q \<longleftrightarrow> \<Turnstile> {encode_RUE_1 fn fn1 fn2 x t P} C {encode_RUE_2 fn fn1 fn2 x t Q}"
  using assms by (rule encoding_RUE)


paragraph \<open>Example A.3.2: Expressing program refinement in Hyper Hoare Logic.\<close>

proposition proving_refinement:
  fixes P :: "(('lvar \<Rightarrow> 'lval) \<times> ('pvar \<Rightarrow> 'pval)) set \<Rightarrow> bool"
    and t :: 'pvar
  assumes "(one :: 'pval) \<noteq> two" \<comment>\<open>We assume two distinct program values \<open>one\<close> and \<open>two\<close>, to represent 1 and 2.\<close>
      and "P = (\<lambda>S. card S = 1)"
      and "Q = (\<lambda>S. \<forall>\<phi>\<in>S. snd \<phi> t = two \<longrightarrow> (fst \<phi>, (snd \<phi>)(t := one)) \<in> S)"
      and "not_free_var_stmt t C1"
      and "not_free_var_stmt t C2"
  shows "refinement C2 C1 \<longleftrightarrow>
  \<Turnstile> { P } If (Seq (Assign t (\<lambda>_. one)) C1) (Seq (Assign t (\<lambda>_. two)) C2) { Q }"
proof -
  have "refinement C2 C1 \<longleftrightarrow> \<Turnstile> { P } If (Seq (Assign t (\<lambda>_. two)) C2) (Seq (Assign t (\<lambda>_. one)) C1) { Q }"
    using encoding_refinement[of two one P Q t C2 C1] assms by blast
  then show ?thesis using rewrite_if_commute by blast
qed


end