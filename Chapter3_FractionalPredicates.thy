theory Chapter3_FractionalPredicates
  imports
    "Fractions/CSL_IDF_Unbounded"
    "Fractions/AutomaticVerifiers"
begin

text \<open>The following Isabelle theory file contains references to all the formalised results explicitly
mentioned in chapter 3 of the thesis. The theory file is structured using Isabelle sections and subsections,
which match those from the thesis. Within each subsection we structured the different parts that we 
show via Isabelle paragraphs.\<close>

section \<open>3.2: Unbounded Separation Logic\<close>

subsection \<open>3.2.2. State Model and Multiplication\<close>

paragraph \<open>Definition 3.2.1: Partial commutative monoid\<close>

text \<open>For our partial commutative monoid, we reuse the class \<^class>\<open>pre_pcm\<close> from the IDF algebra:
\<^item> \<^term>\<open>\<sigma> \<oplus> \<sigma>'\<close>: addition of states \<sigma> and \<sigma>'.
\<^item> \<^term>\<open>\<sigma> ## \<sigma>'\<close>: the addition \<^term>\<open>\<sigma> \<oplus> \<sigma>'\<close> is defined.
\<^item> \<^term>\<open>\<sigma>' \<succeq> \<sigma>\<close>: \<sigma>' is greater than \<sigma>.
\<close>

paragraph \<open>Definitions 3.2.2 and 3.2.3: Semifield of scalars and left module\<close>

text \<open>The definitions 3.2.2 and 3.2.3 are formalized via the parametric theory \<^locale>\<open>left_module\<close>.\<close>

context left_module
begin

text \<open>The locale has the following parameters:
\<^item> 'b: corresponds to the set S (semifield of scalars).
  \<^item> The first 6 assumptions of the locale correspond to the axioms from Definition 3.2.2.
\<^item> 'a (of \<^class>\<open>pre_pcm\<close>): corresponds to the set \<Sigma>.
  \<^item> The next 4 assumptions of the locale correspond to the axioms from Definition 3.2.3.
\<^item> \<^term>\<open>\<alpha> \<odot> \<sigma>\<close>: multiplication between a scalar \<alpha> and state \<sigma> (parameter \term\<open>mult\<close>).
\<^item> \<^term>\<open>sadd \<alpha> \<beta>\<close>: addition between scalars.
\<^item> \<^term>\<open>smult \<alpha> \<beta>\<close>: multiplication between scalars.
\<^item> \<^term>\<open>sinv \<alpha>\<close>: mutiplicative inverse for a scalar.
\<^item> \<^term>\<open>one\<close>: scalar 1.
\<^item> \<^term>\<open>valid \<sigma>\<close>: expresses that the state \<sigma> is bounded.

\<^term>\<open>sat\<close>
\<close>

subsection \<open>3.2.3: Assertions\<close>

paragraph \<open>Assertion language\<close>

text \<open>Syntactic assertions are represented by the type \<^typ>\<open>('a, 'b, 'val, 'var) UnboundedLogic.assertion\<close>, where:
\<^item> \<^typ>\<open>'a\<close> is the type of states.
\<^item> \<^typ>\<open>'b\<close> is the type of scalars.
\<^item> \<^typ>\<open>'val\<close> and \<^typ>\<open>'var\<close> represent the type of values and variables, respectively.
\<close>

paragraph \<open>Figure 3.3: Meaning of unbounded SL assertions.\<close>

text \<open>The semantics of unbounded SL assertion is defined as \<^term>\<open>\<sigma>, s, \<Delta> \<Turnstile> A\<close> (function \<^term>\<open>sat\<close>),
where \<sigma> is a state, s is a store mapping local variables to values, \<Delta> an interpretation context
(of type \<^typ>\<open>('var, 'val, 'a) interp\<close>), and A an assertion.\<close>


subsection \<open>3.2.4: Distributivity and Factorizability\<close>

paragraph \<open>Figure 3.4 and Theorem 3.2.1: Distributivity and factorizability in the unbounded logic.\<close>

text \<open>Below we show that all rules from Figure 3.4 hold, in the same order as the figure.
Note that \<^term>\<open>A, \<Delta> \<turnstile> B\<close> means that A entails B on a semantic level, and that
\<^term>\<open>A, \<Delta> \<equiv> B\<close> represents semantic equivalence.\<close>

proposition DotDot:
  "Mult p (Mult q A), \<Delta> \<equiv> Mult (smult p q) A"
  by (simp add: dot_mult1 dot_mult2 equivalent_def)

proposition DotFull:
  "Mult one A, \<Delta> \<equiv> A"
  using equivalent_def mult_one_same1 mult_one_same2 by blast

proposition DotStar:
  "Mult p (Star A B), \<Delta> \<equiv> Star (Mult p A) (Mult p B)"
  by (simp add: dot_star1 dot_star2 equivalent_def)

proposition DotWand:
  "Mult p (Wand A B), \<Delta> \<equiv> Wand (Mult p A) (Mult p B)"
  by (simp add: dot_wand1 dot_wand2 equivalent_def)

proposition DotImp:
  "Mult p (Imp A B), \<Delta> \<equiv> Imp (Mult p A) (Mult p B)"
  by (simp add: dot_imp1 dot_imp2 equivalent_def)

proposition DotPos:
  "A, \<Delta> \<turnstile> B \<longleftrightarrow> (Mult \<pi> A, \<Delta> \<turnstile> Mult \<pi> B)"
  by (simp add: DotPos)

proposition DotExists:
  "Mult p (Exists x A), \<Delta> \<equiv> Exists x (Mult p A)"
  by (simp add: dot_exists1 dot_exists2 equivalent_def)

proposition DotForall:
  "Mult p (Forall x A), \<Delta> \<equiv> Forall x (Mult p A)"
  by (simp add: dot_forall1 dot_forall2 equivalent_def)

proposition DotAnd:
  "And (Mult p A) (Mult p B), \<Delta> \<equiv> Mult p (And A B)"
  by (simp add: dot_and1 dot_and2 equivalent_def)

proposition DotOr:
  "Mult p (Or A B), \<Delta> \<equiv> Or (Mult p A) (Mult p B)"
  by (simp add: dot_or1 dot_or2 equivalent_def)

proposition DotWild:
  "Wildcard (Mult p A), \<Delta> \<equiv> Wildcard A \<and> Mult p (Wildcard A), \<Delta> \<equiv> Wildcard A"
  using WildDot DotWild by blast

proposition Split:
  "Mult (sadd a b) A, \<Delta> \<turnstile> Star (Mult a A) (Mult b A)"
  using split by blast

proposition Combine:
  assumes "combinable \<Delta> A"
  shows "Star (Mult a A) (Mult b A), \<Delta> \<turnstile> Mult (sadd a b) A"
  using assms combinable_def by blast

proposition DotPure: 
  assumes "pure A"
  shows "Mult p A, \<Delta> \<equiv> A"
  by (simp add: assms equivalent_def pure_mult1 pure_mult2)



paragraph \<open>Additional rules for wildcard assertions.\<close>

proposition WildPos:
  "A, \<Delta> \<turnstile> B \<Longrightarrow> (Wildcard A, \<Delta> \<turnstile> Wildcard B)"
  by (metis (no_types, lifting) entails_def sat.simps(12))

proposition WildWild:
  "Wildcard (Wildcard A), \<Delta> \<equiv> Wildcard A"
  using WildWild by blast

proposition WildStar1:
  "Wildcard (Star A B), \<Delta> \<turnstile> Star (Wildcard A) (Wildcard B)"
  using WildStar1 by blast

proposition WildOr:
  "Wildcard (Or A B), \<Delta> \<equiv> Or (Wildcard A) (Wildcard B)"
  using WildOr by blast

proposition WildAnd:
  "Wildcard (And A B), \<Delta> \<turnstile> And (Wildcard A) (Wildcard B)"
  using entails_def by fastforce

proposition WildPure: 
  assumes "pure A"
  shows "Wildcard A, \<Delta> \<equiv> A"
  using WildPure assms by blast

proposition WildExists:
  "Wildcard (Exists x A), \<Delta> \<equiv> Exists x (Wildcard A)"
  using WildExists by fast

proposition WildForall:
  "Wildcard (Forall x A), \<Delta> \<turnstile> Forall x (Wildcard A)"
  by (metis (no_types, lifting) entailsI sat.simps(12) sat.simps(9))




subsection \<open>3.2.5: Reimposing Boundedness in CSL Triples\<close>

paragraph \<open>Definition 3.2.4: Validity of CSL triples in the unbounded logic.\<close>

text \<open>The state model \<Sigma> corresponds to the type \<^typ>\<open>'a virtual_state\<close>, where the type parameter 'a
is a special user-defined type of values.
The type of states with stores is \<^typ>\<open>'a equi_state\<close>.

The safety predicate is \<^term>\<open>safe n C s \<omega> Q\<close>.

Validity of CSL triples is defined as \<^term>\<open>CSL P C Q\<close>.
\<close>


paragraph \<open>Soundness and adequacy of unbounded CSL.\<close>

text \<open>The rules of the unbounded CSL are given by \<^term>\<open>\<turnstile>CSL [P] C [Q]\<close>.\<close>

theorem soundness_unbounded_CSL:
  assumes "\<turnstile>CSL [P] C [Q]"
    shows "CSL P C Q"
  using assms CSL_sound by auto

theorem adequacy_unbounded_CSL:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "\<turnstile>CSL [assertify_state_exp P] C [assertify_state_exp Q]"
      and "P \<sigma>"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  using adequacy assms by blast


paragraph \<open>Proposition 3.2.2: Bounded consequence rule.\<close>

proposition bounded_consequence_rule:
  assumes "CSL P C Q"
      and "\<And>\<omega>. bounded (snd \<omega>) \<Longrightarrow> \<omega> \<in> P' \<Longrightarrow> \<omega> \<in> P"
      and "\<And>\<omega>. bounded (snd \<omega>) \<Longrightarrow> \<omega> \<in> Q \<Longrightarrow> \<omega> \<in> Q'"
    shows "CSL P' C Q'"
  using assms rule_conseq_stronger
  by (smt (verit, best) snd_conv)



paragraph \<open>Instantiation of the left module interface.\<close>

text \<open>To ensure that the state model we use in Section 3.2.5, we show that it satisfies
all axioms from 3.2.2, by providing the following interpretation of the locale, where
the multiplication is defined between positive real \<^typ>\<open>ppreal\<close> and \<^typ>\<open>'a virtual_state\<close>
as \<^term>\<open>mult_virtual_state \<alpha> \<omega>\<close>.\<close>

interpretation unbounded_logic: left_module mult_virtual_state mult_preal add_preal inv_preal one_preal bounded
  apply standard
apply (metis CSL_IDF_Unbounded.one_preal_def Rep_ppreal Rep_ppreal_inverse inv_preal.rep_eq mem_Collect_eq
      mult_preal.rep_eq pos_perm_class.pinv_pmult_ok)
  apply (metis CSL_IDF_Unbounded.one_preal.rep_eq Rep_ppreal_inject mult_1 mult_preal.rep_eq)
  apply (metis Rep_ppreal_inject add.commute add_preal.rep_eq)
  apply (metis Rep_ppreal_inject mult.commute mult_preal.rep_eq)
  apply (metis PosReal.pmult_distr Rep_ppreal_inject add_preal.rep_eq mult_preal.rep_eq)
 apply (metis ab_semigroup_mult_class.mult_ac(1) mult_preal.rep_eq type_definition.Rep_inject
      type_definition_ppreal)
  unfolding mult_virtual_state_def
  using aux1 apply blast
  using aux3 apply blast
  using aux2 apply blast
  apply (rule ext; simp add: CSL_IDF_Unbounded.one_preal.rep_eq option.map_ident)
  using bounded_smaller by blast




section \<open>3.3: Combinable Assertions\<close>


paragraph \<open>Definition 3.3.1: Combinable assertions.\<close>

text \<open>Combinable assertions correspond to the predicate \<^term>\<open>combinable \<Delta> A\<close>.\<close>


paragraph \<open>Theorem 3.3.1: Soundness of the combinability rules from Figure 3.5.\<close>

text \<open>Each proposition below corresponds to the soundness of one rule from Figure 3.5,
following the order from the figure.\<close>

proposition combinable_star:
  assumes "combinable \<Delta> A"
      and "combinable \<Delta> B"
    shows "combinable \<Delta> (Star A B)"
  using combinable_star assms by blast

proposition combinable_wand:
  assumes "combinable \<Delta> B"
    shows "combinable \<Delta> (Wand A B)"
  using combinable_wand assms by blast

proposition combinable_mult:
  assumes "combinable \<Delta> A"
  shows "combinable \<Delta> (Mult \<pi> A)"
  using combinable_mult assms by blast

proposition combinable_wildcard:
  assumes "combinable \<Delta> A"
  shows "combinable \<Delta> (Wildcard A)"
  using combinable_wildcard assms by fast

proposition combinable_imp:
  assumes "pure A"
    and "combinable \<Delta> B"
  shows "combinable \<Delta> (Imp A B)"
  using combinable_imp assms by fast

proposition combinable_and:
  assumes "combinable \<Delta> A"
      and "combinable \<Delta> B"
    shows "combinable \<Delta> (And A B)"
  using combinable_and assms by blast

proposition combinable_disj_1:
  assumes "pure A \<and> combinable \<Delta> B"
  shows "combinable \<Delta> (Or A B)"
  using combinable_disj_aux_1 assms by fast

proposition combinable_disj_2:
  assumes "pure B \<and> combinable \<Delta> A"
  shows "combinable \<Delta> (Or A B)"
  using combinable_disj_aux_2 assms by fast

proposition combinable_exists:
  assumes "combinable \<Delta> A"
      and "unambiguous \<Delta> A x"
    shows "combinable \<Delta> (Exists x A)"
  using combinable_exists assms by fast

proposition combinable_forall:
  assumes "combinable \<Delta> A"
    shows "combinable \<Delta> (Forall x A)"
  using combinable_forall assms by fast

proposition combinable_pure:
  assumes "pure A"
  shows "combinable \<Delta> A"
  using combinable_pure assms by fast



section \<open>3.4. Combinable (Co)Inductive Predicates\<close>



subsection \<open>3.4.1: Preliminaries: Monotonic Functions and Existence of Fixed Points\<close>

paragraph \<open>Definition 3.4.1: Interpretation context.\<close>

text \<open>The type of interpretation contexts is \<^typ>\<open>('var, 'val, 'a) interp\<close>, where
'var is the type of variables, 'val of values, and 'a the type of states (from \<Sigma>).

\<^term>\<open>smaller_interp \<Delta> \<Delta>'\<close> corresponds to a context smaller than another.\<close>



paragraph \<open>Lemma 3.4.1: Interpretation contexts form a complete lattice.\<close>

text \<open>This interpretation is shown below, by interpreting the Isabelle class \<^class>\<open>complete_lattice\<close>.\<close>

interpretation complete_lattice Inf Sup inf smaller_interp less sup empty_interp full_interp
  apply standard
  apply (metis less_def smaller_interp_antisym)
  apply (simp add: smaller_interp_refl)
  using smaller_interp_trans apply blast
  using smaller_interp_antisym apply blast
  apply (simp add: inf_def smaller_interp_def)
  apply (simp add: inf_def smaller_interp_def)
  apply (simp add: inf_def smaller_interp_def)
  apply (simp add: smaller_interpI sup_def)
  apply (simp add: smaller_interpI sup_def)
  apply (simp add: smaller_interp_def sup_def)
  apply (metis (mono_tags, lifting) CollectD Inf_def smaller_interpI)
  using test_axiom_inf apply blast
  apply (metis (mono_tags, lifting) CollectI Sup_def smaller_interpI)
  using test_axiom_sup apply auto[1]
  apply (simp add: inf_empty)
  by (simp add: sup_empty)



paragraph \<open>Definition 3.4.2: Non-decreasing function.\<close>

text \<open>Non-decreasing functions f correspond to \<^term>\<open>monotonic f\<close>.\<close>


paragraph \<open>Theorem 3.4.2: Knaster-Tarski fixed point construction.\<close>

text \<open>The least fixed point LFP of a function f is defined as \<^term>\<open>LFP f\<close>.
The greatest fixed point GFP of a function f is defined as \<^term>\<open>GFP f\<close>.
The following theorems show that LFP is indeed the least fixed point, and that
GFP is indeed the greatest fixed point.\<close>


theorem GFP_is_fixed_point:
  assumes "monotonic f"
  shows "f (GFP f) = GFP f"
  using GFP_is_FP assms by blast

theorem GFP_is_greatest:
  assumes "f u = u"
  shows "smaller_interp u (GFP f)"
  using GFP_greatest assms by blast

theorem LFP_is_fixed_point:
  assumes "monotonic f"
  shows "f (LFP f) = LFP f"
  using LFP_is_FP assms by blast

theorem LFP_is_least:
  assumes "f u = u"
  shows "smaller_interp (LFP f) u"
  using LFP_least assms by blast




subsection \<open>3.4.2: An Induction Principle for (Co)Inductive Predicates and Set-Closure Properties\<close>


paragraph \<open>Definition 3.4.3: Empty interpretation, full interpretation, transfinite recursion.\<close>

text \<open>
\<^item> Empty interpretation: \<^term>\<open>empty_interp\<close>
\<^item> Full interpretation: \<^term>\<open>full_interp\<close>
\<^item> Transfinite iterations: defined in \<^term>\<open>ccpo.iterates f\<close>
\<close>

paragraph \<open>Definition 3.4.4: Set-closure property.\<close>

text \<open>A predicate P is a set closure property iff it corresponds to \<^term>\<open>set_closure_property M\<close> for some M.\<close>



paragraph \<open>Example 3.4.1: Combinability is a set-closure property.\<close>

proposition combinable_set_closure:
  "sem_combinable = set_closure_property (\<lambda>a b. { \<sigma> |\<sigma> p q. sadd p q = one \<and> Some \<sigma> = p \<odot> a \<oplus> q \<odot> b})"
  using combinable_set_closure by blast


paragraph \<open>Example 3.4.2: Affinity is a set-closure property.\<close>

text \<open>In the following, \<^term>\<open>sem_intui\<close> corresponds to affinity.\<close>

proposition intuitionistic_set_closure:
  "sem_intui = set_closure_property (\<lambda>a b. { \<sigma> |\<sigma>. \<sigma> \<succeq> a})"
  using intuitionistic_set_closure by blast



paragraph \<open>Theorem 3.4.3: Induction principle for set-closure properties.\<close>

theorem induction_principle_set_closure_properties:
  assumes "monotonic f"
      and "P = set_closure_property M"
      and "\<And>\<Delta>. P \<Delta> \<Longrightarrow> P (f \<Delta>)"
    shows "P (GFP f)"
      and "P (LFP f)"
  using assms FP_preserves_set_closure_property by blast+




section \<open>3.5: Formal Foundations for Fractional Predicates and Magic Wands in Automatic SL Verifiers\<close>


subsection \<open>3.5.1: Syntactic Multiplication and Fractional Magic Wands\<close>



paragraph \<open>Figure 3.6: Definition of the syntactic multiplication over assertions.\<close>

text \<open>\<pi> \<odot> A corresponds to \<^term>\<open>syn_mult \<pi> A\<close>.\<close>




paragraph \<open>Theorem 3.5.1: Equivalence of the syntactic and semantic multiplication in the unbounded logic.\<close>

proposition equivalence_syntactic_semantic:
  "\<sigma>, s, \<Delta> \<Turnstile> syn_mult \<pi> A \<longleftrightarrow> \<sigma>, s, \<Delta> \<Turnstile> Mult \<pi> A"
  using syn_sen_mult_same by blast


paragraph \<open>Proposition 3.5.2: Rules for applying and packaging fractional wands.\<close>

proposition PackageWand:
  assumes "Star F (syn_mult \<pi> A), \<Delta> \<turnstile> syn_mult \<pi> B"
  shows "F, \<Delta> \<turnstile> Mult \<pi> (Wand A B)"
  using package_wand assms by blast

proposition ApplyWand:
  "Star (syn_mult \<pi> A) (Mult \<pi> (Wand A B)), \<Delta> \<turnstile> syn_mult \<pi> B"
  using apply_wand by blast



paragraph \<open>Figure 3.8 (left): Syntactic condition to ensure the existence of a least and greatest fixed point.\<close>

text \<open>correctRec b of A is represented by \<^term>\<open>pos_neg_rec_call True A\<close>.\<close>



paragraph \<open>Figure 3.8 (right): Syntactic condition to ensure that an assertion is combinable.\<close>

text \<open>comb(A) is represented by \<^term>\<open>wf_assertion A\<close>.\<close>




subsection \<open>3.5.2: Folding and Unfolding Fractions of Recursively-Defined Predicates\<close>



paragraph \<open>Lemma 3.5.3: Correct fixed point interpretation.\<close>

theorem exists_lfp_gfp:
  assumes "pos_neg_rec_call True A"
  shows "\<sigma>, s, LFP (applies_eq A) \<Turnstile> A \<longleftrightarrow> \<sigma> \<in> LFP (applies_eq A) s"
    and "\<sigma>, s, GFP (applies_eq A) \<Turnstile> A \<longleftrightarrow> \<sigma> \<in> GFP (applies_eq A) s"
  using exists_lfp_gfp assms by blast+


paragraph \<open>Proposition 3.5.4: Rules for folding and unfolding fractional predicates.\<close>

theorem FoldLFP:
  assumes "pos_neg_rec_call True A"
    shows "syn_mult \<pi> A, LFP (applies_eq A) \<turnstile> Mult \<pi> Pred"
  by (simp add: assms entails_def exists_lfp_gfp(1) syn_sen_mult_same)

theorem UnfoldLFP:
  assumes "pos_neg_rec_call True A"
    shows "Mult \<pi> Pred, LFP (applies_eq A) \<turnstile> syn_mult \<pi> A"
  by (simp add: assms entails_def exists_lfp_gfp(1) syn_sen_mult_same)

theorem FoldGFP:
  assumes "pos_neg_rec_call True A"
    shows "syn_mult \<pi> A, GFP (applies_eq A) \<turnstile> Mult \<pi> Pred"
  by (simp add: assms entails_def exists_lfp_gfp(2) syn_sen_mult_same)

theorem UnfoldGFP:
  assumes "pos_neg_rec_call True A"
    shows "Mult \<pi> Pred, GFP (applies_eq A) \<turnstile> syn_mult \<pi> A"
  by (simp add: assms entails_def exists_lfp_gfp(2) syn_sen_mult_same)


paragraph \<open>Proposition 3.5.5: Rule for combining fractions of the same predicates.\<close>


theorem CombineFractions:
  assumes "wf_assertion A"
      and "pos_neg_rec_call True A"
    shows "Star (Mult \<alpha> Pred) (Mult \<beta> Pred), LFP (applies_eq A) \<turnstile> Mult (sadd \<alpha> \<beta>) Pred"
    and "Star (Mult \<alpha> Pred) (Mult \<beta> Pred), GFP (applies_eq A) \<turnstile> Mult (sadd \<alpha> \<beta>) Pred"
  using assms wf_combine by blast+



end