theory CombinableWands
  imports PartialHeapSA "../CoreIVL/SepLogic"
begin

section \<open>Definitions\<close>

type_synonym sem_assertion = "state set"

fun multiply :: "prat \<Rightarrow> state \<Rightarrow> state" where
  "multiply p \<phi> = Abs_state (multiply_mask p (get_m \<phi>), get_h \<phi>)"

fun multiply_sem_assertion :: "prat \<Rightarrow> sem_assertion \<Rightarrow> sem_assertion" where
  "multiply_sem_assertion p P = upper_closure (multiply p ` P)"

definition combinable :: "sem_assertion \<Rightarrow> bool" where
  "combinable P \<longleftrightarrow> (\<forall>\<alpha> \<beta>. \<alpha> > 0 \<and> \<beta> > 0 \<and> 1 \<ge> (\<alpha> + \<beta>) \<longrightarrow> ((multiply_sem_assertion \<alpha> P) \<otimes> (multiply_sem_assertion \<beta> P)) \<subseteq> multiply_sem_assertion (\<alpha> + \<beta>) P)"

definition scaled where
  "scaled \<phi> = { multiply p \<phi> |p. p > 0 \<and> 1 \<ge> p }"

definition comp_min_mask :: "mask \<Rightarrow> (mask \<Rightarrow> mask)" where
  "comp_min_mask b a hl = inf (a hl) (1 - (b hl))"

definition half_scalable where
  "half_scalable w a \<longleftrightarrow> (\<forall>\<phi> \<in> scaled w. \<not> a ## \<phi>)"

definition R where
  "R a w = (if half_scalable w a then w else Abs_state (comp_min_mask (get_m a) (get_m w), get_h w))"

definition cwand where
  "cwand A B = { w |w. \<forall>a x. a \<in> A \<and> Some x = R a w \<oplus> a \<longrightarrow> x \<in> B }"

definition binary_mask :: "mask \<Rightarrow> mask" where
  "binary_mask \<pi> l = (if \<pi> l = 1 then 1 else 0)"

definition binary :: "sem_assertion \<Rightarrow> bool" where
  "binary A \<longleftrightarrow> (\<forall>\<phi> \<in> A. Abs_state (binary_mask (get_m \<phi>), get_h \<phi>) \<in> A)"




section Lemmas


lemma wand_equiv_def:
  "wand A B = { \<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B }"
proof
  show "wand A B \<subseteq> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}"
  proof
    fix w assume "w \<in> wand A B"
    have "A \<otimes> {w} \<subseteq> B"
    proof
      fix x assume "x \<in> A \<otimes> {w}"
      then show "x \<in> B"
        using add_set_elem \<open>w \<in> wand A B\<close> commutative wand_def
        by (smt (verit, ccfv_SIG) mem_Collect_eq singletonD)
    qed
    then show "w \<in> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}"
      by simp
  qed
  show "{\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B} \<subseteq> wand A B"
  proof
    fix w assume "w \<in> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}"
    have "\<And>a x. a \<in> A \<and> Some x = w \<oplus> a \<Longrightarrow> x \<in> B"
    proof -
      fix a x assume "a \<in> A \<and> Some x = w \<oplus> a"
      then have "x \<in> A \<otimes> {w}"
        using add_set_commm is_in_set_sum by blast
      then show "x \<in> B"
        using \<open>w \<in> {\<phi> |\<phi>. A \<otimes> {\<phi>} \<subseteq> B}\<close> by blast
    qed
    then show "w \<in> wand A B"
      unfolding wand_def
      using pre_pcm_class.commutative by force
  qed
qed

lemma w_in_scaled:
  "w \<in> scaled w"
proof -
  have "multiply 1 w = w"
    by (simp add: Rep_state_inverse mult_write_mask)
  then show ?thesis
    by (smt (verit, best) PosRat.pmin_is PosRat.sum_larger add_0 inf_le1 less_le mem_Collect_eq nle_le scaled_def zero_neq_one)
qed

lemma non_half_scalable_instantiate:
  assumes "\<not> half_scalable w a"
  shows "\<exists>p. p > 0 \<and> 1 \<ge> p \<and> a ## multiply p w"
  using assms half_scalable_def scaled_def by auto

lemma compatible_same_mask:
  assumes "valid_mask (add_masks a w)"
  shows "w = comp_min_mask a w"
proof (rule ext)
  fix x
  have "1 \<ge> ((a x) + (w x))"
    by (metis PosRat.pgte.rep_eq add_masks.elims assms less_eq_prat.rep_eq valid_mask.simps)
  then have "1 \<ge> a x"
    by (meson PosRat.pgte.rep_eq PosRat.sum_larger dual_order.trans less_eq_prat.rep_eq)
  then have "(a x) + (1 - (a x)) = 1"
  proof -
    have "Rep_prat (a x) + Rep_prat (1 - (a x)) = Rep_prat 1"
      using Abs_prat_inverse \<open>a x \<le> PosRat.pwrite\<close> less_eq_prat.rep_eq minus_prat_def by auto
    then show ?thesis
      by (metis Rep_prat_inverse plus_prat.rep_eq)
  qed
  then have "(1 - (a x)) \<ge> (w x)"
    by (metis \<open>PosRat.padd (a x) (w x) \<le> PosRat.pwrite\<close> add_le_cancel_left less_eq_prat.rep_eq plus_prat.rep_eq)
  then show "w x = comp_min_mask a w x"
    by (simp add: comp_min_mask_def le_iff_inf)
qed

lemma R_smaller:
  "w \<succeq> R a w"
proof (cases "half_scalable w a")
  case True
  then show ?thesis
    by (simp add: succ_refl R_def)
next
  case False
  then have "R a w = Abs_state (comp_min_mask (get_m a) (get_m w), get_h w)"
    by (meson R_def)
  moreover have "greater_mask (get_m w) (comp_min_mask (get_m a) (get_m w))"
  proof (rule greater_maskI)
    fix hl show "PosRat.pgte (get_m w hl) (comp_min_mask (get_m a) (get_m w) hl)"
      by (simp add: PosRat.pmin_greater comp_min_mask_def)
  qed
  ultimately show ?thesis
    by (metis Abs_state_cases larger_heap_refl Rep_state_cases Rep_state_inverse fst_conv get_h_m greaterI greater_mask_def mem_Collect_eq snd_conv valid_state_decompose)
qed

lemma R_compatible_same:
  assumes "a ## w"
  shows "R a w = w"
proof -
  have "\<not> half_scalable w a"
    using assms half_scalable_def w_in_scaled by blast
  then have "R a w = Abs_state (comp_min_mask (get_m a) (get_m w), get_h w)"
    using R_def by auto
  then show ?thesis
    by (metis defined_def Rep_state_inverse assms compatible_same_mask get_h.simps get_m.simps plus_ab_defined prod.collapse)
qed

lemma in_cwand:
  assumes "\<And>a x. a \<in> A \<and> Some x = R a w \<oplus> a \<Longrightarrow> x \<in> B"
  shows "w \<in> cwand A B"
  using assms cwand_def by force

lemma wandI:
  assumes "\<And>a x. a \<in> A \<and> Some x = a \<oplus> w \<Longrightarrow> x \<in> B"
  shows "w \<in> wand A B"
proof -
  have "A \<otimes> {w} \<subseteq> B"
  proof (rule subsetI)
    fix x assume "x \<in> A \<otimes> {w}"
    then obtain a where "Some x = a \<oplus> w" "a \<in> A"
      by (metis singletonD x_elem_set_product)
    then show "x \<in> B"
      using assms by blast
  qed
  then show ?thesis
    using wand_equiv_def by force
qed

lemma non_half_scalable_R_charact:
  assumes "\<not> half_scalable w a"
  shows "get_m (R a w) = comp_min_mask (get_m a) (get_m w) \<and> get_h (R a w) = get_h w"
proof -
  have "R a w = Abs_state (comp_min_mask (get_m a) (get_m w), get_h w)"
    using R_def assms by auto
  moreover have "valid_state (comp_min_mask (get_m a) (get_m w), get_h w)"
  proof (rule valid_stateI)
    show "valid_mask (comp_min_mask (get_m a) (get_m w))"
    proof (rule valid_maskI)
      show "\<And>f. comp_min_mask (get_m a) (get_m w) (null, f) = 0"
        by (metis PosRat.pgte_antisym PosRat.pmin_greater PosRat.sum_larger comm_monoid_add_class.add_0 comp_min_mask_def valid_mask.elims(1) valid_state.simps valid_state_stabilize)
      fix hl show "PosRat.pgte 1 (comp_min_mask (get_m a) (get_m w) hl)"
        by (smt (verit, del_insts) PosRat.not_pgte_charact PosRat.pgt_implies_pgte PosRat.pmin_comm PosRat.pmin_is comp_min_mask_def upper_bounded_bigger upper_bounded_def valid_mask.simps valid_state.simps valid_state_stabilize)
    qed
    fix hl assume "PosRat.pnone < (comp_min_mask (get_m a) (get_m w) hl)"
    show "get_h w hl \<noteq> None"
      by (metis \<open>PosRat.pnone < comp_min_mask (get_m a) (get_m w) hl\<close> comp_min_mask_def dual_order.strict_trans1 inf_le1 stabilize_charact(1) stabilize_charact(2) stabilize_heap_def stabilize_is_stable stable_state_def)
  qed
  ultimately show ?thesis
    by (metis Rep_state_cases Rep_state_inverse fst_conv get_h.simps get_m.simps mem_Collect_eq snd_conv)
qed

lemma valid_bin:
  "valid_state (binary_mask (get_m a), get_h a)"
proof (rule valid_stateI)
  show "valid_mask (binary_mask (get_m a))"
    by (metis binary_mask_def valid_mask.simps valid_state.simps valid_state_stabilize)
  show "\<And>hl. PosRat.pnone < (binary_mask (get_m a) hl) \<Longrightarrow> get_h a hl \<noteq> None"
    by (metis Rep_state binary_mask_def get_h_m linorder_neq_iff mem_Collect_eq valid_heap_def valid_state.simps)
qed

lemma in_multiply_sem:
  assumes "x \<in> multiply_sem_assertion p A"
  shows "\<exists>a \<in> A. x \<succeq> multiply p a"
  using assms
  unfolding multiply_sem_assertion.simps upper_closure_def multiply.simps
  by blast

lemma get_h_multiply:
  assumes "1 \<ge> p"
  shows "get_h (multiply p x) = get_h x"
  using Abs_state_inverse assms multiply_valid by auto

lemma in_multiply_refl:
  assumes "x \<in> A"
  shows "multiply p x \<in> multiply_sem_assertion p A"
  using succ_refl upper_closure_def assms by fastforce

lemma get_m_smaller:
  assumes "1 \<ge> p"
  shows "get_m (multiply p a) hl = PosRat.pmult p (get_m a hl)"
  using Abs_state_inverse assms multiply_mask_def multiply_valid by auto

lemma get_m_smaller_mask:
  assumes "1 \<ge> p"
  shows "get_m (multiply p a) = multiply_mask p (get_m a)"
  using Abs_state_inverse assms multiply_mask_def multiply_valid by auto

lemma multiply_order:
  assumes "1 \<ge> p"
      and "a \<succeq> b"
    shows "multiply p a \<succeq> multiply p b"
proof (rule greaterI)
  show "larger_heap (get_h (multiply p a)) (get_h (multiply p b))"
    using assms(1) assms(2) get_h_multiply larger_implies_larger_heap by presburger
  show "greater_mask (get_m (multiply p a)) (get_m (multiply p b))"
    by (metis assms(1) assms(2) get_m_smaller_mask greater_def greater_mask_def mult_greater plus_charact(1))
qed

lemma multiply_twice:
  assumes "1 \<ge> a \<and> 1 \<ge> b"
  shows "multiply a (multiply b x) = multiply (PosRat.pmult a b) x"
proof -
  have "get_h (multiply (PosRat.pmult a b) x) = get_h x"
    by (metis PosRat.pmin_is PosRat.pmult_distr PosRat.sum_larger assms dual_order.trans get_h_multiply inf_le1 mult.right_neutral prat_gte_padd)
  moreover have "get_h (multiply a (multiply b x)) = get_h x"
    using assms get_h_multiply by presburger
  moreover have "get_m (multiply a (multiply b x)) = get_m (multiply (PosRat.pmult a b) x)"
  proof (rule ext)
    fix l
    have "1 \<ge> (PosRat.pmult a b)" 
      by (metis PosRat.pgte.rep_eq PosRat.pmult_distr PosRat.sum_larger assms dual_order.trans less_eq_prat.rep_eq mult.right_neutral prat_gte_padd)
    then have "get_m (multiply (PosRat.pmult a b) x) l = PosRat.pmult (PosRat.pmult a b) (get_m x l)"
      using get_m_smaller by blast
    then show "get_m (multiply a (multiply b x)) l = get_m (multiply (PosRat.pmult a b) x) l"
      by (metis assms get_m_smaller mult.assoc)
  qed
  ultimately show ?thesis
    using state_ext by presburger
qed

lemma valid_mask_add_comp_min:
  assumes "valid_mask a"
      and "valid_mask b"
  shows "valid_mask (add_masks (comp_min_mask b a) b)"
proof (rule valid_maskI)
  show "\<And>f. add_masks (comp_min_mask b a) b (null, f) = 0"
  proof -
    fix f
    have "comp_min_mask b a (null, f) = 0"
      by (metis PosRat.not_pgte_charact PosRat.pmin_greater assms(1) comp_min_mask_def prat_pnone_pgt valid_mask.simps)
    then show "add_masks (comp_min_mask b a) b (null, f) = 0"
      using assms(2) by auto
  qed
  fix hl show "PosRat.pgte PosRat.pwrite (add_masks (comp_min_mask b a) b hl)"
  proof (cases "PosRat.pgte (a hl) (1 - (b hl))")
    case True
    then have "add_masks (comp_min_mask b a) b hl = PosRat.padd (1 - (b hl)) (b hl)"
      by (simp add: PosRat.pmin_is comp_min_mask_def)
    then have "add_masks (comp_min_mask b a) b hl = 1"
      by (smt (verit, best) Abs_prat_inverse PosRat.pgte.rep_eq Rep_prat_inverse add.commute assms(2) diff_ge_0_iff_ge le_add_diff_inverse mem_Collect_eq minus_prat_def plus_prat.rep_eq valid_mask.simps)
    then show ?thesis
      by (simp add: PosRat.pgte.rep_eq)
  next
    case False
    then have "comp_min_mask b a hl = a hl"
      by (metis PosRat.not_pgte_charact PosRat.pgt_implies_pgte PosRat.pmin_is comp_min_mask_def inf.commute)
    then have "add_masks (comp_min_mask b a) b hl = PosRat.padd (a hl) (b hl)"
      by auto
    moreover have "PosRat.pgte (PosRat.padd (1 - (b hl)) (b hl)) (PosRat.padd (a hl) (b hl))"
      using False PosRat.not_pgte_charact PosRat.pgt_implies_pgte PosRat.pgte_pgt by blast
    moreover have "PosRat.padd (1 - (b hl)) (b hl) = 1"
      by (metis Abs_prat_inverse PosRat.pgte.rep_eq Rep_prat_inverse assms(2) diff_add_cancel diff_ge_0_iff_ge mem_Collect_eq minus_prat_def plus_prat.rep_eq valid_mask.simps)
    ultimately show ?thesis by simp
  qed
qed



section \<open>Stronger wand\<close>

lemma cwand_stronger:
  "cwand A B \<subseteq> wand A B"
proof
  fix w assume asm0: "w \<in> cwand A B"
  then have r: "\<And>a x. a \<in> A \<and> Some x = R a w \<oplus> a \<Longrightarrow> x \<in> B"
    using cwand_def by blast
  show "w \<in> wand A B"
  proof (rule wandI)
    fix a x assume asm1: "a \<in> A \<and> Some x = a \<oplus> w"
    then have "R a w = w"
      by (metis defined_def R_compatible_same option.distinct(1))
    then show "x \<in> B"
      by (metis commutative asm1 r)
  qed
qed


section Binary

lemma binary_same:
  assumes "binary A"
      and "up_closed B"
  shows "wand A B \<subseteq> cwand A B"
proof (rule subsetI)
  fix w assume "w \<in> wand A B"
  then have asm0: "A \<otimes> {w} \<subseteq> B"
    by (simp add: wand_equiv_def)
  show "w \<in> cwand A B"
  proof (rule in_cwand)
    fix a x assume "a \<in> A \<and> Some x = R a w \<oplus> a"
    show "x \<in> B"
    proof (cases "half_scalable w a")
      case True
      then show ?thesis
        by (metis commutative defined_def R_def \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> option.distinct(1) half_scalable_def w_in_scaled)
    next
      case False
      then have "get_m (R a w) = comp_min_mask (get_m a) (get_m w) \<and> get_h (R a w) = get_h w"
        using non_half_scalable_R_charact by blast
      moreover have "Abs_state (binary_mask (get_m a), get_h a) \<in> A"
        using \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> assms(1) binary_def by blast
      moreover have "greater_mask (add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a))
  (add_masks (binary_mask (get_m a)) (get_m w))"
      proof (rule greater_maskI)
        fix hl show "PosRat.pgte (add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a) hl) (add_masks (binary_mask (get_m a)) (get_m w) hl)"
        proof (cases "get_m a hl = 1")
          case True
          obtain \<phi> where "\<phi> \<in> scaled w" "a ## \<phi>" using False half_scalable_def[of w a]
            by blast
          then obtain p where "p > 0" "1 \<ge> p" "multiply p w ## a"
            using False defined_comm non_half_scalable_instantiate by blast
          have "get_m w hl = 0"
          proof (rule ccontr)
            assume "get_m w hl \<noteq> 0"
            then have "PosRat.pnone < (get_m w hl)"
              by (metis PosRat.pgte.rep_eq PosRat.sum_larger add_0 less_eq_prat.rep_eq linorder_cases linorder_not_less)
            moreover have "get_m (multiply p \<phi>) = multiply_mask p (get_m \<phi>)"
              using multiply_valid[of p \<phi>] multiply.simps[of p \<phi>]
              by (metis Rep_state_cases Rep_state_inverse \<open>1 \<ge> p\<close> fst_conv get_pre(2) mem_Collect_eq)
            then have "PosRat.pnone < (get_m (multiply p w) hl)"
              using \<open>PosRat.pnone < p\<close> \<open>p \<le> PosRat.pwrite\<close> calculation get_m_smaller less_prat.rep_eq times_prat.rep_eq zero_prat.rep_eq by auto
            then have "PosRat.pgt (PosRat.padd (get_m (multiply p w) hl) (get_m a hl)) 1"
              using PosRat.pgt.rep_eq True less_prat.rep_eq plus_prat.rep_eq zero_prat.rep_eq by auto
            then have "\<not> valid_mask (add_masks (get_m (multiply p w)) (get_m a))"
              by (metis PosRat.not_pgte_charact add_masks.elims valid_mask.simps)
            then show False
              using defined_def \<open>multiply p w ## a\<close> plus_ab_defined by blast
          qed
          then show ?thesis
            by (metis PosRat.sum_larger True add.right_neutral add_masks.elims add_masks_comm binary_mask_def)
        next
          case False
          then have "add_masks (binary_mask (get_m a)) (get_m w) hl = get_m w hl"
            by (simp add: binary_mask_def)
          then show ?thesis
          proof (cases "PosRat.pgte (get_m w hl) (1 - (get_m a hl))")
            case True
            then have "comp_min_mask (get_m a) (get_m w) hl = 1 - (get_m a hl)"
              by (simp add: PosRat.pmin_is comp_min_mask_def)
            then have "add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a) hl = 1"
              by (smt (verit, ccfv_threshold) Abs_prat_inverse PosRat.pgte.rep_eq Rep_prat_inverse \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> add_masks.elims diff_add_cancel diff_ge_0_iff_ge mem_Collect_eq minus_prat_def option.discI plus_ab_defined plus_prat.rep_eq upper_valid valid_mask.simps)
            then show ?thesis
              by (metis \<open>add_masks (binary_mask (get_m a)) (get_m w) hl = get_m w hl\<close> valid_mask.elims(2) valid_state.simps valid_state_stabilize)
          next
            case False
            then have "comp_min_mask (get_m a) (get_m w) hl = get_m w hl"
              by (metis PosRat.not_pgte_charact PosRat.pgt_implies_pgte PosRat.pmin_comm PosRat.pmin_is comp_min_mask_def)
            then show ?thesis
              using \<open>add_masks (binary_mask (get_m a)) (get_m w) hl = get_m w hl\<close>
              by (simp add: PosRat.sum_larger)
          qed
        qed
      qed
      then have "valid_mask (add_masks (binary_mask (get_m a)) (get_m w))"
        by (metis \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> calculation(1) greater_mask_def option.distinct(1) plus_ab_defined upper_valid_aux)
      moreover have "compatible_heaps (get_h a) (get_h w)"
        by (metis commutative \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> \<open>get_m (R a w) = comp_min_mask (get_m a) (get_m w) \<and> get_h (R a w) = get_h w\<close> option.simps(3) plus_ab_defined)
      then obtain xx where "Some xx = Abs_state (binary_mask (get_m a), get_h a) \<oplus> w"
        using Abs_state_inverse calculation(3) compatible_def fst_eqD get_pre(1) get_pre(2) plus_state_def valid_bin by fastforce
      then have "xx \<in> B" using asm0
        by (meson add_set_elem \<open>Abs_state (binary_mask (get_m a), get_h a) \<in> A\<close> singletonI subset_iff)
      moreover have "x \<succeq> xx"
      proof (rule greaterI)
        show "greater_mask (get_m x) (get_m xx)"
          using Abs_state_inverse \<open>Some xx = Abs_state (binary_mask (get_m a), get_h a) \<oplus> w\<close> \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> \<open>greater_mask (add_masks (comp_min_mask (get_m a) (get_m w)) (get_m a)) (add_masks (binary_mask (get_m a)) (get_m w))\<close> calculation(1) plus_charact(1) valid_bin by auto
        show "larger_heap (get_h x) (get_h xx)"
        proof (rule larger_heapI)
          fix hl xa assume "get_h xx hl = Some xa"
          then show "get_h x hl = Some xa"
            by (metis commutative Rep_state_cases Rep_state_inverse \<open>Some xx = Abs_state (binary_mask (get_m a), get_h a) \<oplus> w\<close> \<open>a \<in> A \<and> Some x = R a w \<oplus> a\<close> calculation(1) get_h.simps mem_Collect_eq plus_charact(2) snd_conv valid_bin)
        qed
      qed
      ultimately show ?thesis
        using assms(2) up_closed_def by blast
    qed
  qed
qed


section Combinability

lemma padd_one_ineq_sum:
  assumes "PosRat.padd a b = PosRat.pwrite"
      and "PosRat.pgte x aa"
      and "PosRat.pgte x bb" 
    shows "PosRat.pgte x (PosRat.padd (PosRat.pmult a aa) (PosRat.pmult b bb))"
  by (metis (mono_tags, lifting) PosRat.pgte.rep_eq Rep_prat assms(1) assms(2) assms(3) convex_bound_le mem_Collect_eq one_prat.rep_eq plus_prat.rep_eq times_prat.rep_eq)

lemma sum_coeff:
  assumes "PosRat.ppos a"
      and "PosRat.ppos b"
    shows "PosRat.padd (PosRat.pdiv a (PosRat.padd a b)) (PosRat.pdiv b (PosRat.padd a b)) = PosRat.pwrite"
proof -
  let ?a = "Rep_prat a"
  let ?b = "Rep_prat b"
  have "(?a / (?a + ?b)) + (?b / (?a + ?b)) = 1"
    by (metis PosRat.ppos.rep_eq add_divide_distrib add_pos_pos assms(1) assms(2) eq_divide_eq_1 less_numeral_extra(3))
  then show ?thesis
    by (metis Rep_prat_inverse divide_prat.rep_eq one_prat.rep_eq plus_prat.rep_eq)
qed


lemma combinableI:
  assumes "\<And>a b. PosRat.pnone < a \<and> PosRat.pnone < b \<and> PosRat.padd a b = 1 \<Longrightarrow> (multiply_sem_assertion a (cwand A B)) \<otimes> (multiply_sem_assertion b (cwand A B)) \<subseteq> cwand A B"
  shows "combinable (cwand A B)"
proof -
  have "\<And>a b. PosRat.pnone < a \<and> PosRat.pnone < b \<and> 1 \<ge> (PosRat.padd a b) \<Longrightarrow> (multiply_sem_assertion a (cwand A B)) \<otimes> (multiply_sem_assertion b (cwand A B)) \<subseteq> multiply_sem_assertion (PosRat.padd a b) (cwand A B)"
  proof -    
    fix a b assume asm0: "PosRat.pnone < a \<and> PosRat.pnone < b \<and> 1 \<ge> (PosRat.padd a b)"
    then have "1 \<ge> a \<and> 1 \<ge> b"
      by (metis PosRat.pmin_is PosRat.sum_larger add.commute dual_order.trans inf_le1)
    show "(multiply_sem_assertion a (cwand A B)) \<otimes> (multiply_sem_assertion b (cwand A B)) \<subseteq> multiply_sem_assertion (PosRat.padd a b) (cwand A B)"
    proof
      fix x assume "x \<in> multiply_sem_assertion a (cwand A B) \<otimes> multiply_sem_assertion b (cwand A B)"
      then obtain xa xb where "Some x = xa \<oplus> xb" "xa \<in> multiply_sem_assertion a (cwand A B)" "xb \<in> multiply_sem_assertion b (cwand A B)"
        by (meson add_set_elem)
      then obtain wa wb where "wa \<in> cwand A B" "wb \<in> cwand A B" "xa \<succeq> multiply a wa" "xb \<succeq> multiply b wb"
        by (meson in_multiply_sem)
      let ?a = "PosRat.pdiv a (PosRat.padd a b)"
      let ?b = "PosRat.pdiv b (PosRat.padd a b)"
      have "1 \<ge> ?a \<and> 1 \<ge> ?b"
        apply (intro conjI)
        using asm0
         apply (simp add: divide_prat.rep_eq less_eq_prat.rep_eq less_prat.rep_eq one_prat.rep_eq plus_prat.rep_eq zero_prat.rep_eq)
        using asm0
        by (simp add: divide_prat.rep_eq less_prat.rep_eq one_prat.rep_eq order_less_imp_le plus_prat.rep_eq zero_prat.rep_eq)
      have "multiply ?a wa ## multiply ?b wb"
      proof (rule compatibleI)
        show "compatible_heaps (get_h (multiply (PosRat.pdiv a (PosRat.padd a b)) wa)) (get_h (multiply (PosRat.pdiv b (PosRat.padd a b)) wb))"
        proof -
          have "compatible_heaps (get_h (multiply a wa)) (get_h (multiply b wb))"
            by (metis asso2 asso3 greater_equiv minus_some \<open>Some x = xa \<oplus> xb\<close> \<open>xa \<succeq> multiply a wa\<close> \<open>xb \<succeq> multiply b wb\<close> option.simps(3) plus_ab_defined)
          moreover have "get_h (multiply (PosRat.pdiv a (PosRat.padd a b)) wa) = get_h (multiply a wa) \<and> get_h (multiply (PosRat.pdiv b (PosRat.padd a b)) wb) = get_h (multiply b wb)"
          proof -
            have "1 \<ge> a \<and> 1 \<ge> b"
              by (simp add: \<open>a \<le> PosRat.pwrite \<and> b \<le> PosRat.pwrite\<close>)
            moreover have "1 \<ge> ?a \<and> 1 \<ge> ?b"
              by (simp add: \<open>PosRat.pdiv a (PosRat.padd a b) \<le> PosRat.pwrite \<and> PosRat.pdiv b (PosRat.padd a b) \<le> PosRat.pwrite\<close>)
            ultimately show ?thesis
              using get_h_multiply by presburger
          qed
          then show ?thesis
            using calculation by presburger
        qed
        show "valid_mask (add_masks (get_m (multiply (PosRat.pdiv a (PosRat.padd a b)) wa)) (get_m (multiply (PosRat.pdiv b (PosRat.padd a b)) wb)))"
        proof (rule valid_maskI)
          show "\<And>f. add_masks (get_m (multiply (PosRat.pdiv a (PosRat.padd a b)) wa)) (get_m (multiply (PosRat.pdiv b (PosRat.padd a b)) wb)) (null, f) = 0"
            using valid_state_stabilize by auto
          fix hl have "add_masks (get_m (multiply (PosRat.pdiv a (PosRat.padd a b)) wa)) (get_m (multiply (PosRat.pdiv b (PosRat.padd a b)) wb)) hl
                      = PosRat.padd (PosRat.pmult ?a (get_m wa hl)) (PosRat.pmult ?b (get_m wb hl))"
          proof -
            have "get_m (multiply ?a wa) hl = PosRat.pmult ?a (get_m wa hl)"
              using Abs_state_inverse \<open>1 \<ge> (PosRat.pdiv a (PosRat.padd a b)) \<and> 1 \<ge> (PosRat.pdiv b (PosRat.padd a b))\<close> multiply_mask_def multiply_valid by auto
            moreover have "get_m (multiply ?b wb) hl = PosRat.pmult ?b (get_m wb hl)"
              using Abs_state_inverse \<open>1 \<ge> (PosRat.pdiv a (PosRat.padd a b)) \<and> 1 \<ge> (PosRat.pdiv b (PosRat.padd a b))\<close> multiply_mask_def multiply_valid by auto
            ultimately show ?thesis by simp
          qed
          moreover have "PosRat.pgte 1 (PosRat.padd (PosRat.pmult ?a (get_m wa hl)) (PosRat.pmult ?b (get_m wb hl)))"
          proof (rule padd_one_ineq_sum)
            show "PosRat.pgte 1 (get_m wa hl)"
              using valid_mask.simps valid_state.simps valid_state_stabilize by blast
            show "PosRat.pgte 1 (get_m wb hl)"
              using valid_mask.simps valid_state.simps valid_state_stabilize by blast
            show "PosRat.padd (PosRat.pdiv a (PosRat.padd a b)) (PosRat.pdiv b (PosRat.padd a b)) = 1"
              using asm0 sum_coeff
              by (simp add: PosRat.ppos.rep_eq less_prat.rep_eq zero_prat.rep_eq)
          qed
          ultimately show "PosRat.pgte PosRat.pwrite
           (add_masks (get_m (multiply (PosRat.pdiv a (PosRat.padd a b)) wa)) (get_m (multiply (PosRat.pdiv b (PosRat.padd a b)) wb)) hl)"
            by argo
        qed
      qed
      then obtain xx where "Some xx = multiply ?a wa \<oplus> multiply ?b wb"        
        using defined_def
        using sumI by blast
      moreover have "(multiply_sem_assertion ?a (cwand A B)) \<otimes> (multiply_sem_assertion ?b (cwand A B)) \<subseteq> cwand A B"
      proof (rule assms)
        show "PosRat.pnone < PosRat.pdiv a (PosRat.padd a b) \<and>
    PosRat.pnone < PosRat.pdiv b (PosRat.padd a b) \<and> PosRat.padd (PosRat.pdiv a (PosRat.padd a b)) (PosRat.pdiv b (PosRat.padd a b)) = PosRat.pwrite"
          using asm0 PosRat.ppos.rep_eq sum_coeff
          by (simp add: divide_prat.rep_eq less_prat.rep_eq plus_prat.rep_eq zero_prat.rep_eq)
      qed
      ultimately have "xx \<in> cwand A B"
      proof -
        have "multiply ?a wa \<in> multiply_sem_assertion ?a (cwand A B)"
          using \<open>wa \<in> cwand A B\<close> in_multiply_refl by presburger
        moreover have "multiply ?b wb \<in> multiply_sem_assertion ?b (cwand A B)"
          by (meson \<open>wb \<in> cwand A B\<close> in_multiply_refl)
        ultimately show ?thesis
          using \<open>Some xx = multiply (PosRat.pdiv a (PosRat.padd a b)) wa \<oplus> multiply (PosRat.pdiv b (PosRat.padd a b)) wb\<close> \<open>multiply_sem_assertion (PosRat.pdiv a (PosRat.padd a b)) (cwand A B) \<otimes> multiply_sem_assertion (PosRat.pdiv b (PosRat.padd a b)) (cwand A B) \<subseteq> cwand A B\<close> in_starI by blast
      qed
      moreover have "x \<succeq> multiply (PosRat.padd a b) xx"
      proof (rule greaterI)
        have "valid_state (multiply_mask (PosRat.padd a b) (get_m xx), get_h xx)"
          using asm0 multiply_valid by blast
        show "larger_heap (get_h x) (get_h (multiply (PosRat.padd a b) xx))"
        proof -
          have "get_h (multiply (PosRat.padd a b) xx) = get_h xx"
            using asm0 get_h_multiply by blast
          moreover have "get_h xx = get_h wa ++ get_h wb"
            using \<open>PosRat.pdiv a (PosRat.padd a b) \<le> PosRat.pwrite \<and> PosRat.pdiv b (PosRat.padd a b) \<le> PosRat.pwrite\<close> \<open>Some xx = multiply (PosRat.pdiv a (PosRat.padd a b)) wa \<oplus> multiply (PosRat.pdiv b (PosRat.padd a b)) wb\<close> get_h_multiply plus_charact(2) by presburger
          moreover have "get_h x = get_h xa ++ get_h xb"
            using \<open>Some x = xa \<oplus> xb\<close> plus_charact(2) by presburger
          moreover have "get_h wa = get_h (multiply a wa) \<and> get_h wb = get_h (multiply b wb)"
            using \<open>a \<le> PosRat.pwrite \<and> b \<le> PosRat.pwrite\<close> get_h_multiply by presburger
          moreover have "larger_heap (get_h xa) (get_h wa) \<and> larger_heap (get_h xb) (get_h wb)"
            using \<open>xa \<succeq> multiply a wa\<close> \<open>xb \<succeq> multiply b wb\<close> calculation(4) larger_implies_larger_heap by presburger
          ultimately show ?thesis
            by (metis \<open>Some x = xa \<oplus> xb\<close> larger_heaps_sum_ineq option.simps(3) plus_ab_defined)
        qed
        show "greater_mask (get_m x) (get_m (multiply (PosRat.padd a b) xx))"
        proof (rule greater_maskI)
          fix hl
          have "PosRat.pgte (get_m x hl) (PosRat.padd (get_m xa hl) (get_m xb hl))"
            using \<open>Some x = xa \<oplus> xb\<close> PosRat.pgte.rep_eq plus_charact(1) by auto
          moreover have "PosRat.pgte (get_m xa hl) (get_m (multiply a wa) hl) \<and> PosRat.pgte (get_m xb hl) (get_m (multiply b wb) hl)"
            using PosRat.pgte.rep_eq \<open>xa \<succeq> multiply a wa\<close> \<open>xb \<succeq> multiply b wb\<close> larger_implies_greater_mask_hl less_eq_prat.rep_eq by blast
          moreover have "get_m (multiply (PosRat.padd a b) xx) hl = PosRat.pmult (PosRat.padd a b) (get_m xx hl)"
            by (metis Rep_state_cases Rep_state_inverse \<open>valid_state (multiply_mask (PosRat.padd a b) (get_m xx), get_h xx)\<close> fst_conv get_pre(2) mem_Collect_eq multiply.simps multiply_mask_def)
          moreover have "... = PosRat.padd (PosRat.pmult (PosRat.pmult (PosRat.padd a b) ?a) (get_m wa hl)) (PosRat.pmult (PosRat.pmult (PosRat.padd a b) ?b) (get_m wb hl))"
          proof -
            have "get_m (multiply ?a wa) hl = PosRat.pmult ?a (get_m wa hl)"
              using \<open>PosRat.pdiv a (PosRat.padd a b) \<le> PosRat.pwrite \<and> PosRat.pdiv b (PosRat.padd a b) \<le> PosRat.pwrite\<close> get_m_smaller by blast
            moreover have "get_m (multiply ?b wb) hl = PosRat.pmult ?b (get_m wb hl)"
              using \<open>PosRat.pdiv a (PosRat.padd a b) \<le> PosRat.pwrite \<and> PosRat.pdiv b (PosRat.padd a b) \<le> PosRat.pwrite\<close> get_m_smaller by blast
            ultimately have "get_m xx hl = PosRat.padd (PosRat.pmult ?a (get_m wa hl)) (PosRat.pmult ?b (get_m wb hl))"
              using \<open>Some xx = multiply (PosRat.pdiv a (PosRat.padd a b)) wa \<oplus> multiply (PosRat.pdiv b (PosRat.padd a b)) wb\<close> plus_charact(1) by fastforce
            then show ?thesis
              by (simp add: ab_semigroup_mult_class.mult_ac(1) distrib_left)
          qed
          moreover have "... = PosRat.padd (PosRat.pmult a (get_m wa hl)) (PosRat.pmult b (get_m wb hl))"
            by (smt (verit, ccfv_threshold) PosRat.field_divide_inverse PosRat.ppos.rep_eq Rings.ring_distribs(2) asm0 less_prat.rep_eq mult.left_commute mult.right_neutral sum_coeff zero_prat.rep_eq)
          moreover have "get_m (multiply a wa) hl = PosRat.pmult a (get_m wa hl) \<and> get_m (multiply b wb) hl = PosRat.pmult b (get_m wb hl)"
          proof -
            have "valid_mask (multiply_mask a (get_m wa))"
              using asm0 mult_add_states multiply_valid upper_valid_aux valid_state.simps by blast
            moreover have "valid_mask (multiply_mask b (get_m wb))"
              using asm0 mult_add_states multiply_valid upper_valid valid_state.simps by blast
            ultimately show ?thesis
              using \<open>a \<le> PosRat.pwrite \<and> b \<le> PosRat.pwrite\<close> get_m_smaller by presburger
          qed
          ultimately show "PosRat.pgte (get_m x hl) (get_m (multiply (PosRat.padd a b) xx) hl)"
            by (simp add: PosRat.pgte.rep_eq plus_prat.rep_eq)          
        qed
      qed
      ultimately show "x \<in> multiply_sem_assertion (PosRat.padd a b) (cwand A B)"
        by (metis up_closed_def upper_closure_up_closed in_multiply_refl multiply_sem_assertion.simps)
    qed
  qed
  then show ?thesis
    using combinable_def by presburger
qed

lemma combinable_cwand:
  assumes "combinable B"
      and "up_closed B"
    shows "combinable (cwand A B)"
proof (rule combinableI)
  fix \<alpha> \<beta> :: prat
  assume asm0: "\<alpha> > 0 \<and> \<beta> > 0 \<and> \<alpha> + \<beta> = 1"
  then have "1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>"
    by (metis PosRat.pmin_is PosRat.sum_larger add.commute inf_le1)
  show "multiply_sem_assertion \<alpha> (cwand A B) \<otimes> multiply_sem_assertion \<beta> (cwand A B) \<subseteq> cwand A B"
  proof
    fix w assume "w \<in> multiply_sem_assertion \<alpha> (cwand A B) \<otimes> multiply_sem_assertion \<beta> (cwand A B)"
    then obtain xa xb where "Some w = xa \<oplus> xb" "xa \<in> multiply_sem_assertion \<alpha> (cwand A B)" "xb \<in> multiply_sem_assertion \<beta> (cwand A B)"
      by (meson add_set_elem)
    then obtain wa wb where "wa \<in> cwand A B" "wb \<in> cwand A B" "xa \<succeq> multiply \<alpha> wa" "xb \<succeq> multiply \<beta> wb"
      by (meson in_multiply_sem)
    then obtain r: "\<And>a x. a \<in> A \<and> Some x = R a wa \<oplus> a \<Longrightarrow> x \<in> B" "\<And>a x. a \<in> A \<and> Some x = R a wb \<oplus> a \<Longrightarrow> x \<in> B"
      using cwand_def by blast
    show "w \<in> cwand A B"
    proof (rule in_cwand)
      fix a x assume asm1: "a \<in> A \<and> Some x = R a w \<oplus> a"
      have "\<not> half_scalable w a"
      proof (rule ccontr)
        assume "\<not> \<not> half_scalable w a"
        then have "R a w = w \<and> \<not> a ## R a w"
          by (simp add: R_def half_scalable_def w_in_scaled)
        then show False
          using PartialHeapSA.commutative asm1 defined_def by fastforce
      qed
      then have "get_h (R a w) = get_h w \<and> get_m (R a w) = comp_min_mask (get_m a) (get_m w)"
        using non_half_scalable_R_charact by blast
      moreover obtain p where "a ## multiply p w" "p > 0 \<and> 1 \<ge> p"
        using \<open>\<not> half_scalable w a\<close> non_half_scalable_instantiate by blast
      moreover have "\<not> half_scalable wa a"
      proof -
        have "a ## multiply (PosRat.pmult \<alpha> p) wa"
        proof -
          have "w \<succeq> xa" using \<open>Some w = xa \<oplus> xb\<close> using greater_def by blast
          then have "multiply p w \<succeq> multiply p xa"
            using calculation(3) multiply_order by blast
          then have "multiply p w \<succeq> multiply (PosRat.pmult \<alpha> p) wa"
          proof -
            have "multiply p w \<succeq> multiply p (multiply \<alpha> wa)"
              using succ_trans \<open>w \<succeq> xa\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> calculation(3) multiply_order by blast
            then show ?thesis
              using \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> calculation(3) multiply_twice PosRat.pmult_comm by auto
          qed
          then show ?thesis
            using calculation(2) defined_comm smaller_compatible by blast
        qed
        moreover have "PosRat.pnone < (PosRat.pmult \<alpha> p) \<and> 1 \<ge> (PosRat.pmult \<alpha> p)"
          by (smt (verit, best) PosRat.pgte.rep_eq PosRat.sum_larger \<open>PosRat.pnone < p \<and> p \<le> PosRat.pwrite\<close> asm0 comm_semiring_class.distrib dual_order.trans less_eq_prat.rep_eq less_prat.rep_eq mult_1 times_prat.rep_eq zero_less_mult_iff zero_prat.rep_eq)
        ultimately show ?thesis
          using half_scalable_def scaled_def by auto
      qed
      then have "get_h (R a wa) = get_h wa \<and> get_m (R a wa) = comp_min_mask (get_m a) (get_m wa)"
        using non_half_scalable_R_charact by blast
      moreover have "R a wa ## a"
      proof (rule compatibleI)
        have "larger_heap (get_h w) (get_h xa) \<and> larger_heap (get_h xa) (get_h wa)"
          by (metis commutative greater_equiv \<open>Some w = xa \<oplus> xb\<close> \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_h_multiply larger_implies_larger_heap)
        then show "compatible_heaps (get_h (R a wa)) (get_h a)"
          by (metis asm1 calculation(1) calculation(4) larger_heap_comp option.distinct(1) plus_ab_defined)
        show "valid_mask (add_masks (get_m (R a wa)) (get_m a))"
          using calculation(4) valid_mask_add_comp_min valid_state.simps valid_state_stabilize by presburger
      qed
      then obtain ba where "Some ba = R a wa \<oplus> a"
        using sumI by blast

      moreover have "\<not> half_scalable wb a"
      proof -
        have "a ## multiply (PosRat.pmult \<beta> p) wb"
        proof -
          have "w \<succeq> xb" using \<open>Some w = xa \<oplus> xb\<close>
            using greater_equiv by blast
          then have "multiply p w \<succeq> multiply p xb"
            using calculation(3) multiply_order by blast
          then have "multiply p w \<succeq> multiply (PosRat.pmult \<beta> p) wb"
          proof -
            have "multiply p w \<succeq> multiply p (multiply \<beta> wb)"
              using succ_trans \<open>w \<succeq> xb\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> calculation(3) multiply_order by blast
            then show ?thesis
              using \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> calculation(3) multiply_twice PosRat.pmult_comm by auto
          qed
          then show ?thesis
            using calculation(2) defined_comm smaller_compatible by blast
        qed
        moreover have "PosRat.pnone < (PosRat.pmult \<beta> p) \<and> 1 \<ge> (PosRat.pmult \<beta> p)"
          by (metis PosRat.not_pgte_charact PosRat.pgt.rep_eq PosRat.pmult_distr PosRat.sum_larger \<open>PosRat.pnone < p \<and> p \<le> PosRat.pwrite\<close> add.commute asm0 comm_monoid_add_class.add_0 dual_order.trans less_prat.rep_eq linorder_less_linear linorder_not_less mult.commute mult.right_neutral mult_eq_0_iff times_prat.rep_eq zero_prat.rep_eq)
        ultimately show ?thesis
          using half_scalable_def scaled_def by auto
      qed
      then have "get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)"
        using non_half_scalable_R_charact by blast
      moreover have "R a wb ## a"
      proof (rule compatibleI)
        have "larger_heap (get_h w) (get_h xb) \<and> larger_heap (get_h xb) (get_h wb)"
          using \<open>Some w = xa \<oplus> xb\<close> \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_h_multiply larger_heap_def larger_implies_larger_heap plus_charact(2) by fastforce
        then show "compatible_heaps (get_h (R a wb)) (get_h a)"
          by (metis asm1 calculation(1) calculation(6) larger_heap_comp option.simps(3) plus_ab_defined)
        show "valid_mask (add_masks (get_m (R a wb)) (get_m a))"
          using calculation(6) valid_mask_add_comp_min valid_state.simps valid_state_stabilize by presburger
      qed
      then obtain bb where "Some bb = R a wb \<oplus> a"
        using sumI by blast

      moreover obtain ya where "Some ya = R a wa \<oplus> a"
        using calculation(5) by auto
      then have "ya \<in> B"
        using asm1 r(1) by blast
      then have "multiply \<alpha> ya \<in> multiply_sem_assertion \<alpha> B"
        using in_multiply_refl by blast
      moreover obtain yb where "Some yb = R a wb \<oplus> a"
        using calculation(7) by auto
      then have "yb \<in> B"
        using asm1 r(2) by blast
      then have "multiply \<beta> yb \<in> multiply_sem_assertion \<beta> B"
        using in_multiply_refl by blast
      moreover have "(multiply \<alpha> ya) ## (multiply \<beta> yb)"
      proof (rule compatibleI)
        have "get_h ya = get_h wa ++ get_h a"
          using \<open>Some ya = R a wa \<oplus> a\<close> \<open>get_h (R a wa) = get_h wa \<and> get_m (R a wa) = comp_min_mask (get_m a) (get_m wa)\<close> plus_charact(2) by presburger
        then have "get_h (multiply \<alpha> ya) = get_h wa ++ get_h a"
          using \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> get_h_multiply by presburger

        moreover have "get_h yb = get_h wb ++ get_h a"
          using \<open>Some yb = R a wb \<oplus> a\<close> \<open>get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)\<close> plus_charact(2) by presburger
        then have "get_h (multiply \<beta> yb) = get_h wb ++ get_h a"
          using \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> get_h_multiply by presburger
        moreover have "compatible_heaps (get_h wa) (get_h wb)"
        proof (rule compatible_heapsI)
          fix hl a b assume "get_h wa hl = Some a" "get_h wb hl = Some b"
          then have "get_h xa hl = Some a" "get_h xb hl = Some b"
           apply (metis (full_types) \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_h_multiply larger_heap_def larger_implies_larger_heap)
            by (metis \<open>get_h wb hl = Some b\<close> \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_h_multiply larger_heap_def larger_implies_larger_heap)
          moreover have "compatible_heaps (get_h xa) (get_h xb)"
            by (metis \<open>Some w = xa \<oplus> xb\<close> option.simps(3) plus_ab_defined)
          ultimately show "a = b"
            by (metis compatible_heaps_def compatible_options.simps(1))
        qed
        ultimately show "compatible_heaps (get_h (multiply \<alpha> ya)) (get_h (multiply \<beta> yb))"
          by (metis commutative core_is_smaller \<open>Some ya = R a wa \<oplus> a\<close> \<open>Some yb = R a wb \<oplus> a\<close> \<open>get_h (R a wa) = get_h wa \<and> get_m (R a wa) = comp_min_mask (get_m a) (get_m wa)\<close> \<open>get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)\<close> compatible_heaps_sum core_defined(1) core_defined(2) option.distinct(1) plus_ab_defined)
        show "valid_mask (add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)))"
        proof (rule valid_maskI)
          show "\<And>f. add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)) (null, f) = 0"
            by (metis (no_types, opaque_lifting) core_is_smaller add_masks.simps core_defined(2) minus_empty not_None_eq plus_ab_defined valid_mask.simps)
          fix hl 
          have "add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)) hl = PosRat.padd (PosRat.pmult \<alpha> (get_m ya hl)) (PosRat.pmult \<beta> (get_m yb hl))"
            using \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> get_m_smaller by auto
          moreover have "get_m ya hl = PosRat.padd (get_m (R a wa) hl) (get_m a hl) \<and> get_m yb hl = PosRat.padd (get_m (R a wb) hl) (get_m a hl)"
            using \<open>Some ya = R a wa \<oplus> a\<close> \<open>Some yb = R a wb \<oplus> a\<close> plus_charact(1) by auto          
          ultimately show "PosRat.pgte 1 (add_masks (get_m (multiply \<alpha> ya)) (get_m (multiply \<beta> yb)) hl)"
            by (metis \<open>R a wa ## a\<close> \<open>R a wb ## a\<close> add_masks.elims asm0 defined_def padd_one_ineq_sum plus_ab_defined valid_mask.elims(2))
        qed
      qed
      then obtain y where "Some y = multiply \<alpha> ya \<oplus> multiply \<beta> yb"
        using sumI by blast
      moreover have "x \<succeq> y"
      proof (rule greaterI)
        have "get_h y = get_h ya ++ get_h yb"
          using \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> calculation(10) get_h_multiply plus_charact(2) by presburger
        moreover have "get_h ya = get_h wa ++ get_h a"
          using \<open>Some ya = R a wa \<oplus> a\<close> \<open>get_h (R a wa) = get_h wa \<and> get_m (R a wa) = comp_min_mask (get_m a) (get_m wa)\<close> plus_charact(2) by presburger
        moreover have "get_h yb = get_h wb ++ get_h a"
          using \<open>Some yb = R a wb \<oplus> a\<close> \<open>get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)\<close> plus_charact(2) by presburger
        moreover have "larger_heap (get_h x) (get_h wa)"
        proof -
          have "larger_heap (get_h x) (get_h xa)"
            by (metis greater_def \<open>Some w = xa \<oplus> xb\<close> \<open>get_h (R a w) = get_h w \<and> get_m (R a w) = comp_min_mask (get_m a) (get_m w)\<close> asm1 larger_heap_trans larger_implies_larger_heap)
          moreover have "larger_heap (get_h xa) (get_h wa)"
            by (metis \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_h_multiply larger_implies_larger_heap)
          ultimately show ?thesis
            using larger_heap_trans by blast
        qed
        moreover have "larger_heap (get_h x) (get_h wb)"
        proof -
          have "larger_heap (get_h x) (get_h xb)"
            by (metis greater_def greater_equiv \<open>Some w = xa \<oplus> xb\<close> \<open>get_h (R a w) = get_h w \<and> get_m (R a w) = comp_min_mask (get_m a) (get_m w)\<close> asm1 larger_heap_trans larger_implies_larger_heap)
          moreover have "larger_heap (get_h xb) (get_h wb)"
            by (metis \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_h_multiply larger_implies_larger_heap)
          ultimately show ?thesis
            using larger_heap_trans by blast
        qed
        moreover have "larger_heap (get_h x) (get_h a)"
          using greater_equiv asm1 larger_implies_larger_heap by blast
        ultimately show "larger_heap (get_h x) (get_h y)"          
          by (simp add: larger_heap_plus)
        show "greater_mask (get_m x) (get_m y)"
        proof (rule greater_maskI)
          fix hl 
          have "get_m x hl = PosRat.padd (get_m (R a w) hl) (get_m a hl)"
            using asm1 plus_charact(1) by auto
          moreover have "get_m y hl = PosRat.padd (PosRat.pmult \<alpha> (PosRat.padd (get_m (R a wa) hl) (get_m a hl))) (PosRat.pmult \<beta> (PosRat.padd (get_m (R a wb) hl) (get_m a hl)))"
            by (metis \<open>Some y = multiply \<alpha> ya \<oplus> multiply \<beta> yb\<close> \<open>Some ya = R a wa \<oplus> a\<close> \<open>Some yb = R a wb \<oplus> a\<close> \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> add_masks.simps get_m_smaller plus_charact(1))

          moreover have "PosRat.padd (PosRat.pmult \<alpha> (PosRat.padd (get_m (R a wa) hl) (get_m a hl))) (PosRat.pmult \<beta> (PosRat.padd (get_m (R a wb) hl) (get_m a hl)))
= PosRat.padd (PosRat.padd (PosRat.pmult \<alpha> (get_m a hl)) (PosRat.pmult \<beta> (get_m a hl))) (PosRat.padd (PosRat.pmult \<alpha> (get_m (R a wa) hl)) (PosRat.pmult \<beta> (get_m (R a wb) hl)))"
            by (smt (verit, ccfv_SIG) PosRat.pmult_distr add.commute group_cancel.add1)
          have "PosRat.pgte (get_m (R a w) hl) (PosRat.padd (PosRat.pmult \<alpha> (get_m (R a wa) hl)) (PosRat.pmult \<beta> (get_m (R a wb) hl)))"
          proof (cases "PosRat.pgte (get_m w hl) (1 - (get_m a hl))")
            case True
            then have "get_m (R a w) hl = (1 - (get_m a hl))"
              using PosRat.pmin_is \<open>get_h (R a w) = get_h w \<and> get_m (R a w) = comp_min_mask (get_m a) (get_m w)\<close> comp_min_mask_def by presburger
            moreover have "PosRat.pgte (1 - (get_m a hl)) (get_m (R a wa) hl)"
              by (metis PosRat.pmin_comm PosRat.pmin_greater \<open>get_h (R a wa) = get_h wa \<and> get_m (R a wa) = comp_min_mask (get_m a) (get_m wa)\<close> comp_min_mask_def)
            then have "PosRat.pgte (PosRat.pmult \<alpha> (1 - (get_m a hl))) (PosRat.pmult \<alpha> (get_m (R a wa) hl))"
              by (metis PosRat.pmult_distr PosRat.sum_larger prat_greater_exists)
            moreover have "PosRat.pgte (1 - (get_m a hl)) (get_m (R a wb) hl)"
              by (metis PosRat.pmin_comm PosRat.pmin_greater \<open>get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)\<close> comp_min_mask_def)
            then have "PosRat.pgte (PosRat.pmult \<beta> (1 - (get_m a hl))) (PosRat.pmult \<beta> (get_m (R a wb) hl))"
              by (metis PosRat.sum_larger distrib_left prat_greater_exists)
            ultimately show ?thesis
              using \<open>PosRat.pgte (PosRat.pwrite - get_m a hl) (get_m (R a wa) hl)\<close> \<open>PosRat.pgte (PosRat.pwrite - get_m a hl) (get_m (R a wb) hl)\<close> asm0 padd_one_ineq_sum by presburger
          next
            case False
            then have "get_m (R a w) hl = get_m w hl"
              by (metis PosRat.pgte.rep_eq \<open>get_h (R a w) = get_h w \<and> get_m (R a w) = comp_min_mask (get_m a) (get_m w)\<close> comp_min_mask_def inf.orderE less_eq_prat.rep_eq linorder_le_cases)
            moreover have "PosRat.pgte (get_m w hl) (PosRat.padd (PosRat.pmult \<alpha> (get_m wa hl)) (PosRat.pmult \<beta> (get_m wb hl)))"
            proof -
              have "PosRat.pgte (get_m w hl) (PosRat.padd (get_m xa hl) (get_m xb hl))"
                using PosRat.not_pgte_charact PosRat.pgt_implies_pgte \<open>Some w = xa \<oplus> xb\<close> plus_charact(1) by auto
              moreover have "PosRat.pgte (get_m xa hl) (PosRat.pmult \<alpha> (get_m wa hl))"
                by (metis PosRat.pmin_greater \<open>\<alpha> \<le> PosRat.pwrite \<and> \<beta> \<le> PosRat.pwrite\<close> \<open>xa \<succeq> multiply \<alpha> wa\<close> get_m_smaller inf.absorb_iff2 larger_implies_greater_mask_hl)
              moreover have "PosRat.pgte (get_m xb hl) (PosRat.pmult \<beta> (get_m wb hl))"
                by (metis PosRat.pgte.rep_eq \<open>\<alpha> \<le> PosRat.pwrite \<and> \<beta> \<le> PosRat.pwrite\<close> \<open>xb \<succeq> multiply \<beta> wb\<close> get_m_smaller larger_implies_greater_mask_hl less_eq_prat.rep_eq)
              ultimately show ?thesis
                by (simp add: PosRat.pgte.rep_eq plus_prat.rep_eq)
            qed
            moreover have "PosRat.pgte (PosRat.pmult \<alpha> (get_m wa hl)) (PosRat.pmult \<alpha> (get_m (R a wa) hl))"
              by (metis PosRat.sum_larger R_smaller distrib_left larger_implies_greater_mask_hl prat_gte_padd)
            moreover have "PosRat.pgte (PosRat.pmult \<beta> (get_m wb hl)) (PosRat.pmult \<beta> (get_m (R a wb) hl))"
              by (metis PosRat.pmin_greater PosRat.pmult_distr PosRat.sum_larger \<open>get_h (R a wb) = get_h wb \<and> get_m (R a wb) = comp_min_mask (get_m a) (get_m wb)\<close> comp_min_mask_def prat_greater_exists)
            ultimately show ?thesis
              using PosRat.pgte.rep_eq plus_prat.rep_eq by force
          qed
          moreover have "get_m x hl = PosRat.padd (get_m (R a w) hl) (get_m a hl)"
            using calculation(1) by auto
          moreover have "get_m y hl = PosRat.padd (PosRat.pmult \<alpha> (get_m ya hl)) (PosRat.pmult \<beta> (get_m yb hl))"
            using \<open>Some y = multiply \<alpha> ya \<oplus> multiply \<beta> yb\<close> \<open>1 \<ge> \<alpha> \<and> 1 \<ge> \<beta>\<close> get_m_smaller plus_charact(1) by auto
          moreover have "PosRat.padd (PosRat.pmult \<alpha> (get_m ya hl)) (PosRat.pmult \<beta> (get_m yb hl)) = 
PosRat.padd (PosRat.pmult \<alpha> (PosRat.padd (get_m (R a wa) hl) (get_m a hl))) (PosRat.pmult \<beta> (PosRat.padd (get_m (R a wb) hl) (get_m a hl)))"
            using calculation(2) calculation(5) by presburger
          moreover have "... = PosRat.padd (PosRat.pmult (\<alpha> + \<beta>) (get_m a hl)) (PosRat.padd (PosRat.pmult \<alpha> (get_m (R a wa) hl)) (PosRat.pmult \<beta> (get_m (R a wb) hl)))"
            by (metis \<open>PosRat.padd (PosRat.pmult \<alpha> (PosRat.padd (get_m (R a wa) hl) (get_m a hl))) (PosRat.pmult \<beta> (PosRat.padd (get_m (R a wb) hl) (get_m a hl))) = PosRat.padd (PosRat.padd (PosRat.pmult \<alpha> (get_m a hl)) (PosRat.pmult \<beta> (get_m a hl))) (PosRat.padd (PosRat.pmult \<alpha> (get_m (R a wa) hl)) (PosRat.pmult \<beta> (get_m (R a wb) hl)))\<close> PosRat.pmult_comm PosRat.pmult_distr)
          ultimately show "PosRat.pgte (get_m x hl) (get_m y hl)"
            using asm0 PosRat.pmult_special(1)
            by (smt (verit, best) PosRat.sum_larger add.assoc add.commute prat_greater_exists)
        qed
      qed
      ultimately have "y \<in> multiply_sem_assertion \<alpha> B \<otimes> multiply_sem_assertion \<beta> B"
        using add_set_elem by blast
      then have "y \<in> multiply_sem_assertion 1 B"
        by (metis (no_types, lifting) asm0 assms(1) combinable_def in_mono order_le_less)
      then obtain b where "y \<succeq> multiply 1 b" "b \<in> B"
        using in_multiply_sem by blast
      then have "multiply 1 b = b"
        by (metis Rep_state_inverse get_h_m mult_write_mask multiply.simps)
      then have "y \<in> B"
        by (metis \<open>b \<in> B\<close> \<open>y \<succeq> multiply 1 b\<close> assms(2) up_closed_def)
      show "x \<in> B"
        using \<open>x \<succeq> y\<close> \<open>y \<in> B\<close> assms(2) up_closed_def by blast
    qed
  qed
qed





section Theorems

theorem R_mono_transformer:
  "mono_transformer (R a)"
  unfolding mono_transformer_def
  apply (intro conjI)
  apply (clarsimp)
proof -
  show "\<forall>x. R a (stabilize |x| ) = stabilize |x|"
    by (metis R_smaller compatible_with_stab_pure_larger smaller_compatible_core stab_pure_is_pure succ_antisym)
  show "\<And>\<phi> \<phi>'. \<phi>' \<succeq> \<phi> \<Longrightarrow> R a \<phi>' \<succeq> R a \<phi>"
  proof -
    fix \<phi> \<phi>' :: state
    assume "\<phi>' \<succeq> \<phi>"
    show "R a \<phi>' \<succeq> R a \<phi>"
    proof (cases "half_scalable \<phi>' a")
      case True
      then show ?thesis
        by (metis succ_trans R_def R_smaller \<open>\<phi>' \<succeq> \<phi>\<close>)
    next
      case False
      then obtain p where "p > 0" "1 \<ge> p" "multiply p \<phi>' ## a"
        by (metis commutative defined_def non_half_scalable_instantiate)
      then have "multiply p \<phi> ## a"
        using smaller_compatible \<open>\<phi>' \<succeq> \<phi>\<close> multiply_order by blast
      then have "\<not> half_scalable \<phi> a"
        using \<open>PosRat.pnone < p\<close> \<open>p \<le> PosRat.pwrite\<close> defined_comm half_scalable_def scaled_def by auto
      moreover have "greater_mask (comp_min_mask (get_m a) (get_m \<phi>')) (comp_min_mask (get_m a) (get_m  \<phi>))"
      proof (rule greater_maskI)
        fix hl show "PosRat.pgte (comp_min_mask (get_m a) (get_m \<phi>') hl) (comp_min_mask (get_m a) (get_m \<phi>) hl)"
        proof (cases "PosRat.pgte (get_m \<phi>' hl) (1 - (get_m a hl))")
          case True
          then show ?thesis
            by (metis PosRat.pmin_comm PosRat.pmin_greater PosRat.pmin_is comp_min_mask_def)
        next
          case False
          then show ?thesis
            by (metis (no_types, opaque_lifting) PosRat.pmin_comm PosRat.pmin_greater R_smaller \<open>\<phi>' \<succeq> \<phi>\<close> calculation comp_min_mask_def inf.orderE inf.strict_order_iff larger_implies_greater_mask_hl linorder_not_less non_half_scalable_R_charact succ_trans)
        qed
      qed
      ultimately show ?thesis
        using False \<open>\<phi>' \<succeq> \<phi>\<close> greaterI larger_implies_larger_heap non_half_scalable_R_charact by presburger
    qed
  qed
qed

theorem properties_of_combinable_wands:
  assumes "up_closed B"
    shows "combinable B \<Longrightarrow> combinable (cwand A B)"
      and "cwand A B \<subseteq> wand A B"
      and "binary A \<Longrightarrow> cwand A B = wand A B"
  by (simp_all add: assms combinable_cwand cwand_stronger binary_same dual_order.eq_iff)


end