theory PartialHeapSA
  imports PackageLogic "../CoreIVL/SepAlgebra" Mask
begin


section \<open>Definitions\<close>

type_synonym heap = "heap_loc \<rightharpoonup> val"
type_synonym pre_state = "mask \<times> heap"


definition valid_heap :: "mask \<Rightarrow> heap \<Rightarrow> bool" where
  "valid_heap \<pi> h \<longleftrightarrow> (\<forall>hl. \<pi> hl > 0 \<longrightarrow> h hl \<noteq> None)"

fun valid_state :: "pre_state \<Rightarrow> bool" where
  "valid_state (\<pi>, h) \<longleftrightarrow> valid_mask \<pi> \<and> valid_heap \<pi> h"

lemma valid_stateI:
  assumes "valid_mask \<pi>"
      and "\<And>hl. \<pi> hl > 0 \<Longrightarrow> h hl \<noteq> None"
    shows "valid_state (\<pi>, h)"
  using assms(1) assms(2) valid_heap_def valid_state.simps by blast

definition empty_heap where "empty_heap hl = None"

lemma valid_pre_unit:
  "valid_state (empty_mask, empty_heap)"
  using ppos.rep_eq valid_empty valid_stateI by fastforce

typedef state = "{ \<phi> |\<phi>. valid_state \<phi> }"
  using valid_pre_unit by blast

fun get_m :: "state \<Rightarrow> mask" where "get_m a = fst (Rep_state a)"
fun get_h :: "state \<Rightarrow> heap" where "get_h a = snd (Rep_state a)"

fun compatible_options where
  "compatible_options (Some a) (Some b) \<longleftrightarrow> a = b"
| "compatible_options _ _ \<longleftrightarrow> True"

definition compatible_heaps :: "heap \<Rightarrow> heap \<Rightarrow> bool" where
  "compatible_heaps h h' \<longleftrightarrow> (\<forall>hl. compatible_options (h hl) (h' hl))"

definition compatible :: "pre_state \<Rightarrow> pre_state \<Rightarrow> bool" where
  "compatible \<phi> \<phi>' \<longleftrightarrow> compatible_heaps (snd \<phi>) (snd \<phi>') \<and> valid_mask (add_masks (fst \<phi>) (fst \<phi>'))"

fun add_states :: "pre_state \<Rightarrow> pre_state \<Rightarrow> pre_state" where
  "add_states (\<pi>, h) (\<pi>', h') = (add_masks \<pi> \<pi>', h ++ h')"

definition larger_heap where
  "larger_heap h' h \<longleftrightarrow> (\<forall>hl x. h hl = Some x \<longrightarrow> h' hl = Some x)"

definition unit :: "state" where
  "unit = Abs_state (empty_mask, empty_heap)"


instantiation state :: pcm_with_core
begin

definition plus_state :: "state \<Rightarrow> state \<rightharpoonup> state" where
  "a \<oplus> b = (if compatible (Rep_state a) (Rep_state b) then Some (Abs_state (add_states (Rep_state a) (Rep_state b))) else None)"

definition core_state :: "state \<Rightarrow> state" where
  "core_state \<phi> = Abs_state (empty_mask, get_h \<phi>)"

section Lemmas

lemma valid_heapI:
  assumes "\<And>hl. \<pi> hl > 0 \<Longrightarrow> h hl \<noteq> None"
  shows "valid_heap \<pi> h"
  using assms valid_heap_def by presburger

lemma valid_state_decompose:
  assumes "valid_state (add_masks a b, h)"
  shows "valid_state (a, h)"
proof (rule valid_stateI)
  show "valid_mask a"
    using assms upper_valid_aux valid_state.simps by blast
  fix hl assume "a hl > 0" then show "h hl \<noteq> None"
    using assms
    unfolding add_masks.simps assms valid_heap_def valid_state.simps
    by (metis PosRat.pgte_antisym PosRat.sum_larger add_0 linorder_not_le prat_gte_padd)
qed

lemma compatible_heapsI:
  assumes "\<And>hl a b. h hl = Some a \<Longrightarrow> h' hl = Some b \<Longrightarrow> a = b"
  shows "compatible_heaps h h'"
  by (metis assms compatible_heaps_def compatible_options.elims(3))

lemma compatibleI_old:
  assumes "\<And>hl x y. snd \<phi> hl = Some x \<and> snd \<phi>' hl = Some y \<Longrightarrow> x = y"
      and "valid_mask (add_masks (fst \<phi>) (fst \<phi>'))"
    shows "compatible \<phi> \<phi>'"
  using assms(1) assms(2) compatible_def compatible_heapsI by presburger

lemma larger_heap_anti:
  assumes "larger_heap a b"
      and "larger_heap b a"
    shows "a = b"
proof (rule ext)
  fix x show "a x = b x"
  proof (cases "a x")
    case None
    then show ?thesis
      by (metis assms(1) larger_heap_def not_None_eq)
  next
    case (Some a)
    then show ?thesis
      by (metis assms(2) larger_heap_def)
  qed
qed

lemma larger_heapI:
  assumes "\<And>hl x. h hl = Some x \<Longrightarrow> h' hl = Some x"
  shows "larger_heap h' h"
  by (simp add: assms larger_heap_def)

lemma larger_heap_refl:
  "larger_heap h h"
  using larger_heap_def by blast

lemma compatible_heaps_comm:
  assumes "compatible_heaps a b"
  shows "a ++ b = b ++ a"
proof (rule ext)
  fix x show "(a ++ b) x = (b ++ a) x"
  proof (cases "a x")
    case None
    then show ?thesis
      by (simp add: domIff map_add_dom_app_simps(2) map_add_dom_app_simps(3))
  next
    case (Some a)
    then show ?thesis
      by (metis (no_types, lifting) assms compatible_heaps_def compatible_options.elims(2) map_add_None map_add_dom_app_simps(1) map_add_dom_app_simps(3))
  qed
qed

lemma larger_heaps_sum_ineq:
  assumes "larger_heap a' a"
      and "larger_heap b' b"
      and "compatible_heaps a' b'"
    shows "larger_heap (a' ++ b') (a ++ b)"
proof (rule larger_heapI)
  fix hl x assume "(a ++ b) hl = Some x"
  show "(a' ++ b') hl = Some x"
  proof (cases "a hl")
    case None
    then show ?thesis
      by (metis \<open>(a ++ b) hl = Some x\<close> assms(2) larger_heap_def map_add_SomeD map_add_find_right)
  next
    case (Some aa)
    then show ?thesis
      by (metis (mono_tags, lifting) \<open>(a ++ b) hl = Some x\<close> assms(1) assms(2) assms(3) compatible_heaps_comm larger_heap_def map_add_Some_iff)
  qed
qed

lemma larger_heap_trans:
  assumes "larger_heap a b"
      and "larger_heap b c"
    shows "larger_heap a c"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) larger_heap_def)

lemma larger_heap_comp:
  assumes "larger_heap a b"
      and "compatible_heaps a c"
    shows "compatible_heaps b c"
proof (rule compatible_heapsI)
  fix hl a ba
  assume "b hl = Some a" "c hl = Some ba"
  then show "a = ba"
    by (metis assms(1) assms(2) compatible_heaps_def compatible_options.simps(1) larger_heap_def)
qed

lemma larger_heap_plus:
  assumes "larger_heap a b"
      and "larger_heap a c"
    shows "larger_heap a (b ++ c)"
proof (rule larger_heapI)
  fix hl x assume "(b ++ c) hl = Some x"
  then show "a hl = Some x"
  proof (cases "b hl")
    case None
    then show ?thesis
      by (metis \<open>(b ++ c) hl = Some x\<close> assms(2) larger_heap_def map_add_SomeD)
  next
    case (Some bb)
    then show ?thesis
      by (metis \<open>(b ++ c) hl = Some x\<close> assms(1) assms(2) larger_heap_def map_add_SomeD)
  qed
qed

lemma compatible_heaps_sum:
  assumes "compatible_heaps a b"
      and "compatible_heaps a c"
    shows "compatible_heaps a (b ++ c)"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) compatible_heaps_def map_add_dom_app_simps(1) map_add_dom_app_simps(3))

lemma larger_compatible_sum_heaps:
  assumes "larger_heap a x"
      and "larger_heap b y"
      and "compatible_heaps a b"
    shows "compatible_heaps x y"
proof (rule compatible_heapsI)
  fix hl a b assume "x hl = Some a" "y hl = Some b"
  then show "a = b"
    by (metis assms(1) assms(2) assms(3) compatible_heaps_def compatible_options.simps(1) larger_heap_def)
qed

lemma get_h_m:
  "Rep_state x = (get_m x, get_h x)" by simp

lemma get_pre:
  "get_h x = snd (Rep_state x)"
  "get_m x = fst (Rep_state x)"
  by simp_all

lemma plus_ab_defined:
  "\<phi> \<oplus> \<phi>' \<noteq> None \<longleftrightarrow> compatible_heaps (get_h \<phi>) (get_h \<phi>') \<and> valid_mask (add_masks (get_m \<phi>) (get_m \<phi>'))"
  (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B"
    by (metis compatible_def get_pre(1) get_pre(2) plus_state_def)
  show "?B \<Longrightarrow> ?A"
    using compatible_def plus_state_def by auto
qed

lemma plus_charact:
  assumes "a \<oplus> b = Some x"
    shows "get_m x = add_masks (get_m a) (get_m b)"
      and "get_h x = (get_h a) ++ (get_h b)"
proof -
  have "x = (Abs_state (add_states (Rep_state a) (Rep_state b)))"
    by (metis assms option.discI option.inject plus_state_def)
  moreover have "compatible (Rep_state a) (Rep_state b)"
    using assms(1) plus_state_def by (metis option.discI)

  moreover have "valid_state (add_states (Rep_state a) (Rep_state b))"
  proof -
    have "valid_state (add_masks (get_m a) (get_m b), (get_h a) ++ (get_h b))"
    proof (rule valid_stateI)
      show "valid_mask (add_masks (get_m a) (get_m b))"
        using calculation(2) compatible_def by fastforce
      fix hl assume "PosRat.pnone < add_masks (get_m a) (get_m b) hl"
      then show "(get_h a ++ get_h b) hl \<noteq> None"
      proof (cases "get_m a hl > 0")
        case True
        then show ?thesis
          by (metis Rep_state get_h_m map_add_None mem_Collect_eq valid_heap_def valid_state.simps)
      next
        case False
        then have "get_m b hl > 0"
          by (metis PosRat.padd_mono \<open>PosRat.pnone < add_masks (get_m a) (get_m b) hl\<close> add.right_neutral add_masks.simps linorder_not_le)
        then show ?thesis
          by (metis Rep_state get_h_m map_add_None mem_Collect_eq valid_heap_def valid_state.simps)
      qed
    qed
    then show ?thesis
      using add_states.simps get_h_m by presburger
  qed
  ultimately show "get_m x = add_masks (get_m a) (get_m b)"
    by (metis Abs_state_inverse add_states.simps fst_conv get_h_m mem_Collect_eq)

  show "get_h x = (get_h a) ++ (get_h b)"
    by (metis Abs_state_inject CollectI Rep_state Rep_state_inverse \<open>valid_state (add_states (Rep_state a) (Rep_state b))\<close> \<open>x = Abs_state (add_states (Rep_state a) (Rep_state b))\<close> add_states.simps eq_snd_iff get_h.simps)
qed

lemma commutative:
  "(a :: state) \<oplus> b = b \<oplus> a"
proof (cases "compatible_heaps (get_h a) (get_h b) \<and> valid_mask (add_masks (get_m a) (get_m b))")
  case True
  then have "compatible_heaps (get_h b) (get_h a) \<and> add_masks (get_m a) (get_m b) = add_masks (get_m b) (get_m a)"
    by (metis add_masks_comm compatible_heapsI compatible_heaps_def compatible_options.simps(1))
  then have "(get_h a) ++ (get_h b) = (get_h b) ++ (get_h a)"
    by (simp add: compatible_heaps_comm)
  then show ?thesis
    by (metis (mono_tags, lifting) True \<open>compatible_heaps (get_h b) (get_h a) \<and> add_masks (get_m a) (get_m b) = add_masks (get_m b) (get_m a)\<close> add_states.simps get_h_m plus_ab_defined plus_state_def)
next
  case False
  then show ?thesis
    by (metis add_masks_comm compatible_heapsI compatible_heaps_def compatible_options.simps(1) plus_ab_defined)
qed

lemma asso1:
  assumes "(a::state) \<oplus> b = Some ab \<and> b \<oplus> c = Some bc"
  shows "ab \<oplus> c = a \<oplus> bc"
proof (cases "ab \<oplus> c")
  case None
  then show ?thesis
  proof (cases "compatible_heaps (get_h ab) (get_h c)")
    case True
    then have "\<not> valid_mask (add_masks (add_masks (get_m a) (get_m b)) (get_m c))"
      by (metis None assms plus_ab_defined plus_charact(1))
    then show ?thesis
      by (metis add_masks_asso assms plus_ab_defined plus_charact(1))
  next
    case False
    then have "\<not> compatible_heaps (get_h a ++ get_h b) (get_h c)"
      using assms plus_charact(2) by force
    then obtain l x y where "(get_h a ++ get_h b) l = Some x" "get_h c l = Some y" "x \<noteq> y"
      using compatible_heapsI by blast
    then have "\<not> compatible_heaps (get_h a) (get_h b ++ get_h c)"
    proof (cases "get_h a l")
      case None
      then show ?thesis
        by (metis \<open>(get_h a ++ get_h b) l = Some x\<close> \<open>get_h c l = Some y\<close> \<open>x \<noteq> y\<close> assms compatible_heaps_comm map_add_dom_app_simps(1) map_add_dom_app_simps(3) map_add_find_right option.inject option.simps(3) plus_ab_defined)
    next
      case (Some aa)
      then show ?thesis
        by (metis (no_types, lifting) \<open>(get_h a ++ get_h b) l = Some x\<close> \<open>get_h c l = Some y\<close> \<open>x \<noteq> y\<close> assms compatible_heaps_comm compatible_options.simps(1) map_add_find_right option.discI plus_ab_defined)
    qed
    then show ?thesis
      by (metis None assms plus_ab_defined plus_charact(2))
  qed
next
  case (Some x)
  then have "compatible_heaps (get_h a ++ get_h b) (get_h c)"
    by (metis assms option.simps(3) plus_ab_defined plus_charact(2))
  then have "compatible_heaps (get_h a) (get_h b ++ get_h c)"
    by (metis (full_types) assms compatible_heaps_comm compatible_heaps_def compatible_heaps_sum compatible_options.simps(2) domIff map_add_dom_app_simps(1) option.distinct(1) plus_ab_defined)
  moreover have "valid_mask (add_masks (get_m a) (add_masks (get_m b) (get_m c)))"
    by (metis Some add_masks_asso assms option.distinct(1) plus_ab_defined plus_charact(1))
  ultimately obtain y where "Some y = a \<oplus> bc"
    by (metis assms plus_ab_defined plus_charact(1) plus_charact(2) plus_state_def)
  then show ?thesis
    by (metis (mono_tags, lifting) Some add_masks_asso add_states.simps assms get_h_m map_add_assoc option.distinct(1) plus_charact(1) plus_charact(2) plus_state_def)
qed

lemma asso2:
  assumes "(a::state) \<oplus> b = Some ab \<and> b \<oplus> c = None"
  shows "ab \<oplus> c = None"
proof (cases "valid_mask (add_masks (get_m b) (get_m c))")
  case True
  then have "\<not> compatible_heaps (get_h b) (get_h c)"
    using assms plus_ab_defined by blast
  then obtain l x y where "get_h b l = Some x" "get_h c l = Some y" "x \<noteq> y"
    using compatible_heapsI by blast
  then have "get_h ab l = Some x"
    by (metis assms map_add_find_right plus_charact(2))
  then show ?thesis
    by (metis \<open>get_h c l = Some y\<close> \<open>x \<noteq> y\<close> compatible_heaps_def compatible_options.simps(1) plus_ab_defined)
next
  case False
  then obtain l where "\<not> (1 \<ge> (add_masks (get_m b) (get_m c) l))"
    by (metis (no_types, lifting) PosRat.sum_larger Rep_state add_0 add_masks.elims get_h_m mem_Collect_eq prat_gte_padd valid_mask.simps valid_state.simps)
  then have "\<not> (1 \<ge> (add_masks (get_m ab) (get_m c) l))"
  proof -
    have "(add_masks (get_m ab) (get_m c) l) \<ge> (add_masks (get_m b) (get_m c) l)"
      using PosRat.pgte_antisym PosRat.sum_larger add_masks.elims add_masks_asso add_masks_comm assms nle_le plus_charact(1) prat_gte_padd
      by (smt (verit, del_insts))
    then show ?thesis
      by (meson \<open>\<not> 1 \<ge> (add_masks (get_m b) (get_m c) l)\<close> order_trans pgte.rep_eq)
  qed
  then show ?thesis
    using plus_ab_defined valid_mask.simps
    by (metis PosRat.pgte_antisym PosRat.sum_larger nle_le prat_gte_padd)
qed


lemma core_defined:
  "get_h |\<phi>| = get_h \<phi>"
  "get_m |\<phi>| = empty_mask"
  using Abs_state_inverse core_state_def ppos.rep_eq valid_empty valid_stateI apply force
  by (metis Abs_state_inverse CollectI core_state_def empty_mask.simps fst_conv get_pre(2) less_irrefl valid_empty valid_stateI)


lemma state_ext:
  assumes "get_h a = get_h b"
      and "get_m a = get_m b"
    shows "a = b"
  by (metis Rep_state_inverse assms(1) assms(2) get_h_m)


lemma positivity:
  assumes "(a::state) \<oplus> b = Some c"
      and "Some c = c \<oplus> c"
    shows "Some a = a \<oplus> a"
proof -
  obtain x where "Some x = a \<oplus> a"
    by (metis assms(1) assms(2) asso2 commutative option.exhaust_sel)
  moreover have "x = a"
    apply (rule state_ext)
     apply (metis calculation larger_heap_anti larger_heap_def larger_heap_plus map_add_find_right plus_charact(2))
    by (metis add_masks_cancellative add_masks_comm assms(1) assms(2) calculation greater_mask_def greater_mask_properties(3) minus_empty plus_charact(1))
  ultimately show ?thesis by blast
qed



lemma core_is_smaller:
  "Some x = (x::state) \<oplus> |x|"
proof -
  obtain y where "Some y = x \<oplus> |x|"
    by (metis (mono_tags) Rep_state compatible_heapsI core_defined(1) core_defined(2) get_h_m mem_Collect_eq minus_empty option.collapse option.sel plus_ab_defined valid_state.simps)
  moreover have "y = x"
  proof (rule state_ext)
    have "get_h x = get_h x ++ get_h x"
      by (simp add: map_add_subsumed1)
    then show "get_h y = get_h x"
      using calculation core_defined(1) plus_charact(2) by presburger
    show "get_m y = get_m x"
      by (metis calculation core_defined(2) minus_empty plus_charact(1))
  qed
  ultimately show ?thesis by blast
qed

lemma core_is_pure:
  "Some |x :: state| = |x| \<oplus> |x|"
proof -
  obtain y where "Some y = |x| \<oplus> |x|"
    by (metis (mono_tags) core_state_def core_defined(1) core_is_smaller)
  moreover have "y = |x|"
    by (metis (mono_tags) PartialHeapSA.core_is_smaller calculation core_defined(1) core_state_def option.sel)
  ultimately show ?thesis by blast
qed

lemma core_sum:
  assumes "Some (c::state) = a \<oplus> b"
  shows "Some |c| = |a| \<oplus> |b|"
proof -
  obtain x where "Some x = |a| \<oplus> |b|"
    by (metis (mono_tags) assms core_defined(1) core_defined(2) minus_empty option.exhaust_sel plus_ab_defined valid_empty)
  moreover have "x = |c|"
    by (metis (mono_tags) assms calculation core_defined(1) core_defined(2) minus_empty plus_charact(1) plus_charact(2) state_ext)
  ultimately show ?thesis by blast
qed

lemma core_max:
  assumes "Some (x::state) = x \<oplus> c"
  shows "\<exists>r. Some |x| = c \<oplus> r"
proof -
  obtain y where "Some y = c \<oplus> |x|"
    by (metis assms asso2 core_is_smaller plus_state_def)
  moreover have "|x| = y"
    by (metis (mono_tags, opaque_lifting) Rep_state_inverse add_masks_cancellative assms calculation commutative core_defined(1) core_sum get_h_m minus_empty option.inject plus_charact(1))
  ultimately show ?thesis by blast
qed


lemma cancellative:
  assumes "Some (a::state) = b \<oplus> x"
      and "Some a = b \<oplus> y"
      and "( core x) = ( core y )"
    shows "x = y"
  by (metis add_masks_cancellative assms(1) assms(2) assms(3) core_defined(1) plus_charact(1) state_ext)


instance
proof
  fix a b ab c bc x y :: state
  show "a \<oplus> b = b \<oplus> a"
    by (simp add: PartialHeapSA.commutative)
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
    using PartialHeapSA.asso1 by blast
  show "a \<oplus> b = Some ab \<and> b \<oplus> c = None \<Longrightarrow> ab \<oplus> c = None"
    using PartialHeapSA.asso2 by blast
  show "a \<oplus> b = Some c \<Longrightarrow> Some c = c \<oplus> c \<Longrightarrow> Some a = a \<oplus> a"
    using PartialHeapSA.positivity by blast
  show "Some x = x \<oplus> |x|"
    using PartialHeapSA.core_is_smaller by auto
  show "Some |x| = |x| \<oplus> |x|"
    by (simp add: PartialHeapSA.core_is_pure)
  show "Some x = x \<oplus> c \<Longrightarrow> \<exists>r. Some |x| = c \<oplus> r"
    by (simp add: PartialHeapSA.core_max)
  show "Some c = a \<oplus> b \<Longrightarrow> Some |c| = |a| \<oplus> |b|"
    using PartialHeapSA.core_sum by blast
  show "Some a = b \<oplus> x \<Longrightarrow> Some a = b \<oplus> y \<Longrightarrow> |x| = |y| \<Longrightarrow> x = y"
    using PartialHeapSA.cancellative by blast
qed

lemma definedI:
  assumes "compatible_heaps (get_h a) (get_h b)"
      and "valid_mask (add_masks (get_m a) (get_m b))"
  shows "(a::state) ## b"
  unfolding defined_def plus_state_def
  using assms
  by (simp add: compatible_def)
end

instantiation state :: sep_algebra
begin

definition stable_state :: "state \<Rightarrow> bool" where
  "stable_state \<phi> \<longleftrightarrow> (\<forall>hl. get_m \<phi> hl > 0 \<longleftrightarrow> get_h \<phi> hl \<noteq> None)"

definition stabilize_heap :: "state \<Rightarrow> heap" where
  "stabilize_heap \<phi> l = (if get_m \<phi> l > 0 then get_h \<phi> l else None)"

definition stabilize_state :: "state \<Rightarrow> state" where
  "stabilize_state \<phi> = Abs_state (get_m \<phi>, stabilize_heap \<phi>)"

lemma valid_state_stabilize:
  "valid_state (get_m \<phi>, stabilize_heap \<phi>)"
  apply (rule valid_stateI)
   apply (rule valid_maskI)
  apply (metis Rep_state get_h_m mem_Collect_eq valid_mask.simps valid_state.simps)
  apply (metis Rep_state get_h_m mem_Collect_eq valid_mask.elims(2) valid_state.simps)
  by (metis Rep_state get_h_m mem_Collect_eq stabilize_heap_def valid_heap_def valid_state.simps)

lemma stabilize_charact[simp]:
  "get_m (stabilize x) = get_m x"
  "get_h (stabilize x) = stabilize_heap x"
  using Abs_state_inverse stabilize_state_def valid_state_stabilize apply auto[1]
  using Abs_state_inverse stabilize_state_def valid_state_stabilize by auto


lemma unit_charact:
  "get_h unit = empty_heap"
  "get_m unit = empty_mask"
proof -
  have "valid_state (empty_mask, empty_heap)"
    using valid_pre_unit by auto
  then show "get_h unit = empty_heap" using unit_def
    by (simp add: \<open>unit = Abs_state (empty_mask, empty_heap)\<close> Abs_state_inverse)
  show "get_m unit = empty_mask"
    using \<open>valid_state (empty_mask, empty_heap)\<close> unit_def Abs_state_inverse
    by fastforce
qed

lemma empty_heap_neutral:
  "a ++ empty_heap = a"
proof (rule ext)
  fix x show "(a ++ empty_heap) x = a x"
    by (simp add: domIff empty_heap_def map_add_dom_app_simps(3))
qed

lemma stableI:
  assumes "\<And>hl. get_m \<phi> hl > 0 \<longleftrightarrow> get_h \<phi> hl \<noteq> None"
  shows "stable \<phi>"
  using assms stable_state_def by blast

lemma stable_sum:
  assumes "stable (a::state)"
      and "stable b"
      and "Some x = a \<oplus> b"
    shows "stable x"
proof (rule stableI)
  fix hl
  show "get_m x hl > 0 = (get_h x hl \<noteq> None)" (is "?A \<longleftrightarrow> ?B")
  proof
    show "?A \<Longrightarrow> ?B"
      by (metis Rep_state get_h.simps get_m.simps mem_Collect_eq prod.collapse valid_heap_def valid_state.simps)
    show "?B \<Longrightarrow> ?A"
      using assms(1) assms(2) assms(3) map_add_None plus_charact(1) plus_charact(2)
      unfolding add_masks.simps stable_state_def
      by (metis (no_types, lifting) PosRat.pgte_antisym PosRat.sum_larger add_0 linorder_not_le prat_gte_padd)
  qed
qed

lemma multiply_valid:
  assumes "1 \<ge> p"
  shows "valid_state (multiply_mask p (get_m \<phi>), get_h \<phi>)"
proof (rule valid_stateI)
  show "valid_mask (multiply_mask p (get_m \<phi>))"
    by (metis PartialHeapSA.core_is_smaller PosRat.sum_larger assms core_defined(2) minus_empty option.simps(3) plus_ab_defined prat_gte_padd valid_mult)
  fix hl assume "multiply_mask p (get_m \<phi>) hl > 0"
  then have "get_m \<phi> hl > 0"
    by (metis PosRat.pmin_is PosRat.pmult_comm PosRat.sum_larger Rep_prat_inverse add_0 inf_le1 linorder_not_less mult_cancel_left1 multiply_mask_def nle_le times_prat.rep_eq zero_prat.rep_eq)
  then show "get_h \<phi> hl \<noteq> None"
    by (metis Rep_state get_h_m mem_Collect_eq valid_heap_def valid_state.simps)
qed

section \<open>Instantiation of the package logic with this concrete state model\<close>


lemma get_h_stab_pure[simp]:
  "get_h (stabilize |c| ) = Map.empty"
  apply (rule ext)
  using core_defined(2) stabilize_charact(2) stabilize_heap_def by force

instance
proof
  fix x a b c :: state

  show "sep_algebra_class.stable x \<Longrightarrow> stabilize x = x"
    apply (rule state_ext)
    using stabilize_charact(2) stabilize_heap_def stable_state_def apply auto[1]
    using stabilize_charact(1) by blast

  show "sep_algebra_class.stable (stabilize x)"
    apply (rule stableI)
    unfolding stabilize_state_def stabilize_heap_def
    apply rule
    apply (metis (no_types, lifting) Rep_state get_h_m mem_Collect_eq valid_heap_def valid_state.simps)
    apply simp
    by (smt (verit, best) Abs_state_inverse Rep_state fst_eqD get_pre(1) mem_Collect_eq option.discI prod.collapse sndI valid_heap_def valid_state.simps)
  
  show "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
  proof -
    assume asm0: "Some x = a \<oplus> b"
    have "stabilize a ## stabilize b"
      apply (rule definedI)
       apply (metis asm0 compatible_heaps_def compatible_options.simps(2) compatible_options.simps(3) not_Some_eq plus_ab_defined stabilize_charact(2) stabilize_heap_def)
      by (metis asm0 not_None_eq plus_ab_defined stabilize_charact(1))
    then obtain sab where "Some sab = stabilize a \<oplus> stabilize b"
      by (metis defined_def plus_state_def)
    moreover have "sab = stabilize x"
      unfolding stabilize_state_def stabilize_heap_def
      apply (rule state_ext)
       apply (rule ext)
      defer
      apply (smt (verit, ccfv_threshold) Abs_state_inverse \<open>sep_algebra_class.stable (stabilize x)\<close> \<open>stabilize a ## stabilize b\<close> asm0 calculation defined_def fst_eqD get_pre(2) mem_Collect_eq plus_ab_defined plus_charact(1) stabilize_charact(1) stabilize_charact(2) stabilize_heap_def stable_state_def valid_stateI)
    proof -
      fix xa show "get_h sab xa = get_h (Abs_state (get_m x, \<lambda>l. if PosRat.pnone < get_m x l then get_h x l else None)) xa"
      proof (cases "get_m a xa = 0 \<and> get_m b xa = 0")
        case True
        then have "get_h sab xa = None"
          using calculation plus_charact(2) stabilize_charact(2) stabilize_heap_def by auto
        then show ?thesis
          by (smt (verit, best) Abs_state_inverse Rep_state asm0 calculation get_h_m get_pre(1) mem_Collect_eq plus_charact(1) sndI stabilize_charact(1) valid_heap_def valid_state.simps)
      next
        case False
        then have "get_m a xa > 0 \<or> get_m b xa > 0"
          by (metis PosRat.pgte.rep_eq PosRat.sum_larger add_0 less_prat.rep_eq linorder_less_linear linorder_not_le)
        then have "get_h (stabilize a) xa \<noteq> None \<or> get_h (stabilize b) xa \<noteq> None"
          using stabilize_charact(2) valid_heap_def valid_state.simps valid_state_stabilize by presburger
        moreover have "get_m x xa > 0"
          by (metis False PosRat.pgte_antisym PosRat.sum_larger add_0 add_masks_comm asm0 greater_mask_def greater_mask_equiv_def less_le_not_le linorder_neqE plus_charact(1) prat_gte_padd)
        then have "get_h (Abs_state (get_m x, \<lambda>l. if PosRat.pnone < get_m x l then get_h x l else None)) xa \<noteq> None"
          by (smt (verit, best) Abs_state_inverse get_pre(1) mem_Collect_eq sndI stabilize_heap_def valid_heap_def valid_state.simps valid_state_stabilize)
        then obtain xx where "Some xx = get_h (Abs_state (get_m x, \<lambda>l. if PosRat.pnone < get_m x l then get_h x l else None)) xa"
          "Some xx = get_h x xa"
          by (smt (verit, best) Abs_state_inverse Rep_state get_h_m mem_Collect_eq not_None_eq sndI valid_heap_def valid_state.simps)

        then show ?thesis
          by (smt (verit, del_insts) \<open>Some sab = stabilize a \<oplus> stabilize b\<close> asm0 calculation compatible_heaps_comm map_add_Some_iff plus_ab_defined plus_charact(2) stabilize_charact(2) stabilize_heap_def)
      qed
    qed
    ultimately show "Some (stabilize x) = stabilize a \<oplus> stabilize b"
      by blast
  qed
  
  show "Some x = stabilize x \<oplus> |x|"
    apply (rule sumI)
    apply (metis (mono_tags) compatible_heaps_def compatible_options.simps(2) core_defined(2) defined_def plus_ab_defined smaller_compatible_core stabilize_charact(2) stabilize_heap_def succ_refl)
    apply (rule state_ext)
    defer
    using core_defined(2) plus_charact(1) stabilize_charact(1) apply auto[1]
    apply (subgoal_tac "get_h (stabilize x) ++ get_h |x| = get_h x")
    using plus_charact(2) apply presburger
    apply (rule ext)
    by (metis core_defined(1) map_add_None map_add_dom_app_simps(1) map_add_dom_app_simps(3) stabilize_charact(2) stabilize_heap_def)
  
  show "Some a = b \<oplus> stabilize |c| \<Longrightarrow> a = b"
    apply (rule state_ext)
     apply (rule ext)
    using plus_charact(2) apply simp
    using get_h_stab_pure apply auto[1]
    using core_defined(2) plus_charact(1) stabilize_charact(1) by auto
qed


end

(*


global_interpretation PartialSA: sep_algebra plus_state core
  defines greater (infixl "\<succeq>" 50) = "PartialSA.greater"
      and add_set (infixl "\<otimes>" 60) = "PartialSA.add_set"
      and defined (infixl "|#|" 60) = "PartialSA.defined"
      and greater_set (infixl "|\<ggreater>|" 50) = "PartialSA.greater_set"
      and minus (infixl "|\<ominus>|" 60) = "PartialSA.minus"
  apply standard
  apply (simp add: commutative)
  using asso1 apply blast
  using asso2 apply blast
  using core_is_smaller apply blast
  using core_is_pure apply blast
  using core_max apply blast
  using core_sum apply blast
  using positivity apply blast
  using cancellative apply blast
  using unit_neutral apply blast
  using stable_sum apply blast
  using stable_unit by blast
*)


section \<open>Some lemmas about this instantiation\<close>

lemma greaterI:
  assumes "larger_heap (get_h a) (get_h b)"
      and "greater_mask (get_m a) (get_m b)"
    shows "a \<succeq> b"
proof -
  let ?m = "\<lambda>l. SOME p. get_m a l = get_m b l + p"
  have "get_m a = add_masks (get_m b) ?m"
  proof (rule ext)
    fix l
    have "get_m a l \<ge> (get_m b l)"
      by (meson PosRat.pgte.rep_eq assms(2) greater_mask_equiv_def leD less_prat.rep_eq linorder_le_less_linear)
    then have "get_m a l = (get_m b l) + (SOME p. get_m a l = (get_m b l) + p)"
      by (meson prat_gte_padd someI_ex)
    then show "get_m a l = add_masks (get_m b) (\<lambda>l. SOME p. get_m a l = (get_m b l) + p) l"
      by simp
  qed
  moreover have "valid_state (?m, get_h a)"
  proof (rule valid_stateI)
    show "valid_mask (\<lambda>l. SOME p. get_m a l = (get_m b l) + p)"
      by (metis (no_types, lifting) Rep_state calculation get_h_m mem_Collect_eq upper_valid valid_state.simps)
    fix hl
    assume asm0: "(SOME p. get_m a hl = (get_m b hl) + p) > 0"
    then have "(get_m a hl) > 0"
    proof -
      have "PosRat.pnone \<noteq> get_m b hl \<or> PosRat.pnone \<noteq> get_m a hl"
        using asm0 by fastforce
      then show ?thesis
        by (metis PosRat.pgte.rep_eq PosRat.sum_larger antisym_conv3 assms(2) comm_monoid_add_class.add_0 greater_mask_equiv_def less_le_not_le less_prat.rep_eq)
    qed
    then show "get_h a hl \<noteq> None"
      by (metis Rep_state get_h.simps get_pre(2) mem_Collect_eq prod.collapse valid_heap_def valid_state.simps)
  qed
  moreover have "compatible_heaps (get_h b) (get_h a)"
    by (metis (mono_tags, lifting) assms(1) compatible_heapsI larger_heap_def option.inject)
  ultimately have "(get_m a, get_h a) = add_states (get_m b, get_h b) (?m, get_h a)"
  proof -
    have "get_h b ++ get_h a = get_h a"
    proof (rule ext)
      fix x show "(get_h b ++ get_h a) x = get_h a x"
        by (metis assms(1) domIff larger_heap_def map_add_dom_app_simps(1) map_add_dom_app_simps(3) not_Some_eq)
    qed
    then show ?thesis
      by (metis \<open>get_m a = add_masks (get_m b) (\<lambda>l. SOME p. get_m a l = (get_m b l) + p)\<close> add_states.simps)
  qed
  moreover have "compatible_heaps (get_h b) (get_h a) \<and> valid_mask (add_masks (get_m b) ?m)"
    by (metis Rep_state \<open>compatible_heaps (get_h b) (get_h a)\<close> \<open>get_m a = add_masks (get_m b) (\<lambda>l. SOME p. get_m a l = (get_m b l) + p)\<close> get_h_m mem_Collect_eq valid_state.simps)
  ultimately have "Some a = b \<oplus> Abs_state (?m, get_h a)"
  proof -
    have "Rep_state (Abs_state (?m, get_h a)) = (?m, get_h a)"
      using Abs_state_inverse \<open>valid_state (\<lambda>l. SOME p. get_m a l = (get_m b l) + p, get_h a)\<close> by blast
    moreover have "compatible (Rep_state b) (?m, get_h a)"
      using \<open>compatible_heaps (get_h b) (get_h a) \<and> valid_mask (add_masks (get_m b) (\<lambda>l. SOME p. get_m a l = (get_m b l) + p))\<close> compatible_def by auto
    moreover have "valid_state (add_states (Rep_state b) (?m, get_h a))"
      by (metis Rep_state \<open>(get_m a, get_h a) = add_states (get_m b, get_h b) (\<lambda>l. SOME p. get_m a l = (get_m b l) + p, get_h a)\<close> get_h_m mem_Collect_eq)
    ultimately show ?thesis
      by (metis (no_types, lifting) Rep_state_inverse \<open>(get_m a, get_h a) = add_states (get_m b, get_h b) (\<lambda>l. SOME p. get_m a l = (get_m b l) + p, get_h a)\<close> get_h_m plus_state_def)
  qed
  then show ?thesis
    using greater_def by blast
qed

lemma larger_implies_greater_mask_hl:
  assumes "a \<succeq> b"
  shows "get_m a hl \<ge> get_m b hl"
  by (metis PosRat.pgte.rep_eq PosRat.sum_larger add_masks.simps assms greater_equiv less_eq_prat.rep_eq pre_pcm_class.commutative plus_charact(1))

lemma larger_implies_larger_heap:
  assumes "a \<succeq> b"
  shows "larger_heap (get_h a) (get_h b)"
  by (metis (full_types) greater_equiv assms larger_heapI map_add_find_right plus_charact(2))

lemma compatibleI:
  assumes "compatible_heaps (get_h a) (get_h b)"
      and "valid_mask (add_masks (get_m a) (get_m b))"
    shows "a ## b"
  using assms(1) assms(2) definedI by blast

end