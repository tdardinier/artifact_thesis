theory CSL_IDF_Unbounded
  imports "../FrontEnd/ParImp" "../CoreIVL/SepLogic" "../Viper/ViperLang" UnboundedLogic
begin


type_synonym 'a virtual_state = "heap_loc \<rightharpoonup> (preal \<times> 'a val)"

type_synonym 'v abs_vtyp = "'v set"

record ('v, 'c) abs_type_context =
  variables :: "var \<rightharpoonup> 'v abs_vtyp"
  custom_context :: 'c




subsection \<open>Better definition\<close>



subsection \<open>Pre-virtual equi_states\<close>


lemma plus_val_id :
  "(v :: 'a val) \<oplus> v = Some v"
  by (simp add: plus_val_def)

lemma defined_val :
  "(v :: 'a val) ## v' \<longleftrightarrow> v = v'"
  by (simp add: defined_def plus_val_def)




instantiation val :: (type) sep_algebra
begin

definition stable_val :: "'a val \<Rightarrow> bool" where
  "stable_val _ \<longleftrightarrow> True"

definition stabilize_val :: "'a val \<Rightarrow> 'a val" where
  "stabilize_val v = v"

lemma stable_stabilize_val[simp]:
  fixes v :: "'a val"
  shows "stable v"
    and "stabilize v = v"
  unfolding stabilize_val_def stable_val_def by simp_all

definition core_val :: "'a val \<Rightarrow> 'a val" where
  "core_val v = v"

instance proof
  fix x a b c y :: "'a val"
  show "stable x \<Longrightarrow> stabilize x = x"
    unfolding plus_val_def stabilize_val_def by metis
  show "stable (stabilize x)"
    unfolding plus_val_def stable_val_def by metis
  show "Some x = a \<oplus> b \<Longrightarrow> Some (stabilize x) = stabilize a \<oplus> stabilize b"
    unfolding plus_val_def stabilize_val_def by metis
  show "Some x = stabilize x \<oplus> |x|"
    unfolding plus_val_def stabilize_val_def core_val_def
    by (simp add: EquiSemAuxLemma.core_val_def)
  show "Some a = b \<oplus> stabilize |c| \<Longrightarrow> a = b"
    unfolding plus_val_def stabilize_val_def core_val_def
    by (meson option.inject option.simps(3))
qed

end

subsection \<open>Safety\<close>



definition real_state :: "'a virtual_state \<Rightarrow> bool" where
  "real_state \<omega> \<longleftrightarrow> (\<forall>l p. \<omega> l = Some p \<longrightarrow> fst p = 1)"


definition actual_stable :: "'a virtual_state \<Rightarrow> bool" where
  "actual_stable \<omega> \<longleftrightarrow> (\<forall>l p. \<omega> l = Some p \<longrightarrow> fst p > 0)"

lemma actual_stableI:
  assumes "\<And>l p. \<omega> l = Some p \<Longrightarrow> fst p > 0"
  shows "actual_stable \<omega>"
  using actual_stable_def assms by blast

definition actual_stabilize :: "'a virtual_state \<Rightarrow> 'a virtual_state" where
  "actual_stabilize \<omega> l = (if \<exists>v. \<omega> l = Some (0, v) then None else \<omega> l)"

lemma actual_stabilize_get:
  assumes "actual_stabilize \<omega> l = Some p"
  shows "fst p > 0"
  apply (cases "\<omega> l")
   apply (metis actual_stabilize_def assms option.discI)
  using assms
  unfolding actual_stabilize_def
  apply simp
  apply (case_tac "fst a = 0")
   apply force
  using pperm_pnone_pgt by fastforce


lemma actual_stabilize_is_stable[simp]:
  "actual_stable (actual_stabilize \<omega>)"
  apply (rule actual_stableI)
  by (simp add: actual_stabilize_get)

lemma preal_sumI:
  "Some (a + (b::preal)) = a \<oplus> b"
using SepAlgebra.plus_preal_def by force

lemma compatibleI:
  assumes "\<And>l p p'. a l = Some p \<Longrightarrow> b l = Some p' \<Longrightarrow> snd p = snd p'"
  shows "(a::'a virtual_state) ## b"
proof -
  have "compatible_fun a b"
    apply (rule compatible_funI)
    apply (case_tac "a l"; case_tac "b l")
    apply simp_all
  proof -
    fix l aa bb
    assume asm0: "a l = Some aa" "b l = Some bb"
    moreover have "Some (fst aa + fst bb, snd aa) = aa \<oplus> bb"
      apply (rule plus_prodI)
      apply simp_all      
      using preal_sumI apply blast
      by (metis asm0(1) asm0(2) assms plus_val_def)
    ultimately show "\<exists>y. (let r = aa \<oplus> bb in if r = None then None else Some r) = Some y"
      by (metis (mono_tags, lifting) option.simps(3))
  qed
  then show ?thesis
    by (simp add: defined_def plus_fun_def)
qed

lemma actual_stabilize_smaller[simp]:
  "\<omega> \<succeq> actual_stabilize \<omega>"
proof -
  have "Some \<omega> = actual_stabilize \<omega> \<oplus> |\<omega>| "
    apply (rule plus_funI)
    apply (case_tac "\<omega> l")
    unfolding actual_stabilize_def
    apply simp_all
     apply (simp add: core_fun)
    apply (intro conjI)
     apply clarify
     defer
     apply (simp add: core_fun core_is_smaller)
  proof -
    fix a b aa ba v
    assume "\<omega> (a, b) = Some (0, v)"
    then have "|\<omega>| (a, b) = Some ( |0|, |v| )"
      by (simp add: core_def core_fun)
    then show "Some (0, v) = |\<omega>| (a, b)"
      using core_preal_def core_val_def
      by (simp add: EquiSemAuxLemma.core_val_def)
  qed
  then show ?thesis
    using greater_def by blast
qed

lemma actual_stable_sum:
  assumes "actual_stable a"
      and "actual_stable b"
      and "Some x = a \<oplus> b"
    shows "actual_stable x"
  apply (rule actual_stableI)
  apply (case_tac "a l", case_tac "b l")
  using assms(3) result_sum_partial_functions(2) apply fastforce
   apply (metis actual_stable_def assms(2) assms(3) result_sum_partial_functions(1))
  apply (case_tac "b l")
  apply (metis actual_stable_def assms(1) assms(3) result_sum_partial_functions(2))
proof -
  fix l p aa aaa
  assume asm0: "x l = Some p" "a l = Some aa" "b l = Some aaa"
  then have "fst aa > 0 \<and> fst aaa > 0"
    using actual_stable_def assms(1) assms(2) by blast
  then show "0 < fst p"
  proof -
    have "x l = aa \<oplus> aaa"
      by (meson asm0(2) asm0(3) assms(3) result_sum_partial_functions(3))
    then have "Some (fst p) = Some (fst aa + fst aaa)"
      by (metis (full_types) SepAlgebra.plus_preal_def asm0(1) plus_prodE)
    then show ?thesis
      by (metis (no_types) \<open>0 < fst aa \<and> 0 < fst aaa\<close> antisym_conv2 option.inject order.strict_trans pos_perm_class.sum_larger)
  qed
qed




lemma real_state_implies_stable[simp]:
  assumes "real_state \<omega>"
  shows "actual_stable \<omega>"
  using assms
  unfolding real_state_def actual_stable_def
  by (metis one_neq_zero pperm_pnone_pgt)

abbreviation concretize_heap :: "'a virtual_state \<Rightarrow> 'a partial_heap" where
  "concretize_heap \<omega> l \<equiv> (map_option snd) (\<omega> l)"


abbreviation concretize where                                              
  "concretize s \<omega> \<equiv> (s, concretize_heap \<omega>)"

definition read_dom :: "'a virtual_state \<Rightarrow> address set" where 
  "read_dom \<omega> = { l |l p. \<omega> (l, field_val) = Some p \<and> fst p > 0 }"

definition write_dom :: "'a virtual_state \<Rightarrow> address set" where 
  "write_dom \<omega> = { l |l p. \<omega> (l, field_val) = Some p \<and> fst p \<ge> 1 }"



definition no_aborts where
  "no_aborts C s0 \<omega>0 \<longleftrightarrow> (\<forall>\<omega>0' \<omega>f. actual_stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> real_state \<omega>0' \<longrightarrow> \<not> aborts C (s0, concretize_heap \<omega>0'))"

lemma no_abortsI[intro]:
  assumes "\<And>\<omega>0' \<omega>f. real_state \<omega>0' \<Longrightarrow> actual_stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> \<not> aborts C (s0, concretize_heap \<omega>0')"
  shows "no_aborts C s0 \<omega>0"
  using assms no_aborts_def by fast

lemma no_abortsE:
  assumes "no_aborts C s0 \<omega>0"
      and "real_state \<omega>0'"
      and "actual_stable \<omega>f"
      and "Some \<omega>0' = \<omega>0 \<oplus> \<omega>f"
    shows "\<not> aborts C (s0, concretize_heap \<omega>0')"
  using assms no_aborts_def by fast


type_synonym 'a equi_state = "'a stack agreement \<times> 'a virtual_state"

primrec
  safe :: "nat \<Rightarrow> cmd \<Rightarrow> 'a stack \<Rightarrow> 'a virtual_state \<Rightarrow> 'a equi_state set \<Rightarrow> bool"
where
  "safe 0 C s \<omega> Q \<longleftrightarrow> True"
| "safe (Suc n) C s0 \<omega>0 Q \<longleftrightarrow>
  (C = Cskip \<longrightarrow> (Ag s0, \<omega>0) \<in> Q)
  \<and> accesses C s0 \<subseteq> read_dom \<omega>0
  \<and> writes C s0 \<subseteq> write_dom \<omega>0
  \<and> no_aborts C s0 \<omega>0
  \<and> (\<forall>\<omega>0' \<omega>f C' \<sigma>'. actual_stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> real_state \<omega>0'
\<longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q))"

lemma safeI:
  assumes "C = Cskip \<Longrightarrow> (Ag s0, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "no_aborts C s0 \<omega>0"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. actual_stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> real_state \<omega>0' \<Longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q)"
    shows "safe (Suc n) C s0 \<omega>0 Q"
  using assms safe.simps(1) by auto


lemma safeI_alt:
  assumes "C = Cskip \<Longrightarrow> (Ag s0, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "\<And>\<omega>0' \<omega>f. real_state \<omega>0' \<Longrightarrow> actual_stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> real_state \<omega>0' \<Longrightarrow> aborts C (concretize s0 \<omega>0') \<Longrightarrow> False"
      and "\<And>\<omega>0' \<omega>f C' \<sigma>'. actual_stable \<omega>f \<Longrightarrow> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<Longrightarrow> real_state \<omega>0' \<Longrightarrow>
  (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q)"
    shows "safe (Suc n) C s0 \<omega>0 Q"
  using assms safe.simps(1) 
  by fastforce

lemma safeE:
  assumes "safe (Suc n) C s0 \<omega>0 Q"
  shows "C = Cskip \<Longrightarrow> (Ag s0, \<omega>0) \<in> Q"
      and "accesses C s0 \<subseteq> read_dom \<omega>0"
      and "writes C s0 \<subseteq> write_dom \<omega>0"
      and "no_aborts C s0 \<omega>0"
      and "actual_stable \<omega>f \<and> Some \<omega>0' = \<omega>0 \<oplus> \<omega>f \<and> real_state \<omega>0' \<and> (\<langle>C, concretize s0 \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>)
\<Longrightarrow> (\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q)"
  using assms safe.simps(1) apply simp_all
  by (metis prod.collapse)


definition bounded :: "'a virtual_state \<Rightarrow> bool" where
  "bounded \<omega> \<longleftrightarrow> (\<forall>l p. \<omega> l = Some p \<longrightarrow> fst p \<le> 1)"

definition CSL :: "'a equi_state set \<Rightarrow> cmd \<Rightarrow> 'a equi_state set \<Rightarrow> bool" where
  "CSL P C Q \<longleftrightarrow> (\<forall>n s \<omega>. (Ag s, \<omega>) \<in> P \<and> actual_stable \<omega> \<and> bounded \<omega> \<longrightarrow> safe n C s \<omega> Q)"

lemma real_implies_bounded:
  assumes "real_state \<omega>"
  shows "bounded \<omega>"
  using assms
  unfolding real_state_def bounded_def
  by auto


lemma virtual_state_greater_then:
  assumes "\<omega>' \<succeq> (\<omega>::'a virtual_state)"
      and "\<omega> l = Some (p, v)"
    shows "\<exists>p'. \<omega>' l = Some (p', v) \<and> p' \<ge> p"
proof -
  obtain r where "Some \<omega>' = \<omega> \<oplus> r"
    using assms(1) greater_def by blast
  then have "Some (\<omega>' l) = Some (p, v) \<oplus> r l"
    by (simp add: assms(2) plus_funE)
  then show ?thesis
  proof (cases "r l")
    case None
    then have "\<omega>' l = Some (p, v)"
      using \<open>Some (\<omega>' l) = Some (p, v) \<oplus> r l\<close> by auto
    then show ?thesis
      by blast
  next
    case (Some a)
    then have "Some v = v \<oplus> snd a"
      by (smt (verit) \<open>Some (\<omega>' l) = Some (p, v) \<oplus> r l\<close> option.simps(3) plus_option_Some_None plus_prod_def plus_val_def snd_conv)
    then have "\<omega>' l = Some (p + fst a, v)"
      by (smt (verit) Some \<open>Some \<omega>' = \<omega> \<oplus> r\<close> assms(2) fst_conv plus_prodI preal_plus_iff result_sum_partial_functions(3) snd_conv)
    then show ?thesis
      using padd_pgte by blast
  qed
qed
    

lemma bounded_smaller:
  assumes "\<omega>' \<succeq> \<omega>"
      and "bounded \<omega>'"
    shows "bounded \<omega>"
  using assms
  unfolding bounded_def
  by (smt (verit, del_insts) eq_fst_iff order_trans virtual_state_greater_then)

lemma CSL_I:
  assumes "\<And>n s \<omega>. (Ag s, \<omega>) \<in> P \<Longrightarrow> actual_stable \<omega> \<Longrightarrow> bounded \<omega> \<Longrightarrow> safe (Suc n) C s \<omega> Q"
  shows "CSL P C Q"
  by (metis CSL_def assms not0_implies_Suc safe.simps(1))

lemma CSL_E:
  assumes "CSL P C Q"
      and "(Ag s, \<omega>) \<in> P"
      and "actual_stable \<omega>"
      and "bounded \<omega>"
    shows "safe n C s \<omega> Q"
  using CSL_def assms by fast




lemma safety_mono:
  assumes "safe n C s \<omega> Q"
      and "m \<le> n"
    shows "safe m C s \<omega> Q"
  using assms
proof (induct m arbitrary: C n s \<omega>)
  case (Suc m)
  then obtain k where "n = Suc k"
    using Suc_le_D by presburger
  then show ?case using safeI[of C s \<omega> Q] safeE
    by (smt (verit, ccfv_threshold) Suc.hyps Suc.prems(1) Suc.prems(2) Suc_le_mono)
qed (simp)

lemma no_aborts_agrees:
  assumes "no_aborts C s \<omega>"
      and "agrees (fvC C) s s'"
    shows "no_aborts C s' \<omega>"
proof (rule no_abortsI)
  fix \<omega>0' \<omega>f
  assume asm0: "real_state \<omega>0'" "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
  then show "\<not> aborts C (concretize s' \<omega>0')"
    by (metis asm0(2-4) aborts_agrees agrees_search(1) assms(1) assms(2) fst_conv no_aborts_def snd_conv)
qed

definition overapprox_fv where
  "overapprox_fv A S \<longleftrightarrow> (\<forall>s1 s2 \<gamma>. agrees S s1 s2 \<longrightarrow> ((Ag s1, \<gamma>) \<in> A \<longleftrightarrow> (Ag s2, \<gamma>) \<in> A))"

definition fvA where
  "fvA A = (SOME S. overapprox_fv A S)"

lemma agrees_UNIV_same:
  assumes "agrees UNIV s1 s2"
  shows "s1 = s2"
  apply (rule ext)
  by (meson UNIV_I agrees_def assms)

lemma fvA_agrees:
  assumes "agrees (fvA Q) s s'"
    shows "(Ag s, \<omega>) \<in> Q \<longleftrightarrow> (Ag s', \<omega>) \<in> Q"
proof -
  have "overapprox_fv Q UNIV"
    unfolding overapprox_fv_def
    using agrees_UNIV_same by blast
  then show ?thesis using someI
    by (metis assms fvA_def overapprox_fv_def)
qed



(*
lemma compatibleI:
  assumes "get_store a = get_store b"
      and "get_trace a = get_trace b"
      and "get_state a ## get_state b"
    shows "a ## b"
proof (rule compatible_prodI)
  show "fst a ## fst b"
    using assms(1) get_store_trace_comp by blast
  show "snd a ## snd b"
    apply (rule compatible_prodI)
    apply (metis ag_comp agreement.expand assms(2) get_trace_def)
    by (metis assms(3) get_state_def)
qed
*)

lemma sum_equi_statesI:
  assumes "fst (x :: 'a equi_state) = fst a"
      and "fst x = fst b"
      and "\<And>l. Some (snd x l) = snd a l \<oplus> snd b l"
    shows "Some x = a \<oplus> b"
proof (rule plus_prodI)
  show "Some (fst x) = fst a \<oplus> fst b"
    using assms(1) assms(2) plus_AgI by blast
  show "Some (snd x) = snd a \<oplus> snd b"
    using assms(3) plus_funI by blast
qed


lemma sum_equi_states_easy:
  assumes "Some \<omega> = a \<oplus> b"
  shows "Some (Ag s, \<omega>) = (Ag s, a) \<oplus> (Ag s, b)"
  apply (rule plus_prodI)
  apply (simp add: plus_AgI)
  using assms by auto

lemma sum_equi_states_easy_rev:
  assumes "Some (Ag s, \<omega>) = (s1, \<omega>1) \<oplus> (s2, \<omega>2)"
  shows "s1 = Ag s \<and> s2 = Ag s \<and> Some \<omega> = \<omega>1 \<oplus> \<omega>2"
  using plus_prodE[OF HOL.sym[OF assms(1)]]
  by (metis agreement.collapse fstI plus_AgE snd_eqD)


definition mk_virtual_state :: "'a partial_heap \<Rightarrow> 'a virtual_state" where
  "mk_virtual_state h l = map_option (\<lambda>v. (1, v)) (h l)"

(*
lemma get_wf_easy:
  assumes "wf_pre_virtual_state \<phi>"
  shows "get_vm (Abs_virtual_state \<phi>) = fst \<phi> \<and> concretize_heap (Abs_virtual_state \<phi>) = snd \<phi>"
  by (simp add: Abs_virtual_state_inverse assms get_vh_def get_vm_def)
*)



lemma mk_virtual_state_simps[simp]:
  "concretize_heap (mk_virtual_state h) = h"
  apply (rule ext)
  unfolding mk_virtual_state_def
  by (case_tac "h l") simp_all


lemma mk_virtual_state_charact[simp]:
  "real_state (mk_virtual_state h)"
  "actual_stable (mk_virtual_state h)"
  "concretize s (mk_virtual_state h) = (s, h)"
    apply simp_all
  by (simp_all add: mk_virtual_state_def real_state_def)


lemma binary_mask_and_stable_then_mk_virtual:
  assumes "actual_stable \<omega>"
      and "real_state \<omega>"
    shows "\<omega> = mk_virtual_state (concretize_heap \<omega>)"
  apply (rule ext)
(*  by (case_tac "\<omega> l") simp_all *)
  by (smt (verit, best) assms(2) mk_virtual_state_def option.collapse option.map_disc_iff option.map_sel prod.collapse real_state_def)




lemma fvA_agrees_better:
  assumes "agrees (fvA A) (the_ag (fst a)) (the_ag (fst b))"
      and "a \<in> A"
      and "snd a = snd b"
    shows "b \<in> A"
  using fvA_agrees[OF assms(1), of "snd a"]
  by (metis agreement.exhaust_sel assms(2) assms(3) prod.exhaust_sel)


lemma safe_agrees:
  assumes "safe n C s \<omega> Q"
      and "agrees (fvC C \<union> fvA Q) s s'"
    shows "safe n C s' \<omega> Q"
  using assms
proof (induct n arbitrary: C s s' \<omega>)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s', \<omega>) \<in> Q"
      apply (rule fvA_agrees_better[of _ "(Ag s, \<omega>)"])
            apply (simp_all add: Suc)
      using Suc.prems(2) apply auto[1]
      by (simp add: safeE(1)[OF Suc.prems(1)])

    show "accesses C s' \<subseteq> read_dom \<omega>"
      using Suc.prems(1) Suc.prems(2) accesses_agrees by force
    show "writes C s' \<subseteq> write_dom \<omega>"
      using Suc.prems(1) Suc.prems(2) agrees_simps(4) safeE(3) writes_agrees by blast
    show "no_aborts C s' \<omega>"
      by (metis Suc.prems(1) Suc.prems(2) agrees_simps(4) no_aborts_agrees safeE(4))
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'" "\<langle>C, concretize s' \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain s'' h' where "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'"
      using red_agrees[OF asm0(4)]
      by (metis Suc.prems(2) Un_upper1 agrees_search(1) fst_conv snd_conv)
    then obtain \<omega>1 \<omega>1' where r1: "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1'
  \<and> snd (s'', h') = concretize_heap \<omega>1' \<and> safe n C' (fst (s'', h')) \<omega>1 Q"
      using safeE(5)[OF Suc(2), of \<omega>f \<omega>0' C']
      using asm0(1) asm0(2) asm0(3) by blast
    moreover have "safe n C' (fst \<sigma>') \<omega>1 Q"
    proof (rule Suc.hyps)
      show "safe n C' (fst (s'', h')) \<omega>1 Q"
        using r1 by blast
      show "agrees (fvC C' \<union> fvA Q) (fst (s'', h')) (fst \<sigma>')"
        by (metis \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'\<close> agreesC agrees_simps(4) fst_eqD red_properties sup.absorb_iff1)
    qed
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
      using \<open>\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', (s'', h')\<rangle> \<and> agrees (fvC C \<union> fvA Q) (fst \<sigma>') s'' \<and> snd \<sigma>' = h'\<close> r1 by auto
  qed
qed (simp)



subsection \<open>Skip\<close>

lemma safe_skip[intro!]:
  assumes "(Ag s, \<omega>) \<in> Q"
  shows "safe n Cskip s \<omega> Q"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "no_aborts Cskip s \<omega>"
      by (simp add: no_abortsI)
    show "Cskip = Cskip \<Longrightarrow> (Ag s, \<omega>) \<in> Q"
      by (simp add: assms)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume "\<langle>Cskip, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
      by force
  qed (simp_all)
qed (simp)

proposition rule_skip:
  "CSL P Cskip P"
  using CSL_def by blast




subsection \<open>Frame rule\<close>



lemma read_dom_mono:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "read_dom \<omega> \<subseteq> read_dom \<omega>'"
  unfolding read_dom_def
  apply rule
  apply simp
  by (meson assms dual_order.strict_trans1 virtual_state_greater_then)


lemma write_dom_mono:
  assumes "\<omega>' \<succeq> \<omega>"
  shows "write_dom \<omega> \<subseteq> write_dom \<omega>'"
  unfolding write_dom_def
  apply rule
  apply simp
  by (meson assms dual_order.trans virtual_state_greater_then)


lemma no_aborts_mono_aux:
  assumes "aborts C \<sigma>'"
      and "fst \<sigma>' = s"
      and "snd \<sigma>' = h'"
      and "h \<subseteq>\<^sub>m h'"
    shows "aborts C (s, h)"
  using assms
proof (induct arbitrary:  rule: aborts.induct)
  case (aborts_Read \<sigma> r l x)
  then show ?case
    by (metis (no_types, lifting) aborts.aborts_Read fst_conv map_le_implies_dom_le snd_conv subsetD)
next
  case (aborts_Write \<sigma> r l E)
  then show ?case
    by (metis (no_types, lifting) aborts.aborts_Write fst_conv map_le_implies_dom_le snd_conv subsetD)
next
  case (aborts_Free \<sigma> r l)
  then show ?case
    by (metis (no_types, lifting) aborts.aborts_Free fst_conv map_le_implies_dom_le snd_conv subsetD)
qed (auto)

lemma actual_stabilize_sum_result_stable:
  assumes "Some x = a \<oplus> b"
      and "actual_stable x"
    shows "Some x = actual_stabilize a \<oplus> b"
proof (rule plus_funI)
  fix l show "Some (x l) = actual_stabilize a l \<oplus> b l"
    apply (cases "b l")
    apply (smt (verit, ccfv_threshold) actual_stabilize_def actual_stable_def assms(1) assms(2) linorder_neq_iff option_plus_None_r result_sum_partial_functions(2) split_pairs)
    apply (cases "a l")
     apply (simp add: actual_stabilize_def assms(1) plus_funE)
  proof -
    fix bb aa
    assume asm0: "b l = Some bb" "a l = Some aa"
    then have "x l = aa \<oplus> bb"
      by (meson assms(1) result_sum_partial_functions(3))
    show "Some (x l) = actual_stabilize a l \<oplus> b l"
      apply (cases "fst aa \<noteq> 0")
      apply (metis actual_stabilize_def asm0(2) assms(1) fst_conv fun_plus_iff option.sel)
    proof -
      assume "\<not> fst aa \<noteq> 0"
      then have "actual_stabilize a l = None"
        by (metis actual_stabilize_def actual_stabilize_get asm0(2) pperm_pgt_pnone)
      moreover have "Some bb = aa \<oplus> bb"
        apply (rule plus_prodI)
        using \<open>\<not> fst aa \<noteq> 0\<close> preal_plus_iff apply auto[1]
      proof -
        have "Some (snd (the (x l))) = snd aa \<oplus> snd bb"
          by (metis \<open>x l = aa \<oplus> bb\<close> asm0(1) asm0(2) assms(1) fun_plus_iff option.expand option.sel option.simps(3) plus_option_Some_None plus_prodE)
        then show "Some (snd bb) = snd aa \<oplus> snd bb"
          by (metis option.simps(3) plus_val_def)
      qed
      ultimately show "Some (x l) = actual_stabilize a l \<oplus> b l"
        by (simp add: \<open>x l = aa \<oplus> bb\<close> asm0(1))
    qed
  qed
qed



lemma no_aborts_mono:
  assumes "no_aborts C s \<omega>"
      and "\<omega>' \<succeq> \<omega>"
    shows "no_aborts C s \<omega>'"
proof (rule no_abortsI)
  fix \<omega>0' \<omega>f
  assume asm0: "real_state \<omega>0'" "actual_stable \<omega>f" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f"
  then obtain r where "Some \<omega>0' = \<omega> \<oplus> r"
    using assms(2) bigger_sum_smaller by blast
  then have "Some \<omega>0' = \<omega> \<oplus> actual_stabilize r"

    by (metis (no_types, lifting) asm0(1) commutative real_state_implies_stable actual_stabilize_sum_result_stable)
  then show "\<not> aborts C (concretize s \<omega>0')"
    using asm0(1) asm0(2) asm0(3) assms(1) no_abortsE actual_stabilize_is_stable by blast
qed


lemma frame_safe:
  assumes "safe n C s \<omega> Q"
      and "fvA R \<inter> wrC C = {}"
      and "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "(Ag s, \<omega>f) \<in> R"
      and "actual_stable \<omega>f"
    shows "safe n C s \<omega>' (Q \<otimes> R)"
  using assms
proof (induct n arbitrary: C \<omega> \<omega>' \<omega>f s)
  case (Suc n)
  show ?case
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<omega>') \<in> Q \<otimes> R"
      using safeE(1)[OF Suc(2)]
      by (meson Suc.prems(3) Suc.prems(4) sum_equi_states_easy x_elem_set_product)
    show "accesses C s \<subseteq> read_dom \<omega>'"
      using safeE(2)[OF Suc(2)]
      using Suc.prems(3) commutative greater_equiv read_dom_mono by fastforce
    show "writes C s \<subseteq> write_dom \<omega>'"
      by (metis (no_types, lifting) Suc.prems(1) Suc.prems(3) greater_def inf.absorb_iff2 inf.coboundedI1 safeE(3) write_dom_mono)
    show "no_aborts C s \<omega>'"
      using safeE(4)[OF Suc.prems(1)]
      using Suc.prems(3) greater_def no_aborts_mono by blast
    fix \<omega>0' \<omega>f' C' \<sigma>'
    assume asm0: "actual_stable \<omega>f'" "Some \<omega>0' = \<omega>' \<oplus> \<omega>f'" "real_state \<omega>0'" "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain \<omega>f'' where "Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'"
      by (metis (no_types, opaque_lifting) Suc.prems(3) asso2 option.collapse)
    then have "Some \<omega>0' = \<omega> \<oplus> \<omega>f''"
      using asm0 Suc.prems(3) asso1 by force
    then obtain \<omega>1'' \<omega>1' where "Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1'" "safe n C' (fst \<sigma>') \<omega>1'' Q"
      "actual_stable \<omega>1''"
      using safeE(5)[OF Suc(2), of \<omega>f'' \<omega>0' C' \<sigma>'] asm0 safeE(5)
      by (meson Suc.prems(1) Suc.prems(5) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> safeE(5) actual_stable_sum)
    then obtain \<omega>1 where "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
      by (metis (no_types, opaque_lifting) \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> asso3 option.collapse)
    moreover have "safe n C' (fst \<sigma>') \<omega>1 (Q \<otimes> R)"
      using \<open>safe n C' (fst \<sigma>') \<omega>1'' Q\<close>
    proof (rule Suc(1)[of C' _ \<omega>1'' \<omega>1 \<omega>f])
      show "fvA R \<inter> wrC C' = {}"
        by (meson Suc.prems(2) asm0 disjoint_iff red_properties subset_iff)
      show "Some \<omega>1 = \<omega>1'' \<oplus> \<omega>f"
        using calculation by auto
      have "agrees (-(wrC C)) s (fst \<sigma>')"
        by (metis agrees_search(1) asm0(4) fst_conv red_properties)
      then have "agrees (fvA R) s (fst \<sigma>')"
        using Suc.prems(2) agrees_search(3) by auto
      show "(Ag (fst \<sigma>'), \<omega>f) \<in> R"
        by (meson Suc.prems(4) \<open>agrees (fvA R) s (fst \<sigma>')\<close> fvA_agrees)
    qed (simp_all add: Suc.prems)
    ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f' \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (Q \<otimes> R)"
      by (metis Suc.prems(5) \<open>Some \<omega>1' = \<omega>1'' \<oplus> \<omega>f'' \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1'\<close> \<open>Some \<omega>f'' = \<omega>f \<oplus> \<omega>f'\<close> \<open>actual_stable \<omega>1''\<close> asso1 actual_stable_sum)
  qed
qed (simp)


lemma sum_equi_states_easy_decompose:
  assumes "(Ag s, \<omega>) \<in> P \<otimes> R"
  shows "\<exists>\<omega>p \<omega>r. Some \<omega> = \<omega>p \<oplus> \<omega>r \<and> (Ag s, \<omega>p) \<in> P \<and> (Ag s, \<omega>r) \<in> R"
  by (smt (verit, ccfv_threshold) assms prod.exhaust_sel sum_equi_states_easy_rev x_elem_set_product)


lemma actual_stabilize_sum_of_stable:
  assumes "actual_stable x"
      and "Some x = a \<oplus> b"
    shows "Some x = actual_stabilize a \<oplus> actual_stabilize b"
  by (metis (no_types, lifting) actual_stabilize_sum_result_stable assms(1) assms(2) commutative)


definition actual_self_framing where
  "actual_self_framing A \<longleftrightarrow> (\<forall>s \<omega>. (s, \<omega>) \<in> A \<longleftrightarrow> (s, actual_stabilize \<omega>) \<in> A)"

lemma actual_self_framingE:
  assumes "actual_self_framing A"
      and "(s, \<omega>) \<in> A"
    shows "(s, actual_stabilize \<omega>) \<in> A"
  using actual_self_framing_def assms(1) assms(2) by fastforce

proposition frame_rule:
  assumes "CSL P C Q"
      and "disjoint (fvA R) (wrC C)"
      and "actual_self_framing P"
      and "actual_self_framing R"
    shows "CSL (P \<otimes> R) C (Q \<otimes> R)"
proof (rule CSL_I)
  fix n s \<omega> assume asm0: "(Ag s, \<omega>) \<in> P \<otimes> R" "actual_stable \<omega>" "bounded \<omega>"
  then obtain \<omega>p \<omega>r where r: "Some \<omega> = \<omega>p \<oplus> \<omega>r" "(Ag s, \<omega>p) \<in> P" "(Ag s, \<omega>r) \<in> R"
    by (meson sum_equi_states_easy_decompose)

  show "safe (Suc n) C s \<omega> (Q \<otimes> R)"
  proof (rule frame_safe[of "Suc n" C s "actual_stabilize \<omega>p" Q R \<omega> "actual_stabilize \<omega>r"])
    show "Some \<omega> = actual_stabilize \<omega>p \<oplus> actual_stabilize \<omega>r"
      using \<open>actual_stable \<omega>\<close> actual_stabilize_sum_of_stable r by blast
    show "safe (Suc n) C s (actual_stabilize \<omega>p) Q"
      by (meson CSL_def \<open>Some \<omega> = actual_stabilize \<omega>p \<oplus> actual_stabilize \<omega>r\<close> actual_self_framingE actual_stabilize_is_stable asm0(3) assms(1) assms(3) bounded_smaller greater_def r(2))
    show "fvA R \<inter> wrC C = {}"
      by (meson assms(2) disjoint_def)
    show "(Ag s, actual_stabilize \<omega>r) \<in> R"
      by (metis assms(4) r(3) actual_self_framingE)
  qed (simp_all add: assms)
qed




subsection \<open>Parallel rule\<close>

lemma compatible_sum_less_one:
  assumes "Some \<omega> = a \<oplus> b"
      and "bounded \<omega>"
      and "a l = Some (p1, v)"
      and "b l = Some (p2, v)"
    shows "p1 + p2 \<le> 1"
proof -
  have "Some (the (\<omega> l)) = (p1, v) \<oplus> (p2, v)"
    by (smt (verit, ccfv_threshold) assms(1) assms(3) assms(4) option.exhaust_sel option.simps(3) plus_funE plus_option_Some_None result_sum_partial_functions(3))
  then show ?thesis
    by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) bounded_def fst_eqD plus_prodE preal_plusE result_sum_partial_functions(3))
qed

lemma disj_conv:
  assumes "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
      and "bounded \<omega>"
  shows "disjoint (write_dom \<omega>1) (read_dom \<omega>2)"
  unfolding disjoint_def
proof
  show "write_dom \<omega>1 \<inter> read_dom \<omega>2 \<subseteq> {}"
  proof
    fix l assume "l \<in> write_dom \<omega>1 \<inter> read_dom \<omega>2"
    then obtain p1 p2 where "\<omega>1 (l, field_val) = Some p1 \<and> fst p1 \<ge> 1" "\<omega>2 (l, field_val) = Some p2 \<and> fst p2 > 0"
      by (smt (verit) IntD1 IntD2 mem_Collect_eq read_dom_def write_dom_def)
    then obtain p where "\<omega> (l, field_val) = Some p"
      by (metis (no_types, opaque_lifting) assms(1) greater_def split_pairs virtual_state_greater_then)
    then have "Some p = p1 \<oplus> p2"
      using \<open>\<omega>1 (l, field_val) = Some p1 \<and> 1 \<le> fst p1\<close> \<open>\<omega>2 (l, field_val) = Some p2 \<and> 0 < fst p2\<close> assms(1) result_sum_partial_functions(3) by fastforce
    then have "fst p = fst p1 + fst p2"
      by (metis plus_prodE preal_plusE)
    then show "l \<in> {}"
      using compatible_sum_less_one[OF assms(1-2), of "(l, field_val)" "fst p1" "snd p1" "fst p2"]
      by (metis (mono_tags, opaque_lifting) PosReal.padd_cancellative \<open>\<omega> (l, field_val) = Some p\<close> \<open>\<omega>1 (l, field_val) = Some p1 \<and> 1 \<le> fst p1\<close> \<open>\<omega>2 (l, field_val) = Some p2 \<and> 0 < fst p2\<close> add.commute antisym_conv1 assms(2) bounded_def comm_monoid_add_class.add_0 dual_order.strict_trans1 leD padd_pgte)
  qed
qed (simp)

lemma read_dom_union:
  assumes "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
  shows "read_dom \<omega> = read_dom \<omega>1 \<union> read_dom \<omega>2" (is "?A = ?B")
  unfolding read_dom_def
  apply rule
   apply rule
   apply simp
   apply (elim exE conjE)
   apply (case_tac "\<omega>1 (x, field_val)")
  using assms result_sum_partial_functions(1) apply fastforce
   apply (case_tac "\<omega>2 (x, field_val)")
  using assms result_sum_partial_functions(2) apply fastforce
proof -
  fix x a b aa ab
  assume asm0: "0 < a" "\<omega> (x, field_val) = Some (a, b)" "\<omega>1 (x, field_val) = Some aa"
       "\<omega>2 (x, field_val) = Some ab"
  then have "a = fst aa + fst ab"
    by (smt (verit) assms fst_conv plus_prodE preal_plus_iff result_sum_partial_functions(3))
  then have "fst aa > 0 \<or> fst ab > 0"
    using asm0(1) preal_not_0_gt_0 by fastforce
  then show "(\<exists>a. (\<exists>b. \<omega>1 (x, field_val) = Some (a, b)) \<and> 0 < a) \<or> (\<exists>a. (\<exists>b. \<omega>2 (x, field_val) = Some (a, b)) \<and> 0 < a)"
    by (metis asm0(3) asm0(4) prod.exhaust_sel)
next
  show "{uu. \<exists>l p. uu = l \<and> \<omega>1 (l, field_val) = Some p \<and> 0 < fst p} \<union> {uu. \<exists>l p. uu = l \<and> \<omega>2 (l, field_val) = Some p \<and> 0 < fst p}
    \<subseteq> {uu. \<exists>l p. uu = l \<and> \<omega> (l, field_val) = Some p \<and> 0 < fst p}"
    apply rule
    apply simp
    apply (elim exE disjE conjE)
  proof -
    fix x a b
    assume asm0: "0 < a" "\<omega>1 (x, field_val) = Some (a, b)"
    then have "\<exists>p'. \<omega> (x, field_val) = Some (p', b) \<and> a \<le> p'"
      using virtual_state_greater_then[of \<omega> \<omega>1 "(x, field_val)" a b]
      using assms greater_def by blast
    then show "\<exists>a. (\<exists>b. \<omega> (x, field_val) = Some (a, b)) \<and> 0 < a"
      using asm0(1) dual_order.strict_trans1 by blast
  next
    fix x a b
    assume asm0: "0 < a" "\<omega>2 (x, field_val) = Some (a, b)"
    then have "\<exists>p'. \<omega> (x, field_val) = Some (p', b) \<and> a \<le> p'"
      using virtual_state_greater_then[of \<omega> \<omega>2 "(x, field_val)" a b]
      using assms greater_def commutative by fastforce
    then show "\<exists>a. (\<exists>b. \<omega> (x, field_val) = Some (a, b)) \<and> 0 < a"
      using asm0(1) dual_order.strict_trans1 by blast
  qed
qed
    
(*

proof -
  have "\<And>l. l \<in> ?A \<longleftrightarrow> l \<in> ?B"
  proof -
    fix l
    have "l \<in> ?A \<longleftrightarrow> get_vm \<omega> (l, field_val) > 0"
      unfolding read_dom_def by simp
    also have "... \<longleftrightarrow> get_vm \<omega>1 (l, field_val) + get_vm \<omega>2 (l, field_val) > 0"
      by (simp add: EquiViper.add_masks_def assms get_vm_additive)
    also have "... \<longleftrightarrow> get_vm \<omega>1 (l, field_val) > 0 \<or> get_vm \<omega>2 (l, field_val) > 0"
      by (metis add_0 padd_pos pperm_pnone_pgt)
    finally show "l \<in> ?A \<longleftrightarrow> l \<in> ?B"
      unfolding read_dom_def by blast
  qed
  then show ?thesis by blast
qed
*)

lemma write_dom_union:
  assumes "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
  shows "write_dom \<omega>1 \<union> write_dom \<omega>2 \<subseteq> write_dom \<omega>"
  by (meson Un_least assms greater_def greater_equiv write_dom_mono)

lemma safe_par:
  assumes "safe n C1 s \<omega>1 Q1"
      and "safe n C2 s \<omega>2 Q2"
      and "Some \<omega> = \<omega>1 \<oplus> \<omega>2"
      and "disjoint (fvC C1 \<union> fvA Q1) (wrC C2)"
      and "disjoint (fvC C2 \<union> fvA Q2) (wrC C1)"
      and "actual_stable \<omega>1"
      and "actual_stable \<omega>2"
    shows "safe n ({A1} C1 {B1} || {A2} C2 {B2}) s \<omega> (Q1 \<otimes> Q2)"
  using assms
proof (induct n arbitrary: C1 C2 \<omega>1 \<omega>2 \<omega> s)
  case (Suc n)
  show "safe (Suc n) ({A1} C1 {B1} || {A2} C2 {B2}) s \<omega> (Q1 \<otimes> Q2)"
  proof (rule safeI_alt)
    show "accesses ({A1} C1 {B1} || {A2} C2 {B2}) s \<subseteq> read_dom \<omega>"
      by (metis Suc.prems(1) Suc.prems(2) Suc.prems(3) Un_mono accesses.simps(8) read_dom_union safeE(2))
    show "writes ({A1} C1 {B1} || {A2} C2 {B2}) s \<subseteq> write_dom \<omega>"
    proof -
      have "writes C1 s \<subseteq> write_dom \<omega> \<and> writes C2 s \<subseteq> write_dom \<omega>"
        by (metis (no_types, lifting) Suc.prems(1) Suc.prems(2) Suc.prems(3) dual_order.trans le_supE safeE(3) write_dom_union)
      then show ?thesis
        by simp
    qed
    fix \<omega>0' \<omega>f
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    show "aborts ({A1} C1 {B1} || {A2} C2 {B2}) (concretize s \<omega>0') \<Longrightarrow> False"
    proof -
      assume "aborts ({A1} C1 {B1} || {A2} C2 {B2}) (concretize s \<omega>0')"
      then show "False"
      proof (rule aborts_par_elim)
        obtain \<omega>f1 where "Some \<omega>f1 = \<omega>2 \<oplus> \<omega>f"
          by (metis (no_types, lifting) Suc.prems(3) asm0(2) asso2 plus_fun_def)
        then show "aborts C1 (concretize s \<omega>0') \<Longrightarrow> False"
          using no_abortsE[OF safeE(4)[OF Suc.prems(1)], of \<omega>0' \<omega>f1]
          by (metis Suc.prems(3) Suc.prems(7) asm0(1) asm0(2) asm0(3) asso1 actual_stable_sum)
        obtain \<omega>f2 where "Some \<omega>f2 = \<omega>1 \<oplus> \<omega>f"
          by (metis (no_types, opaque_lifting) Suc.prems(3) asm0(2) asso3 commutative option.exhaust)
        then show "aborts C2 (concretize s \<omega>0') \<Longrightarrow> False"
          using no_abortsE[OF safeE(4)[OF Suc.prems(2)], of \<omega>0' \<omega>f2]
          by (metis (no_types, lifting) Suc.prems(3) Suc.prems(6) asm0(1) asm0(2) asm0(3) asso1 commutative actual_stable_sum)
        have r1: "accesses C1 s \<subseteq> read_dom \<omega>1 \<and> writes C1 s \<subseteq> write_dom \<omega>1"
          using Suc.prems(1) by auto
        moreover have r2: "accesses C2 s \<subseteq> read_dom \<omega>2 \<and> writes C2 s \<subseteq> write_dom \<omega>2"
          using Suc.prems(2) by auto
        moreover have "bounded \<omega>0'"
          using asm0(3) real_implies_bounded by blast
        moreover obtain \<omega>12 where "Some \<omega>12 = \<omega>1 \<oplus> \<omega>2"
          using Suc.prems(3) by auto
        then have "bounded \<omega>12"
          by (metis Suc.prems(3) asm0(2) bounded_smaller calculation(3) greater_def option.inject)
        ultimately show "\<not> disjoint (accesses C1 (fst (concretize s \<omega>0'))) (writes C2 (fst (concretize s \<omega>0'))) \<Longrightarrow> False"
          using Pair_inject Suc.prems(3) commutative disjoint_search(3) disjoint_search(4) prod.exhaust_sel
          by (metis (no_types, lifting) \<open>Some \<omega>12 = \<omega>1 \<oplus> \<omega>2\<close> \<open>bounded \<omega>12\<close> disj_conv)
        show "\<not> disjoint (writes C1 (fst (concretize s \<omega>0'))) (accesses C2 (fst (concretize s \<omega>0'))) \<Longrightarrow> False"
          by (metis \<open>Some \<omega>12 = \<omega>1 \<oplus> \<omega>2\<close> \<open>bounded \<omega>12\<close> disj_conv disjoint_search(3) fst_conv r1 r2)
      qed
    qed

    fix C' \<sigma>'
    assume asm1: "\<langle>({A1} C1 {B1} || {A2} C2 {B2}), concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (Q1 \<otimes> Q2)"
    proof (rule red_par_cases)
      assume "C' = Cskip" "\<sigma>' = concretize s \<omega>0'" "C1 = Cskip" "C2 = Cskip"
      then have "(Ag s, \<omega>1) \<in> Q1 \<and> (Ag s, \<omega>2) \<in> Q2"
        using safeE(1)[OF Suc.prems(1)] safeE(1)[OF Suc.prems(2)]
        by simp
      then have "(Ag s, \<omega>) \<in> Q1 \<otimes> Q2"
        by (meson Suc.prems(3) sum_equi_states_easy x_elem_set_product)
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (Q1 \<otimes> Q2)"
        using Suc.prems(3) Suc.prems(6) Suc.prems(7) asm0(3) fst_conv safe_skip snd_conv actual_stable_sum
        by (metis (no_types, lifting) \<open>C' = Cskip\<close> \<open>\<sigma>' = concretize s \<omega>0'\<close> asm0(2))
    next
      fix C1'
      assume asm2: "C' = ({A1} C1' {B1} || {A2} C2 {B2})" "\<langle>C1, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle>"
      obtain \<omega>f' where "Some \<omega>f' = \<omega>2 \<oplus> \<omega>f"
        by (metis (no_types, lifting) Suc.prems(3) asm0(2) asso2 plus_fun_def)
      then have "Some \<omega>0' = \<omega>1 \<oplus> \<omega>f'"
        using Suc.prems(3) asm0(2) asso1 by force
      then obtain \<omega>a \<omega>a' where ra: "Some \<omega>a' = \<omega>a \<oplus> \<omega>f' \<and> real_state \<omega>a' \<and> snd \<sigma>' = concretize_heap \<omega>a'" "safe n C1' (fst \<sigma>') \<omega>a Q1"
        "actual_stable \<omega>a"
        using safeE(5)[OF Suc(2), of \<omega>f' \<omega>0' C1' \<sigma>'] asm0 asm2(2)
        using Suc.prems(7) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> actual_stable_sum by blast
      moreover have "safe n C2 (fst \<sigma>') \<omega>2 Q2"
      proof (rule safe_agrees)
        show "safe n C2 s \<omega>2 Q2"
          by (meson Suc.prems(2) Suc_n_not_le_n nat_le_linear safety_mono)
        have "agrees (-wrC C1) s (fst \<sigma>')"
          by (metis agrees_search(1) asm2(2) fst_conv red_properties)
        then show "agrees (fvC C2 \<union> fvA Q2) s (fst \<sigma>')"
          using Suc.prems(5) agrees_minusD disjoint_search(1) by blast
      qed
      moreover obtain \<omega>' where "Some \<omega>' = \<omega>a \<oplus> \<omega>2"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asso2 calculation(1) commutative option.exhaust_sel)
      then have "Some \<omega>a' = \<omega>' \<oplus> \<omega>f"
        by (metis \<open>Some \<omega>f' = \<omega>2 \<oplus> \<omega>f\<close> asso1 calculation(1))
      moreover have "safe n {A1} C1' {B1} || {A2} C2 {B2} (fst \<sigma>') \<omega>' (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>2\<close>
      proof (rule Suc(1)[OF ra(2) \<open>safe n C2 (fst \<sigma>') \<omega>2 Q2\<close>])
        show "disjoint (fvC C1' \<union> fvA Q1) (wrC C2)"
          by (metis Suc.prems(4) asm2(2) disjoint_search(2) disjoint_simps(3) red_properties)
        show "disjoint (fvC C2 \<union> fvA Q2) (wrC C1')"
          by (meson Suc.prems(5) asm2(2) disjoint_search(1) disjoint_search(2) red_properties)
      qed (simp_all add: Suc disjoint_def ra(3))
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>a' = \<omega>' \<oplus> \<omega>f\<close> ra(1)
        using Suc.prems(7) \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>2\<close> \<open>actual_stable \<omega>a\<close> actual_stable_sum
        using asm2(1) by blast
    next
      fix C2'
      assume asm2: "C' = ({A1} C1 {B1} || {A2} C2' {B2})" "\<langle>C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C2', \<sigma>'\<rangle>"
      obtain \<omega>f' where "Some \<omega>f' = \<omega>1 \<oplus> \<omega>f"
        by (metis (no_types, lifting) Suc.prems(3) asm0(2) asso2 commutative plus_fun_def)
      then have "Some \<omega>0' = \<omega>2 \<oplus> \<omega>f'"
        using Suc.prems(3) asm0(2) asso1 commutative by force
      then obtain \<omega>a \<omega>a' where ra: "Some \<omega>a' = \<omega>a \<oplus> \<omega>f' \<and> real_state \<omega>a' \<and> snd \<sigma>' = concretize_heap \<omega>a'" "safe n C2' (fst \<sigma>') \<omega>a Q2"
        "actual_stable \<omega>a"
        using safeE(5)[OF Suc(3), of \<omega>f' \<omega>0' C2' \<sigma>'] asm0 asm2(2)
        using Suc.prems(6) \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> actual_stable_sum by blast
      moreover have "safe n C1 (fst \<sigma>') \<omega>1 Q1"
      proof (rule safe_agrees)
        show "safe n C1 s \<omega>1 Q1"
          by (meson Suc.prems(1) Suc_n_not_le_n nat_le_linear safety_mono)
        have "agrees (-wrC C2) s (fst \<sigma>')"
          by (metis agrees_search(1) asm2(2) fst_conv red_properties)
        then show "agrees (fvC C1 \<union> fvA Q1) s (fst \<sigma>')"
          using Suc.prems(4) agrees_minusD disjoint_search(1) by blast
      qed
      moreover obtain \<omega>' where "Some \<omega>' = \<omega>a \<oplus> \<omega>1"
        by (metis (no_types, opaque_lifting) \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asso2 calculation(1) commutative option.exhaust_sel)
      then have "Some \<omega>a' = \<omega>' \<oplus> \<omega>f"
        by (metis \<open>Some \<omega>f' = \<omega>1 \<oplus> \<omega>f\<close> asso1 calculation(1))
      moreover have "safe n {A1} C1 {B1} || {A2} C2' {B2} (fst \<sigma>') \<omega>' (Q1 \<otimes> Q2)"
      proof (rule Suc(1)[OF  \<open>safe n C1 (fst \<sigma>') \<omega>1 Q1\<close> ra(2)])
        show "Some \<omega>' = \<omega>1 \<oplus> \<omega>a"
          by (simp add: \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>1\<close> commutative)
        show "disjoint (fvC C2' \<union> fvA Q2) (wrC C1)"
          by (metis Suc.prems(5) asm2(2) disjoint_search(2) disjoint_simps(3) red_properties)
        show "disjoint (fvC C1 \<union> fvA Q1) (wrC C2')"
          by (meson Suc.prems(4) asm2(2) disjoint_search(1) disjoint_search(2) red_properties)
      qed (simp_all add: Suc disjoint_def ra(3))
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (Q1 \<otimes> Q2)"
        using \<open>Some \<omega>a' = \<omega>' \<oplus> \<omega>f\<close> ra(1)
        using Suc.prems(6) \<open>Some \<omega>' = \<omega>a \<oplus> \<omega>1\<close> \<open>actual_stable \<omega>a\<close> actual_stable_sum
        using asm2(1) by blast
    qed
  qed (simp)
qed (simp)




proposition rule_par:
  assumes "CSL P1 C1 Q1"
      and "CSL P2 C2 Q2"
      and "disjoint (fvC C1 \<union> fvA Q1) (wrC C2)"
      and "disjoint (fvC C2 \<union> fvA Q2) (wrC C1)"
      and "actual_self_framing P1"
      and "actual_self_framing P2"
    shows "CSL (P1 \<otimes> P2) ({A1} C1 {B1} || {A2} C2 {B2}) (Q1 \<otimes> Q2)"
proof (rule CSL_I)
  fix n s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> P1 \<otimes> P2" "actual_stable \<omega>" "bounded \<omega>"
  then obtain p1 p2 where "Some \<omega> = p1 \<oplus> p2" "(Ag s, p1) \<in> P1" "(Ag s, p2) \<in> P2"
    by (meson sum_equi_states_easy_decompose)
  then have r: "Some \<omega> = actual_stabilize p1 \<oplus> actual_stabilize p2"
    using asm0(2) actual_stabilize_sum_of_stable by blast
  moreover have "(Ag s, actual_stabilize p1) \<in> P1 \<and> (Ag s, actual_stabilize p2) \<in> P2"
    by (metis \<open>(Ag s, p1) \<in> P1\<close> \<open>(Ag s, p2) \<in> P2\<close> assms(5) assms(6) actual_self_framingE)
  show "safe (Suc n) {A1} C1 {B1} || {A2} C2 {B2} s \<omega> (Q1 \<otimes> Q2)"
  proof (rule safe_par[of "Suc n" C1 s "actual_stabilize p1" Q1 C2 "actual_stabilize p2" Q2 \<omega>])
    show "safe (Suc n) C1 s (actual_stabilize p1) Q1"
      by (meson CSL_E \<open>(Ag s, actual_stabilize p1) \<in> P1 \<and> (Ag s, actual_stabilize p2) \<in> P2\<close> \<open>Some \<omega> = p1 \<oplus> p2\<close> actual_stabilize_is_stable actual_stabilize_smaller asm0(3) assms(1) bounded_smaller greater_def)
    show "safe (Suc n) C2 s (actual_stabilize p2) Q2"
      using CSL_E \<open>(Ag s, actual_stabilize p1) \<in> P1 \<and> (Ag s, actual_stabilize p2) \<in> P2\<close> actual_stabilize_is_stable asm0(3) assms(2) bounded_smaller greater_equiv r by blast
    show "disjoint (fvC C1 \<union> fvA Q1) (wrC C2)"      
      using assms(3) by auto
    show "disjoint (fvC C2 \<union> fvA Q2) (wrC C1)"
      using assms(4) by auto
  qed (simp_all add: assms r asm0)
qed



subsection \<open>Sequential composition\<close>


lemma safe_seq:
  assumes "safe n C1 s \<omega> Q"
      and "\<And>m \<omega>' s'. m \<le> n \<and> (Ag s', \<omega>') \<in> Q \<and> actual_stable \<omega>' \<Longrightarrow> bounded \<omega>' \<Longrightarrow> safe m C2 s' \<omega>' R"
      and "actual_stable \<omega>"
    shows "safe n (Cseq C1 C2) s \<omega> R"
  using assms
proof (induct n arbitrary: C1 \<omega> s)
  case (Suc n)
  show "safe (Suc n) (Cseq C1 C2) s \<omega> R"
  proof (rule safeI)
    show "accesses (Cseq C1 C2) s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) accesses.simps(7) safeE(2) by blast
    show "writes (Cseq C1 C2) s \<subseteq> write_dom \<omega>"
      by (metis Suc.prems(1) safeE(3) writes.simps(7))
    show "no_aborts (Cseq C1 C2) s \<omega>"
      using safeE(4)[OF Suc.prems(1)] aborts_seq_elim
      by (meson no_aborts_def)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    assume "\<langle>Cseq C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 R"
    proof (rule red_seq_cases)
      assume asm1: "C1 = Cskip" "C' = C2" "\<sigma>' = concretize s \<omega>0'"
      moreover have "bounded \<omega>"
        using asm0(2) asm0(3) bounded_smaller greater_def real_implies_bounded by blast
      ultimately have "safe (Suc n) C2 s \<omega> R"
        using Suc.prems(2)[of "Suc n" _ \<omega>] safeE(1)[OF Suc.prems(1)] Suc.prems(3)
        by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 R"
        by (metis (no_types, lifting) Suc.prems(3) Suc_n_not_le_n asm0(2) asm0(3) asm1(2) asm1(3) fst_conv nat_le_linear safety_mono snd_conv)
    next
      fix C1' assume asm1: "C' = Cseq C1' C2" "\<langle>C1, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C1', \<sigma>'\<rangle>"
      then obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f" "actual_stable \<omega>1" "real_state \<omega>1'"
        "snd \<sigma>' = concretize_heap \<omega>1'" "safe n C1' (fst \<sigma>') \<omega>1 Q"
        using safeE(5)[OF Suc.prems(1), of \<omega>f \<omega>0' C1' \<sigma>'] asm0(1) asm0(2) asm0(3) by blast
      then have "safe n (Cseq C1' C2) (fst \<sigma>') \<omega>1 R" using Suc(1)[OF \<open>safe n C1' (fst \<sigma>') \<omega>1 Q\<close>]
        by (metis (no_types, lifting) Suc.prems(2) asm1(1) nat_le_linear not_less_eq_eq)
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 R"
        using \<open>Some \<omega>1' = \<omega>1 \<oplus> \<omega>f\<close> \<open>real_state \<omega>1'\<close> \<open>actual_stable \<omega>1\<close> \<open>snd \<sigma>' = concretize_heap \<omega>1'\<close> asm1(1) by blast
    qed
  qed (simp)
qed (simp)


proposition rule_seq:
  assumes "CSL P C1 Q"
      and "CSL Q C2 R"
    shows "CSL P (Cseq C1 C2) R"
proof (rule CSL_I)
  fix n s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> P" "actual_stable \<omega>" "bounded \<omega>"
  show "safe n (Cseq C1 C2) s \<omega> R"
  proof (rule safe_seq[of n C1 s \<omega> Q C2 R])
    show "safe n C1 s \<omega> Q"
      using CSL_E asm0 assms(1) asm0(3) by blast
    show "\<And>m \<omega>' s'. m \<le> n \<and> (Ag s', \<omega>') \<in> Q \<and> actual_stable \<omega>' \<Longrightarrow> bounded \<omega>' \<Longrightarrow> safe m C2 s' \<omega>' R"
      using CSL_E[OF assms(2)]
      by blast
  qed (simp_all add: asm0)
qed



subsection \<open>Consequence rule\<close>

lemma safe_conseq:
  assumes "safe n C s \<omega> Q"
      and "Q \<subseteq> Q'"
    shows "safe n C s \<omega> Q'"
  using assms
proof (induct n arbitrary: C \<omega> s)
  case (Suc n)
  show "safe (Suc n) C s \<omega> Q'"
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<omega>) \<in> Q'"
      using Suc.prems(1) assms(2) safe.simps(2) by blast
    show "accesses C s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) safeE(2) by blast
    show "writes C s \<subseteq> write_dom \<omega>"
      using Suc.prems(1) by auto
    show "no_aborts C s \<omega>"
      using Suc.prems(1) safe.simps(2) by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
      "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q'"
      using safeE(5)[OF Suc.prems(1)] by (meson Suc.hyps assms(2))
  qed
qed (simp)

proposition rule_conseq:
  assumes "CSL P C Q"
      and "P' \<subseteq> P"
      and "Q \<subseteq> Q'"
    shows "CSL P' C Q'"
proof (rule CSL_I)
  show "\<And>n s \<omega>. (Ag s, \<omega>) \<in> P' \<Longrightarrow> actual_stable \<omega> \<Longrightarrow> bounded \<omega> \<Longrightarrow> safe (Suc n) C s \<omega> Q'"
    using CSL_E assms(1) assms(2) assms(3) safe_conseq by blast
qed


lemma safe_conseq_stronger:
  assumes "safe n C s \<omega> Q"
      and "bounded \<omega>"
      and "\<And>s x. bounded x \<Longrightarrow> (s, x) \<in> Q \<Longrightarrow> (s, x) \<in> Q'"
    shows "safe n C s \<omega> Q'"
  using assms
proof (induct n arbitrary: C \<omega> s)
  case (Suc n)
  show "safe (Suc n) C s \<omega> Q'"
  proof (rule safeI)
    show "C = Cskip \<Longrightarrow> (Ag s, \<omega>) \<in> Q'"
      using Suc.prems(1) assms(2) safe.simps(2)
      using Suc.prems(2) assms(3) by force
    show "accesses C s \<subseteq> read_dom \<omega>"
      using Suc.prems(1) safeE(2) by blast
    show "writes C s \<subseteq> write_dom \<omega>"
      using Suc.prems(1) by auto
    show "no_aborts C s \<omega>"
      using Suc.prems(1) safe.simps(2) by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
      "\<langle>C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
      using safeE(5)[OF Suc.prems(1), of \<omega>f \<omega>0' C' \<sigma>'] by blast
    then have "safe n C' (fst \<sigma>') \<omega>1 Q'"
      using Suc.hyps[of C' "fst \<sigma>'" \<omega>1]
      using Suc.prems(3) bounded_smaller greater_def real_implies_bounded by blast
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q'"
      using \<open>Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q\<close> by blast
  qed
qed (simp)

proposition rule_conseq_stronger:
  assumes "CSL P C Q"
      and "\<And>s x. bounded x \<Longrightarrow> (s, x) \<in> P' \<Longrightarrow> (s, x) \<in> P"
      and "\<And>s x. bounded x \<Longrightarrow> (s, x) \<in> Q \<Longrightarrow> (s, x) \<in> Q'"
    shows "CSL P' C Q'"
proof (rule CSL_I)
  show "\<And>n s \<omega>. (Ag s, \<omega>) \<in> P' \<Longrightarrow> actual_stable \<omega> \<Longrightarrow> bounded \<omega> \<Longrightarrow> safe (Suc n) C s \<omega> Q'"
    using CSL_E assms(1) assms(2) assms(3) safe_conseq_stronger
    by (metis (no_types, lifting))
qed




subsection \<open>Conditional rule\<close>

definition assertify_bexp where
  "assertify_bexp b = { \<omega> |\<omega>. bdenot b (the_ag (fst \<omega>))}"

lemma in_assertify_bexp:
  assumes "bdenot b (the_ag (fst \<omega>))"
  shows "\<omega> \<in> assertify_bexp b"
  by (simp add: assertify_bexp_def assms)

lemma in_assertify_bexp_alt:
  assumes "bdenot b s"
  shows "(Ag s, \<omega>) \<in> assertify_bexp b"
  by (simp add: assms in_assertify_bexp)

proposition rule_if:
  assumes "CSL (P \<inter> assertify_bexp b) C1 Q"
      and "CSL (P \<inter> assertify_bexp (Bnot b)) C2 Q"
    shows "CSL P (Cif b C1 C2) Q"
proof (rule CSL_I)
  fix n s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> P" "actual_stable \<omega>"
  show "safe (Suc n) (Cif b C1 C2) s \<omega> Q"
  proof (rule safeI)
    show "no_aborts (Cif b C1 C2) s \<omega>"
      using aborts.cases cmd.distinct(45) cmd.distinct(57) cmd.distinct(85) cmd.simps(91) no_aborts_def by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm1: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    assume "\<langle>Cif b C1 C2, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
    proof (rule red_if_cases)
      assume asm2: "C' = C1" "\<sigma>' = concretize s \<omega>0'" "bdenot b (fst (concretize s \<omega>0'))"
      then have "(Ag s, \<omega>) \<in> P \<inter> assertify_bexp b"
        by (simp add: asm0(1) in_assertify_bexp_alt)
      then have "safe n C' s \<omega> Q"
        using CSL_E[OF assms(1), of s \<omega> n] asm0 asm2
        using asm1(2) asm1(3) bounded_smaller greater_def real_implies_bounded by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
        using asm0 asm1 asm2 by auto
    next
      assume asm2: "C' = C2" "\<sigma>' = concretize s \<omega>0'" "\<not> bdenot b (fst (concretize s \<omega>0'))"
      then have "(Ag s, \<omega>) \<in> P \<inter> assertify_bexp (Bnot b)"
        by (simp add: asm0(1) in_assertify_bexp_alt)
      then have "safe n C' s \<omega> Q"
        using CSL_E[OF assms(2), of s \<omega> n] asm0 asm2
        using asm1(2) asm1(3) bounded_smaller greater_def real_implies_bounded by blast
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
        using asm0 asm1 asm2 by auto
    qed
  qed (simp_all)
qed


subsection \<open>While loops\<close>


lemma safe_while:
  assumes "CSL (I \<inter> (assertify_bexp b)) C I"
      and "(Ag s, \<omega>) \<in> I"
      and "actual_stable \<omega>"
    shows "safe n (Cwhile b I' C) s \<omega> (I \<inter> (assertify_bexp (Bnot b)))"
  using assms
proof (induct n arbitrary: \<omega> s)
  case (Suc n)
  note SucOuter = Suc
  show "safe (Suc n) (Cwhile b I' C) s \<omega> (I \<inter> assertify_bexp (Bnot b))"
  proof (rule safeI)
    show "no_aborts (Cwhile b I' C) s \<omega>"
      using aborts_while_elim no_aborts_def by blast
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    assume "\<langle>Cwhile b I' C, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
    proof (rule red_while_cases)
      assume asm1: "C' = Cif b (Cseq C (Cwhile b I' C)) Cskip" "\<sigma>' = concretize s \<omega>0'"
      have "safe n C' s \<omega> (I \<inter> assertify_bexp (Bnot b))"
      proof (cases n)
        case (Suc m)
        show "safe n C' s \<omega> (I \<inter> assertify_bexp (Bnot b))"
          unfolding Suc
        proof (rule safeI)
          show "no_aborts C' s \<omega>"
            using asm1(1) by blast
          fix \<omega>0' \<omega>f C'' \<sigma>'
          assume asm2: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
          assume "\<langle>C', concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C'', \<sigma>'\<rangle>"
          then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe m C'' (fst \<sigma>') \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
            unfolding asm1(1)
          proof (rule red_if_cases)
            show "C'' = Cskip \<Longrightarrow> \<sigma>' = concretize s \<omega>0' \<Longrightarrow> \<not> bdenot b (fst (concretize s \<omega>0')) \<Longrightarrow>
    \<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe m C'' (fst \<sigma>') \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
              by (metis IntI SucOuter(3) SucOuter(4) asm2(2) asm2(3) bdenot.simps(3) fst_conv in_assertify_bexp_alt safe_skip snd_conv)
            assume asm3: "C'' = Cseq C (Cwhile b I' C)" "\<sigma>' = concretize s \<omega>0'" "bdenot b (fst (concretize s \<omega>0'))"
            have "safe m C'' s \<omega> (I \<inter> assertify_bexp (Bnot b))"
              unfolding asm3(1)
            proof (rule safe_seq)
              have "bounded \<omega>"
                using asm0(2) asm0(3) bounded_smaller greater_def real_implies_bounded by blast
              then show "safe m C s \<omega> I"
                by (metis CSL_E IntI SucOuter(3) SucOuter(4) asm3(3) assms(1) fst_conv in_assertify_bexp_alt)
              show "\<And>ma \<omega>' s'. ma \<le> m \<and> (Ag s', \<omega>') \<in> I \<and> actual_stable \<omega>' \<Longrightarrow> safe ma (Cwhile b I' C) s' \<omega>' (I \<inter> assertify_bexp (Bnot b))"
                using Suc Suc.hyps[OF assms(1)] le_SucI safety_mono by blast
            qed (simp_all add: \<open>actual_stable \<omega>\<close>)
            then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe m C'' (fst \<sigma>') \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
              using SucOuter(4) asm2(2) asm2(3) asm3(2) by auto
          qed
        qed (simp_all add: asm1(1))
      qed (simp)
      then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (I \<inter> assertify_bexp (Bnot b))"
        using asm0 Suc.prems(3) asm1(2) by auto
    qed
  qed (simp_all)
qed (simp)


proposition rule_while:
  assumes "CSL (I \<inter> (assertify_bexp b)) C I"
    shows "CSL I (Cwhile b I' C) (I \<inter> (assertify_bexp (Bnot b)))"
proof (rule CSL_I)
  fix n s \<omega>
  assume "(Ag s, \<omega>) \<in> I" "actual_stable \<omega>"
  then show "safe (Suc n) (Cwhile b I' C) s \<omega> (I \<inter> assertify_bexp (Bnot b))"
    using assms(1) safe_while 
    by meson
qed




subsection \<open>Rule FieldAssign\<close>

abbreviation update_virtual_state_val where
  "update_virtual_state_val \<omega> l v \<equiv> \<omega>(l := Some (1, v))"

abbreviation update_virtual_state_perm_val where
  "update_virtual_state_perm_val \<omega> l p v \<equiv> \<omega>(l := Some (p, v))"

(* How do I update a virtual_state? *)
abbreviation update_heap_val where
  "update_heap_val \<omega> l v \<equiv> (fst \<omega>, update_virtual_state_val (snd \<omega>) l v)"


lemma write_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "actual_stable \<omega>f"
      and "\<omega> l = Some (1, v0)"
      and "bounded \<omega>'"
    shows "Some (update_virtual_state_val \<omega>' l v) = update_virtual_state_val \<omega> l v \<oplus> \<omega>f"
proof -
  have "\<omega>f l = None"
  proof (rule ccontr)
    assume "\<omega>f l \<noteq> None"
    then obtain p where "\<omega>f l = Some p"
      by blast
    then have "fst p > 0"
      by (meson actual_stable_def assms(2))
    then obtain pp where "\<omega>' l = Some pp"
      using assms(1) assms(3) greater_def virtual_state_greater_then by blast
      then have "fst pp > 1"
        by (smt (verit) PosReal.padd_cancellative \<open>0 < fst p\<close> \<open>\<omega>f l = Some p\<close> add.commute add_0 assms(1) assms(3) fst_conv nless_le plus_prodE pos_perm_class.sum_larger preal_plusE result_sum_partial_functions(3))
    then show False
      using \<open>\<omega>' l = Some pp\<close> assms(4) bounded_def leD by blast
  qed
  moreover have "concretize_heap \<omega>f l = None"
    using calculation by blast
  show ?thesis
  proof (rule plus_funI)
    fix la show "Some (update_virtual_state_val \<omega>' l v la) = update_virtual_state_val \<omega> l v la \<oplus> \<omega>f la"
      apply (cases "l = la")
      using calculation apply auto[1]
      by (simp add: assms(1) plus_funE)
  qed
qed

definition full_ownership :: "var \<Rightarrow> 'a equi_state set"
  where
  "full_ownership r = { \<omega> |\<omega> l v. the_ag (fst \<omega>) r = Some (VRef (Address l)) \<and>
  snd \<omega> (l, field_val) = Some (1, v) \<and> dom (snd \<omega>) = {(l, field_val)}}"


lemma in_full_ownership:
  assumes "the_ag (fst \<omega>) r = Some (VRef (Address l))"
      and "snd \<omega> (l, field_val) = Some (1, v)"
      and "dom (snd \<omega>) = {(l, field_val)}"
    shows "\<omega> \<in> full_ownership r"
  using assms full_ownership_def 
  by force



definition full_ownership_with_val where
  "full_ownership_with_val r e = { \<omega> |\<omega> l.
   the_ag (fst \<omega>) r = Some (VRef (Address l))
\<and> snd \<omega> (l, field_val) = Some (1, VInt (edenot e (the_ag (fst \<omega>)))) \<and> dom (snd \<omega>) = {(l, field_val)} }"



lemma in_full_ownership_with_val:
  assumes "s r = Some (VRef (Address l))"
      and "\<omega> (l, field_val) = Some (1, VInt (edenot e s))"
      and "dom \<omega> = {(l, field_val)}"
    shows "(Ag s, \<omega>) \<in> full_ownership_with_val r e"
  unfolding full_ownership_with_val_def
  using assms by auto


lemma in_read_dom_write_dom:
  assumes "\<omega> (l, field_val) = Some (1, v)"
  shows "l \<in> read_dom \<omega>"
    and "l \<in> write_dom \<omega>"
  unfolding read_dom_def write_dom_def
  using assms
  using preal_not_0_gt_0 apply fastforce
  by (simp add: assms)


lemma stable_before_then_update_stable:
  assumes "actual_stable \<omega>"
      and "concretize_heap \<omega> l \<noteq> None"
    shows "actual_stable (update_virtual_state_val \<omega> l v)"
  by (smt (verit, ccfv_SIG) actual_stable_def assms(1) fst_conv map_upd_Some_unfold norm_preal(4) zero_neq_one)


proposition rule_write:
  "CSL (full_ownership r) (Cwrite r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> full_ownership r" "actual_stable \<omega>"
  then obtain l v where "s r = Some (VRef (Address l))" "\<omega> (l, field_val) = Some (1, v)"
      "dom \<omega> = {(l, field_val)}"
    by (smt (z3) agreement.sel fst_conv full_ownership_def mem_Collect_eq snd_conv)
  fix n
  show "safe n (Cwrite r e) s \<omega> (full_ownership_with_val r e)"
  proof (cases n)
    case (Suc m)
    moreover have "safe (Suc m) (Cwrite r e) s \<omega> (full_ownership_with_val r e)"
    proof (rule safeI_alt)
      have "accesses (Cwrite r e) s = {l}" 
        by (simp add: \<open>s r = Some (VRef (Address l))\<close>)
      then show "accesses (Cwrite r e) s \<subseteq> read_dom \<omega>"
        by (simp add: \<open>\<omega> (l, field_val) = Some (1, v)\<close> in_read_dom_write_dom(1))
      show "writes (Cwrite r e) s \<subseteq> write_dom \<omega>"
        by (simp add: \<open>\<omega> (l, field_val) = Some (1, v)\<close> \<open>s r = Some (VRef (Address l))\<close> in_read_dom_write_dom(2))
      fix \<omega>0' \<omega>f
      assume asm1: "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'" "actual_stable \<omega>f"
      then obtain pp where "s r = Some (VRef (Address l)) \<and> \<omega>0' (l, field_val) = Some (pp, v)" "pp \<ge> 1"
        using virtual_state_greater_then[of \<omega>0' \<omega> "(l, field_val)" 1 v]
        using \<open>\<omega> (l, field_val) = Some (1, v)\<close> \<open>s r = Some (VRef (Address l))\<close> greater_def by blast
      moreover have "pp \<le> 1"
        using asm1(2) calculation(1) real_state_def by fastforce
      ultimately have "pp = 1"
        by order
      then have "concretize_heap \<omega>0' (l, field_val) \<noteq> None"
        by (simp add: \<open>s r = Some (VRef (Address l)) \<and> \<omega>0' (l, field_val) = Some (pp, v)\<close>)
      show "aborts (Cwrite r e) (concretize s \<omega>0') \<Longrightarrow> False"
      proof -
        assume "aborts (Cwrite r e) (concretize s \<omega>0')"
        moreover have "s r = Some (VRef (Address l))"
          by (simp add: \<open>s r = Some (VRef (Address l))\<close>)
        moreover have "(l, field_val) \<in> dom (snd (concretize s \<omega>0'))"
          using \<open>concretize_heap \<omega>0' (l, field_val) \<noteq> None\<close> by force
        ultimately show False
          by auto
      qed
      fix C' \<sigma>'
      assume asm2: "actual_stable \<omega>f" "\<langle>Cwrite r e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
      let ?v = "VInt (edenot e s)"

      have "bounded \<omega>0'"
        using asm1(2) real_implies_bounded by blast
      then have "Some (update_virtual_state_val \<omega>0' (l, field_val) ?v) = update_virtual_state_val \<omega> (l, field_val) ?v \<oplus> \<omega>f"
        using write_helper
        using \<open>\<omega> (l, field_val) = Some (1, v)\<close> asm1(1) asm2(1) by blast
     moreover have "\<sigma>' = concretize s (update_virtual_state_val \<omega>0' (l, field_val) ?v) \<and> C' = Cskip"
       apply (rule red_write_cases[OF asm2(2)])
       apply simp
       apply (rule ext)
       apply simp
       using \<open>s r = Some (VRef (Address l))\<close> by auto
      moreover have "safe m Cskip s (update_virtual_state_val \<omega> (l, field_val) ?v) (full_ownership_with_val r e)"
      proof (rule safe_skip)
        show "(Ag s, update_virtual_state_val \<omega> (l, field_val) (VInt (edenot e s))) \<in> full_ownership_with_val r e"
        proof (rule in_full_ownership_with_val)
          show "s r = Some (VRef (Address l))"            
            by (simp add: \<open>s r = Some (VRef (Address l))\<close>)
          show "update_virtual_state_val \<omega> (l, field_val) (VInt (edenot e s)) (l, field_val) = Some (1, VInt (edenot e s))"
            by simp
          show "dom (update_virtual_state_val \<omega> (l, field_val) (VInt (edenot e s))) = {(l, field_val)}"
            by (simp add: \<open>dom \<omega> = {(l, field_val)}\<close>)
        qed
      qed

      show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe m C' (fst \<sigma>') \<omega>1 (full_ownership_with_val r e)"
      proof (intro exI conjI)
        show "safe m C' (fst \<sigma>') (update_virtual_state_val \<omega> (l, field_val) ?v) (full_ownership_with_val r e)"
          by (simp add: \<open>safe m Cskip s (update_virtual_state_val \<omega> (l, field_val) (VInt (edenot e s))) (full_ownership_with_val r e)\<close> calculation(2))
        show "Some (update_virtual_state_val \<omega>0' (l, field_val) (VInt (edenot e s))) = update_virtual_state_val \<omega> (l, field_val) (VInt (edenot e s)) \<oplus> \<omega>f"
          using calculation(1) by blast
        show "actual_stable (update_virtual_state_val \<omega> (l, field_val) (VInt (edenot e s)))"
          apply (rule actual_stableI)
          apply (case_tac "(l, field_val) = la")
          apply simp_all
          using preal_not_0_gt_0 apply force
          using actual_stable_def asm0(2) by blast
        show "real_state (update_virtual_state_val \<omega>0' (l, field_val) (VInt (edenot e s)))"
          by (smt (verit, ccfv_SIG) asm1(2) fun_upd_apply option.inject real_state_def split_pairs)
        show "snd \<sigma>' = concretize_heap (update_virtual_state_val \<omega>0' (l, field_val) (VInt (edenot e s)))"
          by (simp add: calculation(2))
      qed
    qed (simp)
    ultimately show ?thesis by blast
  qed (simp)
qed


subsection \<open>Rule assignment\<close>



definition sub_pre where
  "sub_pre x e P = { (Ag s, \<omega>) |s \<omega>. (Ag (s(x \<mapsto> VInt (edenot e s))), \<omega>) \<in> P }"

proposition rule_assign:
  "CSL (sub_pre x e P) (Cassign x e) P"
proof (rule CSL_I)
  fix n s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> sub_pre x e P" "actual_stable \<omega>"
  then have r: "(Ag (s(x \<mapsto> VInt (edenot e s))), \<omega>) \<in> P"
    by (simp add: sub_pre_def)
  show "safe (Suc n) (Cassign x e) s \<omega> P"
  proof (rule safeI)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm1: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    assume "\<langle>Cassign x e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 P"
      by (metis asm0(2) asm1(2) asm1(3) fst_eqD r red_assign_cases safe_skip snd_eqD)
  qed (auto simp add: no_aborts_def)
qed



subsection \<open>Rule Alloc\<close>

definition set_perm_and_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> preal \<Rightarrow> 'a val \<Rightarrow> 'a virtual_state" where
  "set_perm_and_value \<phi> hl p v = \<phi>(hl := Some (p, v))"

(*
lemma update_perm_simps[simp]:
  assumes "p > 0 \<Longrightarrow> v \<noteq> None"
      and "p \<le> 1"
    shows "concretize_heap (set_perm_and_value \<phi> hl p v) = (concretize_heap \<phi>)(hl := v)"
      and "set_perm_and_value \<phi> hl p v = \<phi>(hl := p)"
  unfolding set_perm_and_value_def
  apply (metis Abs_virtual_state_inverse assms get_vh_def mem_Collect_eq snd_conv wf_set_perm)
  by (metis Abs_virtual_state_inverse assms fst_conv get_vm_def mem_Collect_eq wf_set_perm)
*)

(*
lemma stable_set_perm_and_value:
  assumes "p > 0 \<longleftrightarrow> v \<noteq> None"
      and "stable \<omega>"
      and "p \<le> 1"
    shows "stable (set_perm_and_value \<omega> hl p v)"
proof (rule stable_virtual_stateI)
  show "\<And>hla. concretize_heap (set_perm_and_value \<omega> hl p v) hla \<noteq> None \<Longrightarrow> PosReal.pnone < get_vm (set_perm_and_value \<omega> hl p v) hla"
    by (metis EquiSemAuxLemma.gr_0_is_ppos assms(1) assms(2) assms(3) fun_upd_apply stable_virtual_state_def update_perm_simps(1) update_perm_simps(2))
qed
*)


lemma alloc_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "concretize_heap \<omega>f l = None"
      and "p \<le> 1"
    shows "Some (set_perm_and_value \<omega>' l p v) = set_perm_and_value \<omega> l p v \<oplus> \<omega>f"
  unfolding set_perm_and_value_def
  apply (rule plus_funI)
  apply (case_tac "l = la")
  apply simp_all
  using assms(2) apply force
  by (simp add: assms(1) plus_funE)

lemma stable_uu:
  "actual_stable Map.empty"
  by (rule actual_stableI) simp_all

lemma uu_neutral:
  "Some (\<omega> :: 'a virtual_state) = \<omega> \<oplus> Map.empty"
proof (rule plus_funI)
  show "\<And>l. Some (\<omega> l) = \<omega> l \<oplus> None"
    by simp
qed

definition no_perm :: "'a equi_state set" where
  "no_perm = { (Ag s, Map.empty) |s. True }"


proposition rule_alloc:
  assumes "r \<notin> fvE e"
  shows "CSL no_perm (Calloc r e) (full_ownership_with_val r e)"
proof (rule CSL_I)
  fix n :: nat
  fix s :: "'a stack"
  fix \<omega> :: "'a virtual_state"
  assume asm: "actual_stable \<omega>" "(Ag s, \<omega>) \<in> no_perm" 


  show "safe (Suc n) (Calloc r e) s \<omega> (full_ownership_with_val r e)"
  proof (rule safeI)
    fix \<omega>0' \<omega>f C' \<sigma>'
    assume asm0: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    assume "\<langle>Calloc r e, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (full_ownership_with_val r e)"
    proof (rule red_alloc_cases)
      fix sa h l
      assume asm1: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "(l, field_val) \<notin> dom h"
        "\<sigma>' = (sa(r \<mapsto> VRef (Address l)), h((l, field_val) \<mapsto> VInt (edenot e sa)))"
      then have r: "Some (set_perm_and_value \<omega>0' (l, field_val) 1 (VInt (edenot e s)))
  = set_perm_and_value \<omega> (l, field_val) 1 (VInt (edenot e s)) \<oplus> \<omega>f"
        using alloc_helper
        by (smt (verit, best) no_perm_def Pair_inject asm(2) asm0(2) commutative dom_eqD mem_Collect_eq order_refl result_sum_partial_functions(2))

     let ?\<omega>1 = "set_perm_and_value \<omega> (l, field_val) 1 (VInt (edenot e s))"
      let ?\<omega>1' = "set_perm_and_value \<omega>0' (l, field_val) 1  (VInt (edenot e s))"

      have "actual_stable ?\<omega>1"
        apply (rule actual_stableI)
        unfolding set_perm_and_value_def apply simp
        by (metis actual_stable_def asm(1) fst_conv one_neq_zero option.inject pperm_pnone_pgt)
      moreover have "real_state ?\<omega>1'"
        unfolding real_state_def set_perm_and_value_def apply simp
        by (metis asm0(3) fst_conv real_state_def)
      moreover have "\<sigma>' = concretize (fst \<sigma>') ?\<omega>1'"
        using asm1(1) asm1(4) unfolding set_perm_and_value_def
        apply simp
        apply (rule ext)
        apply simp
        by meson
      moreover have "(Ag (fst \<sigma>'), ?\<omega>1) \<in> full_ownership_with_val r e"
      proof (rule in_full_ownership_with_val[of "(fst \<sigma>')" r l])
        show "fst \<sigma>' r = Some (VRef (Address l))"
          by (simp add: asm1(4))
        have "edenot e (fst \<sigma>') = edenot e s"
          using asm1(1) asm1(4) assms by auto
        then show "set_perm_and_value \<omega> (l, field_val) 1 (VInt (edenot e s)) (l, field_val) = Some (1, VInt (edenot e (fst \<sigma>')))"
          unfolding set_perm_and_value_def by simp
        show "dom (set_perm_and_value \<omega> (l, field_val) 1 (VInt (edenot e s))) = {(l, field_val)}"
          unfolding set_perm_and_value_def apply simp
          using asm(2) no_perm_def by force
      qed
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (full_ownership_with_val r e)"
        using r asm1(2)
        by (metis safe_skip snd_conv)
    qed
  qed (auto)
qed





subsection \<open>Rule free\<close>

abbreviation erase_perm_and_value :: "'a virtual_state \<Rightarrow> (address \<times> field_ident) \<Rightarrow> 'a virtual_state" where
  "erase_perm_and_value \<phi> hl \<equiv> \<phi>(hl := None)"


lemma free_helper:
  assumes "Some \<omega>' = \<omega> \<oplus> \<omega>f"
      and "actual_stable \<omega>f"
      and "\<omega> hl = Some (1, v)"
      and "bounded \<omega>'"
    shows "Some (erase_perm_and_value \<omega>' hl) = erase_perm_and_value \<omega> hl \<oplus> \<omega>f"
  apply (rule plus_funI)
  apply (case_tac "l = hl")
  apply simp_all
proof -
  show "None = \<omega>f hl"
  proof (rule ccontr)
    assume "None \<noteq> \<omega>f hl"
    then obtain p where "\<omega>f hl = Some p"
      by (metis option.exhaust_sel)
    then have "fst p > 0"
      using actual_stable_def assms(2) by blast
    moreover obtain pp where "\<omega>' hl = Some pp"
      using assms(1) assms(3) greater_def virtual_state_greater_then by blast
    then have "fst pp = fst p + 1"
      by (smt (verit) \<open>\<omega>f hl = Some p\<close> assms(1) assms(3) commutative fst_conv plus_funE plus_optionE plus_prodE preal_plusE)
    then show False
      by (metis PosReal.padd_cancellative \<open>\<omega>' hl = Some pp\<close> add.commute add_0 antisym assms(4) bounded_def calculation pos_perm_class.sum_larger preal_not_0_gt_0)
  qed
  fix l show "l \<noteq> hl \<Longrightarrow> Some (\<omega>' l) = \<omega> l \<oplus> \<omega>f l"
    by (simp add: assms(1) plus_funE)
qed

lemma stable_erase_perm_value:
  assumes "actual_stable \<omega>"
  shows "actual_stable (erase_perm_and_value \<omega> hl)"
  apply (rule actual_stableI)
  by (metis actual_stable_def assms fun_upd_def option.discI)

lemma binary_mask_erase_perm_value:
  assumes "real_state \<omega>"
  shows "real_state (erase_perm_and_value \<omega> hl)"
  by (metis (no_types, lifting) assms fun_upd_apply option.simps(3) real_state_def)

proposition rule_free:
  "CSL (full_ownership r) (Cfree r) UNIV"
proof (rule CSL_I)
  fix n s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> full_ownership r" "actual_stable \<omega>"
  then obtain l v where "s r = Some (VRef (Address l))" "\<omega> (l, field_val) = Some (1, v)"
    "dom \<omega> = {(l, field_val)}"
    unfolding full_ownership_def by auto
  show "safe (Suc n) (Cfree r) s \<omega> UNIV"
  proof (rule safeI_alt)
    show "accesses (Cfree r) s \<subseteq> read_dom \<omega>"
      by (simp add: \<open>\<omega> (l, field_val) = Some (1, v)\<close> \<open>s r = Some (VRef (Address l))\<close> in_read_dom_write_dom(1))
    show "writes (Cfree r) s \<subseteq> write_dom \<omega>"
      by (simp add: \<open>\<omega> (l, field_val) = Some (1, v)\<close> \<open>s r = Some (VRef (Address l))\<close> in_read_dom_write_dom(2))
    fix \<omega>0' \<omega>f
    assume asm1: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    show "aborts (Cfree r) (concretize s \<omega>0') \<Longrightarrow> False"
    proof -
      assume "aborts (Cfree r) (concretize s \<omega>0')"
      then show False
      proof (rule aborts_free_elim)
        show "fst (concretize s \<omega>0') r = Some (VRef Null) \<Longrightarrow> False"
          by (simp add: \<open>s r = Some (VRef (Address l))\<close>)
        fix hl assume "fst (concretize s \<omega>0') r = Some (VRef (Address hl))"
        then have "hl = l"
          by (simp add: \<open>s r = Some (VRef (Address l))\<close>)
        moreover assume "(hl, field_val) \<notin> dom (snd (concretize s \<omega>0'))"
        moreover obtain pp where "\<omega>0' (hl, field_val) = Some pp"
          using \<open>\<omega> (l, field_val) = Some (1, v)\<close> asm1(2) calculation(1) greater_def virtual_state_greater_then by blast
        then have "pp \<succeq> (1, v)"
          using calculation(2) by force
        ultimately show False          
          using \<open>\<omega>0' (hl, field_val) = Some pp\<close> by auto
      qed
    qed
    fix C' \<sigma>'
    assume "\<langle>Cfree r, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (UNIV)"
    proof (rule red_free_cases)
      fix sa h l'
      assume asm2: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "\<sigma>' = (sa, h((l', field_val) := None))"
        "sa r = Some (VRef (Address l'))"
      let ?\<omega>1 = "erase_perm_and_value \<omega> (l', field_val)"
      let ?\<omega>1' = "erase_perm_and_value \<omega>0' (l', field_val)"

      have "snd \<sigma>' = concretize_heap ?\<omega>1' \<and> safe n C' (fst \<sigma>') ?\<omega>1 (UNIV)"
        using asm2(1) asm2(2) asm2(3) by auto
      moreover have "Some ?\<omega>1' = ?\<omega>1 \<oplus> \<omega>f \<and> actual_stable ?\<omega>1"
        by (metis Pair_inject \<open>\<omega> (l, field_val) = Some (1, v)\<close> \<open>s r = Some (VRef (Address l))\<close> asm0(2) asm1(1) asm1(2) asm1(3) asm2(1) asm2(4) free_helper option.inject real_implies_bounded ref.inject stable_erase_perm_value val.inject(4))
      moreover have "real_state ?\<omega>1'"
        by (simp add: asm1(3) binary_mask_erase_perm_value)        
      ultimately show
        "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (UNIV)"
        by blast
    qed
  qed (simp_all)
qed


definition read_result :: "'a equi_state set \<Rightarrow> var \<Rightarrow> var \<Rightarrow> 'a equi_state set" where
  "read_result A x r = { (Ag (s(x := Some (snd p))), \<omega>) |s \<omega> l p. \<omega> (l, field_val) = Some p \<and> (Ag s, \<omega>) \<in> A \<and> s r = Some (VRef (Address l)) }"


definition read_perm :: "var \<Rightarrow> 'a equi_state set" where
  "read_perm r = { (Ag s, \<omega>) |s \<omega> l p. s r = Some (VRef (Address l)) \<and> fst p > 0 \<and> \<omega> (l, field_val) = Some p}"

proposition rule_read:
  assumes "A \<subseteq> read_perm r"
    shows "CSL A (Cread x r) (read_result A x r)"
proof (rule CSL_I)
  fix n s \<omega>
  assume asm0: "(Ag s, \<omega>) \<in> A" "actual_stable \<omega>"
  then obtain l p where lv_def: "s r = Some (VRef (Address l))" "fst p > 0" "\<omega> (l, field_val) = Some p"
    using assms(1) unfolding read_perm_def by force
  show "safe (Suc n) (Cread x r) s \<omega> (read_result A x r)"
  proof (rule safeI_alt)
    show "accesses (Cread x r) s \<subseteq> read_dom \<omega>"
      unfolding read_dom_def
      apply simp
      using lv_def
      by (metis get_address_simp prod.collapse)
    fix \<omega>0' \<omega>f
    assume asm1: "actual_stable \<omega>f" "Some \<omega>0' = \<omega> \<oplus> \<omega>f" "real_state \<omega>0'"
    then have "concretize_heap \<omega>0' (l, field_val) = Some (snd p)"
      using lv_def
      by (smt (verit, del_insts) greater_def map_option_eq_Some prod.collapse snd_conv virtual_state_greater_then)
    then show "aborts (Cread x r) (concretize s \<omega>0') \<Longrightarrow> False"
      using lv_def(1) by auto

    fix C' \<sigma>'
    assume "\<langle>Cread x r, concretize s \<omega>0'\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    then show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 (read_result A x r)"
    proof (rule red_read_cases)
      fix sa h l' v'
      assume asm2: "concretize s \<omega>0' = (sa, h)" "C' = Cskip" "\<sigma>' = (sa(x \<mapsto> VInt v'), h)" "sa r = Some (VRef (Address l'))"
      "h (l', field_val) = Some (VInt v')"
      then have "l = l' \<and> (snd p) = VInt v'"
        using \<open>concretize_heap \<omega>0' (l, field_val) = Some (snd p)\<close> lv_def(1) by auto
      moreover have "(Ag (s(x := Some (snd p))), \<omega>) \<in> read_result A x r"
        unfolding read_result_def
        using asm0(1) lv_def by blast
      ultimately show "\<exists>\<omega>1 \<omega>1'. Some \<omega>1' = \<omega>1 \<oplus> \<omega>f \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1'
        \<and> safe n C' (fst \<sigma>') \<omega>1 (read_result A x r)"
        using asm0(2) asm1(2) asm1(3) asm2(1) asm2(2) asm2(3) by auto
    qed
  qed (simp_all)
qed


section \<open>Actual logic\<close>

inductive CSL_syn :: "'a equi_state set \<Rightarrow> cmd \<Rightarrow> 'a equi_state set \<Rightarrow> bool" 
  ("\<turnstile>CSL [_] _ [_]" [51,0,0] 81)
  where
  RuleSkip: "\<turnstile>CSL [P] Cskip [P]"
| RuleFrame: "\<lbrakk> \<turnstile>CSL [P] C [Q]; disjoint (fvA R) (wrC C); actual_self_framing P; actual_self_framing R\<rbrakk>
  \<Longrightarrow> \<turnstile>CSL [P \<otimes> R] C [Q \<otimes> R]"
| RulePar: "\<lbrakk> disjoint (fvC C1 \<union> fvA Q1) (wrC C2); disjoint (fvC C2 \<union> fvA Q2) (wrC C1); actual_self_framing P1;
  actual_self_framing P2;
    \<turnstile>CSL [P1] C1 [Q1]; \<turnstile>CSL [P2] C2 [Q2] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [P1 \<otimes> P2] {_} C1 {_} || {_} C2 {_} [Q1 \<otimes> Q2]"
| RuleSeq: "\<lbrakk> \<turnstile>CSL [P] C1 [Q]; \<turnstile>CSL [Q] C2 [R] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [P] Cseq C1 C2 [R]"
| RuleIf: "\<lbrakk> \<turnstile>CSL [P \<inter> assertify_bexp b] C1 [Q]; \<turnstile>CSL [P \<inter> assertify_bexp (Bnot b)] C2 [Q]\<rbrakk> \<Longrightarrow> \<turnstile>CSL [P] Cif b C1 C2 [Q]"
| RuleWhile: "\<lbrakk> \<turnstile>CSL [I \<inter> assertify_bexp b] C [I] \<rbrakk> \<Longrightarrow> \<turnstile>CSL [I] (Cwhile b I' C) [I \<inter> assertify_bexp (Bnot b)]"
| RuleWrite: "\<turnstile>CSL [full_ownership r] Cwrite r e [full_ownership_with_val r e]"
| RuleAssign: "\<turnstile>CSL [sub_pre x e P] Cassign x e [P]"
| RuleAlloc: "r \<notin> fvE e \<Longrightarrow> \<turnstile>CSL [no_perm] Calloc r e [full_ownership_with_val r e]"
| RuleFree: "\<turnstile>CSL [full_ownership r] Cfree r [UNIV]"
| RuleRead: "\<lbrakk> A \<subseteq> read_perm r\<rbrakk> \<Longrightarrow> \<turnstile>CSL [A] Cread x r [read_result A x r]"
| RuleCons: "\<lbrakk> CSL_syn P C Q; P' \<subseteq> P; Q \<subseteq> Q'\<rbrakk> \<Longrightarrow> CSL_syn P' C Q'"


theorem CSL_sound:
  assumes "\<turnstile>CSL [P] C [Q]"
    shows "CSL P C Q"
  using assms
  apply (induct rule: CSL_syn.induct)
  by (simp_all add: rule_skip rule_seq rule_if rule_while rule_free
      rule_write rule_assign frame_rule rule_par rule_alloc rule_read rule_conseq)



subsection \<open>Adequacy\<close>

inductive n_steps where
  NoStep: "n_steps C \<sigma> C \<sigma>"
| OneStep: "\<lbrakk> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<langle>C'', \<sigma>''\<rangle>; n_steps C'' \<sigma>'' C' \<sigma>' \<rbrakk> \<Longrightarrow>  n_steps C \<sigma> C' \<sigma>'"

definition assertify_state_exp :: "(('a store \<times> 'a partial_heap) \<Rightarrow> bool) \<Rightarrow> 'a equi_state set" where
  "assertify_state_exp P = { (Ag s, h) |s h. P (s, concretize_heap h) }"

lemma in_assertify_equiv:
  "(Ag s, \<omega>) \<in> assertify_state_exp P \<longleftrightarrow> P (s, concretize_heap \<omega>)"
  by (simp add: assertify_state_exp_def)






lemma safeE_no_frame:
  assumes "safe (Suc n) C s \<omega> Q"
      and "real_state \<omega>"
      and "\<langle>C, concretize s \<omega>\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    shows "\<exists>\<omega>1. actual_stable \<omega>1 \<and> real_state \<omega>1 \<and> snd \<sigma>' = concretize_heap \<omega>1 \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
proof -
  obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> Map.empty \<and> actual_stable \<omega>1 \<and> real_state \<omega>1' \<and> snd \<sigma>' = concretize_heap \<omega>1' \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
    using safeE(5)[OF assms(1), of Map.empty \<omega> C' \<sigma>']
    using assms stable_uu uu_neutral by blast
  then show ?thesis
    by (metis option.sel uu_neutral)
qed



lemma safeE_no_frame_alt:
  assumes "safe (Suc n) C s (mk_virtual_state h) Q"
      and "\<langle>C, (s, h)\<rangle> \<rightarrow> \<langle>C', \<sigma>'\<rangle>"
    shows "\<exists>\<omega>1. actual_stable \<omega>1 \<and> real_state \<omega>1 \<and> snd \<sigma>' = concretize_heap \<omega>1 \<and> safe n C' (fst \<sigma>') \<omega>1 Q"
  by (metis assms(1) assms(2) mk_virtual_state_charact(1) mk_virtual_state_charact(3) safeE_no_frame)



lemma safe_n_steps:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "s = fst \<sigma>"
      and "concretize_heap \<omega> = snd \<sigma>"
      and "real_state \<omega>"
      and "actual_stable \<omega>"       
      and "\<And>n. safe n C s \<omega> (assertify_state_exp Q)"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  using assms
proof (induct arbitrary: s \<omega> rule: n_steps.induct)
  case (NoStep C \<sigma>)
  then have r: "safe (Suc 0) C s \<omega> (assertify_state_exp Q)"
    by presburger
  then show ?case
    using safeE(1)[OF r] no_abortsE[OF safeE(4)[OF r], of \<omega> Map.empty]
    using NoStep.prems(1) NoStep.prems(2) stable_uu uu_neutral
    using NoStep.prems(3) NoStep.prems(4)
    by (metis in_assertify_equiv surjective_pairing)
next
  case (OneStep C \<sigma> C'' \<sigma>'' C' \<sigma>')
  show "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
  proof (rule OneStep(3)[of "fst \<sigma>''" "mk_virtual_state (snd \<sigma>'')"])
    fix n
    obtain \<omega>1 \<omega>1' where "Some \<omega>1' = \<omega>1 \<oplus> Map.empty \<and> actual_stable \<omega>1 \<and> real_state \<omega>1'"
      "snd \<sigma>'' = concretize_heap \<omega>1' \<and> safe n C'' (fst \<sigma>'') \<omega>1 (assertify_state_exp Q)"
      using safeE(5)[OF OneStep(8)[of "Suc n"], of Map.empty \<omega> C'' \<sigma>'']
      using OneStep.hyps(1) OneStep.prems(1) OneStep.prems(2) OneStep.prems(3) stable_uu uu_neutral
      by auto
    then show "safe n C'' (fst \<sigma>'') (mk_virtual_state (snd \<sigma>'')) (assertify_state_exp Q)"
      by (metis binary_mask_and_stable_then_mk_virtual option.sel uu_neutral)
  qed (simp_all)
qed

lemma bounded_mk_virtual_state[simp]:
  "bounded (mk_virtual_state h)"
  by (simp add: real_implies_bounded)


theorem adequacy:
  assumes "n_steps C \<sigma> C' \<sigma>'"
      and "\<turnstile>CSL [assertify_state_exp P] C [assertify_state_exp Q]"
      and "P \<sigma>"
    shows "\<not> aborts C' \<sigma>' \<and> (C' = Cskip \<longrightarrow> Q \<sigma>')"
proof (rule safe_n_steps[OF assms(1), where ?Q = Q])
  fix n
  show "safe n C (fst \<sigma>) (mk_virtual_state (snd \<sigma>)) (assertify_state_exp Q)"
  proof (rule CSL_E)
    show "CSL (assertify_state_exp P) C (assertify_state_exp Q)"
      using CSL_sound assms(2) by blast
    show "(Ag (fst \<sigma>), mk_virtual_state (snd \<sigma>)) \<in> assertify_state_exp P"
      by (simp add: assms(3) in_assertify_equiv)
  qed (simp_all)
qed (simp_all add: assms)


definition bounded_assertion_1 where
  "bounded_assertion_1 A = { (s, \<omega>) |s \<omega>. bounded \<omega> \<longrightarrow> (s, \<omega>) \<in> A}"

lemma equiv_on_bounded_1:
  "\<And>s x. bounded x \<Longrightarrow> (s, x) \<in> P \<longleftrightarrow> (s, x) \<in> bounded_assertion_1 P"
  apply rule
  unfolding bounded_assertion_1_def
  by simp_all

definition bounded_assertion_2 where
  "bounded_assertion_2 A = Set.filter (bounded \<circ> snd) A"

lemma equiv_on_bounded_2:
  "\<And>s x. bounded x \<Longrightarrow> (s, x) \<in> P \<longleftrightarrow> (s, x) \<in> bounded_assertion_1 P"
  unfolding bounded_assertion_1_def by simp

lemma bounded_2_star_same:
  fixes A B :: "'a equi_state set"
  shows "bounded_assertion_2 (A \<otimes> B) = bounded_assertion_2 (bounded_assertion_2 A \<otimes> bounded_assertion_2 B)"
  unfolding bounded_assertion_2_def
  apply rule
   apply rule
  apply simp
   apply (elim conjE)
proof -
  fix x assume "x \<in> A \<otimes> B" "bounded (snd x)"
  then obtain a b where "a \<in> A" "b \<in> B" "Some x = a \<oplus> b"
    by (meson x_elem_set_product)
  then have "bounded (snd a) \<and> bounded (snd b)"
    using \<open>bounded (snd x)\<close> bounded_smaller greater_def greater_equiv greater_prod_eq by blast
  then show "x \<in> Set.filter (bounded \<circ> snd) A \<otimes> Set.filter (bounded \<circ> snd) B"
    using \<open>Some x = a \<oplus> b\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> x_elem_set_product by fastforce
next
  show "Set.filter (bounded \<circ> snd) (Set.filter (bounded \<circ> snd) A \<otimes> Set.filter (bounded \<circ> snd) B) \<subseteq> Set.filter (bounded \<circ> snd) (A \<otimes> B)"
  proof
    fix x assume "x \<in> Set.filter (bounded \<circ> snd) (Set.filter (bounded \<circ> snd) A \<otimes> Set.filter (bounded \<circ> snd) B)"
    then obtain a b where "a \<in> A" "b \<in> B" "Some x = a \<oplus> b" "bounded (snd a)" "bounded (snd b)" "bounded (snd x)"
      by (smt (verit, del_insts) comp_apply member_filter x_elem_set_product)
    then show "x \<in> Set.filter (bounded \<circ> snd) (A \<otimes> B)"
      using x_elem_set_product by fastforce
  qed
qed







section \<open>Instantiation of the left module locale with equi states and reals\<close>


typedef ppreal = "{ r :: preal |r. r > 0}"
  by (metis (full_types) mem_Collect_eq not_gr_0 zero_neq_one)

setup_lifting type_definition_ppreal

lift_definition mult_preal :: "ppreal \<Rightarrow> ppreal \<Rightarrow> ppreal" is "(*)"
  using mult_positive_preal_positive by presburger

lift_definition add_preal :: "ppreal \<Rightarrow> ppreal \<Rightarrow> ppreal" is "(+)"
  by (simp add: padd_pos pperm_pnone_pgt)

lift_definition inv_preal :: "ppreal \<Rightarrow> ppreal" is "inverse"
by (metis PosReal.field_inverse_zero div_by_1 divide_divide_eq_right inverse_preal_def mult_1
    preal_not_0_gt_0 preal_to_real(11,8,9))

lift_definition one_preal :: "ppreal" is "1"
  using one_neq_zero pperm_pnone_pgt by blast

abbreviation mult_real :: "ppreal \<Rightarrow> preal \<Rightarrow> preal" where
  "mult_real p q \<equiv> Rep_ppreal p * q"

abbreviation mult_pair :: "ppreal \<Rightarrow> preal \<times> 'a val \<Rightarrow> preal \<times> 'a val" where
  "mult_pair a p \<equiv> (mult_real a (fst p), snd p)"

lemma distrib_mult_pair:
  "Some (mult_pair (add_preal p q) x) = mult_pair p x \<oplus> mult_pair q x"
  apply (rule plus_prodI)
   apply simp_all
  apply (simp add: add_preal.rep_eq comm_semiring_class.distrib preal_plus_iff)
  by (simp add: CSL_IDF_Unbounded.plus_val_id)

lemma plus_mult_pair:
  assumes "Some a = b \<oplus> c"
  shows "Some (mult_pair p a) = mult_pair p b \<oplus> mult_pair p c"
  apply (rule plus_prodI)
   apply simp_all
  apply (metis assms plus_prodE pos_perm_class.pmult_distr preal_plus_iff)
  by (metis assms plus_prodE)


definition mult_virtual_state :: "ppreal \<Rightarrow> 'a virtual_state \<Rightarrow> 'a virtual_state" where
  "mult_virtual_state a p l \<equiv> map_option (mult_pair a) (p l)"

lemma aux1:
  "(\<lambda>l. map_option (mult_pair p) (map_option (mult_pair q) (a l))) = (\<lambda>l. map_option (mult_pair (mult_preal p q)) (a l))"
    apply (rule ext)
    apply (case_tac "a l")
     apply simp_all
    by (simp add: mult.assoc mult_preal.rep_eq)

lemma aux2:
  "Some (\<lambda>l. map_option (mult_pair (add_preal p q)) (x l)) = (\<lambda>l. map_option (mult_pair p) (x l)) \<oplus> (\<lambda>l. map_option (mult_pair q) (x l))"
    apply (rule plus_funI)
    apply (case_tac "x l")
    apply simp_all
    using distrib_mult_pair
    by (smt (verit, del_insts) option.simps(3))

lemma aux3:
  assumes "Some a = b \<oplus> c"
  shows "Some (\<lambda>l. map_option (mult_pair p) (a l)) = (\<lambda>l. map_option (mult_pair p) (b l)) \<oplus> (\<lambda>l. map_option (mult_pair p) (c l))"
    apply (rule plus_funI)
    apply (case_tac "b l"; case_tac "c l")
       apply simp_all
    apply (metis (mono_tags, opaque_lifting) assms result_sum_partial_functions(1))
    apply (metis (mono_tags, opaque_lifting) assms prod.exhaust_sel result_sum_partial_functions(1))
     apply (metis (mono_tags, lifting) assms result_sum_partial_functions(2) surjective_pairing)
    apply (case_tac "mult_pair p aa \<oplus> mult_pair p aaa")
     apply simp_all
  proof -
    fix l bb cc
    assume "b l = Some bb" "c l = Some cc"
    then have "bb ## cc"
      by (smt (verit, best) SepAlgebra.comp_prod assms compatible_partial_functions defined_def option.discI)
    then show "mult_pair p bb \<oplus> mult_pair p cc = None \<Longrightarrow> False"
      by (metis defined_def option.collapse option.distinct(1) plus_mult_pair)

    obtain aa where "Some aa = bb \<oplus> cc"
      by (meson \<open>bb ## cc\<close> sumI)
    then have "a l = Some aa"
      by (smt (verit, ccfv_SIG) \<open>b l = Some bb\<close> \<open>c l = Some cc\<close> assms full_add_charact(2) get_abs_state_def
          result_sum_partial_functions(3))
    fix bc
    assume "mult_pair p bb \<oplus> mult_pair p cc = Some bc"

    then show "\<exists>aa b. a l = Some (aa, b) \<and> (mult_real p aa, b) = bc"
      using plus_mult_pair
      by (metis \<open>Some aa = bb \<oplus> cc\<close> \<open>a l = Some aa\<close> option.sel prod.exhaust_sel)
  qed


end