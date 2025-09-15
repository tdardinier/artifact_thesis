section \<open>Unbounded Separation Logic\<close>

theory UnboundedLogic
  imports Main "../CoreIVL/SepAlgebraDef"
begin

subsection \<open>Assertions and state model\<close>

text \<open>We define our assertion language as described in Section 3.2.3 of the thesis.\<close>

datatype ('a, 'b, 'c, 'd) assertion =
  Sem "('d \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> bool"
  | Mult 'b "('a, 'b, 'c, 'd) assertion"
  | Star "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Wand "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Or "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | And "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Imp "('a, 'b, 'c, 'd) assertion" "('a, 'b, 'c, 'd) assertion"
  | Exists 'd "('a, 'b, 'c, 'd) assertion"
  | Forall 'd "('a, 'b, 'c, 'd) assertion"
  | Pred
  | Bounded "('a, 'b, 'c, 'd) assertion"
  | Wildcard "('a, 'b, 'c, 'd) assertion"


type_synonym ('a, 'b, 'c) interp = "('a \<Rightarrow> 'b) \<Rightarrow> 'c set"

text \<open>The following locale captures the state model described in Section 3.2.2 of the thesis.\<close>

locale left_module =

  fixes mult :: "'b \<Rightarrow> ('a :: pre_pcm) \<Rightarrow> 'a" (infixl "\<odot>" 64)

  fixes smult :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes sadd :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes sinv :: "'b \<Rightarrow> 'b"

  fixes one :: 'b

  fixes valid :: "'a \<Rightarrow> bool"


  assumes sinv_inverse: "smult p (sinv p) = one"
      and sone_neutral: "smult one p = p"
      and sadd_comm: "sadd p q = sadd q p"
      and smult_comm: "smult p q = smult q p"
      and smult_distrib: "smult p (sadd q r) = sadd (smult p q) (smult p r)"
      and smult_asso: "smult (smult p q) r = smult p (smult q r)"

      and double_mult: "p \<odot> (q \<odot> a) = (smult p q) \<odot> a"
      and plus_mult: "Some (a::'a) = b \<oplus> c \<Longrightarrow> Some (p \<odot> a) = (p \<odot> b) \<oplus> (p \<odot> c)"
      and distrib_mult: "Some ((sadd p q) \<odot> x) = p \<odot> x \<oplus> q \<odot> x"
      and one_neutral: "one \<odot> a = a"

      and valid_mono: "valid a \<and> a \<succeq> b \<Longrightarrow> valid b"

begin

lemma commutative: "(a::'a) \<oplus> b = b \<oplus> a"
  by (simp add: commutative)

lemma asso1: "(a::'a) \<oplus> b = Some ab \<and> b \<oplus> c = Some bc \<Longrightarrow> ab \<oplus> c = a \<oplus> bc"
  using asso1 by blast

lemma asso2: "(a::'a) \<oplus> b = Some ab \<and> \<not> b ## c \<Longrightarrow> \<not> ab ## c"
  using asso2 defined_def by blast

text \<open>The validity of assertions corresponds to Figure 3.3 of the thesis.\<close>

fun sat :: "'a \<Rightarrow> ('d \<Rightarrow> 'c) \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" ("_, _, _ \<Turnstile> _" [51, 65, 68, 66] 50) where
  "\<sigma>, s, \<Delta> \<Turnstile> Mult p A \<longleftrightarrow> (\<exists>a. \<sigma> = p \<odot> a \<and> a, s, \<Delta> \<Turnstile> A)"
| "\<sigma>, s, \<Delta> \<Turnstile> Star A B \<longleftrightarrow> (\<exists>a b. Some \<sigma> = a \<oplus> b \<and> a, s, \<Delta> \<Turnstile> A \<and> b, s, \<Delta> \<Turnstile> B)"
| "\<sigma>, s, \<Delta> \<Turnstile> Wand A B \<longleftrightarrow> (\<forall>a \<sigma>'. a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a \<longrightarrow> \<sigma>', s, \<Delta> \<Turnstile> B)"

| "\<sigma>, s, \<Delta> \<Turnstile> Sem b \<longleftrightarrow> b s \<sigma>"
| "\<sigma>, s, \<Delta> \<Turnstile> Imp A B \<longleftrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B)"
| "\<sigma>, s, \<Delta> \<Turnstile> Or A B \<longleftrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<or> \<sigma>, s, \<Delta> \<Turnstile> B)"
| "\<sigma>, s, \<Delta> \<Turnstile> And A B \<longleftrightarrow> (\<sigma>, s, \<Delta> \<Turnstile> A \<and> \<sigma>, s, \<Delta> \<Turnstile> B)"

| "\<sigma>, s, \<Delta> \<Turnstile> Exists x A \<longleftrightarrow> (\<exists>v. \<sigma>, s(x := v), \<Delta> \<Turnstile> A)"
| "\<sigma>, s, \<Delta> \<Turnstile> Forall x A \<longleftrightarrow> (\<forall>v. \<sigma>, s(x := v), \<Delta> \<Turnstile> A)"

| "\<sigma>, s, \<Delta> \<Turnstile> Pred \<longleftrightarrow> (\<sigma> \<in> \<Delta> s)"
| "\<sigma>, s, \<Delta> \<Turnstile> Bounded A \<longleftrightarrow> (valid \<sigma> \<longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> A)"
| "\<sigma>, s, \<Delta> \<Turnstile> Wildcard A \<longleftrightarrow> (\<exists>a p. \<sigma> = p \<odot> a \<and> a, s, \<Delta> \<Turnstile> A)"

definition intuitionistic :: "('d \<Rightarrow> 'c) \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "intuitionistic s \<Delta> A \<longleftrightarrow> (\<forall>a b. a \<succeq> b \<and> b, s, \<Delta> \<Turnstile> A \<longrightarrow> a, s, \<Delta> \<Turnstile> A)"

definition entails :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" ("_, _ \<turnstile> _" [63, 66, 68] 52) where
  "A, \<Delta> \<turnstile> B \<longleftrightarrow> (\<forall>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B)"

definition equivalent :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> ('d, 'c, 'a) interp \<Rightarrow> ('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" ("_, _ \<equiv> _" [63, 66, 68] 52) where
  "A, \<Delta> \<equiv> B \<longleftrightarrow> (A, \<Delta> \<turnstile> B \<and> B, \<Delta> \<turnstile> A)"

definition pure :: "('a, 'b, 'c, 'd) assertion \<Rightarrow> bool" where
  "pure A \<longleftrightarrow> (\<forall>\<sigma> \<sigma>' s \<Delta> \<Delta>'. \<sigma>, s, \<Delta> \<Turnstile> A \<longleftrightarrow> \<sigma>', s, \<Delta>' \<Turnstile> A)"


subsection \<open>Useful lemmas\<close>

lemma sat_forall:
  assumes "\<And>v. \<sigma>, s(x := v), \<Delta> \<Turnstile> A"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Forall x A"
  by (simp add: assms)

lemma intuitionisticI:
  assumes "\<And>a b. a \<succeq> b \<and> b, s, \<Delta> \<Turnstile> A \<Longrightarrow> a, s, \<Delta> \<Turnstile> A"
  shows "intuitionistic s \<Delta> A"
  by (meson assms intuitionistic_def)

lemma can_divide:
  assumes "p \<odot> a = p \<odot> b"
  shows "a = b"
  by (metis assms double_mult one_neutral sinv_inverse smult_comm)

lemma unique_inv:
  "a = p \<odot> b \<longleftrightarrow> b = (sinv p) \<odot> a"
  by (metis double_mult can_divide sinv_inverse sone_neutral)

lemma entailsI:
  assumes "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B"
  shows "A, \<Delta> \<turnstile> B"
  by (simp add: assms entails_def)

lemma equivalentI:
  assumes "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B"
      and "\<And>\<sigma> s. \<sigma>, s, \<Delta> \<Turnstile> B \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> A"
    shows "A, \<Delta> \<equiv> B"
  by (simp add: assms(1) assms(2) entailsI equivalent_def)

lemma compatible_def:
  "(a :: 'a) ## b = (a \<oplus> b \<noteq> None)"
  using defined_def by blast

lemma larger_def:
  "((a :: 'a) \<succeq> b) = (\<exists>c. Some a = b \<oplus> c)"
  using greater_def by blast

lemma compatible_imp:
  assumes "a ## b"
  shows "(p \<odot> a) ## (p \<odot> b)"
  by (metis assms compatible_def option.distinct(1) option.exhaust plus_mult)

lemma compatible_iff:
  "a ## b \<longleftrightarrow> (p \<odot> a) ## (p \<odot> b)"
  by (metis compatible_imp unique_inv)

lemma sat_wand:
  assumes "\<And>a \<sigma>'. a, s, \<Delta> \<Turnstile> A \<and> Some \<sigma>' = \<sigma> \<oplus> a \<Longrightarrow> \<sigma>', s, \<Delta> \<Turnstile> B"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Wand A B"
  using assms by auto

lemma sat_imp:
  assumes "\<sigma>, s, \<Delta> \<Turnstile> A \<Longrightarrow> \<sigma>, s, \<Delta> \<Turnstile> B"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Imp A B"
  using assms by auto

lemma sat_mult:
  assumes "\<And>a. \<sigma> = p \<odot> a \<Longrightarrow> a, s, \<Delta> \<Turnstile> A"
  shows "\<sigma>, s, \<Delta> \<Turnstile> Mult p A"
  by (metis assms sat.simps(1) unique_inv)

lemma larger_same:
  "a \<succeq> b \<longleftrightarrow> p \<odot> a \<succeq> p \<odot> b"
proof -
  have "\<And>a b p. a \<succeq> b \<Longrightarrow> p \<odot> a \<succeq> p \<odot> b"
    by (meson larger_def plus_mult)
  then show ?thesis
    by (metis unique_inv)
qed

lemma asso3:
  assumes "\<not> (a::'a) ## b"
      and "b \<oplus> c = Some bc"
    shows "\<not> a ## bc"
  using assms(1,2) asso3 compatible_def by blast

lemma compatible_smaller:
  assumes "(a::'a) \<succeq> b"
      and "x ## a"
    shows "x ## b"
  by (metis assms(1) assms(2) asso3 larger_def)

lemma compatible_multiples:
  assumes "p \<odot> a ## q \<odot> b"
  shows "a ## b"
  apply (rule compatible_smaller[of "(sadd one p) \<odot> b"])
   apply (metis distrib_mult larger_def one_neutral)
  using distrib_mult[of one p b]
  by (metis assms compatible_iff defined_comm distrib_mult local.asso2 one_neutral sadd_comm)
  
  


lemma move_sum:
  assumes "Some (a::'a) = a1 \<oplus> a2"
      and "Some b = b1 \<oplus> b2"
      and "Some x = a \<oplus> b"
      and "Some x1 = a1 \<oplus> b1"
      and "Some x2 = a2 \<oplus> b2"
    shows "Some x = x1 \<oplus> x2"
proof -
  obtain ab1 where "Some ab1 = a \<oplus> b1"
    by (metis assms(2) assms(3) asso3 compatible_def not_Some_eq)
  then have "Some ab1 = x1 \<oplus> a2"
    by (metis assms(1,4) pre_pcm_class.asso1 pre_pcm_class.commutative)
  then show ?thesis
    by (metis \<open>Some ab1 = a \<oplus> b1\<close> assms(2) assms(3) assms(5) pre_pcm_class.asso1)
qed

lemma sum_both_larger:
  assumes "Some x' = a' \<oplus> b'"
      and "Some (x::'a) = a \<oplus> b"
      and "a' \<succeq> a"
      and "b' \<succeq> b"
    shows "x' \<succeq> x"
proof -
  obtain ra rb where "Some a' = a \<oplus> ra" "Some b' = b \<oplus> rb"
    using assms(3) assms(4) pre_pcm_class.greater_def by blast
  then obtain r where "Some r = ra \<oplus> rb"
    by (metis assms(1) pre_pcm_class.asso3 pre_pcm_class.commutative option.collapse)
  then have "Some x' = x \<oplus> r"
    by (meson \<open>Some a' = a \<oplus> ra\<close> \<open>Some b' = b \<oplus> rb\<close> assms(1) assms(2) move_sum)
  then show ?thesis
    using larger_def by blast
qed

lemma larger_first_sum:
  assumes "Some (y::'a) = a \<oplus> b"
      and "x \<succeq> y"
    shows "\<exists>a'. Some x = a' \<oplus> b \<and> a' \<succeq> a"
proof -
  obtain r where "Some x = y \<oplus> r"
    using assms(2) larger_def by auto
  then obtain a' where "Some a' = a \<oplus> r"
    by (metis assms(1) pre_pcm_class.asso2 pre_pcm_class.commutative option.collapse)
  then show ?thesis
    by (metis \<open>Some x = y \<oplus> r\<close> assms(1) pre_pcm_class.asso1 pre_pcm_class.commutative larger_def)
qed

lemma larger_implies_compatible:
  assumes "x \<succeq> (y::'a)"
  shows "x ## y"
  using assms compatible_def compatible_smaller distrib_mult one_neutral option.distinct(1)
  by metis

end

end