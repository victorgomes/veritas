theory RKAT
  imports "$AFP/KAT_and_DRA/SingleSorted/KAT"
begin

class rkat = kat +
  fixes spec :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def: "test p \<Longrightarrow> test q \<Longrightarrow> p\<cdot>x \<le> x\<cdot>q \<longleftrightarrow> x \<le> spec p q"
begin

definition ref_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y \<equiv> y \<le> x"

lemma ref_order_refl [simp]: "spec p q \<sqsubseteq> spec p q"
  by (auto simp: ref_order_def)

lemma spec_char [simp]: "test p \<Longrightarrow> test q \<Longrightarrow> p\<cdot>(spec p q) \<le> (spec p q)\<cdot>q"
  by (simp add: spec_def)

lemma specI [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> p\<cdot>x \<le> x\<cdot>q \<Longrightarrow> (spec p q) \<sqsubseteq> x"
  by (simp add: spec_def ref_order_def)

lemma spec_mult_isol [intro]: "x \<sqsubseteq> y \<Longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>y"
  by (simp add: mult_isol ref_order_def)

lemma spec_mult_isor [intro]: "x \<sqsubseteq> y \<Longrightarrow> x\<cdot>z \<sqsubseteq> y\<cdot>z"
  by (simp add: mult_isor ref_order_def)

lemma star_iso [intro]: "x \<sqsubseteq> y \<Longrightarrow> x\<^sup>\<star> \<sqsubseteq> y\<^sup>\<star>"
  by (simp add: star_iso ref_order_def)

lemma ref_order_trans [trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  by (simp add: ref_order_def)

lemma strengthen_post [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> test q' \<Longrightarrow> q' \<le> q \<Longrightarrow> spec p q \<sqsubseteq> spec p q'"
  by (meson specI local.mult_isol local.order_trans spec_char)

lemma weaken_pre [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> test p' \<Longrightarrow> p \<le> p' \<Longrightarrow> spec p q \<sqsubseteq> spec p' q"
  by (meson specI local.mult_isor local.order_trans spec_char)

lemma weaken_and_strengthen [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> test p' \<Longrightarrow> test q' \<Longrightarrow> p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> spec p q \<sqsubseteq> spec p' q'"
  by (metis ref_order_trans strengthen_post weaken_pre)

lemma skip_ref [simp]: "spec 1 1 \<sqsubseteq> 1"
  using local.test_one_var by blast

lemma abort_ref [simp]: "spec 0 1 \<sqsubseteq> x"
  using local.test_one_var local.test_zero_var by auto

lemma magic_ref [simp]: "x \<sqsubseteq> spec 1 0"
  by (metis local.annir local.mult_1_left local.zero_least local.zero_unique ref_order_def spec_char test_one_var test_zero_var)

lemma magic_eq_zero [simp]: "spec 1 0 = 0"
  using local.zero_unique magic_ref ref_order_def by blast

lemma skip_ref_var1: "test p \<Longrightarrow> spec p 1 \<sqsubseteq> 1"
  by (auto simp: test_one_var local.test_ub_var)

lemma skip_ref_var2 [intro!]: "test p \<Longrightarrow> test q \<Longrightarrow> p \<le> q \<Longrightarrow> spec p q \<sqsubseteq> 1"
  by auto

lemma sequence_ref [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> spec p q \<sqsubseteq> (spec p r) \<cdot> (spec r q)"
proof -
  assume hyp: "test p" "test q" "test r"
  hence "p \<cdot> (spec p r) \<cdot> (spec r q) \<le> (spec p r) \<cdot> r \<cdot> (spec r q)"
    by (simp add: local.mult_isor)
  also have "... \<le> (spec p r) \<cdot> (spec r q) \<cdot> q"
    by (simp add: hyp local.mult_isol mult_assoc)
  finally show ?thesis
    by (auto simp: hyp mult_assoc)
qed

lemma choice_ref [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> spec p q \<sqsubseteq> x \<Longrightarrow> spec p q \<sqsubseteq> y \<Longrightarrow> spec p q \<sqsubseteq> x + y"
  by (simp add: local.add_lub ref_order_def)

lemma test_expl_ref: "test b \<Longrightarrow> test p \<Longrightarrow> test q \<Longrightarrow> spec p q \<sqsubseteq>  b \<cdot> (spec (p\<cdot>b) q)"
  sorry

lemma test_expr_ref: "test b \<Longrightarrow> test p \<Longrightarrow> test q \<Longrightarrow> spec p (q\<cdot>b) \<sqsubseteq> (spec p q) \<cdot> b"
oops

lemma conditional_ref: "test b \<Longrightarrow> test p \<Longrightarrow> test q \<Longrightarrow> spec p q \<sqsubseteq>  b \<cdot> (spec (p\<cdot>b) q) + !b \<cdot> (spec (p\<cdot>!b) q)"
  by (auto intro: test_expl_ref test_comp_closed)

lemma while_ref: "test b \<Longrightarrow> test c \<Longrightarrow> test p \<Longrightarrow> spec p (p\<cdot>c) \<sqsubseteq> (b \<cdot> (spec (p\<cdot>b) p))\<^sup>\<star>\<cdot>c"
  apply (auto intro!: specI)
  apply (simp add: local.test_comp_closed_var local.test_mult_closed)
  apply (subst mult_assoc[symmetric]) back
  apply (subst mult_assoc)
  apply (subst test_mult_comm_var) back back back back back back back
  apply (simp add: test_comp_closed)
  apply simp
  apply (subst mult_assoc[symmetric]) back
  apply (subst mult_assoc) back
  apply (subst test_mult_idem_var)
  apply (simp add: test_comp_closed)
  apply (subst mult_assoc[symmetric])
  apply (rule mult_isor[THEN impE])
  prefer 2
  apply assumption
  apply (rule star_sim2)
using local.spec_def ref_order_def test_expl_ref by auto
  
end

end
