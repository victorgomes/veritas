theory RKAT
  imports "$AFP/KAT_and_DRA/SingleSorted/KAT"
begin

class rkat = kat +
  fixes spec_op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (":[_ _]" [50,50] 100)
  assumes spec_def: "test p \<Longrightarrow> test q \<Longrightarrow> p\<cdot>x \<le> x\<cdot>q \<longleftrightarrow> x \<le> :[p q]"
begin

definition ref_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y \<equiv> y \<le> x"

lemma spec_char: "test p \<Longrightarrow> test q \<Longrightarrow> p\<cdot>:[p q] \<le> :[p q]\<cdot>q"
  by (metis eq_refl spec_def)

lemma specI [intro]: "test p \<Longrightarrow> test q \<Longrightarrow> p\<cdot>x \<le> x\<cdot>q \<Longrightarrow> :[p q] \<sqsubseteq> x"
  by (simp add: spec_def ref_order_def)

lemma spec_mult_isol: "x \<sqsubseteq> y \<Longrightarrow> z\<cdot>x \<sqsubseteq> z\<cdot>y"
  by (simp add: mult_isol ref_order_def)

lemma spec_mult_isor: "x \<sqsubseteq> y \<Longrightarrow> x\<cdot>z \<sqsubseteq> y\<cdot>z"
  by (simp add: mult_isor ref_order_def)

lemma star_iso: "x \<sqsubseteq> y \<Longrightarrow> x\<^sup>\<star> \<sqsubseteq> y\<^sup>\<star>"
  by (simp add: star_iso ref_order_def)

lemma ref_order_trans [trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  by (simp add: ref_order_def)

lemma strengthen_post: "\<lbrakk>test p; test q; test q'\<rbrakk> \<Longrightarrow> q' \<le> q \<Longrightarrow> :[p q] \<sqsubseteq> :[p q']"
  by (meson specI local.mult_isol local.order_trans spec_char)

lemma weaken_pre: "\<lbrakk>test p; test p'; test q\<rbrakk> \<Longrightarrow> p \<le> p' \<Longrightarrow> :[p q] \<sqsubseteq> :[p' q]"
  by (meson specI local.mult_isor local.order_trans spec_char)

lemma weaken_and_strengthen: "\<lbrakk>test p; test p'; test q; test q'\<rbrakk> \<Longrightarrow> p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> :[p q] \<sqsubseteq> :[p' q']"
  by (metis ref_order_trans strengthen_post weaken_pre)

lemma skip_ref: ":[1 1] \<sqsubseteq> 1"
  using local.test_one_var by blast

lemma abort_ref: ":[0 1] \<sqsubseteq> x"
  using local.test_one_var local.test_zero_var by auto

lemma magic_ref: "x \<sqsubseteq> :[1 0]"
  using local.spec_def local.test_one_var local.test_zero_var ref_order_def by force

lemma magic_eq_zero [simp]: ":[1 0] = 0"
  using local.zero_unique magic_ref ref_order_def by blast

lemma skip_ref_var1: "test p \<Longrightarrow> :[p 1] \<sqsubseteq> 1"
  by (auto simp: test_one_var local.test_ub_var)

lemma skip_ref_var2 [intro!]: "\<lbrakk>test p; test q; p \<le> q\<rbrakk> \<Longrightarrow> :[p q] \<sqsubseteq> 1"
  by auto

lemma sequence_ref [intro]: "\<lbrakk>test p; test q; test r\<rbrakk> \<Longrightarrow> :[p q] \<sqsubseteq> :[p r] \<cdot> :[r q]"
proof -
  assume hyp: "test p" "test q" "test r"
  hence "p \<cdot> :[p r] \<cdot> :[r q] \<le> :[p r] \<cdot> r \<cdot> :[r q]"
    by (simp add: local.mult_isor spec_char)
  also have "... \<le> :[p r] \<cdot> :[r q] \<cdot> q"
    by (simp add: hyp local.mult_isol mult_assoc spec_char)
  finally show ?thesis
    by (auto simp: hyp mult_assoc)
qed

lemma choice_ref [intro]: ":[p q] \<sqsubseteq> x \<Longrightarrow> :[p q] \<sqsubseteq> y \<Longrightarrow> :[p q] \<sqsubseteq> x + y"
  by (simp add: local.add_lub ref_order_def)

lemma test1_ref: "\<lbrakk>test b; test p; test q\<rbrakk> \<Longrightarrow> :[p q] \<sqsubseteq>  b\<cdot>:[p\<cdot>b q]"
  by (metis local.test_eq3 local.test_mult_closed mult_assoc specI spec_char)

lemma test2_ref: "\<lbrakk>test b; test p; test q\<rbrakk> \<Longrightarrow> :[p q\<cdot>b] \<sqsubseteq> :[p q] \<cdot> b"
oops

  
lemma conditional_ref: "\<lbrakk>test b; test p; test q\<rbrakk> \<Longrightarrow> :[p q] \<sqsubseteq>  b\<cdot>:[p\<cdot>b q] + !b\<cdot>:[p\<cdot>!b q]"
  by (auto intro: test_ref test_comp_closed)

lemma while_ref: "\<lbrakk>test b; test p\<rbrakk> \<Longrightarrow> :[p p\<cdot>!b] \<sqsubseteq> (b\<cdot>:[p\<cdot>b p])\<^sup>\<star>\<cdot>!b"
  apply (auto intro: specI)
  by (metis hoare_triple_def_var spec_char1 spec_def test_mult_closed  while_rule)

lemma ref_order_sym [simp]: ":[p q] \<sqsubseteq> :[p q]"
  by (metis eq_refl)

end

end
