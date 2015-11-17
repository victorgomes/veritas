theory Refinement
  imports StoreHeapModel
begin

text {* Morgan Refinement Laws *}

named_theorems ref_simps

definition spec :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a ptran"  where
  "spec p q \<equiv> Inf {F. p \<le> F q \<and> mono F}"

lemma spec_ht [ref_simps]: "ht p (spec p q) q"
  by (auto simp: ht_def spec_def)

lemma spec_char [ref_simps]: "p \<le> (spec p q) q"
  by (auto simp: ht_def spec_def)

lemma specI: "mono F \<Longrightarrow> ht p F q \<Longrightarrow> spec p q \<le> F"
  by (auto simp: ht_def spec_def intro: Inf_lower)

lemma ht_spec_eq: "mono F \<Longrightarrow> ht p F q \<longleftrightarrow> spec p q \<le> F"
proof (auto intro: specI, simp add: ht_def)
  assume assm: "spec p q \<le> F"
  have "p \<le> (spec p q) q"
    by (rule spec_char)
  also have "... \<le> F q" using assm
    by (auto simp: le_fun_def)
  finally show "p \<le> F q"
    by simp
qed 

lemma spec_mono [mptran]: "mono (spec p q)"
  by (auto simp: spec_def intro: mptran)

(***********************************************************************************************)

text {* Morgan's refinement laws *}

named_theorems rlaw

lemma strengthen_post [rlaw]: "q' \<le> q \<Longrightarrow> spec p q \<le> spec p q'"
  by (meson hl_post ht_def specI spec_char spec_mono)

lemma weaken_pre [rlaw]: "p \<le> p' \<Longrightarrow> spec p q \<le> spec p' q"
  by (meson dual_order.trans ht_def specI spec_char spec_mono)

lemma weaken_and_strengthen [rlaw]: "p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> spec p q \<le> spec p' q'"
  by (meson dual_order.trans strengthen_post weaken_pre)

lemma skip_ref: "spec true true \<le> skip"
  by (auto simp: skip_def spec_def mono_def intro!: Inf_lower)

lemma abort_ref [rlaw]: "spec false true \<le> F"
  by (metis (no_types, hide_lams) bot.extremum bot_apply dual_order.trans ht_def ht_spec_eq mono_def)

lemma magic_ref [rlaw]: "F \<le> spec true false"
  by (metis (no_types, hide_lams) antisym_conv bot.extremum ht_def ht_spec_eq le_fun_def spec_mono strengthen_post top_greatest)

lemma skip_ref_var1: "spec p true \<le> skip"
  by (simp add: hl_skip mono_skip specI)

lemma skip_ref_var2 [rlaw]: "p \<le> q \<Longrightarrow> spec p q \<le> skip"
  using hl_skip ht_spec_eq mono_skip by blast

lemma sequence_ref [rlaw]: "spec p q \<le> (spec p r); (spec r q)"
  using hl_seq mono_seq specI spec_ht spec_mono by blast

lemma following_ref: "mono y \<Longrightarrow> x \<le> y ; z \<Longrightarrow> z \<le> w \<Longrightarrow> x \<le> y ; w"
proof -
  assume m: "mono y" and zw: "z \<le> w" and "x \<le> y ; z"
  hence "x \<le> y ; z"
    by simp
  also have "... \<le> y ; w"
    apply (simp add: seq_def)
    apply (rule le_funI)
    apply simp
    apply (rule monoD, rule m)
    using zw by (auto simp: le_fun_def)
  finally show ?thesis
    by simp
qed

lemma leading_ref: "x \<le> y ; w \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z ; w"
proof -
  assume zw: "y \<le> z" and "x \<le> y ; w"
  hence "x \<le> y ; w"
    by simp
  also have "... \<le> z ; w"
    using zw by (auto simp: seq_def le_fun_def)
  finally show ?thesis
    by simp
qed

lemma leading_ref' [rlaw]: "spec p r \<le> F \<Longrightarrow> spec p q \<le> F; spec r q"
  apply (rule leading_ref[rotated])
  apply assumption
  apply (rule sequence_ref)
done

lemma mono_law [rlaw]: "mono x \<Longrightarrow> y \<le> z \<Longrightarrow> x ; y \<le> x ; z"
  apply (auto simp: seq_def)
  by (metis following_ref order_refl seq_def)

lemma choice_ref [rlaw]: "spec p q \<le> x \<Longrightarrow> spec p q \<le> y \<Longrightarrow> spec p q \<le> x \<sqinter> y"
  by simp

lemma test_expl_ref [rlaw]: "spec p q \<le>  \<lfloor>b\<rfloor>; (spec (p \<sqinter> b) q)"
  by (metis hl_asumption ht_def inf_commute mono_assumption mono_seq seq_def specI spec_char spec_mono)

lemma test_expr_ref [rlaw]: "spec p (q \<sqinter> b) \<le> (spec p q); \<lfloor>b\<rfloor>"
  by (metis Assertions.bbi.join_meet_galois Sup.order_refl assumption_def hl_seq ht_def inf_commute mono_assumption mono_seq specI spec_char spec_mono)

lemma conditional_ref [rlaw]: "spec p q \<le> cond b (spec (p \<sqinter> b) q) (spec (p \<sqinter> -b) q)"
  by (metis hl_cond ht_def inf_commute mono_cond specI spec_char spec_mono)

lemma while_ref [rlaw]: "spec p (p \<sqinter> -b) \<le> cwhile b (spec (p \<sqinter> b) p)"
  by (metis hl_while ht_def inf_commute mono_while specI spec_char spec_mono)

lemma iso_while_spec: "mono (\<lambda>p. cwhile b (spec p i))"
proof (auto simp: mono_def)
  fix x y :: "'a pred" assume "x \<le> y"
  moreover have "mono (spec x i)"
    by (simp add: spec_mono)
  moreover have "(spec x i) \<le> (spec y i)"
    by (meson calculation(1) hl_pre specI spec_ht spec_mono)
  ultimately show "cwhile b (spec x i) \<le> cwhile b (spec y i)"
    by (auto intro!: iso_while)
qed

lemma while_ref_tactic [rlaw]: "\<lbrakk>i \<sqinter> b \<le> p'; p \<le> i; i - b \<le> q\<rbrakk> \<Longrightarrow> spec p q \<le> cwhile b (spec p' i)"
proof -
  assume "p \<le> i" "i - b \<le> q" and assm: "i \<sqinter> b \<le> p'"
  hence "spec p q \<le> spec i (i \<sqinter> -b)"
    by (metis diff_eq weaken_and_strengthen)
  also have "... \<le> cwhile b (spec (i \<sqinter> b) i)"
    by (simp add: while_ref)
  also have "... \<le> cwhile b (spec p' i)"
    using assm by (auto intro!: monoD iso_while_spec)
  finally show ?thesis
    by simp
qed

lemma exs_ref [rlaw]: "mono R \<Longrightarrow> (\<And>x. spec (P x) (Q x) \<le> R) \<Longrightarrow> spec (EXS x. P x) (EXS y. Q y) \<le> R"
  by (auto simp: ht_spec_eq[symmetric] intro: hl_exs2)

(***********************************************************************************************)

text {* Framing laws *}

lemma frame_ref [rlaw]: "mono x \<Longrightarrow> local x r \<Longrightarrow> spec p q \<le> x \<Longrightarrow> spec (p * r) (q * r) \<le> x"
  using ht_spec_eq sl_frame by blast

lemma frame_ref2 [rlaw]: "mono x \<Longrightarrow> local x r \<Longrightarrow> spec p q \<le> x \<Longrightarrow> spec (r * p) (r * q) \<le> x"
  by (simp add: frame_ref sep_comm)

(***********************************************************************************************)

text {* Assignment and mutation laws *}

lemma assignment_ref [rlaw]: "p \<subseteq> subst_pred q v m \<Longrightarrow> spec p q \<le> assign v m"
  by (auto simp: subst_pred_def assign_def spec_def basic_def valid_mem_def intro!: Inf_lower mptran)

lemma following_assignment_ref [rlaw]: "q' \<subseteq> subst_pred q v m \<Longrightarrow> spec p q \<le> spec p q'; assign v m"
  by (auto intro: following_ref mptran rlaw)

lemma leading_assignment_ref [rlaw]: "p \<subseteq> subst_pred p' v m \<Longrightarrow> spec p q \<le> assign v m; spec p' q"
  by (auto intro: leading_ref rlaw)

lemma lookup_ref [rlaw]: "\<forall>s x. k (k_update (\<lambda>_. x) s) = x \<Longrightarrow> 
            \<forall>s x. i (k_update (\<lambda>_. x) s) = i s \<Longrightarrow> 
            \<forall>x. subst_pred (R k) k_update (\<lambda>_. x) = R (\<lambda>_. x) \<Longrightarrow> 
            spec (EXS x. (i \<mapsto> (\<lambda>_. x)) * R (\<lambda>_. x)) ((i \<mapsto> k) * R k) \<le> lookup k_update i"
   apply (rule specI)
   apply (rule mptran)+
   apply (rule hl_pre[rotated])
   apply (rule sl_lookup_alt')
   apply (rule mono_exs)
   apply sep_simp
   apply simp
   apply (metis (no_types, lifting) bbi.Sup.qisol bbi.mult.left_commute top_greatest)
done

lemma lookup_suc_ref [rlaw]: "\<forall>s x. k (k_update (\<lambda>_. x) s) = x \<Longrightarrow> 
            \<forall>s x. i (k_update (\<lambda>_. x) s) = i s \<Longrightarrow> 
            \<forall>x. subst_pred (R k) k_update (\<lambda>_. x) = R (\<lambda>_. x) \<Longrightarrow> 
            spec (EXS x. (i \<mapsto> (\<lambda>_. a), (\<lambda>_. x)) * R (\<lambda>_. x)) ((i \<mapsto> (\<lambda>_. a), k) * R k) \<le> lookup k_update (\<lambda>s. i s + 1)"
   apply (rule specI)
   apply (rule mptran)+
   apply (rule hl_pre[rotated])
   apply (rule sl_lookup_alt')
   apply (rule mono_exs)
   apply sep_simp
   apply simp
   apply (metis (no_types, lifting) bbi.Sup.qisol bbi.mult.left_commute top_greatest)
done

lemma alloc_ref [rlaw]: "free x_upd e \<Longrightarrow> vars1 x_upd x \<Longrightarrow> spec emp (x \<mapsto> e) \<le> alloc x_upd e"
  by (auto intro: specI mptran sl)

lemma disposal_ref [rlaw]: "spec ((e \<mapsto> n) * r) r \<le> disposal e"
  by (simp add: mono_disposal sl_disposal_alt specI)

lemma mutation_ref [rlaw]: "spec ((e \<mapsto> n) * r) ((e \<mapsto> e') * r) \<le> mutation e e'"
  by (auto intro: specI mptran sl)

lemma mutation_suc_ref [rlaw]: "spec ((i \<mapsto> a, b) * r) ((i \<mapsto> a, e) * r) \<le> mutation (\<lambda>s. i s + 1) e"
  by (auto simp: doublet_def sep_assoc intro: frame_ref2 mptran lptran specI sl)

(***********************************************************************************************)

text {* \emph{morgan} tactic *}

method morgan_step uses simp ref = 
  (assumption | subst sep_assoc | subst seq_assoc | rule iso_while | rule ref rlaw mptran)

method morgan uses simp ref = 
  (morgan_step simp: simp ref: ref; (morgan simp: simp ref: ref)?)+


end