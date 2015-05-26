theory Hoare
  imports While "$AFP/KAT_and_DRA/SingleSorted/KAT_Models"
begin

no_notation comp_op ("n_" [90] 91)
  and test_operator  ("t_" [100] 101)
  and floor ("\<lfloor>_\<rfloor>")
  and ceiling ("\<lceil>_\<rceil>")
  
notation inf (infixl "\<sqinter>" 60)

definition ht :: "('v \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> ('v \<Rightarrow> 's set) \<Rightarrow> bool" where
  "ht P x Q \<equiv> \<forall>u. \<lfloor>P u\<rfloor>;x \<subseteq> x;\<lfloor>Q u\<rfloor>"

lemma hl_abort: "ht P abort Q"
  by (auto simp: ht_def abort_def seq_def)
  
lemma hl_skip: "P \<le> Q \<Longrightarrow> ht P skip Q"
  by (auto simp: ht_def skip_def le_fun_def seq_def)
  
lemma hl_to_rel: "\<forall>u. P u \<subseteq> {s. f s \<in> Q u} \<Longrightarrow> ht P (\<langle>f\<rangle>) Q"
  by (auto simp: ht_def to_rel_def seq_def)

lemma hl_seq: "ht R y Q \<Longrightarrow> ht P x R \<Longrightarrow> ht P (x; y) Q"
  by (force simp: ht_def seq_def)

lemma hl_cond: "ht (<b> \<sqinter> P) x Q \<Longrightarrow> ht (-<b> \<sqinter> P) y Q \<Longrightarrow> ht P (cond b x y) Q"
  by (fastforce simp: ht_def cond_def seq_def assert_def)
  
lemma hl_while: "ht (<b> \<sqinter> i) x i \<Longrightarrow> ht i (while b x) (-<b> \<sqinter> i)"
proof (simp add: ht_def while_def seq_def, rule allI)
  fix u
  assume "\<forall>u. \<lfloor><b> u \<sqinter> i u\<rfloor> O x \<subseteq> x O \<lfloor>i u\<rfloor>"
  hence "\<lfloor>i u\<rfloor> O (\<lfloor><b> u\<rfloor> O x)\<^sup>* \<subseteq> (\<lfloor><b> u\<rfloor> O x)\<^sup>* O \<lfloor>i u\<rfloor>"
    by (force intro!: rel_kat.star_sim2)
  thus "\<lfloor>i u\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor> \<subseteq> ((\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor>) O \<lfloor>-<b> u \<sqinter> i u\<rfloor>"
    by (auto simp: assert_def)
qed

lemma hl_dyn: "\<forall>u. \<forall>s \<in> P u. ht P (g s) Q \<Longrightarrow> ht P (\<lceil>g\<rceil>) Q"
  by (fastforce simp: ht_def seq_def dyn_def)
  
lemma hl_pre: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def)

lemma hl_post: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def)
  
lemma hl_conseq: "ht P' x Q' \<Longrightarrow> P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P x Q"
  by (metis hl_pre hl_post)

lemma hl_block: "\<forall>u. P u \<subseteq> {s. init s \<in> P' s u} \<Longrightarrow> \<forall>s. ht (P' s) x (\<lambda>u. {t. ret s t \<in> R s t u}) 
  \<Longrightarrow> \<forall>s t. ht (R s t) (c s t) Q \<Longrightarrow> ht P (block init x ret c) Q"
  apply (simp add: block_def)
  apply (rule hl_dyn)
  apply clarsimp
  apply (rule hl_seq)
  apply (rule hl_seq)
  prefer 2
  apply (erule_tac x=s in allE)
  apply assumption
  apply (rule hl_dyn)
  apply clarsimp
  apply (clarsimp simp: ht_def to_rel_def seq_def)
sorry

text {* Annotated programs *}

lemma hl_awhile: "P \<le> i \<Longrightarrow> -<b> \<sqinter> i \<le> Q \<Longrightarrow> ht (<b> \<sqinter> i) x i \<Longrightarrow> ht P (awhile i b x) Q"
  by (auto simp: awhile_def intro: hl_while hl_conseq)

lemma hl_apre: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P (apre P' x) Q"
  by (auto simp: apre_def intro: hl_pre)
  
lemma hl_apost: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P (apost x Q') Q"
  by (auto simp: apost_def intro!: hl_seq hl_apre hl_skip)
  
lemma hl_aprog: "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P (aprog P' x Q') Q"
  by (auto simp: aprog_def intro: hl_conseq)


end
