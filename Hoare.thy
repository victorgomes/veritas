theory Hoare
  imports While "$AFP/KAT_and_DRA/SingleSorted/KAT_Models" "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"
begin

no_notation comp_op ("n_" [90] 91)
  and test_operator  ("t_" [100] 101)
  and floor ("\<lfloor>_\<rfloor>")
  and ceiling ("\<lceil>_\<rceil>")
  and Set.image (infixr "`" 90)
  
notation inf (infixl "\<sqinter>" 60)

named_theorems hl_rules

method hoare_step uses simp declares hl_rules = (
  ((rule allI | rule ballI | subst simp)+)?;
  (assumption | rule subset_refl | rule hl_rules)
)

method hoare uses simp declares hl_rules = 
  (hoare_step; hoare?)+

method hoarerule uses first simp declares hl_rules = 
  (((rule allI | rule ballI | subst simp)+)?, rule first; hoare?)

definition ht :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's set \<Rightarrow> bool" where
  "ht P x Q \<equiv> \<lfloor>P\<rfloor>;x \<subseteq> x;\<lfloor>Q\<rfloor>"

lemma hl_abort [hl_rules]: "ht P abort Q"
  by (auto simp: ht_def abort_def seq_def)
  
lemma hl_skip [hl_rules]: "P \<subseteq> Q \<Longrightarrow> ht P skip Q"
  by (auto simp: ht_def skip_def seq_def)
  
lemma hl_to_rel [hl_rules]: "P \<subseteq> {s. f s \<in> Q} \<Longrightarrow> ht P (\<langle>f\<rangle>) Q"
  by (auto simp: ht_def to_rel_def seq_def)

lemma hl_seq [hl_rules]: "ht R y Q \<Longrightarrow> ht P x R \<Longrightarrow> ht P (x; y) Q"
  by (force simp: ht_def seq_def)

lemma hl_split: "ht P x {t. Q t} \<Longrightarrow> ht P x {t. Q' t} \<Longrightarrow> ht P x {t. Q t \<and> Q' t}"
  by (force simp: ht_def seq_def)

lemma hl_cond : "ht (b \<sqinter> P) x Q \<Longrightarrow> ht (-b \<sqinter> P) y Q \<Longrightarrow> ht P (cond b x y) Q"
  by (fastforce simp: ht_def cond_def seq_def)

lemma hl_cond_tac [hl_rules]: "P \<subseteq> P' \<union> - b \<Longrightarrow> P \<subseteq> P''  \<union> b  \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P'' y Q \<Longrightarrow> ht P (cond b x y) Q"
  by (fastforce simp: ht_def cond_def seq_def)
  
lemma hl_while: "ht (b \<sqinter> i) x i \<Longrightarrow> ht i (while b x) (-b \<sqinter> i)"
proof (simp add: ht_def while_def seq_def)
  assume "\<lfloor>b \<sqinter> i\<rfloor> O x \<subseteq> x O \<lfloor>i\<rfloor>"
  hence "\<lfloor>i\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* \<subseteq> (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>i\<rfloor>"
    by (force intro!: rel_kat.star_sim2)
  thus "\<lfloor>i\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor> \<subseteq> ((\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor>) O \<lfloor>-b \<sqinter> i\<rfloor>"
    by auto
qed

lemma hl_dyn [hl_rules]: "\<forall>s \<in> P. ht P (g s) Q \<Longrightarrow> ht P (\<lceil>g\<rceil>) Q"
  by (fastforce simp: ht_def seq_def dyn_def)

lemma hl_pre: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def)

lemma hl_post: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def)

lemma hl_classic: "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def)
  
lemma hl_conseq: "\<forall>s. ht (P' s) c (Q' s) \<Longrightarrow> \<forall>s. s \<in> P \<longrightarrow> (\<exists>s'. s \<in> P' s' \<and> (Q' s' \<subseteq> Q)) \<Longrightarrow> ht P c Q"
  by (force simp: ht_def seq_def)

lemma hl_block [hl_rules]: "P \<subseteq> {s. init s \<in> P' s} \<Longrightarrow> \<forall>s. ht (P' s) x {t. ret s t \<in> R s t}
  \<Longrightarrow> \<forall>s t. ht (R s t) (c s t) Q \<Longrightarrow> ht P (block init x ret c) Q"
  apply (rule hl_conseq [where P'="\<lambda>s'. {s. s = s' \<and> init s \<in> P' s'}" and Q'="\<lambda> s'. Q"])
  apply (hoare_step simp: block_def, hoare_step)
  apply (rule_tac R="{t. ret s t \<in> R s t}" in hl_seq)
  apply (rule_tac P'="\<lambda>s'. {t. t=s' \<and> ret s t \<in> R s t}" and Q'="\<lambda>s'. Q" in hl_conseq)
  apply hoare
  apply (erule_tac x=sa in allE, erule_tac x=sc in allE, assumption)
  apply force
  apply force
  apply (erule_tac x=s in allE, assumption)
  apply hoare_step
  apply force+
 done

lemma ht_true [intro]: "ht UNIV x UNIV"
  by (auto simp: ht_def seq_def)

lemma hl_false [intro]: "ht {} x {}"
  by (auto simp: ht_def seq_def)

lemma hl_Sup: "\<forall>x \<in> X. ht P x Q \<Longrightarrow> ht P (Sup X) Q"
  by (fastforce simp: ht_def seq_def)
thm allE
lemma hl_rec [hl_rules]: "mono f \<Longrightarrow> (\<And>x. \<forall>z. ht (P z) x (Q z) \<Longrightarrow> \<forall>z. ht (P z) (f x) (Q z)) \<Longrightarrow> \<forall>z. ht (P z) (lfp f) (Q z)"

  apply (rule lfp_ordinal_induct)
apply simp
apply force
apply (auto intro: hl_Sup)
done

lemma hl_rec2 [hl_rules]: "mono f \<Longrightarrow> (\<And>x. \<forall>z. ht (P z) x (Q z) \<Longrightarrow> \<forall>z. ht (P z) (f z x) (Q z)) \<Longrightarrow> \<forall>z. ht (P z) (lfp (f z)) (Q z)"
sorry

text {* Annotated programs *}

lemma hl_awhile [hl_rules]: "P \<subseteq> i \<Longrightarrow> -b \<inter> i \<subseteq> Q \<Longrightarrow> ht (b \<sqinter> i) x i \<Longrightarrow> ht P (awhile i b x) Q"
  by (hoarerule simp: awhile_def first: hl_conseq hl_rules: hl_while) force
  
lemma hl_apre: "P \<subseteq> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P (apre P' x) Q"
  by (hoarerule simp: apre_def first: hl_pre)

lemma hl_apre2: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> \<forall>z. ht (P z) x (Q z)"
  apply (simp add: apre_def seq_def ht_def)
  apply auto
  by force

lemma hl_apre3: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> ht (P z) x (Q z)"
  apply (simp add: apre_def seq_def ht_def)
  apply auto
  by force

lemma hl_2: "P \<subseteq> {s. (\<exists>z. s \<in> P' z \<and> Q' z \<subseteq> Q)} \<Longrightarrow> \<forall>z. ht (P' z) x (Q' z) 
  \<Longrightarrow> ht P x Q"
sorry
  
lemma hl_apost [hl_rules]: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P (apost x Q') Q"
  by (auto simp: apost_def le_fun_def intro!: hl_seq hl_apre hl_skip)
  
lemma hl_aprog [hl_rules]: "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P (aprog P' x Q') Q"
  by (hoarerule simp: aprog_def first: hl_classic)


end
