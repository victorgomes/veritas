section {* Verification condition generator *}

theory VCG
  imports While "$AFP/KAT_and_DRA/SingleSorted/KAT_Models" "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"
begin

no_notation comp_op ("n_" [90] 91)
  and test_operator  ("t_" [100] 101)
  and floor ("\<lfloor>_\<rfloor>")
  and ceiling ("\<lceil>_\<rceil>")
  and Set.image (infixr "`" 90)
  
notation inf (infixl "\<sqinter>" 60)

(***********************************************************************************************)

text {* \emph{hoare} tactic *}

named_theorems hl_rules

method hoare_init uses simp = 
  ((subst simp | subst fst_conv | subst snd_conv)+)?

method hoare_step uses simp hl = 
  (hoare_init simp: simp, (assumption | rule subset_refl | rule mono_rules | rule hl hl_rules | rule allI | rule ballI))

method hoare_ind uses simp hl = 
  (hoare_step simp: simp hl: hl; (hoare_ind simp: simp hl: hl)?)+

method hoare uses simp hl = 
  (hoare_init simp: simp; (hoare_ind simp: simp hl: hl)?)

method hl_aux uses rule =
  (rule allI, rule rule; ((erule_tac x=u in allE)+, assumption))
  

(***********************************************************************************************)

text {* Classic Hoare logic *}

definition ht :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "ht P x Q \<equiv> \<lfloor>P\<rfloor>;x \<subseteq> x;\<lfloor>Q\<rfloor>"

lemma ht_true: "ht P x UNIV"
  by (auto simp: ht_def seq_def)

lemma hl_false [intro]: "ht {} x Q"
  by (auto simp: ht_def seq_def test_def)

lemma hl_abort [hl_rules]: "ht P abort Q"
  by (auto simp: ht_def abort_def seq_def)
  
lemma hl_skip [hl_rules]: "P \<subseteq> Q \<Longrightarrow> ht P skip Q"
  by (auto simp: ht_def skip_def seq_def test_def)
  
lemma hl_graph [hl_rules]: "P \<subseteq> {s. f s \<in> Q} \<Longrightarrow> ht P (graph f) Q"
  by (auto simp: ht_def graph_def seq_def test_def)

lemma hl_assign [hl_rules]: "P \<subseteq> subst Q z_upd t \<Longrightarrow> ht P (assign z_upd t) Q"
  by (auto simp: assign_def subst_def intro!: hl_graph)

lemma hl_assign_aux [hl_rules]: "\<forall>z. P z \<subseteq> subst (Q z) z_upd t \<Longrightarrow> \<forall>z. ht (P z) (assign z_upd t) (Q z)"
  by (auto simp: assign_def subst_def intro!: hl_graph)

lemma hl_seq [hl_rules]: "ht R y Q \<Longrightarrow> ht P x R \<Longrightarrow> ht P (x; y) Q"
  by (force simp: ht_def seq_def)

lemma hl_seq_aux [hl_rules]: "\<forall>u. ht (R u) (y u) (Q u) \<Longrightarrow> \<forall>u. ht (P u) (x u) (R u) \<Longrightarrow> \<forall>u. ht (P u) (x u; y u) (Q u)"
  by (hl_aux rule: hl_seq)

lemma hl_split: "ht P x {t. Q t} \<Longrightarrow> ht P x {t. Q' t} \<Longrightarrow> ht P x {t. Q t \<and> Q' t}"
  by (force simp: ht_def seq_def test_def)

lemma hl_split_aux: "\<forall>u. ht (P u) x {t. (Q u) t} \<Longrightarrow> \<forall>u. ht (P u) x {t. Q' u t} \<Longrightarrow> \<forall>u. ht (P u) x {t. Q u t \<and> Q' u t}"
  by (hl_aux rule: hl_split)

lemma hl_cassic_cond : "ht (b \<sqinter> P) x Q \<Longrightarrow> ht (-b \<sqinter> P) y Q \<Longrightarrow> ht P (cond b x y) Q"
  by (fastforce simp: ht_def cond_def seq_def test_def)

lemma hl_cond [hl_rules]: "P \<subseteq> (P' \<union> - b) \<inter> (P'' \<union> b)  \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P'' y Q \<Longrightarrow> ht P (cond b x y) Q"
  by (fastforce simp: ht_def cond_def seq_def)

lemma hl_cond_aux [hl_rules]: "\<forall>u. P u \<subseteq> (P' u \<union> - b) \<inter> (P'' u \<union> b)  \<Longrightarrow> \<forall>u. ht (P' u) x (Q u) \<Longrightarrow> \<forall>u. ht (P'' u) y (Q u) \<Longrightarrow> \<forall>u. ht (P u) (cond b x y) (Q u)"
  by (hl_aux rule: hl_cond)

lemma hl_while: "ht (b \<sqinter> i) x i \<Longrightarrow> ht i (cwhile b x) (-b \<sqinter> i)"
proof (simp add: ht_def cwhile_def seq_def)
  assume "\<lfloor>b \<sqinter> i\<rfloor> O x \<subseteq> x O \<lfloor>i\<rfloor>"
  hence "\<lfloor>i\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* \<subseteq> (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>i\<rfloor>"
    by (force intro!: rel_kat.star_sim2)
  thus "\<lfloor>i\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor> \<subseteq> ((\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor>) O \<lfloor>-b \<sqinter> i\<rfloor>"
    by auto
qed

(***********************************************************************************************)

text {* Weakening / Strengthening / Consequence Rules *}

lemma hl_pre: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def test_def)

lemma hl_post: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def test_def)

lemma hl_post_aux: "\<forall>u. Q' u \<le> Q u \<Longrightarrow> \<forall>u. ht (P u) x (Q' u) \<Longrightarrow> \<forall>u. ht (P u) x (Q u)"
  by (fastforce simp: ht_def le_fun_def seq_def test_def)

lemma hl_classic: "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def)
  
lemma hl_conseq: "\<forall>z. ht (P' z) c (Q' z) \<Longrightarrow> \<forall>s. s \<in> P \<longrightarrow> (\<exists>z. s \<in> P' z \<and> (Q' z \<subseteq> Q)) \<Longrightarrow> ht P c Q"
  by (force simp: ht_def seq_def)

lemma hl_kleymann: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> ht (P z) x (Q z)"
 by (fastforce simp: apre_def seq_def ht_def)

lemma hl_kleymann_aux: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> \<forall>z. ht (P z) x (Q z)"
 by (hl_aux rule: hl_kleymann)

lemma hl_for [hl_rules]: "\<forall>s. m_upd(\<lambda>_. m s) s = s \<Longrightarrow> 
  ht P (assign j_upd n) (subst Q m_upd j \<inter> {s. j s \<le> m s}) \<Longrightarrow> 
  ht ({s. j s < m s} \<inter> subst Q m_upd j) x (subst (subst Q m_upd j \<inter> {s. j s \<le> m s}) j_upd (\<lambda>s. j s + 1)) \<Longrightarrow> 
  ht P (cfor (j_upd, j) n (m_upd, m) x) Q"
  apply (rule hl_post [where Q'="(-{s. j s < m s} \<inter> (subst Q m_upd j \<inter> {s. j s \<le> m s}))"])
  apply (subgoal_tac "-{s. j s < m s} \<inter> (subst Q m_upd j \<inter> {s. j s \<le> m s}) = {s. j s = m s} \<inter> subst Q m_upd j")
  apply (force simp: subst_def)
  apply force
  apply (hoare simp: cfor_def hl: hl_while)
  apply (subgoal_tac "{s. j s < m s} \<inter> (subst Q m_upd j \<inter> {s. j s \<le> m s}) = {s. j s < m s} \<inter> subst Q m_upd j")
  apply force+
done

(***********************************************************************************************)

text {* Blocks / Procedures / Recursive Calls *}


lemma hl_dyn [hl_rules]: "\<forall>s \<in> P. ht P (g s) Q \<Longrightarrow> ht P (\<lceil>g\<rceil>) Q"
  by (fastforce simp: ht_def seq_def dyn_def)

lemma hl_local_inv: "\<forall>s s'. z (z_upd (\<lambda>_. z s) s') = z s \<Longrightarrow> P \<le> {s. z s = u} \<Longrightarrow> ht P (loc_block (z_upd, z) t x) {s. z s = u}"
  by (auto simp: block_def loc_block_def graph_def dyn_def seq_def ht_def)

lemma hl_block: "\<forall>s. ht P x {t. f s t \<in> Q} \<Longrightarrow> ht P (block x f) Q"
  by (hoare simp: block_def hl: ballI) force

lemma hl_loc_block: "\<forall>s. ht P (\<langle>\<lambda>s. z_upd (\<lambda>_. t s) s\<rangle>; x) {t. z_upd s t \<in> Q} \<Longrightarrow> ht P (loc_block (z_upd, z) t x) Q"
  by (auto simp: loc_block_def intro: hl_block)

lemma hl_fun_block_inv: "\<forall>s s'. y (y_upd (\<lambda>_. y s) s') = y s \<Longrightarrow> P \<le> {s. y s = u} \<Longrightarrow> ht P (fun_call z_upd (R, (y_upd, y))) {s. y s = u }"
  by (auto simp: block_def loc_block_def graph_def dyn_def seq_def ht_def fun_call_def)

lemma hl_fun_block: "\<forall>s. ht P R {t. y_upd (\<lambda>_. y s) (z_upd (\<lambda>_. y t) t) \<in> Q} \<Longrightarrow> ht P (fun_call z_upd (R, (y_upd, y))) Q"
  by (auto simp: fun_call_def intro: hl_block)

lemma hl_Sup: "\<forall>x \<in> X. \<forall>z. ht (P z) (x z) (Q z) \<Longrightarrow> \<forall>z. ht (P z) (Sup X z) (Q z)"
  by (fastforce simp: ht_def seq_def)

lemma hl_rec_dep: "mono f \<Longrightarrow> (\<And>x. \<forall>z. ht (P z) (x z) (Q z) \<Longrightarrow> \<forall>z. ht (P z) (f x z) (Q z)) \<Longrightarrow> \<forall>z. ht (P z) (lfp f z) (Q z)"
  apply (erule lfp_ordinal_induct [where f=f], assumption)
  by (force intro!: hl_Sup)

lemma hl_rec_aux [hl_rules]: "mono f \<Longrightarrow> (\<And>x. \<forall>z. ht (P z) x (Q z) \<Longrightarrow> \<forall>z. ht (P z) (f x) (Q z)) \<Longrightarrow> \<forall>z. ht (P z) (lfp f) (Q z)"
  apply (erule lfp_ordinal_induct [where f=f], simp)
  by (fastforce simp: ht_def seq_def)

lemma hl_rec [hl_rules]: "mono f \<Longrightarrow> (\<And>x. \<forall>z. ht (P z) x (Q z) \<Longrightarrow> \<forall>z. ht (P z) (f x) (Q z)) \<Longrightarrow> ht (P z) (lfp f) (Q z)"
  apply (drule hl_rec_aux)
prefer 2
  apply (erule_tac x=z in allE)
  apply assumption
apply simp
done

(***********************************************************************************************)

text {* Annotated programs *}

lemma hl_awhile [hl_rules]: "P \<subseteq> i \<Longrightarrow> -b \<inter> i \<subseteq> Q \<Longrightarrow> ht (b \<sqinter> i) x i \<Longrightarrow> ht P (awhile i b x) Q"
  apply (rule hl_conseq)
  by (hoare simp: awhile_def hl: allI hl_while) force
  
lemma hl_apre_classic: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P (apre P' x) Q"
  apply (rule hl_pre, assumption)
  by (hoare simp: apre_def)

lemma hl_apre_kleymann [hl_rules]: "ht P' x Q' \<Longrightarrow> \<forall>s t. (s \<in> P' \<longrightarrow> t \<in> Q') \<longrightarrow> (s \<in> P \<longrightarrow> t \<in> Q) \<Longrightarrow> ht P (apre P x) Q"
  by (force simp add: apre_def seq_def ht_def)

lemma hl_apre_kleymann_aux [hl_rules]: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> \<forall>z. ht (P z) (apre_aux P x) (Q z)"
  by (force simp add: apre_aux_def seq_def ht_def)
                                                                 
lemma hl_apost_classic [hl_rules]: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P (apost x Q') Q"
  by (hoare simp: apost_def hl: hl_apre_kleymann) force
  
lemma hl_aprog_classic : "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P (aprog P' x Q') Q"
  apply (rule hl_classic, assumption+)
  by (hoare simp: aprog_def)

lemma hl_aprog_kleymann_aux [hl_rules]: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> \<forall>z. Q z \<le> Q'' z \<Longrightarrow> \<forall>z. ht (P z) (aprog_aux P x Q) (Q'' z)"
  apply (simp add: aprog_aux_def)
  apply (rule hl_post_aux)
  apply assumption
  by (force simp add: aprog_aux_def seq_def ht_def)

(***********************************************************************************************)

text {* When using hoare, rules should be applied in the following order *}

declare 
  hl_local_inv [hl_rules]
  hl_loc_block [hl_rules]
  hl_fun_block_inv [hl_rules]
  hl_fun_block [hl_rules]
  hl_block [hl_rules]

declare subst_def [simp]

method hoare_split uses simp hl = 
  (hoare_init simp: simp; (rule hl_split)+; (hoare_ind simp: simp hl: hl)?)

end
