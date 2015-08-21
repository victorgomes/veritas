section {* Verification condition generator *}

theory VCG
  imports While "$AFP/KAT_and_DRA/SingleSorted/KAT_Models" "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"
  Heap
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
  ((rule allI | rule ballI | subst simp | subst fst_conv | subst snd_conv)+)?

method hoare_step uses simp hl = 
  (hoare_init simp: simp, (assumption | rule subset_refl | rule hl hl_rules))

method hoare_ind uses simp hl = 
  (hoare_step simp: simp hl: hl; (hoare_ind simp: simp hl: hl)?)+

method hoare uses simp first hl = 
  (hoare_init; (rule first)?; (hoare_ind simp: simp hl: hl)?)

(***********************************************************************************************)

text {* Classic Hoare logic *}

definition ht :: "'a set \<Rightarrow> 'a option rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "ht P x Q \<equiv> \<lfloor>P\<rfloor>;x \<subseteq> x;\<lfloor>Q\<rfloor>"

lemma ht_true: "ht P x UNIV"
  oops

lemma hl_false [intro]: "ht {} x Q"
  by (auto simp: ht_def seq_def torel_def)

lemma hl_abort [hl_rules]: "ht P abort Q"
  by (auto simp: ht_def abort_def seq_def)
  
lemma hl_skip [hl_rules]: "P \<subseteq> Q \<Longrightarrow> ht P skip Q"
  by (auto simp: ht_def skip_def seq_def torel_def)
  
lemma hl_graph [hl_rules]: "P \<subseteq> {s. case f (Some s) of None \<Rightarrow> False | Some q \<Rightarrow> q \<in> Q} \<Longrightarrow> ht P (graph f) Q"
  apply (auto simp: ht_def graph_def seq_def torel_def)
apply (rule relcompI)
apply auto
by (metis (no_types, lifting) Ball_Collect case_optionE)

lemma hl_assign [hl_rules]: "P \<subseteq> subst Q z_upd t \<Longrightarrow> ht P (assign z_upd t) Q"
  by (auto simp: assign_def subst_def intro!: hl_graph)

lemma hl_seq [hl_rules]: "ht R y Q \<Longrightarrow> ht P x R \<Longrightarrow> ht P (x; y) Q"
  by (force simp: ht_def seq_def)

lemma hl_split: "ht P x {t. Q t} \<Longrightarrow> ht P x {t. Q' t} \<Longrightarrow> ht P x {t. Q t \<and> Q' t}"
  by (force simp: ht_def seq_def torel_def)

definition only_modifies :: "('s \<times> 'h) option rel \<Rightarrow> ('v, 's) var \<Rightarrow> bool" where
  "only_modifies R x \<equiv> \<forall>y s s' h h'. (<s, h>, <s', h'>) \<in> R \<longrightarrow> x \<noteq> y \<longrightarrow> val y s = val y s'"
 
lemma tt2: "(<a>, <b>) \<in> X \<Longrightarrow> b \<in> p \<Longrightarrow> (<a>, <b>) \<in> X O \<lfloor>p\<rfloor>"
  by (auto simp: torel_def)

lemma tt2_sym: "(<a>, <b>) \<in> X O \<lfloor>p\<rfloor> \<Longrightarrow> (<a>, <b>) \<in> X \<and> b \<in> p"
  by (auto simp: torel_def)

lemma tt2': "(<a>, <b>) \<in> X \<Longrightarrow> a \<in> p \<Longrightarrow> (<a>, <b>) \<in> \<lfloor>p\<rfloor> O X"
  by (auto simp: torel_def)

lemma tt3: "(a, b) \<in> \<lfloor>P\<rfloor> \<Longrightarrow> \<exists>c. a = Some c \<and> c \<in> P \<and> a = b"
by (auto simp: torel_def)


record test = x :: nat

lemma dd: "(<a, h ++ h'>, <aa, b>) \<in> assign (x_update, x) t \<Longrightarrow> h \<bottom> h' \<Longrightarrow> \<exists>h''. h'' \<bottom> h' \<and> h ++ h' = h'' ++ h' \<and> (<a, h>, <aa, h''>) \<in> assign (x_update, x) t"
  by (auto simp: assign_def graph_def)

lemma dd2: "(<a, h'' ++ h'>, <aa, b>) \<in> assign (x_update, x) t \<Longrightarrow> b = h'' ++ h'"
  by (auto simp: assign_def graph_def)

lemma dd3: "(<a, h'' ++ h'>, <aa, b>) \<in> assign (x_update, x) t \<Longrightarrow> aa = x_update (\<lambda>_. t a) a"
  by (auto simp: assign_def graph_def)

lemma "\<forall>e. R = subst R (x_update, x) e \<Longrightarrow> ht P (assign (x_update, x) t) Q \<Longrightarrow> ht (sep P R) (assign (x_update, x) t) (sep Q R)"
apply (auto simp: sep_def ht_def seq_def)
apply (drule tt3)
apply clarsimp
apply (case_tac z)
apply simp
defer
apply clarsimp
apply (rule tt2)
apply clarsimp
apply clarsimp
apply (frule dd)
apply clarsimp
apply clarsimp
apply (rule_tac x=h in exI)
apply (rule_tac x=h' in exI)
apply clarsimp
apply (rule conjI)
apply (rule dd2)
apply assumption
apply (rule conjI)
prefer 2
apply (drule dd3)
apply clarsimp
apply (clarsimp simp: subst_def)
apply (erule_tac x=t in allE)
apply force





definition mod_var :: "('s \<times> 'h) option rel \<Rightarrow> ('v, 's) var set" where
  "mod_var R \<equiv> {x. \<forall>s s' h h'. (<s, h>, <s', h'>) \<in> R \<longrightarrow> val x s \<noteq> val x s'}"


definition var_loc :: "('s \<times> 'h) option rel \<Rightarrow> ('v, 's) var  \<Rightarrow> bool" where
  "var_loc R x \<equiv> \<forall>s h s' h'. (<s, h>, <s', h'>) \<in> R \<longrightarrow> (\<exists>t. s' = set x (\<lambda>_. t s) s)"


lemma "var_loc (assign (x_update, x) t) (x_update, x)"
apply (auto simp: var_loc_def assign_def graph_def) oops

lemma tt: "\<And>y z s h0 h1.
       locality.frame op ++ op \<bottom> x \<Longrightarrow>
       locality.safe op ++ op \<bottom> x \<Longrightarrow>
       \<lfloor>P\<rfloor> O x \<subseteq> x O \<lfloor>Q\<rfloor> \<Longrightarrow>
       (y, z) \<in> x \<Longrightarrow>
       h0 \<bottom> h1 \<Longrightarrow>
       (s, h0) \<in> P \<Longrightarrow>
       (s, h1) \<in> R \<Longrightarrow>
       z = fault \<Longrightarrow>
       (<s, h0 ++ h1>, z)
       \<in> x O \<lfloor>{(s, h ++ h') |s h h'. h \<bottom> h' \<and> (s, h) \<in> Q \<and> (s, h') \<in> R}\<rfloor>"
sorry


lemma tt4 [dest]: "the fault = (s, h) \<Longrightarrow> False"
sorry

lemma "\<forall>t. R = subst R v t \<Longrightarrow> var_loc x v \<Longrightarrow> frame x \<Longrightarrow> safe x \<Longrightarrow> ht P x Q \<Longrightarrow> ht (sep P R) x (sep Q R)"
apply (auto simp: sep_def ht_def seq_def)
apply (drule tt3)
apply clarsimp
apply (case_tac y)
apply clarsimp
apply (drule tt4)
apply clarsimp
apply clarsimp
apply (rename_tac s h0 h1)
apply (case_tac z)
apply (clarsimp simp: tt)
apply (case_tac a)
apply clarsimp
apply (rename_tac s' h)
apply (rule tt2)
apply clarsimp
apply clarsimp
apply (auto simp: frame_def)
apply (erule_tac x=s in allE)
apply (erule_tac x=h0 in allE)
apply (erule_tac x=h1 in allE)
apply (erule_tac x=s' in allE)
apply (erule_tac x=h in allE)
apply clarsimp
apply (subgoal_tac "(<s, h0>, fault) \<notin> x")
apply clarsimp
apply (rule_tac x=ho' in exI)
apply (rule_tac x=h1 in exI)
apply clarsimp
apply (subgoal_tac "(<s, h0>, <s', ho'>) \<in> \<lfloor>P\<rfloor> O x")
prefer 2
apply (rule tt2')
apply clarsimp
apply clarsimp
apply (subgoal_tac "(<s, h0>, <s', ho'>) \<in> x O \<lfloor>Q\<rfloor>")
prefer 2
apply force
apply (rule conjI)
apply (drule tt2_sym)
apply force
apply (clarsimp simp: var_loc_def subst_def)
apply (erule_tac x=s in allE)
apply (erule_tac x=h0 in allE)
apply (erule_tac x=s' in allE)
apply (erule impE)
apply (rule_tac x=ho' in exI)
apply force
apply clarsimp
apply (erule_tac x=t in allE)
apply force




lemma "var_loc (assign v e) v \<Longrightarrow> R = subst R v (val v) \<Longrightarrow> ht P (assign v e) Q \<Longrightarrow> ht (sep P R) (assign v e) (sep Q R)"
  apply (auto simp: sep_def ht_def seq_def)
  apply (rule relcompI)
  apply assumption
  apply clarsimp

declare [[show_types]]
record testqwerty = x :: nat

find_consts name: testqwerty
lemma "var_loc (assign (x_update, x) e) (x_update, x)"
apply (auto simp: var_loc_def assign_def graph_def)


lemma "R = subst R v (val v) \<Longrightarrow> ht P (assign v e) Q \<Longrightarrow> ht (sep P R) (assign v e) (sep Q R)"
  apply (auto simp: sep_def ht_def seq_def torel_def)
  apply (rule relcompI)
  apply assumption
  apply clarsimp



definition to_test :: "('a, 'b) pred \<Rightarrow> ('a, 'b) state set" where
  "to_test P \<equiv> {<p> | p. p \<in> P}"

lemma hl_cond : "ht (b \<sqinter> P) x Q \<Longrightarrow> ht (-b \<sqinter> P) y Q \<Longrightarrow> ht P (cond (to_test b) x y) Q"
sorry(*
  apply (auto simp: ht_def cond_def seq_def to_torel_def torel_def)
*)

lemma hl_cond_aux [hl_rules]: "P \<subseteq> (P' \<union> - b) \<inter> (P'' \<union> b)  \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P'' y Q \<Longrightarrow> ht P (cond (to_test b) x y) Q"
sorry (*
  by (fastforce simp: ht_def cond_def seq_def)
*)

lemma hl_while: "ht (b \<sqinter> i) x i \<Longrightarrow> ht i (cwhile (to_test b) x) (-b \<sqinter> i)"
sorry
(*
proof (simp add: ht_def cwhile_def seq_def)
  assume "\<lfloor>b \<sqinter> i\<rfloor> O x \<subseteq> x O \<lfloor>i\<rfloor>"
  hence "\<lfloor>i\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* \<subseteq> (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>i\<rfloor>"
    by (force intro!: rel_kat.star_sim2)
  thus "\<lfloor>i\<rfloor> O (\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor> \<subseteq> ((\<lfloor>b\<rfloor> O x)\<^sup>* O \<lfloor>-b\<rfloor>) O \<lfloor>-b \<sqinter> i\<rfloor>"
    by auto
qed
*)

(***********************************************************************************************)

text {* Weakening / Strengthening / Consequence Rules *}

lemma hl_pre: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P x Q"
  by (fastforce simp: ht_def le_fun_def seq_def torel_def)

lemma hl_post: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P x Q"
sorry
(*
  by (fastforce simp: ht_def le_fun_def seq_def torel_def)
*)
lemma hl_classic: "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P x Q"
sorry
(*
  by (fastforce simp: ht_def le_fun_def seq_def )
*)
  
lemma hl_conseq: "\<forall>z. ht (P' z) c (Q' z) \<Longrightarrow> \<forall>s. s \<in> P \<longrightarrow> (\<exists>z. s \<in> P' z \<and> (Q' z \<subseteq> Q)) \<Longrightarrow> ht P c Q"
sorry (*
  by (force simp: ht_def seq_def )
*)
lemma hl_kleymann: "\<forall>z. ht (P' z) x (Q' z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q' z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> \<forall>z. ht (P z) x (Q z)"
 sorry
(*
 by (fastforce simp: apre_def seq_def ht_def)
*)
(*
lemma hl_for [hl_rules]: "\<forall>s. m_upd(\<lambda>_. m s) s = s \<Longrightarrow> 
  ht P (assign j_upd n) (subst Q m_upd j \<inter> {s. j s \<le> m s}) \<Longrightarrow> 
  ht ({s. j s < m s} \<inter> subst Q m_upd j) x (subst (subst Q m_upd j \<inter> {s. j s \<le> m s}) j_upd (\<lambda>s. j s + 1)) \<Longrightarrow> 
  ht P (cfor (j_upd, j) n (m_upd, m) x) Q"
  apply (hoare simp: cfor_def first: hl_post [where Q'="(-{s. j s < m s} \<inter> (subst Q m_upd j \<inter> {s. j s \<le> m s}))"] hl: hl_while)
  apply (subgoal_tac "-{s. j s < m s} \<inter> (subst Q m_upd j \<inter> {s. j s \<le> m s}) = {s. j s = m s} \<inter> subst Q m_upd j")
  apply (force simp: subst_def)
  apply force
  apply (subgoal_tac "{s. j s < m s} \<inter> (subst Q m_upd j \<inter> {s. j s \<le> m s}) = {s. j s < m s} \<inter> subst Q m_upd j")
  apply force+
done
*)
(***********************************************************************************************)

text {* Blocks / Procedures / Recursive Calls *}


lemma hl_dyn [hl_rules]: "\<forall>s \<in> P. ht P (g s) Q \<Longrightarrow> ht P (\<lceil>g\<rceil>) Q"
  by (fastforce simp: ht_def seq_def dyn_def)

(*
lemma hl_local_inv: "\<forall>s s'. z (z_upd (\<lambda>_. z s) s') = z s \<Longrightarrow> P \<le> {(s, h). z s = u} \<Longrightarrow> ht P (loc_block (z_upd, z) t x) {(s, h). z s = u}"
  by (auto simp: block_def loc_block_def graph_def dyn_def seq_def ht_def)
*)
(*
lemma hl_block: "\<forall>s. ht P x {t. f s t \<in> Q} \<Longrightarrow> ht P (block x f) Q"
  by (hoare simp: block_def) force

lemma hl_loc_block: "\<forall>s. ht P (\<langle>\<lambda>s. z_upd (\<lambda>_. t s) s\<rangle>; x) {t. z_upd s t \<in> Q} \<Longrightarrow> ht P (loc_block (z_upd, z) t x) Q"
  by (auto simp: loc_block_def intro: hl_block)

lemma hl_fun_block_inv: "\<forall>s s'. y (y_upd (\<lambda>_. y s) s') = y s \<Longrightarrow> P \<le> {s. y s = u} \<Longrightarrow> ht P (fun_call z_upd (R, (y_upd, y))) {s. y s = u }"
  by (auto simp: block_def loc_block_def graph_def dyn_def seq_def ht_def fun_call_def)

lemma hl_fun_block: "\<forall>s. ht P R {t. y_upd (\<lambda>_. y s) (z_upd (\<lambda>_. y t) t) \<in> Q} \<Longrightarrow> ht P (fun_call z_upd (R, (y_upd, y))) Q"
  by (auto simp: fun_call_def intro: hl_block)
*)
lemma hl_Sup: "\<forall>x \<in> X. \<forall>z. ht (P z) (x z) (Q z) \<Longrightarrow> \<forall>z. ht (P z) (Sup X z) (Q z)"
sorry (*
  by (fastforce simp: ht_def seq_def)
*)

lemma hl_rec [hl_rules]: "mono f \<Longrightarrow> (\<And>x. \<forall>z. ht (P z) (x z) (Q z) \<Longrightarrow> \<forall>z. ht (P z) (f x z) (Q z)) \<Longrightarrow> \<forall>z. ht (P z) (lfp f z) (Q z)"
  apply (erule lfp_ordinal_induct [where f=f], simp)
  by (force intro!: hl_Sup)

(***********************************************************************************************)

text {* Frame rule -- Separation logic *}

no_notation times (infixl "*" 70)
(*
lemma "local x \<Longrightarrow> ht p x q \<Longrightarrow> ht (p * r) x (q * r)"
  apply (auto simp: ht_def local_def sep_conj_def)
  *)

(***********************************************************************************************)

text {* Annotated programs *}

lemma hl_awhile [hl_rules]: "P \<subseteq> i \<Longrightarrow> -b \<inter> i \<subseteq> Q \<Longrightarrow> ht (b \<sqinter> i) x i \<Longrightarrow> ht P (awhile i b x) Q"
  by (hoare simp: awhile_def first: hl_conseq hl: hl_while) force
  
lemma hl_apre_classic: "P \<le> P' \<Longrightarrow> ht P' x Q \<Longrightarrow> ht P (apre P' x) Q"
  by (hoare simp: apre_def first: hl_pre)

lemma hl_apre_kleymann_aux: "\<forall>z. ht (P' z) x (Q z) \<Longrightarrow> \<forall>s t. (\<forall>z. s \<in> P' z \<longrightarrow> t \<in> Q z) \<longrightarrow> (\<forall>z. s \<in> P z \<longrightarrow> t \<in> Q z) \<Longrightarrow> \<forall>z. ht (P z) (apre (P' z) x) (Q z)"
  by (force simp add: apre_def seq_def ht_def)

lemma hl_apre_kleymann: "ht P' x Q \<Longrightarrow> \<forall>s t. (s \<in> P' \<longrightarrow> t \<in> Q) \<longrightarrow> (s \<in> P \<longrightarrow> t \<in> Q) \<Longrightarrow> ht P (apre P' x) Q"
  by (force simp add: apre_def seq_def ht_def)
                                                                               
lemma hl_apost_classic [hl_rules]: "Q' \<le> Q \<Longrightarrow> ht P x Q' \<Longrightarrow> ht P (apost x Q') Q"
  by (hoare simp: apost_def hl: hl_apre_kleymann) force
  
lemma hl_aprog_classic : "P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' x Q' \<Longrightarrow> ht P (aprog P' x Q') Q"
  by (hoare simp: aprog_def first: hl_classic)

(***********************************************************************************************)

text {* When using hoare, rules should be applied in the following order *}
(*
declare 
  hl_local_inv [hl_rules]
  hl_loc_block [hl_rules]
  hl_fun_block_inv [hl_rules]
  hl_fun_block [hl_rules]
  hl_block [hl_rules]
*)
declare subst_def [simp]
  and case_optionE [elim!]
end
