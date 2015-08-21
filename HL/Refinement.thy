theory Refinement
  imports While "../Algebra/RKAT_Models" "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"
begin

no_notation comp_op ("n_" [90] 91)
  and test_operator  ("t_" [100] 101)
  and floor ("\<lfloor>_\<rfloor>")
  and ceiling ("\<lceil>_\<rceil>")
  and Set.image (infixr "`" 90)
  and rkat_class.ref_order (infix "\<sqsubseteq>" 50)

abbreviation rel_ref_order (infix "\<sqsubseteq>" 50) where
  "rel_ref_order \<equiv> rel_rkat.ref_order"

abbreviation Spec :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel" where
  "Spec P Q \<equiv> rel_spec (\<lfloor>P\<rfloor>) (\<lfloor>Q\<rfloor>)"

lemma seq_assoc: "x; y; z = (x; y); z"
  by (auto simp: seq_def)

(***********************************************************************************************)

text {* \emph{morgan} tactic *}

named_theorems ref_rules

method morgan_step uses simp ref = 
  (assumption | rule ref ref_rules | subst seq_assoc)

method morgan uses simp ref = 
  (morgan_step simp: simp ref: ref; (morgan simp: simp ref: ref)?)+

(***********************************************************************************************)

text {* Remaining Morgan Refinement Laws *}

lemma [simp]: "rel_dioid_tests.test (\<lfloor>P\<rfloor>)"
  by (auto simp: rel_dioid_tests.test_def)

lemma assignment_ref [intro]: "P \<subseteq> subst Q v m \<Longrightarrow> Spec P Q \<sqsubseteq> assign v m"
  apply (clarsimp simp: subst_def assign_def rel_rkat.ref_order_def graph_def rel_spec_def)
  apply (rule_tac x="{(s, v (\<lambda>_. m s) s)}" in exI, auto)
done

lemma following_assignment_ref: "Q' \<subseteq> subst Q v m \<Longrightarrow> Spec P Q \<sqsubseteq> Spec P Q'; assign v m"
proof -
  assume assms: "Q' \<subseteq> subst Q v m"
  have "Spec P Q \<sqsubseteq> Spec P Q'; Spec Q' Q"
    by (auto simp: seq_def)
  also have "... \<sqsubseteq> Spec P Q'; assign v m"
    using assms by (auto simp: seq_def)
  finally show ?thesis .
qed

lemma leading_assignment_ref: "P \<subseteq> subst P' v m \<Longrightarrow> Spec P Q \<sqsubseteq> assign v m; Spec P' Q"
proof -
  assume assms: "P \<subseteq> subst P' v m"
  have "Spec P Q \<sqsubseteq> Spec P P'; Spec P' Q"
    by (auto simp: seq_def)
  also have "... \<sqsubseteq> assign v m; Spec P' Q"
    using assms by (auto simp: seq_def)
  finally show ?thesis .
qed

(* Annotated while Specification *)

lemma while_ref_tactic: "\<lbrakk>I \<inter> B \<subseteq> P'; P \<subseteq> I; I - B \<subseteq> Q\<rbrakk> \<Longrightarrow> Spec P Q \<sqsubseteq> cwhile B (Spec P' I)"
proof -
  have a: "\<lfloor>I - B\<rfloor> = \<lfloor>I\<rfloor> O \<lfloor>-B\<rfloor>" by force
  have b: "\<lfloor>I \<inter> B\<rfloor> = \<lfloor>I\<rfloor> O \<lfloor>B\<rfloor>" by force
  assume assms: "I \<inter> B \<subseteq> P'" "P \<subseteq> I" "I - B \<subseteq> Q"
  hence "Spec P Q \<sqsubseteq> rel_spec (\<lfloor>I\<rfloor>) (\<lfloor>I - B\<rfloor>)"
    by auto
  also have "... \<sqsubseteq> (\<lfloor>B\<rfloor> O Spec (I \<inter> B) I)\<^sup>* O \<lfloor>- B\<rfloor>"
    by (auto simp: a b intro: rel_rkat.while_ref)
  also have "... \<sqsubseteq> (\<lfloor>B\<rfloor> O Spec P' I)\<^sup>* O \<lfloor>- B\<rfloor>"
    using assms by force
  finally show ?thesis
    by (simp add: cwhile_def seq_def)
qed
                                       
lemma while_iso: "c \<sqsubseteq> c' \<Longrightarrow> cwhile b c \<sqsubseteq> cwhile b c'"
  by (auto simp: cwhile_def seq_def)

lemma spec_mult_isol: "x \<sqsubseteq> y \<Longrightarrow> z; x \<sqsubseteq> z; y"
  by (simp add: seq_def rel_rkat.spec_mult_isol)

lemma spec_mult_isor: "x \<sqsubseteq> y \<Longrightarrow> x; z \<sqsubseteq> y; z"
  by (simp add: seq_def rel_rkat.spec_mult_isor)

lemma ref_skipI: "p \<le> q \<Longrightarrow> Spec p q \<sqsubseteq> skip"
  by (auto simp: skip_def)

lemma ref_skipE: "x \<sqsubseteq> skip \<Longrightarrow> x;y \<sqsubseteq> y"
  by (auto simp: skip_def seq_def rel_rkat.ref_order_def)

(***********************************************************************************************)

text {* When using morgan, rules should be applied in the following order *}

declare
  spec_mult_isol [ref_rules]
  spec_mult_isor [ref_rules]
  while_iso [ref_rules]
  leading_assignment_ref [ref_rules]
  following_assignment_ref [ref_rules]
  assignment_ref [ref_rules]
  rel_rkat.skip_ref_var2 [ref_rules]
  rel_rkat.sequence_ref [ref_rules]
  rel_rkat.weaken_pre [ref_rules]
  rel_rkat.strengthen_post [ref_rules]
  rel_rkat.weaken_and_strengthen [ref_rules]
  rel_rkat.while_ref [ref_rules]
  while_ref_tactic [ref_rules]
  ref_skipI [ref_rules]
  ref_skipE [ref_rules]

declare subst_def [simp]

end
