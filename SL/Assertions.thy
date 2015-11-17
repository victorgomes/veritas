theory Assertions
  imports "../Algebra/BBI" Heap "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"
begin

no_notation 
  times (infixl "*" 70) and
  sup (infixl "+" 65) and
  bot ("\<bottom>")

notation plus (infixl "+" 65)

type_synonym 'a pred = "('a \<times> heap) set"

(*****************************************************************************************)
section {* Separation Conjunction *}
(*****************************************************************************************)

definition emp :: "'a pred" where
  "emp \<equiv> {(s, h). h = Map.empty}"

definition sep :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixl "*" 80) where
  "p * q \<equiv> {(s, h1 ++ h2) | s h1 h2. h1 \<bottom> h2 \<and> (s, h1) \<in> p \<and> (s, h2) \<in> q}" 

lemma sep_assoc: "(p * q) * r = p * (q * r)"
  apply (auto simp: sep_def)
  using Heap.pmult_ab1 Heap.pmult_ab2 Heap.pmult_ab_assoc apply blast
  using Heap.pmult_def_eq by blast

lemma sep_comm: "p * q = q * p"
  apply (auto simp: sep_def)
  using Heap.pmult_comm Heap.pmult_comm_def apply blast
  using Heap.pmult_comm Heap.pmult_comm_def by blast

(*****************************************************************************************)
section {* Algebraic structure *}
(*****************************************************************************************)

interpretation bbi!: bbi Inf Sup inf less_eq less sup bot top minus uminus sep emp
  apply default
  apply (simp_all add: sep_assoc)
  apply (simp add: sep_comm)
  apply (auto simp: sep_def emp_def)
done

abbreviation wand :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixl "-*" 75) where
  "p -* q \<equiv> bbi.sep_impl p q"

abbreviation (input) 
  constants :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("$_") where
  "$x \<equiv> \<lambda>_. x"

abbreviation
  pred_ex :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "EXS " 10) where
  "EXS x. P x \<equiv> {s. \<exists>x. s \<in> P x}"

abbreviation (input) 
  pred_all :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "ALLS " 10) where
  "ALLS x. P x \<equiv> {s. \<forall>x. s \<in> P x}"

abbreviation (input) 
  pred_eq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<Midarrow>" 50) where
  "e \<Midarrow> e' \<equiv> {(s, h). e s = e' s}"

abbreviation true :: "'a pred" where
  "true \<equiv> \<top>"

abbreviation false :: "'a pred" where
  "false \<equiv> {}"

lemma pred_le_exI: "P x \<subseteq> (EXS x. P x)"
  by auto

lemma pred_le_exE: "(\<And>x. P x \<subseteq> Q) \<Longrightarrow> (EXS x. P x) \<subseteq> Q"
  by auto

lemma exs_sepl: "(EXS x. P x) * Q = (EXS x. P x * Q)"
  by (auto simp: sep_def)

lemma exs_sepr: "P * (EXS x. Q x) = (EXS x. P * Q x)"
  by (auto simp: sep_def)

lemma mono_exs: "(\<And>x. P x \<subseteq> Q x) \<Longrightarrow> (EXS x. P x) \<subseteq> (EXS y. Q y)"
  by auto

(*****************************************************************************************)
section {* Assertions only about store *}
(*****************************************************************************************)

definition store_pred :: "'a set \<Rightarrow> 'a pred" ("<_>") where
  "<P> \<equiv> {(s, h). s \<in> P} \<sqinter> emp"

lemma sp_sep: "<p> * <q> = <p \<sqinter> q>"
  by (auto simp: store_pred_def emp_def sep_def)

lemma sp_sep_inf: "<p> * (<q> * r) = <p \<sqinter> q> * r"
  by (auto simp: store_pred_def emp_def sep_def)

lemma sp_sep_comm: "p * <q>  = <q> * p"
  by (simp add: sep_comm)

lemma sp_sep_comm_var: "q * (<p> * r) = <p> * (q * r)"
  by (auto simp: store_pred_def emp_def sep_def)

lemma sp_emp [simp]: "<UNIV> = emp"
  by (auto simp: store_pred_def)

(*****************************************************************************************)
section {* Variables and Expressions *}
(*****************************************************************************************)

type_synonym ('v, 's) exp = "'s \<Rightarrow> 'v"
type_synonym 'a nat_exp = "'a \<Rightarrow> nat"

text {* The left value of a variable is an update function. *}
type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"

text {* The right value of a variable is a retrieve function. *}
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"

text {* A variable is then a pair of left and right values, satisfying some properties. *}
type_synonym ('v, 's) var = "('v, 's) lval \<times> ('v, 's) rval"

abbreviation (input) subst :: "('s \<Rightarrow> 'v) \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's \<Rightarrow> 'v" where
  "subst e u_upd v \<equiv> \<lambda>s. e (u_upd (\<lambda>_. v s) s)"

abbreviation free :: "('v, 's) lval \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> bool" where
  "free u_upd e \<equiv> \<forall>s t. e (u_upd (\<lambda>_. t) s) = e s"

abbreviation vars1 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "vars1 u_upd u \<equiv> \<forall>s t. u (u_upd (\<lambda>_. t) s) = t"

abbreviation vars2 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "vars2 u_upd u v \<equiv> \<forall>s. u (u_upd (\<lambda>_. v s) s) = v s"

abbreviation vars3 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "vars3 u_upd v \<equiv> \<forall>s t. v (u_upd (\<lambda>_. t s) s) = v s"

definition subst_pred :: "('s \<times> 'h) set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('s \<times> 'h) set" where
  "subst_pred P u t \<equiv> Collect (\<lambda>(s, h). (u (\<lambda>_. t s) s, h) \<in> P)"

abbreviation subst_pred_s :: "'s set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's set" where
  "subst_pred_s P u t \<equiv> Collect (\<lambda>s. (u (\<lambda>_. t s) s) \<in> P)"

abbreviation (input) free_pred :: "('v, 's) lval \<Rightarrow> 's pred \<Rightarrow> bool" where
  "free_pred v R \<equiv> \<forall>t. R = subst_pred R v t"

(*****************************************************************************************)
section {* Substitution Lemmas *}
(*****************************************************************************************)

named_theorems spred

lemma subst_true [spred]: "subst_pred true j_update i = true"
  by (auto simp: subst_pred_def)

lemma subst_inf [spred]: "subst_pred (P \<sqinter> Q) i_update j = (subst_pred P i_update j) \<sqinter> (subst_pred Q i_update j)"
  by (auto simp: subst_pred_def)

lemma subst_sep [spred]: "subst_pred (P * Q) i_update j = (subst_pred P i_update j) * (subst_pred Q i_update j)"
  by (auto simp: subst_pred_def sep_def)

lemma subst_wand [spred]: "subst_pred (P -* Q) i_update j = (subst_pred P i_update j) -* (subst_pred Q i_update j)"
  oops

lemma subst_exs [spred]: "subst_pred (EXS k. (P k)) i_update j = (EXS k. (subst_pred (P k) i_update j))"
  by (auto simp: subst_pred_def)

(*****************************************************************************************)
section {* Predicates over the Heaplet Model*}
(*****************************************************************************************)

definition singleton :: "'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" ("_ \<mapsto> _" [50, 50] 60) where
  "e \<mapsto> e' \<equiv> {(s, h). h = [e s \<mapsto> e' s]}"

definition any_singleton :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<mapsto> -" [50] 60) where
  "e \<mapsto> - \<equiv> EXS e'. e \<mapsto> $e'"

definition points_to :: "'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" ("_ \<hookrightarrow> _" [50, 50] 60) where
  "e \<hookrightarrow> e' \<equiv> (e \<mapsto> e') * \<top>"

definition any_points_to :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<hookrightarrow> -" [50] 60) where
  "e \<hookrightarrow> - \<equiv> (e \<mapsto> -) * \<top>"

definition doublet :: "'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" ("_ \<mapsto> _, _" [50, 50, 50] 60) where
  "e \<mapsto> e1, e2 \<equiv> (e \<mapsto> e1) * ((\<lambda>s. plus (e s) 1) \<mapsto> e2)"

lemma subst_singleton [spred]: "subst_pred (x \<mapsto> y) i_update j = (subst x i_update j \<mapsto> subst y i_update j)"
  by (auto simp: subst_pred_def singleton_def)

lemma subst_any_singleton [spred]: "subst_pred (x \<mapsto> -) i_update j = (subst x i_update j \<mapsto> -)"
  by (auto simp: subst_pred_def any_singleton_def singleton_def)

lemma subst_doublet [spred]: "subst_pred (x \<mapsto> y, z) i_update j = (subst x i_update j \<mapsto> subst y i_update j, subst z i_update j)"
  by (simp add: doublet_def spred)

lemma subst_no_state [spred]: "subst_pred {(s, h). P} i_update j = {(s, h). P}"
  by (simp add: subst_pred_def)

lemma [spred]: "subst_pred <P> i_update j = <subst_pred_s P i_update j>"
  by (auto simp: subst_pred_def store_pred_def emp_def)

(*****************************************************************************************)
section {* Arbitrary Lemmas *}
(*****************************************************************************************)

lemma wand_ineq: "{(s, h). \<forall>h'. h \<bottom> h' \<and> (s, h') \<in> P \<longrightarrow> (s, h ++ h') \<in> Q} \<le> P -* Q"
  apply (rule bbi.sep_implI1)
  apply (clarsimp simp: sep_def)
done

lemma reynolds1: "(a \<mapsto> a') \<sqinter> (b \<mapsto> b') = (a \<mapsto> a') \<sqinter> (a \<Midarrow> b) \<sqinter> (a' \<Midarrow> b')"
  apply (auto simp: singleton_def)
  apply (metis fun_upd_apply option.distinct(1))
  by (metis fun_upd_apply option.sel)

lemma reynolds2: "(a \<hookrightarrow> a') * (b \<hookrightarrow> b') \<le> -(a \<Midarrow> b)"
  by (auto simp: points_to_def singleton_def sep_def ortho_def)

lemma reynolds3: "(ALLS x. - P x) = - (EXS x. P x)"
  by auto

lemma reynolds4_helper: "\<forall>s h. - Q h \<longrightarrow> P (s, h) \<Longrightarrow> - {s. P s} \<subseteq> {(s, h). Q h}"
  by auto

lemma reynolds4: "emp = (ALLS x. -(x \<hookrightarrow> -))"
  apply (subst reynolds3)
  apply (rule antisym)
  apply (simp add: emp_def)
  prefer 2
  apply (subst emp_def)
  apply (rule reynolds4_helper)
  apply (auto simp: any_points_to_def any_singleton_def singleton_def sep_def ortho_def)
  apply (subgoal_tac "\<exists>n. n \<in> dom h")
  prefer 2
  apply force
  apply auto
  apply (rule_tac x="\<lambda>x. n" in exI)
  apply (rule_tac x="[n \<mapsto> y]" in exI)
  apply (rule_tac x="h(n := None)" in exI)
  apply (auto intro: heap_split)
  by (metis fun_upd_same map_add_None)

lemma reynolds5: "(e \<mapsto> e') * ((e \<mapsto> e') -* p) \<le> (e \<hookrightarrow> e') \<sqinter> p"
  apply (subst points_to_def)
  apply (rule bbi.sep_impl_to_meet)
done

lemma reynolds6_helper: "R * {(s, h). \<forall>h'. h \<bottom> h' \<and> (s, h') \<in> P \<longrightarrow> (s, h ++ h') \<in> Q} \<le> R * (P -* Q)"
  using bbi.Sup.qisol wand_ineq by blast

lemma reynolds6: "(e \<hookrightarrow> e') \<sqinter> p \<le> (e \<mapsto> e') * ((e \<mapsto> e') -* p)"
  apply (rule order_trans)
  prefer 2
  apply (rule reynolds6_helper)
  apply (auto simp: points_to_def singleton_def sep_def ortho_def)
  apply (erule_tac x=h2 in allE)
  apply auto
  by (simp add: domIff map_add_upd_left)

lemma reynolds6_var: "P \<le> (e \<mapsto> e') * true \<Longrightarrow> P \<le> Q \<Longrightarrow> P \<le> (e \<mapsto> e') * ((e \<mapsto> e') -* Q)"
  apply (rule order_trans[rotated])
  apply (rule reynolds6)
  apply (auto simp: points_to_def)
done

(*****************************************************************************************)
section {* Tactics *}
(*****************************************************************************************)

(* sep_simp lemmas *)

named_theorems sep_simp

lemmas [sep_simp] =
  bbi.mult_1_left
  bbi.mult_1_right 
  bbi.mult_1_left
  bbi.sep_conj_top
  doublet_def
  points_to_def
  any_singleton_def
  any_points_to_def
  Set.Diff_eq
  sep_assoc
  exs_sepl
  exs_sepr
  sp_sep
  sp_sep_inf
  sp_sep_comm
  sp_sep_comm_var
  sp_emp

lemma [sep_simp]: "true * p = p * true"
  by (simp add: sep_comm)

lemma [sep_simp, simp]: "<{}> = bot"
  by (auto simp: store_pred_def) 

lemma [sep_simp, simp]: "s \<in> (if P then UNIV else {}) = P"
  by auto

(* some intro and elim lemmas *)

lemma infI: "(s, h) \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> P \<sqinter> Q"
  by auto

lemma infE: "(s, h) \<in> P \<sqinter> Q \<Longrightarrow> ((s, h) \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> G) \<Longrightarrow> G"
  by auto

lemma pred_exI: "(s, h) \<in> P x \<Longrightarrow> (s, h) \<in> (EXS x. P x)"
  by auto

lemma pred_exE: "(s, h) \<in> (EXS x. P x) \<Longrightarrow> (\<And>x. (s, h) \<in> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by auto

lemma spE: "(s, h) \<in> <P> * Q \<Longrightarrow> (s \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp: store_pred_def emp_def sep_def)

lemma spI: "s \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> <P> * Q"
  by (auto simp: store_pred_def emp_def sep_def)

(* Heap reduction lemmas *)

lemma heap_reductl: "(s, h) \<in> p \<Longrightarrow> (q = emp) \<Longrightarrow> (s, h) \<in> p * q"
  by (auto simp: sep_def emp_def)

lemma heap_reductr: "(s, h) \<in> q \<Longrightarrow> (p = emp) \<Longrightarrow> (s, h) \<in> p * q"
  by (auto simp: sep_def emp_def)

lemma heap_reduct2: "(s, h) \<in> p * q \<Longrightarrow> (\<And>h'. dom h' \<subseteq> dom h \<Longrightarrow> (s, h') \<in> q \<Longrightarrow> (s, h') \<in> q') \<Longrightarrow> (s, h) \<in> p * q'"
  apply (auto simp: sep_def)
  apply (rule_tac x=h1 in exI)
  apply (rule_tac x=h2 in exI)
  apply auto
done 

lemma pure_allE: "(\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> P y \<Longrightarrow> Q y"
  by auto

lemma heap_reduct3: "(s, h) \<in> p * q \<Longrightarrow> (\<And>h. (s, h) \<in> q \<Longrightarrow> (s, h) \<in> p' * q') \<Longrightarrow> (s, h) \<in> p' * (p * q')"
  apply (auto simp: sep_def ortho_def)
  apply (drule pure_allE, auto)
  apply (rule_tac x=h1a in exI)
  apply (rule_tac x="h1 ++ h2a" in exI)
  apply auto
  apply (metis Heap.pmult_def_eq dom_map_add heap_add_comm ortho_def)
  apply (rule_tac x=h1 in exI)
  apply (rule_tac x="h2a" in exI)
  apply force
done

lemma heap_reduct4: "(s, h) \<in> p * r \<Longrightarrow> (\<And>h. (s, h) \<in> p \<Longrightarrow> (s, h) \<in> q1 * (q2 * q3)) \<Longrightarrow> (s, h) \<in> q1 * (q2 * (q3 * r))"
  apply (auto simp: sep_def ortho_def)
  apply (drule pure_allE, auto)
  apply (rule_tac x=h1a in exI)
  apply (rule_tac x="h1b ++ h2b ++ h2" in exI)
  apply auto
  apply (rule_tac x=h1b in exI)
  apply (rule_tac x="h2b ++ h2" in exI)
  apply auto
  apply (rule_tac x=h2b in exI)
  apply (rule_tac x=h2 in exI)
  apply auto
done

(* Some intro and elim rules *)

named_theorems sep_intro
named_theorems sep_elim

lemma singlE [sep_elim]: "(s, h) \<in> (i \<mapsto> e) * p \<Longrightarrow> e s = e' s \<Longrightarrow> (\<And>h'. (s, h') \<in> p \<Longrightarrow> (s, h') \<in> q) \<Longrightarrow> (s, h) \<in> (i \<mapsto> e') * q"
  by (auto simp: sep_def ortho_def singleton_def)

lemma singlE_var [sep_elim]: "(s, h) \<in> (i \<mapsto> e) * p \<Longrightarrow> e s = e' s \<Longrightarrow> (\<And>h'. (s, h') \<in> p \<Longrightarrow> (s, h') \<in> q * r) \<Longrightarrow> (s, h) \<in> q * ((i \<mapsto> e') * r)"
  apply (auto simp: sep_def ortho_def singleton_def)
  apply (drule pure_allE, auto)
  apply (erule_tac x=h1 in allE)
  apply auto
  apply (erule_tac x="[i s \<mapsto> e' s] ++ h2a" in allE)
  apply auto
  apply (erule contrapos_pp) back back back back back back
  apply simp
by (simp add: domIff map_add_upd_left)

(* Tactics*)

method sep_simp =
  (subst sep_simp | subst (asm) sep_simp | subst spred | subst (asm) spred | rule pred_le_exE)+

named_theorems sep_safe_intro
named_theorems sep_safe_elim

method sep_same = (
    ((erule heap_reductl | erule heap_reductr| erule heap_reduct2 | erule heap_reduct3 | erule heap_reduct4)+)?
)

method sep_safe_split =
  (
    ((rule Set.IntI)+)?;
      (
        ((erule Set.IntE)+)?,
        ((erule pred_exE)+)?,
        ((erule spE)+)?,
    
        sep_same?,
        (sep_simp, sep_safe_split)?,
        (assumption | rule HOL.refl)?
      )
  )

method sep_split =
  (
    sep_safe_split;
    ((rule pred_exI)+)?,
    ((rule spI)+)?;
    simp?;
    (
      (sep_same | sep_simp, sep_split)?,
      (assumption | rule HOL.refl)?
    )
  )

method sep_safe = (
    sep_simp?,
    (rule subrelI)?,
    sep_safe_split?;

    (((erule sep_safe_elim)+, force); sep_safe_split?)?;
    sep_same?;
    (assumption | rule HOL.refl)?
)


method sep_auto uses elim intro = 
  (
    sep_simp?,
    (rule subrelI)?,

    sep_split?;
    ((erule sep_elim | rule sep_intro)+; simp?, sep_split?)?;
    sep_same?;
    (assumption | rule HOL.refl)?;
    auto?
  )

end