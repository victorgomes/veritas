theory Assertions
  imports "../Algebra/BBI" Heap
begin

no_notation 
  times (infixl "*" 70) and
  bot ("\<bottom>")

type_synonym 'a pred = "('a \<times> heap) set"

definition emp :: "'a pred" where
  "emp \<equiv> {(s, h). h = Map.empty}"

definition sep :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixl "*" 80) where
  "p * q \<equiv> {(s, h1 ++ h2) | s h1 h2. h1 \<bottom> h2 \<and> (s, h1) \<in> p \<and> (s, h2) \<in> q}" 

lemma sep_assoc: "p * (q * r) = (p * q) * r"
  apply (auto simp: sep_def)
  using Heap.pmult_def_eq apply blast
  using Heap.pmult_ab1 Heap.pmult_ab2 Heap.pmult_ab_assoc by blast

lemma sep_comm: "p * q = q * p"
  apply (auto simp: sep_def)
  using Heap.pmult_comm Heap.pmult_comm_def apply blast
  using Heap.pmult_comm Heap.pmult_comm_def by blast

section {* Algebraic structure *}

interpretation bbi!: bbi Inf Sup inf less_eq less sup bot top minus uminus sep emp
  apply default
  apply (simp_all add: sep_assoc)
  apply (simp add: sep_comm)
  apply (auto simp: sep_def emp_def)
done

abbreviation wand :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixl "-*" 75) where
  "p -* q \<equiv> bbi.sep_impl p q"

abbreviation (input) 
  constants :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("#_") where
  "#x \<equiv> \<lambda>_. x"

abbreviation (input) 
  pred_ex :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "EXS " 10) where
  "EXS x. P x \<equiv> {s. \<exists>x. s \<in> P x}"

abbreviation (input) 
  pred_all :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a set" (binder "ALLS " 10) where
  "ALLS x. P x \<equiv> {s. \<forall>x. s \<in> P x}"

abbreviation (input) 
  pred_eq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a pred" (infix "\<Midarrow>" 50) where
  "e \<Midarrow> e' \<equiv> {(s, h). e s = e' s}"

no_notation residual_r (infixr "\<rightarrow>" 60)
abbreviation (input) 
  pred_impl :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infix "\<rightarrow>" 60) where
  "p \<rightarrow> q \<equiv> (-p) \<squnion> q"

lemma sexI: "P x \<le> (EXS x. P x)"
  by auto

section {* Variables and Expressions *}

type_synonym ('v, 's) exp = "'s \<Rightarrow> 'v"
type_synonym 'a nat_exp = "'a \<Rightarrow> nat"

text {* The left value of a variable is an update function. *}
type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"

text {* The right value of a variable is a retrieve function. *}
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"

text {* A variable is then a pair of left and right values, satisfying some properties. *}
type_synonym ('v, 's) var = "('v, 's) lval \<times> ('v, 's) rval"

abbreviation subst :: "('s \<Rightarrow> 'v) \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's \<Rightarrow> 'v" where
  "subst e u_upd v \<equiv> \<lambda>s. e (u_upd (\<lambda>_. v s) s)"

abbreviation free :: "('v, 's) lval \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> bool" where
  "free u_upd e \<equiv> \<forall>s t. e (u_upd (\<lambda>_. t) s) = e s"

abbreviation vars1 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "vars1 u_upd u \<equiv> \<forall>s t. u (u_upd (\<lambda>_. t) s) = t"

abbreviation vars2 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "vars2 u_upd u v \<equiv> \<forall>s. u (u_upd (\<lambda>_. v s) s) = v s"

abbreviation vars3 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "vars3 u_upd v \<equiv> \<forall>s t. v (u_upd (\<lambda>_. t s) s) = v s"

abbreviation subst_pred :: "('s \<times> 'h) set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('s \<times> 'h) set" where
  "subst_pred P u t \<equiv> Collect (\<lambda>(s, h). (u (\<lambda>_. t s) s, h) \<in> P)"

abbreviation free_pred :: "('v, 's) lval \<Rightarrow> 's pred \<Rightarrow> bool" where
  "free_pred v R \<equiv> \<forall>t. R = subst_pred R v t"

section {* Predicates over the Heaplet Model*}

definition singleton :: "'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" ("_ \<mapsto> _" [50, 50] 60) where
  "e \<mapsto> e' \<equiv> {(s, h). h = [e s \<mapsto> e' s]}"

definition any_singleton :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<mapsto> -" [50] 60) where
  "e \<mapsto> - \<equiv> EXS e'. e \<mapsto> e'"

definition points_to :: "'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" ("_ \<hookrightarrow> _" [50, 50] 60) where
  "e \<hookrightarrow> e' \<equiv> (e \<mapsto> e') * \<top>"

definition any_points_to :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<hookrightarrow> -" [50] 60) where
  "e \<hookrightarrow> - \<equiv> (e \<mapsto> -) * \<top>"

definition doublet :: "'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" ("_ \<mapsto> _, _" [50, 50, 50] 60) where
  "e \<mapsto> e1, e2 \<equiv> (e \<mapsto> e1) * ((\<lambda>s. plus (e s) 1) \<mapsto> e2)"

lemma wand_eq: "{(s, h). \<forall>h'. h \<bottom> h' \<and> (s, h') \<in> P \<longrightarrow> (s, h ++ h') \<in> Q} \<le> P -* Q"
  apply (rule bbi.sep_implI1)
  apply (clarsimp simp: sep_def)
done

lemma reynolds1: "(a \<mapsto> a') \<sqinter> (b \<mapsto> b') = (a \<mapsto> a') \<sqinter> (a \<Midarrow> b) \<sqinter> (a' \<Midarrow> b')"
  apply (auto simp: singleton_def)
  apply (metis fun_upd_apply option.distinct(1))
  by (metis fun_upd_apply option.sel)

lemma reynolds2: "(a \<hookrightarrow> a') * (b \<hookrightarrow> b') \<le> -(a \<Midarrow> b)"
  by (auto simp: points_to_def singleton_def sep_def ortho_def)

lemma alls_exs_eq: "(ALLS x. - P x) = - (EXS x. P x)"
  by auto

lemma reynolds3_helper: "\<forall>s h. - Q h \<longrightarrow> P (s, h) \<Longrightarrow> - {s. P s} \<subseteq> {(s, h). Q h}"
  by auto

lemma reynolds3: "emp = (ALLS x. -(x \<hookrightarrow> -))"
  apply (subst alls_exs_eq)
  apply (rule antisym)
  apply (simp add: emp_def)
  prefer 2
  apply (subst emp_def)
  apply (rule reynolds3_helper)
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


lemma reynolds4: "(e \<mapsto> e') * ((e \<mapsto> e') -* p) \<le> (e \<hookrightarrow> e') \<sqinter> p"
  apply (subst points_to_def)
  apply (rule bbi.sep_impl_to_meet)
done

lemma reynolds5_helper: "R * {(s, h). \<forall>h'. h \<bottom> h' \<and> (s, h') \<in> P \<longrightarrow> (s, h ++ h') \<in> Q} \<le> R * (P -* Q)"
  using bbi.Sup.qisol wand_eq by blast

lemma reynolds5: "(e \<hookrightarrow> e') \<sqinter> p \<le> (e \<mapsto> e') * ((e \<mapsto> e') -* p)"
  apply (rule order_trans)
  prefer 2
  apply (rule reynolds5_helper)
  apply (auto simp: points_to_def singleton_def sep_def ortho_def)
  apply (erule_tac x=h2 in allE)
  apply auto
  by (simp add: domIff map_add_upd_left)

end