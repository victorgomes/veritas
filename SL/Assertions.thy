theory Assertions
  imports "../Algebra/BBI" Heap "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach"
begin

no_notation 
  times (infixl "*" 70) and
  bot ("\<bottom>")

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
  constants :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("#_") where
  "#x \<equiv> \<lambda>_. x"

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

definition pure_pred :: "'a set \<Rightarrow> 'a pred" ("<_>") where
  "<P> \<equiv> {(s, h). s \<in> P} \<sqinter> emp"

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
  "e \<mapsto> - \<equiv> EXS e'. e \<mapsto> #e'"

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

(*****************************************************************************************)
section {* Arbitrary Lemmas *}
(*****************************************************************************************)

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

lemma reynolds5': "P \<le> (e \<mapsto> e') * true \<Longrightarrow> P \<le> Q \<Longrightarrow> P \<le> (e \<mapsto> e') * ((e \<mapsto> e') -* Q)"
  apply (rule order_trans[rotated])
  apply (rule reynolds5)
  apply (auto simp: points_to_def)
done
  


(*****************************************************************************************)
section {* Lists *}
(*****************************************************************************************)

abbreviation (input) is_nil :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<Midarrow> nil") where
  "i \<Midarrow> nil \<equiv> {(s, h). i s \<notin> dom h}"

primrec list_seg :: "nat list \<Rightarrow> 'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" where
  "list_seg [] i j = emp \<sqinter> (i \<Midarrow> j)"
| "list_seg (x#xs) i k = (EXS j. (i \<mapsto> #x, #j) * list_seg xs #j k)"

lemma list_seg_empty: "list_seg [] i j = <{s. i s = j s}>"
  by (auto simp: pure_pred_def)

lemma singleton_list [simp]: "(list_seg [x] i j) = (i \<mapsto> #x, j)"
  by (auto simp: sep_def doublet_def singleton_def emp_def)

lemma list_seg_exs: "(EXS j. (emp \<sqinter> (i \<Midarrow> j)) * list_seg ys j k) = list_seg ys i k"
  apply (auto simp: sep_def doublet_def singleton_def emp_def)
  apply (induct ys)
  apply (auto simp: doublet_def singleton_def sep_def)
done

lemma list_seg_merge: "(list_seg (xs@ys) i k) = (EXS j. (list_seg xs i j) * (list_seg ys j k))"
  apply (induct xs arbitrary: i)
  apply (simp add: list_seg_exs)
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
  oops

lemma list_seg_rev: "(list_seg (xs@[x]) i k) = (EXS j. (list_seg xs i j) * (j \<mapsto> #x, k))"
  oops

lemma "list_seg xs i j \<le> -(i \<Midarrow> nil) \<squnion> ((#xs \<Midarrow> #[]) \<sqinter> (i \<Midarrow> nil))"
  apply (induct xs)
  apply clarsimp
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
done

lemma "list_seg xs i j \<le> (i \<Midarrow> j) \<squnion> - (#xs \<Midarrow> #[])"
  apply (induct xs)
  apply clarsimp
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
done

lemma subst_list_seg [spred]: "subst_pred (list_seg xs m n) i_update j = list_seg xs (subst m i_update j) (subst n i_update j)"
  apply (induct xs arbitrary: m n)
  apply (force simp: subst_pred_def emp_def)
  apply (auto simp: spred)
done

no_notation sup (infixl "+" 65)

lemma exs1: "(EXS j. (i \<mapsto> a, #j) * P j) = (i \<mapsto> a) * (EXS j. ((\<lambda>s. i s + 1) \<mapsto> #j) * P j)"
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
  apply (erule_tac x="[Suc (i s) \<mapsto> x] ++ h2" in allE)
  apply auto
done
(*
lemma "list_seg [] i j = <{s. i s = j s}>"
  by (auto simp: state_pred_def emp_def)
*)

definition llist :: "nat list \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" where
  "llist xs i \<equiv> list_seg xs i #0 \<sqinter> {(s, h). 0 \<notin> dom h}"

lemma llist_empty_var: "llist [] i = (i \<Midarrow> #0) \<sqinter> emp"
  by (auto simp add: llist_def emp_def)

lemma llist_empty: "llist [] i = <{s. i s = 0}>"
  by (auto simp add: llist_def pure_pred_def emp_def)

lemma llist_empty_zero [simp]: "llist [] (\<lambda>s. 0) = emp"
  by (auto simp add: llist_def emp_def)

lemma llist_simp2: "llist (Cons x xs) i = <{s. i s \<noteq> 0}> * (EXS k. (i \<mapsto> #x, #k) * llist xs #k)"
  apply (auto simp: llist_def sep_def doublet_def singleton_def pure_pred_def emp_def)
  apply auto
  using neq0_conv apply fastforce
done

lemma llist_simp3: "llist (Cons x xs) i = -(i \<Midarrow> #0) \<sqinter> (EXS k. (i \<mapsto> #x, #k) * llist xs #k)"
  apply (auto simp: llist_def sep_def doublet_def singleton_def)
  apply (rule_tac x=xa in exI)
  apply auto
done

lemma subst_llist [spred]: "subst_pred (llist xs m) i_update j = llist xs (subst m i_update j)"
  apply (simp add: llist_def spred)
  apply (simp add: subst_pred_def)

done


(*****************************************************************************************)
section {* Tactics *}
(*****************************************************************************************)


named_theorems sep_simp

lemmas [sep_simp] =
  bbi.mult_1_left
  bbi.mult_1_right 
  bbi.mult_1_left
  bbi.sep_conj_top
  list_seg_empty
  list_seg.simps(2)
  doublet_def
llist_empty
llist_empty_zero
  llist_simp2
  points_to_def
  any_singleton_def
  any_points_to_def

lemma [sep_simp]: "true * p = p * true"
  by (simp add: sep_comm)

lemma [sep_simp]: "<p> * <q> = <p \<sqinter> q>"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma [sep_simp]: "<p> * (<q> * r) = <p \<sqinter> q> * r"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma [sep_simp]: "p * <q>  = <q> * p"
  by (simp add: sep_comm)

lemma [sep_simp]: "q * (<p> * r) = <p> * (q * r)"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma [sep_simp]: "x * y * z = x * (y * z)"
  by (simp add: sep_assoc)

lemma [sep_simp]: "(EXS x. P x) * Q = (EXS x. P x * Q)"
  by (auto simp: sep_def)

lemma exs [sep_simp]: "P * (EXS x. Q x) = (EXS x. P * Q x)"
  by (auto simp: sep_def)

named_theorems cancel_same

lemma [cancel_same]: "p \<subseteq> q \<Longrightarrow> e = e' \<Longrightarrow> (i \<mapsto> e) * p \<subseteq> (i \<mapsto> e') * q"
  by (simp add: bbi.Sup.qisol)

lemma [cancel_same]: "p \<subseteq> q \<Longrightarrow> e = e' \<Longrightarrow> p * (i \<mapsto> e) \<subseteq> q * (i \<mapsto> e')"
  by (simp add: bbi.Sup.qisor)

lemma [cancel_same]: "p \<subseteq> q \<Longrightarrow> xs = ys \<Longrightarrow> (list_seg xs i j) * p \<subseteq> list_seg ys i j * q"
  by (simp add: bbi.Sup.qisol)

lemma [cancel_same]: "p \<subseteq> q \<Longrightarrow> xs = ys \<Longrightarrow> p * (list_seg xs i j) \<subseteq> q * list_seg ys i j"
  by (simp add: bbi.Sup.qisor)


lemma [sep_simp, simp]: "<UNIV> = emp"
  by (auto simp: pure_pred_def)

named_theorems sep_same

declare Set.UNIV_I [sep_same]

lemma [sep_same]: "emp \<le> r \<Longrightarrow> p \<le> p * r"
  apply (auto simp: sep_def emp_def)
  apply (rule_tac x=b in exI)
  apply (rule_tac x=Map.empty in exI)
  apply auto
done
  
lemma [sep_same]: "p \<subseteq> list_seg [] i i * p"
  by (auto simp: sep_def emp_def)

lemma [sep_same]: "p \<le> list_seg cs j k * q \<Longrightarrow> as@cs=bs \<Longrightarrow> list_seg as i j * p \<subseteq> list_seg bs i k * q"
  oops  

lemma [sep_same]: "p \<le> list_seg cs j k \<Longrightarrow> as@cs=bs \<Longrightarrow> list_seg as i j * p \<subseteq> list_seg bs i k"
oops

lemma aa: "(s, h) \<in> llist as i * p \<Longrightarrow> as@cs=bs \<Longrightarrow> ((s, h) \<in> p \<Longrightarrow> (s, h) \<in> llist cs j) \<Longrightarrow> (s, h) \<in> llist bs i"
oops

lemma split_conc: "P \<subseteq> Q \<Longrightarrow> P \<subseteq> <R> * true \<Longrightarrow> P \<subseteq> <R> * Q"
  by (auto simp: sep_def pure_pred_def emp_def)

lemma mono_exs: "(\<And>x s h. (s, h) \<in> P x \<Longrightarrow> (s, h) \<in> Q x) \<Longrightarrow> (EXS x. P x) \<subseteq> (EXS y. Q y)"
  by auto

lemma mono_exs2: "(\<And>x. P x \<subseteq> Q x) \<Longrightarrow> (EXS x. P x) \<subseteq> (EXS y. Q y)"
  by auto

lemma pred_conjI: "(s, h) \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> P \<sqinter> Q"
  by auto

lemma pred_conjE: "(s, h) \<in> P \<sqinter> Q \<Longrightarrow> ((s, h) \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

schematic_lemma pred_exI: "P \<subseteq> Q ?x \<Longrightarrow> P \<subseteq> (EXS x. Q x)"
  by auto

lemma pred_exI2: "P x \<subseteq> (EXS x. P x)"
  by auto

lemma pred_exI': "(s, h) \<in> P x \<Longrightarrow> (s, h) \<in> (EXS x. P x)"
  by auto

lemma pred_exE: "(\<And>x. P x \<subseteq> Q) \<Longrightarrow> (EXS x. P x) \<subseteq> Q"
  by auto

lemma pred_exE': "(s, h) \<in> (EXS x. P x) \<Longrightarrow> (\<And>x. (s, h) \<in> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by auto


lemma split_pure_sep: "(\<And>s h. s \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> R) \<Longrightarrow> <P> * Q \<subseteq> R"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma split_pure_conj: "(\<And>s h. P s \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> R) \<Longrightarrow> Q \<sqinter> {(s, h). P s} \<subseteq> R"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma split_pure_neg: "(\<And>s h. \<not> P s \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> R) \<Longrightarrow> Q - {(s, h). P s} \<subseteq> R"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma split_pure_sepE: "(s, h) \<in> <P> * Q \<Longrightarrow> (s \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma split_pure_sep_nostateE: "(s, h) \<in> <{s. P}> * Q \<Longrightarrow> (P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> R) \<Longrightarrow> (s, h) \<in> R"
  apply (auto simp: pure_pred_def emp_def sep_def)
apply force
done

lemma zero: "(s, h) \<in> llist x i * R \<Longrightarrow> i s = 0 \<Longrightarrow> (x = [] \<Longrightarrow> (s, h) \<in> R \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (induct x)
  apply (simp add: llist_empty)
  apply (erule split_pure_sepE)
  apply simp
  apply (simp add: llist_simp2)
by (metis (no_types, lifting) CollectD bbi.mult_assoc less_numeral_extra(3) split_pure_sepE)

lemma not_zero: "(s, h) \<in> llist x i * R \<Longrightarrow> i s \<noteq> 0 \<Longrightarrow> (x \<noteq> [] \<Longrightarrow> (s, h) \<in> llist (Cons (hd x) (tl x)) i * R \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (induct x)
  apply (simp add: llist_empty)
  apply (erule split_pure_sepE)
  apply simp
  apply (simp add: llist_simp2)
done

lemma split_pureE: "(s, h) \<in> <Q> * P \<Longrightarrow> (s \<in> Q \<Longrightarrow> (s, h) \<in> P \<Longrightarrow> (s, h) \<in> R) \<Longrightarrow> (s, h) \<in> R"
  by (auto simp: pure_pred_def sep_def emp_def)

lemma split_pure_sep2: "(\<And>s h. s \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> R) \<Longrightarrow> <P> * Q \<subseteq> R"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma split_pure_sep': "s \<in> P \<Longrightarrow> (s, h) \<in> Q \<Longrightarrow> (s, h) \<in> <P> * Q"
  by (auto simp: pure_pred_def emp_def sep_def)

lemma tt: "(s, h) \<in> (i \<mapsto> e) * P \<Longrightarrow> (s, h) \<in> (i \<hookrightarrow> e)"
  by (auto simp: points_to_def sep_def)

lemma "(EXS x. Q x \<sqinter> R x) \<subseteq> (EXS x. Q x) \<sqinter> (EXS x. R x)"
apply auto
done

lemma [spred]: "subst_pred <P> i_update j = <subst_pred_s P i_update j>"
  by (auto simp: subst_pred_def pure_pred_def emp_def)

lemma [sep_simp, simp]: "<{}> = bot"
  by (auto simp: pure_pred_def) 

lemma [sep_simp, simp]: "s \<in> (if P then UNIV else {}) = P"
  by auto

lemma hd_tl: "x \<noteq> [] \<Longrightarrow> rev x @ y = rev (tl x) @ (Cons (hd x) y)"
  apply (induct x)
  apply simp
  apply auto
done



schematic_lemma s_singleton: "(s, h) \<in> (i \<mapsto> j) \<Longrightarrow> (s, h) \<in> (i \<mapsto> (\<lambda>_.?x))"
  by (auto simp: singleton_def)

lemma cutE1: "(s, h) \<in> p * q \<Longrightarrow> (\<And>h. (s, h) \<in> q \<Longrightarrow> (s, h) \<in> q') \<Longrightarrow> (s, h) \<in> p * q'"
  by (auto simp: sep_def)

lemma cutE1': "(s, h) \<in> p \<Longrightarrow> (q = emp) \<Longrightarrow> (s, h) \<in> p * q"
  by (auto simp: sep_def emp_def)

lemma cutE1'': "(s, h) \<in> q \<Longrightarrow> (p = emp) \<Longrightarrow> (s, h) \<in> p * q"
  by (auto simp: sep_def emp_def)

schematic_lemma llist_J: "(s, h) \<in> llist xa j \<Longrightarrow> (s, h) \<in> llist xa (\<lambda>_. ?x)"
  apply (induct xa arbitrary: x)
  apply (simp add: llist_empty pure_pred_def)
oops

lemma final: "(s, h) \<in> llist xs j \<Longrightarrow> (s, h) \<in> llist xs (\<lambda>_. j s)"
  apply (induct xs)
  apply (simp add: sep_simp llist_empty pure_pred_def)
  apply (simp add: llist_simp2)
  apply auto

        apply (erule split_pure_sepE)
        apply (erule pred_exE')
        apply (rule_tac x=x in exI)
        apply (simp add: singleton_def doublet_def sep_def)
        apply (erule split_pure_sepE)
        apply simp
done
    
declare  Set.Diff_eq [sep_simp]

lemma test2: "(s, h) \<in> (i \<mapsto> j) * q \<Longrightarrow> ((s, h) \<in> (i \<mapsto> (\<lambda>_. j s)) * q \<Longrightarrow> G) \<Longrightarrow> G"
sorry

lemma test3: "(s, h) \<in> (i \<mapsto> e) * p \<Longrightarrow> e s = e' s \<Longrightarrow> (\<And>h'. (s, h) \<in> p \<Longrightarrow> (s, h) \<in> q) \<Longrightarrow> (s, h) \<in> (i \<mapsto> e') * q"
sorry

schematic_lemma test: "(s, h) \<in> (i \<mapsto> j) * q \<Longrightarrow> ((s, h) \<in> (i \<mapsto> (\<lambda>_.?x)) * q \<Longrightarrow> G) \<Longrightarrow> G"
  by (auto simp: sep_def singleton_def)


lemma cutE2: "(s, h) \<in> p * q \<Longrightarrow> (\<And>h. (s, h) \<in> q \<Longrightarrow> (s, h) \<in> p' * q') \<Longrightarrow> (s, h) \<in> p' * (p * q')"
  apply (auto simp: sep_def ortho_def)
by (smt Int_commute Un_empty dom_map_add inf_sup_distrib1 map_add_assoc map_add_comm)

lemma cutE2': "(s, h) \<in> p * r \<Longrightarrow> (\<And>h. (s, h) \<in> p \<Longrightarrow> (s, h) \<in> q1 * (q2 * q3)) \<Longrightarrow> (s, h) \<in> q1 * (q2 * (q3 * q))"
sorry

method sep_simp =
  (subst sep_simp | subst (asm) sep_simp | subst spred | subst (asm) spred | rule pred_exE)+

named_theorems sep_intro
named_theorems sep_elim

named_theorems sep_safe_intro
named_theorems sep_safe_elim

method sep_same = (
    ((erule cutE1 | erule cutE1'| erule cutE2 | erule cutE1'' | erule cutE2')+)?
)

method sep_safe_split =
  (
    ((rule Set.IntI)+)?;  (* Conjunction elimination *)
      (
        ((erule Set.IntE)+)?,  (* Conjunction elimination *)
    
        ((erule pred_exE')+)?,   (* Eliminate existentials in premises *)
        ((erule split_pure_sepE)+)?,   (* Eliminate existentials in premises *)
    
        sep_same?,
        (sep_simp, sep_safe_split)?,
        (assumption | rule HOL.refl)?
      )
  )

method sep_split =
  (
    sep_safe_split;
    ((rule pred_exI')+)?,
    ((rule split_pure_sep')+)?;
    simp?;
    (
      (sep_same | sep_simp, sep_split)?,
      (assumption | rule HOL.refl)?
    )
  )


method sep_safe = (
    sep_simp?,             (* Normalize *)
    (rule subrelI)?,        (* Subset relation introduction *)

    sep_safe_split?;

    (((erule sep_safe_elim | rule sep_safe_intro)+, simp?); sep_safe_split?)?;
    sep_same?;
    (assumption | rule HOL.refl)?
)


method sep_auto uses elim intro = 
  (
    sep_simp?,             (* Normalize *)
    (rule subrelI)?,        (* Subset relation introduction *)
    sep_safe_split?;

    sep_split?;
    ((erule sep_elim | rule sep_intro)+; simp?, sep_split?)?;
    sep_same?;
    (assumption | rule HOL.refl)?;
    auto?
  )


declare zero [sep_elim]
  not_zero [sep_safe_elim]
  hd_tl [sep_intro]
  final [intro]
  test3 [sep_elim]
(*

record tt =
  i :: nat
  j :: nat
  k :: nat


lemma "<{s. i s = 0}> *  (EXS x xa. llist x i * llist xa j * <{s. rev xs = rev x @ xa}>) \<subseteq> llist (rev xs) j"
apply sep_auto
oops

lemma "list_seg (Cons x xs) i k
    \<subseteq> (EXS x. ((\<lambda>s. i s + 1) \<hookrightarrow> (\<lambda>_. x)) \<inter>
               subst_pred ((i \<mapsto> -) * ((\<lambda>s. i s + 1) \<mapsto> -) * subst_pred (list_seg xs i k) i_update j) j_update (\<lambda>_. x))"
apply sep_auto
oops

lemma "llist xs i \<subseteq> subst_pred (EXS x xa. llist x i * llist xa j \<inter> {(s, h). rev xs = rev x @ xa}) j_update (\<lambda>_. 0)"
apply sep_auto
oops

lemma "{(s, h). i s \<noteq> 0} \<inter> (EXS x xa. llist x i * llist xa j \<inter> {(s, h). rev xs = rev x @ xa})
    \<subseteq> (EXS x. ((\<lambda>s. i s + 1) \<hookrightarrow> (\<lambda>_. x)) \<inter>
               subst_pred
                (((\<lambda>s. i s + 1) \<mapsto> -) *
                 (((\<lambda>s. i s + 1) \<mapsto> j) -*
                  subst_pred (subst_pred (EXS x xa. llist x i * llist xa j \<inter> {(s, h). rev xs = rev x @ xa}) i_update k) j_update i))
                k_update (\<lambda>_. x))"
apply sep_safe

oops

hide_const i j k

(* Examples *)
lemma "list_seg xs i j * list_seg ys j k \<subseteq> list_seg (xs@ys) i k"

oops
(*
  ((subst sep_simp)+ |
  (rule order_trans[rotated], rule l1, rule allI, rule order_refl) | subst sep_simp )
*)

lemma "(EXS x. (x \<mapsto> i) * true * <{s. x s = j s}>) * (EXS x. (x \<hookrightarrow> j) * true) * emp * (k \<mapsto> i, j) * <{s. i s = j s}> \<subseteq> (EXS y :: 'a. F y) "

apply sep_auto
oops

*)
end