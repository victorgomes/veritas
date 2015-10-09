theory LinkedList
  imports Assertions
begin

(*****************************************************************************************)
section {* List Segments *}
(*****************************************************************************************)

abbreviation (input) is_nil :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<Midarrow> nil") where
  "i \<Midarrow> nil \<equiv> {(s, h). i s \<notin> dom h}"

primrec list_seg :: "nat list \<Rightarrow> 'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" where
  "list_seg [] i j = emp \<sqinter> (i \<Midarrow> j)"
| "list_seg (x#xs) i k = (EXS j. (i \<mapsto> $x, $j) * list_seg xs $j k)"


lemma hd_tl: "x \<noteq> [] \<Longrightarrow> rev x @ y = rev (tl x) @ (Cons (hd x) y)"
  apply (induct x)
  apply simp
  apply auto
done

lemma list_seg_empty: "list_seg [] i j = <{s. i s = j s}>"
  by (auto simp: store_pred_def)

lemma lint_seg_singl: "(list_seg [x] i j) = (i \<mapsto> $x, j)"
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

lemma list_seg_reynolds1: "list_seg xs i j \<le> -(i \<Midarrow> nil) \<squnion> (($xs \<Midarrow> $[]) \<sqinter> (i \<Midarrow> nil))"
  apply (induct xs)
  apply clarsimp
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
done

lemma list_seg_reynolds2: "list_seg xs i j \<le> (i \<Midarrow> j) \<squnion> - ($xs \<Midarrow> $[])"
  apply (induct xs)
  apply clarsimp
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
done

lemma subst_list_seg [spred]: "subst_pred (list_seg xs m n) i_update j = list_seg xs (subst m i_update j) (subst n i_update j)"
  apply (induct xs arbitrary: m n)
  apply (force simp: subst_pred_def emp_def)
  apply (auto simp: spred)
done

(*****************************************************************************************)
section {* Linked List *}
(*****************************************************************************************)

definition llist :: "nat list \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" where
  "llist xs i \<equiv> list_seg xs i $0 \<sqinter> {(s, h). 0 \<notin> dom h}"

lemma llist_empty: "llist [] i = <{s. i s = 0}>"
  by (auto simp add: llist_def store_pred_def emp_def)

lemma llist_empty_var: "llist [] i = (i \<Midarrow> $0) \<sqinter> emp"
  by (auto simp add: llist_def emp_def)

lemma llist_empty_zero [simp]: "llist [] (\<lambda>s. 0) = emp"
  by (auto simp add: llist_def emp_def)

lemma llist_simp: "llist (x#xs) i = <{s. i s \<noteq> 0}> * (EXS k. (i \<mapsto> $x, $k) * llist xs $k)"
  apply (auto simp: llist_def sep_def doublet_def singleton_def store_pred_def emp_def)
  apply auto
  using neq0_conv apply fastforce
done

lemma llist_simp_var: "llist (x#xs) i = -(i \<Midarrow> $0) \<sqinter> (EXS k. (i \<mapsto> $x, $k) * llist xs $k)"
  apply (auto simp: llist_def sep_def doublet_def singleton_def)
  apply (rule_tac x=xa in exI)
  apply auto
done

lemma subst_llist [spred]: "subst_pred (llist xs m) i_update j = llist xs (subst m i_update j)"
  apply (simp add: llist_def spred)
  apply (simp add: subst_pred_def)
done

lemmas [sep_simp] =
  list_seg_empty
  list_seg.simps(2)
  llist_empty
  llist_empty_zero
  llist_simp

lemma zero: "(s, h) \<in> llist x i * R \<Longrightarrow> i s = 0 \<Longrightarrow> (x = [] \<Longrightarrow> (s, h) \<in> R \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (induct x)
  apply (simp add: llist_empty)
  apply (erule spE)
  apply simp
  apply (simp add: llist_simp)
by (metis (no_types, lifting) CollectD bbi.mult_assoc less_numeral_extra(3) spE)

lemma not_zero: "(s, h) \<in> llist x i * R \<Longrightarrow> i s \<noteq> 0 \<Longrightarrow> (x \<noteq> [] \<Longrightarrow> (s, h) \<in> llist (Cons (hd x) (tl x)) i * R \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (induct x)
  apply (simp add: llist_empty)
  apply (erule spE)
  apply simp
  apply (simp add: llist_simp)
done

schematic_lemma llist_J: "(s, h) \<in> llist xa j \<Longrightarrow> (s, h) \<in> llist xa (\<lambda>_. ?x)"
  apply (induct xa arbitrary: x)
  apply (simp add: llist_empty store_pred_def)
oops

lemma final: "(s, h) \<in> llist xs j \<Longrightarrow> (s, h) \<in> llist xs (\<lambda>_. j s)"
  apply (induct xs)
  apply (simp add: sep_simp llist_empty store_pred_def)
  apply (simp add: llist_simp)
  apply auto

        apply (erule spE)
        apply (erule pred_exE)
        apply (rule_tac x=x in exI)
        apply (simp add: singleton_def doublet_def sep_def)
        apply (erule spE)
        apply simp
done

declare zero [sep_elim]
  not_zero [sep_safe_elim]
  hd_tl [sep_intro]
  final [intro]
end