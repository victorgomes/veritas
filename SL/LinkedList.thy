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

lemma llist_emptyE: "(s, h) \<in> llist x i * R \<Longrightarrow> i s = 0 \<Longrightarrow> (x = [] \<Longrightarrow> (s, h) \<in> R \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (induct x)
  apply (simp add: llist_empty)
  apply (erule spE)
  apply simp
  apply (simp add: llist_simp)
by (metis (no_types, lifting) CollectD bbi.mult_assoc less_numeral_extra(3) spE)

lemma llist_non_emptyE: "(s, h) \<in> llist x i * R \<Longrightarrow> i s \<noteq> 0 \<Longrightarrow> (x \<noteq> [] \<Longrightarrow> (s, h) \<in> llist (Cons (hd x) (tl x)) i * R \<Longrightarrow> Q) \<Longrightarrow> Q"
  apply (induct x)
  apply (simp add: llist_empty)
  apply (erule spE)
  apply simp
  apply (simp add: llist_simp)
done

lemma llist_store_idepend: "(s, h) \<in> llist xs j \<Longrightarrow> (s, h) \<in> llist xs (\<lambda>_. j s)"
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

lemma sepD: "(x, y) \<in> P * Q \<Longrightarrow> \<exists>y1 y2. y = y1 ++ y2 \<and> y1 \<bottom> y2 \<and> (x, y1) \<in> P \<and> (x, y2) \<in> Q"
  by (auto simp: sep_def)

lemma llist_emp: "i x = 0 \<Longrightarrow> (x, y) \<in> llist xa i \<Longrightarrow> (x, y) \<in> emp"
  apply (simp add: llist_def)
  apply (erule conjE)
  apply (induct xa)
  apply simp
  apply simp
  apply (erule exE)
  apply (drule sepD)
  apply (erule exE)+
  apply (erule conjE)+
  apply (simp add: doublet_def)
  apply (drule sepD)
  apply (erule exE)+
  apply (erule conjE)+  
  apply (simp add: singleton_def)
done

lemma llist_cons: "0 < i x \<Longrightarrow> (x, y) \<in> llist xa i \<Longrightarrow> \<exists>j. (x, y) \<in> (i \<mapsto> (\<lambda>s. hd xa)) * (((\<lambda>s. Suc (i s)) \<mapsto> (\<lambda>s. j)) * llist (tl xa) (\<lambda>s. j))"
  apply (simp add: llist_def)
  apply (erule conjE)
  apply (induct xa)
  apply simp
  apply simp
  apply (erule exE)
  apply (simp add: doublet_def)
  apply (rule_tac x=xb in exI)
  apply sep_simp
  apply sep_auto
  apply force
done

lemma llist_cons_true: "0 < i x \<Longrightarrow> (x, y) \<in> llist xa i \<Longrightarrow> \<exists>j. (x, y) \<in> ((\<lambda>s. Suc (i s)) \<mapsto> (\<lambda>s. j)) * true"
  apply (drule llist_cons) back
  apply assumption
  apply auto
  apply (subst (asm) sep_assoc[symmetric])
  apply (subst (asm) sep_comm)
  apply sep_auto
done

lemma llist_cons_var: "0 < i x \<Longrightarrow> (x, y) \<in> llist xa i \<Longrightarrow> \<exists>xb xc xd. (x, y) \<in> (i \<mapsto> (\<lambda>s. xb)) * (((\<lambda>s. Suc (i s)) \<mapsto> (\<lambda>s. xc)) * llist xd (\<lambda>s. xc))"
  apply (drule llist_cons) back
  apply assumption
  apply auto
done


declare llist_emptyE [sep_elim]
  llist_non_emptyE [sep_safe_elim]
  llist_emp [sep_elim]
  llist_cons_var [intro]
  hd_tl [sep_intro]
  llist_store_idepend [intro]
end