theory LinkedList
  imports StoreHeapModel
begin

(* Single Linked List *)

abbreviation (input) is_nil :: "'a nat_exp \<Rightarrow> 'a pred" ("_ \<Midarrow> nil") where
  "i \<Midarrow> nil \<equiv> {(s, h). i s \<notin> dom h}"

primrec llist :: "nat list \<Rightarrow> 'a nat_exp \<Rightarrow> 'a nat_exp \<Rightarrow> 'a pred" where
  "llist [] i j = emp \<sqinter> (i \<Midarrow> j)"
| "llist (x#xs) i k = (EXS j. (i \<mapsto> #x, j) * llist xs j k)"

lemma singleton_list [simp]: "(llist [x] i j) = (i \<mapsto> #x, j)"
  by (auto simp: sep_def doublet_def singleton_def emp_def)

lemma llist_exs: "(EXS j. (emp \<sqinter> (i \<Midarrow> j)) * llist ys j k) = llist ys i k"
  apply (auto simp: sep_def doublet_def singleton_def emp_def)
  apply (induct ys)
  apply (auto simp: doublet_def singleton_def sep_def)
done

lemma llist_merge: "(llist (xs@ys) i k) = (EXS j. (llist xs i j) * (llist ys j k))"
  apply (induct xs arbitrary: i)
  apply (simp add: llist_exs)
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def
  sorry

lemma llist_rev: "(llist (xs@[x]) i k) = (EXS j. (llist xs i j) * (j \<mapsto> #x, k))"
  by (simp add: llist_merge singleton_list del: llist.simps)

lemma "llist xs i j \<le> (i \<Midarrow> nil) \<rightarrow> ((#xs \<Midarrow> #[]) \<sqinter> (i \<Midarrow> nil))"
  apply (induct xs)
  apply clarsimp
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
done

lemma "llist xs i j \<le> (i \<Midarrow> j) \<squnion> - (#xs \<Midarrow> #[])"
  apply (induct xs)
  apply clarsimp
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
done

no_notation sup (infixl "+" 65)

lemma exs1: "(EXS j. (i \<mapsto> a, j) * P j) = (i \<mapsto> a) * (EXS j. ((\<lambda>s. i s + 1) \<mapsto> j) * P j)"
  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
  apply (erule_tac x="[Suc (i s) \<mapsto> x s] ++ h2" in allE)
  apply auto
done

lemma tt1: "subst_pred (P * Q) i_update j = (subst_pred P i_update j) * (subst_pred Q i_update j)"
  by (auto simp: sep_def)

lemma tt2: "subst_pred (EXS k. (P k)) i_update j = (EXS k. (subst_pred (P k) i_update j))"
  by (auto simp: sep_def)

lemma tt3: "subst_pred (EXS k. (P k) * (Q k)) i_update j = (EXS k. (subst_pred (P k) i_update j) * (subst_pred (Q k) i_update j))"
  by (auto simp: sep_def)

record test =
  i :: nat
  j :: nat
  k :: nat

lemma tt4: "\<forall>a. x a = subst x i_update j a \<Longrightarrow> subst_pred (i \<mapsto> x) i_update j = j \<mapsto> x"
  by (auto simp: singleton_def)

lemma tt5: "\<forall>a. x a = subst x i_update j a \<Longrightarrow> subst_pred (i \<mapsto> (\<lambda>_. a), x) i_update j = j \<mapsto> (\<lambda>_. a), x"
  apply (subst doublet_def)+
  apply (subst tt1)
  apply (subst tt4)
  apply simp
  apply (subgoal_tac "subst_pred ((\<lambda>s. i s + 1) \<mapsto> x) i_update j = ((\<lambda>s. j s + 1) \<mapsto> x)")
  apply simp
  apply (auto simp: singleton_def)
done

lemma "subst_pred (llist xs i k) i_update j = llist xs j k"
  apply (induct xs)
  apply (clarsimp simp add: emp_def)
  apply force

  apply (subst llist.simps)+
  apply (subst tt2)
  apply (subst tt1)
  apply (subst tt)
sorry

apply (subst doublet_def)+


  apply (auto simp: sep_def doublet_def singleton_def emp_def ortho_def)
  apply (erule_tac x="subst x i_update j" in allE)
  apply (erule_tac x=h2 in allE)
  apply auto
lemma "ht (llist (Cons x xs) i k)
    (
      lookup j_update (\<lambda>s. (i s) + 1);
      dispose i;
      dispose (\<lambda>s. i s + 1);
      assign i_update j
    )
    (llist xs i k)"
    apply (rule hl_seq | rule mptran)+
prefer 4
  apply (rule sl)
  apply (rule order_refl)
prefer 3
  apply (rule sl)


    apply (rule hl_seq [where r = "llist xs j k"])
    apply (rule mptran)+
    apply (rule hl_seq [where r = "((\<lambda>s. i s + 1) \<mapsto> j) * (llist xs j k)"])
    apply (rule mptran)+
    apply (rule hl_seq [where r = "(i \<mapsto> #x) * ((\<lambda>s. i s + 1) \<mapsto> j) * (llist xs j k)"])
    apply (rule mptran)+
    apply (rule hl_pre [where P' = "(i \<mapsto> #x) * (EXS j. ((\<lambda>s. i s + 1) \<mapsto> j) * (llist xs j k))"])

    apply (simp add: exs1)
    
    apply (subst sep_comm)
    apply (subst sep_comm) back back
    apply (subst sep_comm) back back back
    apply (subst sep_assoc)
    apply (rule sl_frame)
    apply (rule lptran)
    apply (simp add: doublet_def singleton_def)

    apply (rule hl_pre)
prefer 2
    apply (rule sl_lookup)
    apply (clarsimp simp: sep_def doublet_def singleton_def emp_def ortho_def)
    apply (erule_tac x=x in allE)
    apply (erule_tac x=h2 in allE)
    apply clarsimp
    
    
    
end