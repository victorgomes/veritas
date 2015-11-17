theory Lists
  imports Permutation While
begin

no_notation Set.image (infixr "`" 90)
  and times (infixr ";" 60)

(* Swap in lists preserve permutation *)
lemma id_take_n_1_nth_drop: "\<lbrakk>0 < j; j < length A\<rbrakk> \<Longrightarrow> A = take (j - 1) A @ A ! (j - 1) # A ! j # drop (j + 1) A"
  apply (subgoal_tac "A ! (j - 1) # A ! j # drop (j + 1) A = drop (j - 1) A")
  apply simp
proof -
  assume a1: "j < length A"
  assume a2: "0 < j"
  have "Suc j = j + 1"
    by presburger
  thus "A ! (j - 1) # A ! j # drop (j + 1) A = drop (j - 1) A"
    using a2 a1 by (metis (no_types) Cons_nth_drop_Suc Suc_diff_1 less_eq_Suc_le less_le_not_le)
qed

lemma take_swap: "j < length A \<Longrightarrow> take (j - 1) (A [j := A ! (j - 1), j - 1 := A ! j]) = take (j - 1) A"
by auto

lemma drop_swap: "0 < j \<Longrightarrow> drop (j + 1) (A [j := A ! (j - 1), j - 1 := A ! j]) = drop (j + 1) A"
by simp

lemma perm_swap_list: "\<lbrakk>0 < j; j < length A\<rbrakk> \<Longrightarrow> A [j := A ! (j - 1), j - 1 := A ! j] <~~> A"
proof -
  let ?A' = "(A [j := A ! (j - 1), j - 1 := A ! j])"
  assume assms: "0 < j" "j < length A"
  hence "?A' = take (j - 1) ?A' @ ?A' ! (j - 1) # ?A' ! j # drop (j + 1) ?A'"
    by (metis id_take_n_1_nth_drop length_list_update)
  also have "... = take (j - 1) A @ A ! j # A ! (j - 1) # drop (j + 1) A" using assms
    by (simp del: Nat.One_nat_def)
  finally show ?thesis
    by (metis perm_swap assms id_take_n_1_nth_drop)
qed

(* Array is sorted except in one place *)
definition sorted_but :: "('a :: ord) list \<Rightarrow> nat \<Rightarrow> bool" where
  "sorted_but A k \<equiv> \<forall>i j. i \<le> j \<and> j < length A \<and> i \<noteq> k \<and> k \<noteq> j \<longrightarrow> A ! i \<le> A ! j"

(* Sorted list lemmas *)
lemma sorted_singleton: "A \<noteq> [] \<Longrightarrow> sorted (take 1 A)"
  by simp

lemma take_sorted_equals_nth_mono: "n \<le> length A \<Longrightarrow> (\<forall>i j. i \<le> j \<and> j < n \<longrightarrow> A ! i \<le> A ! j) \<longleftrightarrow> sorted (take n A)"
  using sorted_equals_nth_mono by fastforce

lemma take_sorted_1: "\<lbrakk>sorted (take n A); n < length A; i \<le> j; j < n\<rbrakk> \<Longrightarrow> A ! i \<le> A ! j"
  using less_imp_le_nat take_sorted_equals_nth_mono by blast

lemma sorted_butI: "sorted A \<Longrightarrow> sorted_but A k"
  by (metis sorted_but_def sorted_nth_mono)

lemma take_sorted_butI: "sorted (take n A) \<Longrightarrow> sorted_but (take (Suc n) A) n"
  by (unfold sorted_equals_nth_mono sorted_but_def, auto)

lemma sorted_butE: "\<lbrakk>sorted_but A k; k + 1 < length A; A ! (k - 1) \<le> A ! k; A ! k \<le> A ! (k + 1)\<rbrakk> \<Longrightarrow> sorted A"
  apply (unfold sorted_equals_nth_mono sorted_but_def, auto)
  by (smt Suc_le_mono Suc_pred diff_le_self eq_iff leD le_0_eq le_less_Suc_eq le_less_linear le_less_trans)

lemma take_sorted_butE_0: "\<lbrakk>sorted_but (take n A) 0; A ! 0 \<le> A ! 1\<rbrakk> \<Longrightarrow> sorted (take n A)"
  by (smt One_nat_def Suc_eq_plus1 Suc_lessI length_greater_0_conv length_take min.absorb2 nat_le_linear nth_take order_refl sorted.Nil sorted_butE sorted_singleton take_all zero_diff)

lemma take_sorted_butE: "\<lbrakk>sorted_but (take n A) k; k < n; A ! (k - 1) \<le> A ! k; A ! k \<le> A ! (k + 1)\<rbrakk> \<Longrightarrow> sorted (take n A)"
  apply (unfold sorted_equals_nth_mono sorted_but_def, auto)
  by (smt Suc_pred eq_iff le_0_eq le_less_linear lessI less_eq_Suc_le less_le_trans order.strict_iff_order)

lemma take_sorted_butE_n: "\<lbrakk>sorted_but (take (Suc n) A) n; A ! (n - 1) \<le> A ! n\<rbrakk> \<Longrightarrow> sorted (take (Suc n) A)"
  apply (unfold sorted_equals_nth_mono sorted_but_def, auto)
  by (smt Suc_le_mono Suc_pred diff_le_self eq_iff leD le_0_eq le_less_Suc_eq le_less_linear le_less_trans)
  

end
