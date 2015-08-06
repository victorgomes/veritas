theory InsertionSort
  imports Syntax Array
begin

no_notation Set.image (infixr "`" 90)

record ('a :: ord) insertion_state = 
  k :: 'a
  i :: nat
  j :: nat
  A :: "'a array"
(*
lemma insertion_sort: "\<turnstile> \<lbrace> len Ao > 0 \<and> `A = Ao \<rbrace>
  `i := 1;
  while `i < len `A
  inv sorted (take `i `A) \<and> `A <~~> Ao
  do
    `j := `i;
    while 0 < `j \<and> `A ! `j < `A ! (`j - 1)
    inv
      (sorted_but (take (`i + 1) `A) `j) \<and> (`i < len `A) \<and> (`j \<le> `i) \<and>
      (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`A <~~> Ao)
    do
      `k := `A ! `j;
      `A ! `j := `A ! (`j - 1);
      `A ! (`j - 1) := `k;
      `j := `j - 1
    od;
    `i := `i + 1
  od
  \<lbrace>sorted `A \<and> `A <~~> Ao \<rbrace>"
  apply (hoare, auto)
  apply (metis One_nat_def not_le take_sorted_butE_n)
  apply (metis One_nat_def take_sorted_butE_0)
  apply (simp add: take_sorted_butE)
  apply (unfold sorted_equals_nth_mono sorted_but_def, auto)
  apply (smt Suc_pred diff_less_Suc le_SucE le_less_trans less_Suc_eq_le nth_list_update) 
  apply (metis (hide_lams, no_types) One_nat_def perm.trans perm_swap_list)
  apply (smt Suc_pred diff_less_Suc le_SucE le_less_trans less_Suc_eq_le nth_list_update)
  by (smt One_nat_def le_less_trans perm.trans perm_swap_list)
*)

lemma insertion_sort_refinement: "\<lbrakk> len Ao > 0 \<and> `A = Ao, array_sorted `A \<and> `A <~~> Ao\<rbrakk> \<sqsubseteq>
  `i := 1;
  while `i \<noteq> len `A do
    `j := `i;
    while 0 < `j \<and> `A<`j> < `A<`j - 1> do
      `k := `A<`j>;
      `A := `A<`j := `A<`j - 1>>;
      `A := `A<`j - 1 := k>;
      `j := `j - 1
    od;
    `i := `i + 1
  od"
proof -
  have "\<lbrakk> len Ao > 0 \<and> `A = Ao, array_sorted `A \<and> `A <~~> Ao\<rbrakk> \<sqsubseteq> 
    `i := 1;
    \<lbrakk>`i = 1 \<and> array_sorted_off `A 1 `i \<and> `i \<le> len `A \<and> `A <~~> Ao, array_sorted `A \<and> `A <~~> Ao\<rbrakk>"
    by morgan auto
  also have "... \<sqsubseteq>
    `i := 1;
    while `i \<noteq> len `A do
      \<lbrakk> array_sorted_off `A 1 `i \<and> `i < len `A \<and> `A <~~> Ao, array_sorted_off `A 1 `i \<and> `i \<le> len `A \<and> `A <~~> Ao\<rbrakk>
    od"
    by morgan (auto simp: array_sorted_def)
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        \<lbrakk> array_sorted_off `A 1 `i \<and> `i < len `A \<and> `A <~~> Ao, array_sorted_off `A 1 (`i + 1) \<and> (`i + 1) \<le> len `A \<and> `A <~~> Ao\<rbrakk>;
        `i := `i + 1
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        \<lbrakk> sorted_but `A (`i + 1) (`i + 1) \<and> `i < len `A \<and> `A <~~> Ao, array_sorted_off `A 1 (`i + 1) \<and> (`i + 1) \<le> len `A \<and> `A <~~> Ao\<rbrakk>;
        `i := `i + 1
      od"
    by morgan (auto simp: sorted_but_def array_sorted_off_var)
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        \<lbrakk> sorted_but `A (`i + 1) (`i + 1) \<and> `i < len `A \<and> `A <~~> Ao, 
          `j \<le> `i \<and> sorted_but `A (`i + 1) (`j + 1) 
          \<and> (`j \<noteq> `i \<longrightarrow> `A <`j> \<le> `A <`j + 1>) \<and> (`i + 1) \<le> len `A 
          \<and> (`j = 0 \<or> `A<`j - 1> \<le> `A<`j>) \<and> `A <~~> Ao\<rbrakk>;
        `i := `i + 1
      od"
    apply morgan
    apply auto
    apply (auto simp: sorted_but_def array_sorted_off_var)
    

    
apply (metis Suc_leI dual_order.antisym eq_refl order.trans
    apply refinement
    apply auto
    apply (metis One_nat_def take_sorted_butE_0)
    apply (metis One_nat_def take_sorted_butE_n)
    by (metis One_nat_def Suc_eq_plus1 less_Suc_eq_le take_sorted_butE)
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        `j := `i;
        \<lbrakk> `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j
          \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A  \<and> `A <~~> Ao, 
          `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j
          \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A 
          \<and> (`j = 0 \<or> `A ! (`j - 1) \<le> `A ! `j) \<and> `A <~~> Ao\<rbrakk>;
        `i := `i + 1
      od"
    by refinement auto
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        `j := `i;
        while `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) do
          \<lbrakk> `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j
            \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A 
            \<and> `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) \<and> `A <~~> Ao, 
            `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j 
            \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A  \<and> `A <~~> Ao\<rbrakk>
        od;
        `i := `i + 1
      od"
    by refinement auto
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        `j := `i;
        while `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) do
          \<lbrakk> `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j
            \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A 
            \<and> `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) \<and> `A <~~> Ao, 
            `j - 1 \<le> `i \<and> sorted_but (take (`i + 1) `A) (`j - 1) 
            \<and> (`j - 1 \<noteq> `i \<longrightarrow> `A ! (`j - 1) \<le> `A ! `j) \<and> (`i + 1) \<le> len `A \<and> `j \<noteq> 0  \<and> `A <~~> Ao\<rbrakk>;
          `j := `j - 1
        od;
        `i := `i + 1
      od"
      by refinement auto
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        `j := `i;
        while `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) do
          \<lbrakk> `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j
            \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A 
            \<and> `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) \<and> `A <~~> Ao, 
            `j - 1 \<le> `i \<and> sorted_but (take (`i + 1) (`A[(`j - 1) := `k])) (`j - 1) 
            \<and> (`j - 1 \<noteq> `i \<longrightarrow> (`A[(`j - 1) := `k]) ! (`j - 1) \<le> (`A[(`j - 1) := `k]) ! `j) 
            \<and> (`i + 1) \<le> len (`A[(`j - 1) := `k]) \<and> `j \<noteq> 0 \<and> (`A[(`j - 1) := `k]) <~~> Ao \<rbrakk>;
          `A ! (`j - 1) := `k;
          `j := `j - 1
        od;
        `i := `i + 1
      od"
    by refinement
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        `j := `i;
        while `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) do
          \<lbrakk> `j \<le> `i \<and> sorted_but (take (`i + 1) `A) `j
            \<and> (`j \<noteq> `i \<longrightarrow> `A ! `j \<le> `A ! (`j + 1)) \<and> (`i + 1) \<le> len `A 
            \<and> `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) \<and> `A <~~> Ao, 
            `j - 1 \<le> `i \<and> sorted_but (take (`i + 1) (`A[(`j - 1) := `k, `j := `A ! (`j - 1)])) (`j - 1) 
            \<and> (`j - 1 \<noteq> `i \<longrightarrow> (`A[(`j - 1) := `k, `j := `A ! (`j - 1)]) ! (`j - 1) \<le> (`A[(`j - 1) := `k, `j := `A ! (`j - 1)]) ! `j) 
            \<and> (`i + 1) \<le> len (`A[(`j - 1) := `k, `j := `A ! (`j - 1)]) \<and> `j \<noteq> 0
            \<and> (`A[(`j - 1) := `k, `j := `A ! (`j - 1)]) <~~> Ao \<rbrakk>;
          `A  ! `j := `A ! (`j - 1);
          `A ! (`j - 1) := `k;
          `j := `j - 1
        od;
        `i := `i + 1
      od"
    apply refinement
    by (auto simp add: list_update_swap)
  also have "... \<sqsubseteq>
      `i := 1;
      while `i \<noteq> len `A do
        `j := `i;
        while `j \<noteq> 0 \<and> `A ! `j < `A ! (`j - 1) do
          `k := `A ! `j;
          `A  ! `j := `A ! (`j - 1);
          `A ! (`j - 1) := `k;
          `j := `j - 1
        od;
        `i := `i + 1
      od"
    apply refinement
    apply (unfold sorted_equals_nth_mono sorted_but_def, auto)
    apply (smt Suc_le_lessD Suc_pred diff_less_Suc eq_iff leD le_SucE len_list_update less_SucE nth_list_update order.strict_trans2)
    apply (smt One_nat_def Suc_le_lessD list_update_swap perm.trans perm_swap_list)
    apply (smt Suc_le_lessD Suc_pred diff_le_self le_neq_implies_less le_refl le_trans list_update_swap not_less_eq not_less_eq_eq nth_list_update_eq nth_list_update_neq)
    by (smt One_nat_def Suc_le_lessD le_less_trans list_update_swap perm.trans perm_swap_list)
  finally show ?thesis
    by auto
qed

hide_const k i j A

end
