theory Fibonacci
  imports Syntax
begin

no_notation Set.image (infixr "`" 90)
  and comp_op ("n_" [90] 91)

(* Some numbers written in Suc form *)
lemma numeral_4 [simp]: "4 = Suc (Suc (Suc (Suc 0)))"
  by arith

lemma numeral_6 [simp]: "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  by arith

lemma numeral_8 [simp]: "8 = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  by arith

(* Definition of Fibonacci starting by 1 and 2: [1 2 3 5 8 13 ...] *)
fun fib :: "nat => nat" where
  "fib 0 = 1"
| "fib (Suc 0) = 2"
| "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "fib (Suc n) > 0"
  by (induct n rule: fib.induct) simp_all

(* Calculate the sum of even fibonnaci number smaller than m and maximum index n *)
fun sum_efib :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_efib m 0 = 0"
| "sum_efib m (Suc n) = sum_efib m n + (if (fib n) mod 2 \<noteq> 0 \<or> fib n > m then 0 else fib n)"

(* Predicate that indicates whether the sum is the sum of even fibonnaci numbers smaller than m *)
definition is_sum_efib :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_sum_efib sum m \<equiv> \<exists>n. sum = sum_efib m n \<and> fib n > m"

(* List of even fibonacci number: [2, 8, 34, ...] *)
fun efib :: "nat \<Rightarrow> nat" where
  "efib 0 = 2"
| "efib (Suc 0) = 8"
| "efib (Suc (Suc n)) = 4*efib (Suc n) + efib n"

(* Some lemmas about Fibonacci numbers *)
lemma fib_parity1: "(fib k) mod 2 = 0 \<Longrightarrow> (fib (Suc k)) mod 2 = Suc 0"
  apply (induct k, auto)
  by (metis One_nat_def mod_2_not_eq_zero_eq_one_nat)

lemma fib_parity2: "(fib k) mod 2 = 0 \<Longrightarrow> (fib (Suc (Suc k))) mod 2 = Suc 0"
  apply (induct k, auto)
  by presburger

lemma fib_parity3: "(fib n) mod 2 = 0 \<longleftrightarrow> n mod 3 = 1"
  apply (induct n rule: fib.induct, simp_all, default)
  apply (subgoal_tac "fib x mod 2 = 0 \<or> fib x mod 2 = Suc 0")
  apply (erule disjE)
  apply (subgoal_tac "fib (Suc (Suc x)) mod 2 = Suc 0")
  apply simp
  apply (metis fib_parity2)
  apply (subgoal_tac "x mod 3 = 0 \<or> x mod 3 = Suc (Suc 0)")
  apply (erule disjE)
  apply (metis fib.simps(3) fib_parity1 mod_Suc numeral_plus_numeral one_is_add semiring_norm(3) zero_neq_numeral)
  apply (metis (hide_lams, no_types) Suc_numeral add_One_commute mod_2_not_eq_zero_eq_one_nat mod_Suc numeral_One numeral_plus_numeral one_is_add semiring_norm(3) zero_neq_numeral)
  apply force
  apply force
  apply (subgoal_tac "x mod 3 = 0 \<or> x mod 3 = 1 \<or> x mod 3 = 2")
  apply (erule disjE)
  apply (subgoal_tac "fib x mod 2 = Suc 0 \<and> fib (Suc x) mod 2 = 0")
  apply (metis mod_Suc n_not_Suc_n)
  apply (metis mod_Suc n_not_Suc_n)
  apply (erule disjE)
  apply (subgoal_tac "fib x mod 2 = 0 \<and> fib (Suc x) mod 2 = Suc 0")
  apply (metis Suc_eq_plus1_left Suc_numeral add_2_eq_Suc' mod_add_left_eq mod_self n_not_Suc_n semiring_norm(5))
  apply (metis One_nat_def fib_parity1)
  apply (subgoal_tac "fib x mod 2 = Suc 0 \<and> fib (Suc x) mod 2 = Suc 0")
  apply (simp add: mod_add_eq)
  apply (metis One_nat_def Suc_1 mod_Suc_eq_Suc_mod mod_mod_trivial n_not_Suc_n not_mod_2_eq_1_eq_0)
  by force

lemma efib_correct: "efib n = fib (3*n + 1)"
  apply (induct n rule: fib.induct)
  by simp_all

lemma efib_mod_2_eq_0: "(efib n) mod 2 = 0"
  apply (induct n rule: fib.induct)
  apply force
  apply force
using efib.simps(3) by presburger

lemma fib_6_n: "fib (6 + n) = 4*fib (n + 3) + fib n"
  by (unfold Num.numeral_3_eq_3 numeral_6) simp

lemma sum_efib_fib: "\<lbrakk>(fib k) mod 2 = 0; fib k \<le> m\<rbrakk> \<Longrightarrow> sum_efib m (k + 3) = sum_efib m k + fib k"
proof -
  assume assms: "fib k mod 2 = 0" "fib k \<le> m"
  hence "fib (Suc k) mod 2 = Suc 0"
    by (metis fib_parity1)
  hence "fib (Suc (Suc k)) mod 2 = Suc 0"
    by (simp, metis assms(1) mod_add_left_eq plus_nat.add_0)    
  hence "sum_efib m (k + 3) = sum_efib m (k + 1)" using assms
    apply (simp add: Num.numeral_2_eq_2 Num.numeral_3_eq_3)
    by (metis Zero_not_Suc mod_add_left_eq plus_nat.add_0)
  thus ?thesis using assms
    by simp
qed  

record sum_efib_state =
  x :: nat
  y :: nat
  n :: nat
  k :: nat
  tmp :: nat
  sum :: nat

lemma sum_efib: "\<turnstile> \<lbrace> True \<rbrace>
    `sum := 0
  \<lbrace> is_sum_efib `sum m \<rbrace>"
  apply hoare
  apply (auto simp: is_sum_efib_def)
  apply (rule_tac x=0 in exI)
  apply auto
oops

lemma sum_efib: "\<turnstile> \<lbrace> True \<rbrace>
    `x := 2;
    `y := 8;
    `sum := 0;
    `n := 0;
    `k := 1;
    while `x \<le> m 
    inv
      (`k \<ge> 1) \<and> (`x = efib `n) \<and> (`x = fib `k) \<and>
      (`y = efib (`n + 1)) \<and> (`y = fib (`k + 3)) \<and>
      (`sum = sum_efib m `k)
    do
      `tmp := `x;
      `x := `y;
      `y := 4 * `y + `tmp;
      `sum := `sum + `tmp;
      `n := `n + 1;
      `k := `k + 3
    od
  \<lbrace> is_sum_efib `sum m \<rbrace>"
  apply (hoare, auto)
  apply (force simp: is_sum_efib_def)
  apply (simp add: numeral_3_eq_3)
  by (simp add: efib_mod_2_eq_0 sum_efib_fib)

lemma sum_efib_refinement: "\<lbrakk> True, is_sum_efib `sum m\<rbrakk>
    \<sqsubseteq>
  `x := 2;
  `y := 8;
  `sum := 0;
  `n := 0;
  `k := 1;
  while `x \<le> m do
    `tmp := `x;
    `x := `y;
    `y := 4 * `y + `tmp;
    `sum := `sum + `tmp;
    `n := `n + 1;
    `k := `k + 3
  od"
proof -
  have "\<lbrakk> True, is_sum_efib `sum m\<rbrakk> \<sqsubseteq>
      `x := 2; 
      \<lbrakk> `x = efib 0 \<and> `x = fib 1, is_sum_efib `sum m\<rbrakk>"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      \<lbrakk> `x = efib 0  \<and> `x = fib 1 \<and> `y = efib 1 \<and> `y = fib 4, 
        is_sum_efib `sum m\<rbrakk>"
apply morgan_step
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      \<lbrakk> `x = efib 0  \<and> `x = fib 1 \<and> `y = efib 1 \<and> `y = fib 4 \<and> `sum = sum_efib m 1, 
        is_sum_efib `sum m\<rbrakk>"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      \<lbrakk> `x = efib `n  \<and> `x = fib 1 \<and> `y = efib (`n + 1) \<and> `y = fib 4 \<and> `n \<ge> 0
        \<and> `sum = sum_efib m 1, 
        is_sum_efib `sum m\<rbrakk>"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
        \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k, 
        is_sum_efib `sum m\<rbrakk>"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<rbrakk>
      od"
    by morgan (auto simp: is_sum_efib_def)
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `x = efib `n  \<and> `x = fib (`k + 3) \<and> `y = efib (`n + 1) \<and> `y = fib (6 + `k) \<and> `n \<ge> 0
          \<and> `k + 3 \<ge> 1 \<and> `sum = sum_efib m (`k + 3) \<rbrakk>;
        `k := `k + 3
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `x = efib (`n + 1)  \<and> `x = fib (`k + 3) \<and> `y = efib (`n + 2) \<and> `y = fib (6 + `k) 
          \<and> (`n + 1) \<ge> 0 \<and> `k + 3 \<ge> 1 \<and> `sum = sum_efib m (`k + 3) \<rbrakk>;
        `n := `n + 1;
        `k := `k + 3
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `x = efib (`n + 1)  \<and> `x = fib (`k + 3) \<and> `y = efib (`n + 2) \<and> `y = fib (6 + `k) 
          \<and> (`n + 1) \<ge> 0 \<and> `k + 3 \<ge> 1 \<and> (`sum + `tmp) = sum_efib m (`k + 3) \<rbrakk>;
        `sum := `sum + `tmp;
        `n := `n + 1;
        `k := `k + 3
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `x = efib (`n + 1)  \<and> `x = fib (`k + 3) \<and> (4*`y + `tmp) = efib (`n + 2)
          \<and> (4*`y + `tmp) = fib (6 + `k) \<and> (`n + 1) \<ge> 0 \<and> `k + 3 \<ge> 1 
          \<and> (`sum + `tmp) = sum_efib m (`k + 3) \<rbrakk>;
        `y := 4*`y + `tmp;
        `sum := `sum + `tmp;
        `n := `n + 1;
        `k := `k + 3
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `y = efib (`n + 1)  \<and> `y = fib (`k + 3) \<and> (4*`y + `tmp) = efib (`n + 2)
          \<and> (4*`y + `tmp) = fib (6 + `k) \<and> (`n + 1) \<ge> 0 \<and> `k + 3 \<ge> 1 
          \<and> (`sum + `tmp) = sum_efib m (`k + 3) \<rbrakk>;
        `x := `y;
        `y := 4*`y + `tmp;
        `sum := `sum + `tmp;
        `n := `n + 1;
        `k := `k + 3
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        \<lbrakk> `x = efib `n  \<and> `x = fib `k \<and> `y = efib (`n + 1) \<and> `y = fib (`k + 3) \<and> `n \<ge> 0
          \<and> `k \<ge> 1 \<and> `sum = sum_efib m `k \<and> `x \<le> m, 
          `y = efib (`n + 1)  \<and> `y = fib (`k + 3) \<and> (4*`y + `x) = efib (`n + 2)
          \<and> (4*`y + `x) = fib (6 + `k)
          \<and> (`sum + `x) = sum_efib m (`k + 3) \<rbrakk>;
        `tmp := `x;
        `x := `y;
        `y := 4*`y + `tmp;
        `sum := `sum + `tmp;
        `n := `n + 1;
        `k := `k + 3
      od"
    by morgan simp
  also have "... \<sqsubseteq>
      `x := 2; 
      `y := 8;
      `sum := 0;
      `n := 0;
      `k := 1;
      while `x \<le> m do
        `tmp := `x;
        `x := `y;
        `y := 4*`y + `tmp;
        `sum := `sum + `tmp;
        `n := `n + 1;
        `k := `k + 3
      od"
    apply (morgan, auto)
    apply (simp add: numeral_3_eq_3)
    by (simp add: efib_mod_2_eq_0 sum_efib_fib)
  finally show ?thesis
    by auto
qed

hide_const x y n k tmp sum

end
