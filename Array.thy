section {* Arrays *}

theory Array
  imports Main
begin

type_synonym 'a array = "nat \<Rightarrow> 'a" 

definition interval :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "interval k l \<equiv> {i. k \<le> i \<and> i \<le> l}"

(* Sum from offset the number of value n *)
primrec array_sum :: "'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  'a :: {plus, zero}" where
  "array_sum a off 0 = 0"
| "array_sum a off (Suc n) = a (off + n) + array_sum a off n"

fun array_sorted :: "'a :: order array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "array_sorted a off 0 \<longleftrightarrow> True"
| "array_sorted a off (Suc 0) \<longleftrightarrow> True" 
| "array_sorted a off (Suc (Suc n)) \<longleftrightarrow> a (off + n) \<le> a (off + Suc n) \<and> array_sorted a off (Suc n)"

fun new_array :: "'a list \<Rightarrow> 'a array" where
  "new_array xs = nth xs"

lemma "array_sorted a i n \<Longrightarrow> array_sorted a (Suc i) (n - 1)"
  apply (induct n)
  apply auto
  apply (case_tac n)
  apply auto
  apply (case_tac nat)
by auto

lemma last_num: "n > 0 \<Longrightarrow> array_sorted a i (Suc n) \<Longrightarrow> a (i + n - Suc 0) \<le> a (i + n)"
  by (cases n) auto

lemma tt: "i > 0 \<Longrightarrow> \<forall>k \<le> i. a(k) \<le> a(i) \<Longrightarrow> array_sorted a i (n - 1) \<Longrightarrow> array_sorted a (i - 1) n"
apply (induct n)
apply auto
apply (case_tac n)
apply force
apply simp
apply (rule conjI)
apply (case_tac nat)
apply simp
apply (rule last_num)
apply simp
apply simp
apply (case_tac nat)
apply auto
done

lemma tt2: "i > 0 \<Longrightarrow> \<forall>k. 1 \<le> k \<and> k \<le> i \<longrightarrow> a(k) \<le> a(i + 1) \<Longrightarrow> array_sorted a (Suc i) n \<Longrightarrow> array_sorted a i (Suc n)"
apply (induct n)
apply auto
apply (case_tac n)
apply force
apply simp
apply (case_tac n)
apply force
apply simp
done

lemma "i > 0 \<Longrightarrow> \<forall>k \<le> i. a(k) \<le> a(i) \<Longrightarrow> array_sorted a i (Suc (Suc n)) \<Longrightarrow> array_sorted a  (i - 1) (Suc (Suc (Suc n)))"
apply (induct n)
by auto

value "array_sorted (new_array [2, 2, 1 :: nat]) 1 2"


end