theory Array
  imports Main
begin

type_synonym 'a array = "nat \<Rightarrow> 'a" 

definition interval :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "interval k l \<equiv> {i. k \<le> i \<and> i \<le> l}"

(* Sum from offset the number of value n *)
primrec array_sum :: "nat \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> 'a :: {plus, zero}" where
  "array_sum off 0 a = 0"
| "array_sum off (Suc n) a = a (off + n) + array_sum off n a"

fun array_sorted :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: order array \<Rightarrow> bool" where
  "array_sorted off 0 a \<longleftrightarrow> True"
| "array_sorted off (Suc 0) a \<longleftrightarrow> True" 
| "array_sorted off (Suc (Suc n)) a \<longleftrightarrow> a (off + n) \<le> a (off + Suc n) \<and> array_sorted off (Suc n) a"

fun new_array :: "'a list \<Rightarrow> 'a array" where
  "new_array xs = nth xs"

lemma "array_sorted i n a \<Longrightarrow> array_sorted (Suc i) (n - 1) a"
  apply (induct n)
  apply auto
  apply (case_tac n)
  apply auto
  apply (case_tac nat)
by auto

lemma last_num: "array_sorted i (Suc (Suc n)) a \<Longrightarrow> a (i + n) \<le> a (i + Suc n)"
  by (cases n) auto

lemma "i > 0  \<Longrightarrow> array_sorted i (Suc (Suc n)) a \<Longrightarrow> array_sorted (i - 1) (Suc (Suc (Suc n))) a"
apply (induct n)
apply simp
apply force
apply auto
apply (cases n)
apply force
apply (subgoal_tac 

value "array_sorted 1 2 (new_array [2, 2, 1 :: nat])"


end