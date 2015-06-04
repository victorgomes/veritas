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

value "array_sorted 1 3 (new_array [0, 5, 8 :: nat, 4])"


end