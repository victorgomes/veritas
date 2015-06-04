theory Array
  imports Main
begin

type_synonym 'a array = "(nat \<Rightarrow> 'a) \<times> nat" 

abbreviation array_length :: "'a array \<Rightarrow> nat" ("len _" [999] 1000) where
  "len a \<equiv> snd a"

definition any_value :: "'a" where
  "any_value \<equiv> SOME u. True"

definition array_at :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" (infixl "at" 100) where
  "a at i \<equiv> fst a i"

definition array_update :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" where
  "array_update a i n \<equiv> ((fst a)(i := n), snd a)"

definition new_array :: "nat \<Rightarrow> 'a array" where
  "new_array n \<equiv> (\<lambda>_. any_value, n)"

primrec new_array_acc :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "new_array_acc (x#xs) f n = new_array_acc xs (f(n := x)) (Suc n)"
| "new_array_acc [] f n = f"

definition new_array_list :: "'a list \<Rightarrow> 'a array" where
  "new_array_list xs \<equiv> (new_array_acc xs (\<lambda>_. any_value) 1, length xs + 1)"

fun sum_from_to :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: {plus, zero}) array \<Rightarrow> 'a" where
  "sum_from_to i 0 a = 0"
| "sum_from_to i (Suc j) a = (if i \<le> Suc j then sum_from_to i j a + a at (Suc j) else 0)"

definition sum :: "('a :: {plus, zero}) array \<Rightarrow> 'a" where
  "sum a \<equiv> sum_from_to 1 (len a) a"

fun sorted_from_to :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: order) array \<Rightarrow> bool" where
  "sorted_from_to i 0 a \<longleftrightarrow> True"
| "sorted_from_to i (Suc j) a \<longleftrightarrow> (if i \<le> Suc j then sorted_from_to i j a \<and> (a at j \<le> a at (Suc j)) else False)"

value "sorted_from_to 2 4 (new_array_list [1, 2, 3 :: nat, 4, 5])"
end