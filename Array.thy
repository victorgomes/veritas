theory Array
  imports Main
begin

type_synonym 'a array = "nat \<Rightarrow> 'a" 

definition interval :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "interval k l \<equiv> {i. k \<le> i \<and> i \<le> l}"

abbreviation array_length :: "'a array \<Rightarrow> nat" ("len _" [999] 1000) where
  "len a \<equiv> snd a"

definition array_at :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" (infixl "at" 100) where
  "a at i \<equiv> fst a i"

definition array_update :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" where
  "array_update a i n \<equiv> ((fst a) (i := n), snd a)"

fun array_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b \<Rightarrow> 'b" where
  "array_fold f (a, 0) = id"
| "array_fold f (a, Suc n) = array_fold f (a, n) o f (a (Suc n))"

fun array_foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a array \<Rightarrow> 'b" where
  "array_foldl f b (a, 0) = b"
| "array_foldl f b (a, Suc n) = array_foldl f (f b (a (Suc n))) (a, n)"

primrec new_array_acc :: "'a list \<Rightarrow> (nat \<Rightarrow> 'a ) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "new_array_acc (x#xs) f n = new_array_acc xs (f(n := x)) (Suc n)"
| "new_array_acc [] f n = f"

definition new_array_list :: "'a list \<Rightarrow> 'a array" where
  "new_array_list xs \<equiv> (new_array_acc xs (\<lambda>_. SOME n. True) 1, length xs + 1)"

fun sum_from_to :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: {plus, zero}) array \<Rightarrow> 'a" where
  "sum_from_to i 0 a = 0"
| "sum_from_to i (Suc j) a = (if i \<le> Suc j then sum_from_to i j a + a at (Suc j) else 0)"

definition sum :: "('a :: {plus, zero}) array \<Rightarrow> 'a" where
  "sum a \<equiv> sum_from_to 1 (len a) a"


value "sorted_from_to 2 4 (new_array_list [1, 2, 3 :: nat, 4, 5])"
end