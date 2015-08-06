section {* Arrays *}

theory Array
  imports Main
begin

type_synonym 'a array = "(nat \<Rightarrow> 'a) \<times> nat"

definition len_array :: "'a array \<Rightarrow> nat" ("len _" [100] 100) where
  "len a \<equiv> snd a"

definition access_array :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" ("_<_>" [100, 50] 100) where
  "a<i> \<equiv> (fst a) i" 

definition is_empty_array :: "'a array \<Rightarrow> bool" where
  "is_empty_array a \<equiv> len a = 0"

definition upd_array :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" ("_<_ := _>" [100, 50, 50] 100) where
  "a<i := n> \<equiv> ((fst a)(i := n), snd a)"

definition new_array :: "nat \<Rightarrow> 'a \<Rightarrow> 'a array" where
  "new_array l n = (\<lambda>_. n, l)"

definition array_rev :: "'a array \<Rightarrow> 'a array" ("rev _" [100] 100) where
  "rev a \<equiv> (\<lambda>i. if i > 0 \<and> i \<le> len a then a<len a - i + 1> else a<i>, len a)"

lemma len_rev [simp]: "len (rev a) = len a"
  by (auto simp: len_array_def array_rev_def)

lemma rev_rev [simp]: "rev (rev a) = a"
  apply (auto simp: array_rev_def len_array_def access_array_def)
  apply (case_tac a)
  apply auto
  apply (rule ext)
  apply (auto simp: len_array_def access_array_def)
done

definition interval :: "nat \<Rightarrow> nat \<Rightarrow> nat set" ("\<lbrace>_, _\<rbrace>") where
  "\<lbrace>k, l\<rbrace> \<equiv> {i. k \<le> i \<and> i \<le> l}"

(* Sum from offset the number of value n *)
primrec array_sum :: "'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  'a :: {plus, zero}" where
  "array_sum a off 0 = 0"
| "array_sum a off (Suc n) = a<off + n> + array_sum a off n"

fun array_sorted_off :: "'a :: order array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "array_sorted_off a off 0 \<longleftrightarrow> True"
| "array_sorted_off a off (Suc 0) \<longleftrightarrow> True" 
| "array_sorted_off a off (Suc (Suc n)) \<longleftrightarrow> a<off + n> \<le> a<off + Suc n> \<and> array_sorted_off a off (Suc n)"

lemma array_sorted_off_var: "array_sorted_off a (Suc 0) N \<longleftrightarrow> (\<forall>i j. 0 < i \<and> i \<le> j \<and> j \<le> N \<longrightarrow> a<i> \<le> a <j>)"
  apply (induct N)
  apply clarsimp
  apply (case_tac N)
  apply auto
  using le_Suc_eq apply auto[1]
by (metis dual_order.trans le_SucE le_less)

(* Array is sorted except in one place *)
definition sorted_but :: "('a :: order) array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "sorted_but a N k \<equiv> \<forall>i j. 0 < i \<and> i \<le> j \<and> j \<le> N \<and> i \<noteq> k \<and> k \<noteq> j \<longrightarrow> a<i> \<le> a<j>"

lemma [simp]: "sorted_but a n 0 = array_sorted_off a (Suc 0) n"
  by (auto simp: sorted_but_def array_sorted_off_var)



definition array_sorted :: "'a :: order array \<Rightarrow> bool" where
  "array_sorted a \<equiv> array_sorted_off a 1 (len a)"



(*
fun new_array :: "'a list \<Rightarrow> 'a array" where
  "new_array xs = nth xs"
*)

lemma "array_sorted_off a i n \<Longrightarrow> array_sorted_off a (Suc i) (n - 1)"
  apply (induct n)
  apply auto
  apply (case_tac n)
  apply auto
  apply (case_tac nat)
by auto
(*
lemma last_num: "n > 0 \<Longrightarrow> array_sorted a i (Suc n) \<Longrightarrow> a (i + n - Suc 0) \<le> a (i + n)"
  by (cases n) auto
*)

definition bij_prop :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "bij_prop f x y \<equiv> bij f \<and> (\<forall>i. i \<notin> \<lbrace>x, y\<rbrace> \<longrightarrow> f i = i)"

lemma bij_prop1: "bij_prop f x y \<Longrightarrow> \<forall>i \<in> \<lbrace>x, y\<rbrace>. f i \<in> \<lbrace>x, y\<rbrace>"
  apply (clarsimp simp: bij_prop_def)
  by (metis bij_pointE)

lemma bij_prop2: "bij_prop f x y \<Longrightarrow> x' \<le> x \<Longrightarrow> y \<le> y' \<Longrightarrow> bij_prop f x' y'"
  by (auto simp: bij_prop_def interval_def)

lemma bij_prop_id [simp, intro]: "bij_prop id x y"
  by (auto simp: bij_prop_def)

definition perm_betw :: "'a array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "perm_betw a b x y \<equiv> \<exists>f. bij_prop f x y \<and> (\<forall>i. a<i> = b<f i>)" 

definition perm :: "'a array \<Rightarrow> 'a array \<Rightarrow> bool" ("_ <~~> _"  [50, 50] 50)  where
  "perm a b \<equiv> len a = len b \<and> perm_betw a b 1 (len a)"
 
(*


(* Some theorems about permutation were copied from HOL/HOL-NSA-Examples/Permutation *)
inductive perm :: "'a array \<Rightarrow> 'a array \<Rightarrow> bool"  ("_ <~~> _"  [50, 50] 50) 
where
  Nil [intro!]: "(a, 0) <~~> (b, 0)"
| swap [intro!]: "y # x # l <~~> x # y # l"
| swap [intro!]: "y # x # l <~~> x # y # l"
| Cons [intro!]: "xs <~~> ys ==> z # xs <~~> z # ys"
| trans [intro]: "xs <~~> ys ==> ys <~~> zs ==> xs <~~> zs"
*)

lemma perm_refl [iff]: "l <~~> l"
  by (auto simp: perm_def perm_betw_def)
(*
lemma [simp]: "sorted (take (Suc 0) A)"
  by (induct A) auto
*)
lemma xperm_empty_imp: "is_empty_array a \<Longrightarrow> a <~~> b \<Longrightarrow> is_empty_array b"
  by (auto simp: is_empty_array_def perm_def)

lemma perm_length: "a <~~> b \<Longrightarrow> len a = len b"
  by (auto simp: perm_def)

lemma perm_comm: "a <~~> b \<Longrightarrow> b <~~> a"
  apply (clarsimp simp: perm_def perm_betw_def)
  apply (rule_tac x="the_inv f" in exI)
  apply (clarsimp simp:  bij_prop_def bij_betw_the_inv_into bij_is_inj bij_is_surj f_the_inv_into_f)
  apply (metis bij_is_inj the_inv_f_f)
done
 
(*
lemma perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (induct xs) auto
*)

(*
lemma perm_append_swap: "a <@> b <~~> b <@> a"

  apply (induct xs)
    apply simp_all
  apply (blast intro: perm_append_Cons)
  done

lemma perm_append_single: "a # xs <~~> xs @ [a]"
  by (rule perm.trans [OF _ perm_append_swap]) simp
*)
lemma perm_rev: "rev a <~~> a"
  apply (simp add: perm_def perm_betw_def)
  apply (rule_tac x="\<lambda>i. if i > 0 \<and> i \<le> len a then len a - i + 1 else i" in exI)
  apply (auto simp: array_rev_def access_array_def bij_prop_def interval_def)
  apply (auto simp: bij_def inj_on_def image_def)
  by presburger


(*
lemma perm_append1: "xs <~~> ys ==> l @ xs <~~> l @ ys"
  by (induct l) auto

lemma perm_append2: "xs <~~> ys ==> xs @ l <~~> ys @ l"
  by (blast intro!: perm_append_swap perm_append1)

lemma perm_swap: "xs @ y # x # ys <~~> xs @ x # y # ys"
  apply (induct xs)
  by auto
*)







(*
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
*)

end