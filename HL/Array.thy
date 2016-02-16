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

lemma "array_sorted_off a i n \<Longrightarrow> array_sorted_off a (Suc i) (n - 1)"
  apply (induct n)
  apply auto
  apply (case_tac n)
  apply auto
  apply (case_tac nat)
by auto

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

lemma perm_refl [iff]: "l <~~> l"
  by (auto simp: perm_def perm_betw_def)

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
 
lemma perm_rev: "rev a <~~> a"
  apply (simp add: perm_def perm_betw_def)
  apply (rule_tac x="\<lambda>i. if i > 0 \<and> i \<le> len a then len a - i + 1 else i" in exI)
  apply (auto simp: array_rev_def access_array_def bij_prop_def interval_def)
  apply (auto simp: bij_def inj_on_def image_def)
  by presburger

end