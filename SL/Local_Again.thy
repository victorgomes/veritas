theory Local_Again
  imports Main
begin

type_synonym heap = "nat \<Rightarrow> nat option"

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

type_synonym 'a pred = "('a \<times> heap) set"
type_synonym 'a stran = "'a \<times> heap \<Rightarrow> ('a \<times> heap) option"
type_synonym 'a ptran = "'a pred \<Rightarrow> 'a pred"

definition valid_mem :: "'a option \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "in" 100) where
  "x in Q \<equiv> case x of None \<Rightarrow> False | Some y \<Rightarrow> y \<in> Q"

definition basic :: "'a stran \<Rightarrow> 'a ptran" where
  "basic f Q \<equiv> {(s, h). f (s, h) in Q}"

definition star :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a pred" (infixl "**" 70) where
  "P ** Q \<equiv> {(s, h1 ++ h2) | s h1 h2. h1 \<bottom> h2 \<and> (s, h1) \<in> P \<and> (s, h2) \<in> Q}"

lemma star_iso: "p \<le> q \<Longrightarrow> p ** r \<le> q ** r"
  by (auto simp: star_def)

definition ht :: "'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "ht p F q \<equiv> p \<le> F q"

definition local :: "'a ptran \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "local F R \<equiv> \<forall>Q. F Q ** R \<le> F (Q ** R)"

lemma frame: "local F R \<Longrightarrow> ht P F Q \<Longrightarrow> ht (P ** R) F (Q ** R)"
  apply (simp add: local_def ht_def)
  apply (rule order_trans[of _ "F Q ** R"])
  apply (rule star_iso)
  apply force+
done

definition local2 :: "'a stran \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "local2 f R \<equiv> \<forall>s h1 h2 Q. h1 \<bottom> h2 \<and> f (s, h1) in Q \<and> (s, h2) \<in> R \<longrightarrow> f(s, h1 ++ h2) in (Q ** R)"

lemma "local2 f R \<Longrightarrow> local (basic f) R"
  apply (auto simp: local2_def local_def basic_def)
  apply (subst (asm) star_def) back
  apply clarsimp
done


text {* The left value of a variable is an update function. *}
type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"

text {* The right value of a variable is a retrieve function. *}
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"

definition assign :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's ptran" where
  "assign u t \<equiv> basic (\<lambda>(s, h). Some (u (\<lambda>_. t s) s, h))"

definition subst :: "('s \<times> 'h) set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('s \<times> 'h) set" where
  "subst P u t \<equiv> Collect (\<lambda>(s, h). (u (\<lambda>_. t s) s, h) \<in> P)"


lemma local_assign: "\<forall>t. R = subst R v t \<Longrightarrow> local (assign v t) R"
  apply (auto simp: subst_def local_def assign_def basic_def star_def valid_mem_def)
  apply force
done


record test = x :: nat
  y :: nat

lemma "local (assign (x_update) t) {(s, h). y s = 2}"
  apply (rule local_assign)
  apply (simp add: subst_def)
done
  

end