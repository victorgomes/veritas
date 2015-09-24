theory RelationalWhile
  imports Main
begin

text {* Relations and predicate transformers equivalences *}

definition valid_mem :: "'a option \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "in" 55) where
  "x in Q \<equiv> case x of None \<Rightarrow> False | Some y \<Rightarrow> y \<in> Q"

type_synonym 'a ptran = "'a set \<Rightarrow> 'a set"

definition ptran :: "'a option rel \<Rightarrow> 'a ptran" ("[_| _" [55, 100] 100) where
  "[R| Q \<equiv> {s. \<forall>s'. (Some s, Some s') \<in> R \<longrightarrow> s' \<in> Q}"

text {* Commands *}

definition abort :: "'a rel" ("abort") where "abort \<equiv> {}"

lemma abort_ptran: "[abort| Q = UNIV"
  by (auto simp: abort_def ptran_def)

definition skip :: "'a rel" ("skip") where "skip \<equiv> Id" 

lemma skip_ptran: "[skip| Q = Q"
  by (auto simp: skip_def ptran_def)

definition fault :: "'a option rel" where "fault \<equiv> SOME R. \<exists>\<sigma>. (\<sigma>, None) \<in> R"

definition seq :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" (infixr ";" 60) where
  "seq \<equiv> relcomp"

lemma seq_ptran: "[R; S| Q \<le> [R| [S| Q"
  by (auto simp: ptran_def seq_def)

text {* Relations below the identity form tests *}

definition to_rel :: "'a set \<Rightarrow> 'a option rel" ("\<lfloor>_\<rfloor>" 100)  where
  "\<lfloor>P\<rfloor> \<equiv> {(Some p, Some p) | p. p \<in> P}"

lemma to_rel_ptran: "[\<lfloor>P\<rfloor>| Q = -P \<union> Q"
  by (auto simp: to_rel_def ptran_def)

lemma sup_ptran: "[R \<union> S| Q = [R| Q \<inter> [S| Q"
  by (auto simp: ptran_def)

definition cond :: "'a set \<Rightarrow> 'a option rel \<Rightarrow> 'a option rel \<Rightarrow> 'a option rel" where
  "cond b x y \<equiv> (\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>-b\<rfloor>;y)"

lemma cond_ptran: "[cond b x y| q = ([\<lfloor>b\<rfloor>| [x| q) \<inter> ([\<lfloor>-b\<rfloor>| [y| q)"
  apply (rule antisym)
  apply (simp add: cond_def seq_ptran sup_ptran seq_def ptran_def)
  apply force
  apply (auto simp add: cond_def seq_ptran sup_ptran seq_def ptran_def to_rel_def)
done

definition cwhile :: "'a set \<Rightarrow> 'a option rel \<Rightarrow> 'a option rel" where
  "cwhile b x \<equiv> ((\<lfloor>b\<rfloor>;x)\<^sup>*; \<lfloor>-b\<rfloor>)"
end