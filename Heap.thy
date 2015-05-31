theory Heap
  imports While
begin

no_notation times (infixl "*" 70)

type_synonym heap = "nat \<Rightarrow> nat option"
type_synonym 'a state = "'a \<times> heap"
type_synonym ('a, 'b) pred = "'b \<Rightarrow> 'a state set"

section {* Heap *}

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

lemma theI: "h x = Some y \<Longrightarrow> the (h x) = y"
  by simp

lemma heap_divider: "h1 \<bottom> h2 \<Longrightarrow> h1 x = Some y \<Longrightarrow> (h1 ++ h2) x = Some y"
  by (auto simp: ortho_def map_add_def split: option.splits)

lemma heap_add_comm: "h1 \<bottom> h2 \<Longrightarrow> h1 ++ h2 = h2 ++ h1"
  by (auto simp: ortho_def intro: map_add_comm)
  
section {* Predicates *}

definition emp :: "('a, 'b) pred" where "emp \<equiv> \<lambda>_. {(s, h). h = Map.empty}"

definition sep_conj :: "('a, 'b) pred \<Rightarrow> ('a, 'b) pred \<Rightarrow> ('a, 'b) pred" (infixl "*" 75) where
  "P * Q \<equiv> \<lambda>u. {(s, h1 ++ h2) | s h1 h2. (s, h1) \<in> (P u) \<and> (s, h2) \<in> (Q u) \<and> h1 \<bottom> h2}"  

section {* Locality *}  

definition local :: "('a state) rel \<Rightarrow> bool" where
  "local x \<equiv> \<forall>s h' ho dh. h' \<bottom> dh \<and> ((s, ho), (s, h' ++ dh)) \<in> x \<longrightarrow> (\<exists>h. h \<bottom> dh \<and> ho = h ++ dh \<and> ((s, h), (s, h')) \<in> x)"
  
lemma local_skip: "local skip"
  by (auto simp: local_def skip_def)
  
lemma local_seq: "local x \<Longrightarrow> local y \<Longrightarrow> local (x; y)"
  apply (auto simp: local_def seq_def)
nitpick
  

end
