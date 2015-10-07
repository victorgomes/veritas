theory Heap
  imports Main "../Algebra/PartialMonoid"
begin

section {* Heaplet Model *}

type_synonym heap = "nat \<Rightarrow> nat option"

definition ortho :: "(nat \<Rightarrow> nat option) \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

lemma theI: "h x = Some y \<Longrightarrow> the (h x) = y"
  by simp

lemma heap_divider: "h1 \<bottom> h2 \<Longrightarrow> h1 x = Some y \<Longrightarrow> (h1 ++ h2) x = Some y"
  by (auto simp: ortho_def map_add_def split: option.splits)

lemma heap_add_comm: "h1 \<bottom> h2 \<Longrightarrow> h1 ++ h2 = h2 ++ h1"
  by (auto simp: ortho_def intro: map_add_comm)

interpretation partial_comm_monoid map_add ortho Map.empty
  by default (auto simp: ortho_def intro: map_add_comm)

lemma heap_split: "h x = Some y \<Longrightarrow> h = [x \<mapsto> y] ++ h(x := None)"
  by (metis (mono_tags, lifting) domIff empty_map_add fun_upd_same fun_upd_triv fun_upd_upd map_add_upd_left)

end