theory Heap
  imports While Locality
begin

section {* Heap *}

type_synonym heap = "nat \<Rightarrow> nat option"

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

lemma theI: "h x = Some y \<Longrightarrow> the (h x) = y"
  by simp 

lemma heap_divider: "h1 \<bottom> h2 \<Longrightarrow> h1 x = Some y \<Longrightarrow> (h1 ++ h2) x = Some y"
  by (auto simp: ortho_def map_add_def split: option.splits)

lemma heap_add_comm: "h1 \<bottom> h2 \<Longrightarrow> h1 ++ h2 = h2 ++ h1"
  by (auto simp: ortho_def intro: map_add_comm)

lemma singl_ortho: "[x \<mapsto> y] \<bottom> h \<longleftrightarrow> x \<notin> dom h"
  by (auto simp: ortho_def)

interpretation heap?: locality "op ++" "op \<bottom>" Map.empty
  apply default
  apply (auto simp: ortho_def)
  using map_add_comm by blast

section {* Commands *}

lemma local_skip: "local \<langle>skip\<rangle>"
  by (auto simp: local_def skip_def stran_def)

lemma safe_skip: "safe skip"
  by (simp add: Local_local local_safe local_skip)

lemma frame_skip: "frame skip"
  by (simp add: Local_local local_frame local_skip)

definition lookup :: "(nat, 'a) lval \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a, heap) state rel" where
  "lookup u_upd t \<equiv> \<langle>\<lambda>\<sigma>. case \<sigma> of <s, h> \<Rightarrow> if t s \<in> dom h then <u_upd (\<lambda>_. the (h (t s))) s, h> else fault | fault \<Rightarrow> fault\<rangle>"

definition mutation :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a, heap) state rel" where
  "mutation u t \<equiv> \<langle>\<lambda>\<sigma>. case \<sigma> of <s, h> \<Rightarrow> if u s \<in> dom h then <s, h(u s \<mapsto> t s)> else fault | fault \<Rightarrow> fault\<rangle>"

lemma "safe (assign u_upd t)"
  by (auto simp add: safe_def assign_def graph_def)

lemma "frame (assign u_upd t)"
  by (auto simp add: frame_def assign_def graph_def)

lemma "safe (lookup u_upd t)"
  by (auto simp add: safe_def lookup_def graph_def substate_def)

lemma "frame (lookup u_upd t)"
  by (auto simp add: frame_def lookup_def graph_def)

lemma "safe (mutation u_upd t)"
  by (auto simp add: safe_def mutation_def graph_def substate_def)

lemma "frame (mutation u_upd t)"
  apply (clarsimp simp add: frame_def mutation_def graph_def ortho_def)
  by (metis disjoint_iff_not_equal domI map_add_upd_left)

lemma "safe (assign u_upt t)"
  by (auto simp: assign_def safe_def graph_def)

lemma "frame (assign u_upt t)"
  by (auto simp: assign_def frame_def graph_def)


no_notation heap.stran ("\<langle>_\<rangle>")
end
