theory PHL
  imports MonoPredicateTransformers
begin

definition ht :: "'a :: bbi \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool"  where
  "ht p F q \<equiv> p \<le> F q"

lemma ht_skip: "p \<le> q \<Longrightarrow> ht p id q"
  by (simp add: ht_def)

lemma ht_skip': "ht p id p"
  by (simp add: ht_def)

lemma ht_strengthen: "p' \<le> p \<Longrightarrow> ht p F q \<Longrightarrow> ht p' F q"
  by (simp add: ht_def)

lemma ht_choice: "ht p F q \<Longrightarrow> ht p G q \<Longrightarrow> ht p (F + G) q"
  apply (simp add: ht_def)
  by (metis le_supI2)

notation Sup.qstar ("_\<^sup>\<star>" [1000] 1000)
lemma ht_iteration: "ht p F q \<Longrightarrow> ht p F\<^sup>\<star> q"
  apply (simp add: ht_def)
  by (metis (erased, hide_lams) Sup.order_trans Sup.qisol Sup.qstar_unfoldl_var le_fun_def quantale_unital_class.Sup.qstar_ref qunitr_fun)

lift_definition ht_mono :: "'a :: bbi \<Rightarrow> 'a mtran \<Rightarrow> 'a \<Rightarrow> bool" is "\<lambda>p F q. ht p F q" .

lemma ht_weaken': "q \<le> q' \<Longrightarrow> ht p F q \<Longrightarrow> ht p F q'"
  (* nitpick *) oops

lemma ht_weaken: "q \<le> q' \<Longrightarrow> ht_mono p F q \<Longrightarrow> ht_mono p F q'"
  apply transfer
  apply (simp add: ht_def)
  by (metis mono_def order_trans)

lemma ht_seq: "ht p F r \<Longrightarrow> ht r G q \<Longrightarrow> ht p (F \<cdot> G) q"
  (* nitpick *) oops

lemma ht_seq: "ht_mono p F r \<Longrightarrow> ht_mono r G q \<Longrightarrow> ht_mono p (F \<cdot> G) q"
  apply transfer
  apply (simp add: ht_def)
  by (metis Sup.order_trans monoE)

end
