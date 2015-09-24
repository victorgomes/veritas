theory MonoPredicateTransformers
  imports PredicateTransformers
begin

section {* Monotonic predicate transformers *}

declare [[coercion_enabled]]

text {* Closed operations *}

lemma mono_skip [simp,intro]: "mono id"
  by (auto intro: order_class.monoI)

lemma mono_ex [simp]: "\<exists>f :: 'a :: order \<Rightarrow> 'a. mono f"
  by (rule_tac x=id in exI) simp

lemma mono_comp_clos [intro]: "\<lbrakk>mono F; mono G\<rbrakk> \<Longrightarrow> mono (F o G)"
  by (auto simp: order_class.mono_def intro!: order_class.monoI)

lemma mono_magic [simp,intro]: "mono \<top>"
  by (simp add: order_class.mono_def)

lemma mono_abort [simp,intro]: "mono \<bottom>"
  by (simp add: order_class.mono_def)

lemma mono_sup_clos [intro]: "\<lbrakk>mono F; mono G\<rbrakk> \<Longrightarrow> mono (F + G)"
  by (auto simp: order_class.mono_def intro: sup.coboundedI1 sup.coboundedI2)

lemma mono_inf_clos [intro]: "\<lbrakk>mono F; mono G\<rbrakk> \<Longrightarrow> mono (F \<sqinter> G)"
  by (auto simp: order_class.mono_def intro: inf.coboundedI1 inf.coboundedI2)

text {* The lifting of * is not isotonic closed  *}
lemma mono_inf_clos [intro]: "\<lbrakk>mono F; mono G\<rbrakk> \<Longrightarrow> mono (F * G)"
  (* nitpick[show_all] *) oops   

lemma mono_Sup_clos [intro]: "\<forall>(f :: 'a :: complete_lattice \<Rightarrow> 'a) \<in> F. mono f \<Longrightarrow> mono (\<Squnion> F)"
  by (auto simp: order_class.mono_def, rule SUP_mono) auto

lemma mono_Inf_clos [intro]: "\<forall>(f :: 'a :: complete_lattice \<Rightarrow> 'a) \<in> F. mono f \<Longrightarrow> mono (\<Sqinter> F)"
  by (auto simp: order_class.mono_def, rule INF_mono) auto

text {* Type of monotonic predicate transformers *}

typedef 'a mtran = "{F :: 'a :: bbi \<Rightarrow> 'a. mono F}" by simp
setup_lifting type_definition_mtran

declare [[coercion Rep_mtran]]

text {* It forms a monoid on respect to function aplication *}
instantiation mtran :: (bbi) monoid_mult
begin
  lift_definition one_mtran :: "'a mtran" is id ..
  lift_definition times_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> 'a mtran" is "op o" ..
  instance
    by default (transfer, auto)+
end

text {* It forms a complete lattice *}
instantiation mtran :: (bbi) bounded_lattice
begin
lift_definition bot_mtran :: "'a mtran" is \<bottom>  ..
lift_definition sup_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> 'a mtran" is sup ..
lift_definition top_mtran :: "'a mtran" is \<top>  ..
lift_definition inf_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> 'a mtran" is inf ..
lift_definition less_eq_mtran:: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> bool" is "op \<le>" . 
lift_definition less_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> bool" is "op <" .
instance
  by default (transfer, auto)+
end

instantiation mtran :: (bbi) complete_lattice
begin
lift_definition Inf_mtran :: "'a mtran set \<Rightarrow> 'a mtran" is Inf by auto
lift_definition Sup_mtran :: "'a mtran set \<Rightarrow> 'a mtran" is Sup by auto
instance
  by default (transfer, auto intro: Inf_lower Inf_greatest Sup_upper Sup_least)+
end

text {* It doesn't form a distributivity lattice *}
instance mtran :: (bbi) complete_distrib_lattice
  apply default defer (* nitpick *) oops

text {* It forms a pre quantale on respect to function aplication, but not a full quantale *}

instance mtran :: (bbi) near_quantale_Sup_unital 
  by default (transfer, auto)

lemma mono_qSup_subdistl: "mono (f :: 'a :: complete_lattice \<Rightarrow> 'a) \<Longrightarrow> \<Squnion>((\<lambda>g. f o g) ` G) \<le> f \<circ> \<Squnion>G"
  by (rule Sup_least) (auto intro!: le_funI order_class.monoD[of "\<lambda>x. f x"] SUP_upper)

instance mtran :: (bbi) pre_quantale_Sup
  by default (transfer, simp only: mono_qSup_subdistl)

instance mtran :: (bbi) quantale_Sup_unital
  (* nitpick, it needs to be strict monotone *) oops

end
