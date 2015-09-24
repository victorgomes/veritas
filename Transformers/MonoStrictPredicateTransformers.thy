theory MonoStrictPredicateTransformers
  imports PredicateTransformers
begin

section {* Monotonic predicate transformers *}

declare [[coercion_enabled]]

text {* Closed operations *}

lemma mono_skip [simp,intro]: "mono id \<and> id \<bottom> = \<bottom>"
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

typedef 'a mtran = "{F :: 'a :: bbi \<Rightarrow> 'a. mono F \<and> F \<bottom> = \<bottom>}" by auto
setup_lifting type_definition_mtran

declare [[coercion Rep_mtran]]

text {* It forms a monoid on respect to function aplication *}
instantiation mtran :: (bbi) monoid_mult
begin
  lift_definition one_mtran :: "'a mtran" is id ..
  lift_definition times_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> 'a mtran" is "op o" by auto
  instance
    by default (transfer, auto)+
end

text {* It forms a complete lattice *}
instantiation mtran :: (bbi) bounded_semilattice_sup_bot
begin
lift_definition bot_mtran :: "'a mtran" is \<bottom>  by auto
lift_definition sup_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> 'a mtran" is sup  by auto
lift_definition less_eq_mtran:: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> bool" is "op \<le>" . 
lift_definition less_mtran :: "'a mtran \<Rightarrow> 'a mtran \<Rightarrow> bool" is "op <" .
instance
  by default (transfer, auto)+
end

instantiation mtran :: (bbi) Sup
begin
lift_definition Sup_mtran :: "'a mtran set \<Rightarrow> 'a mtran" is Sup by auto
instance ..
end

instantiation mtran :: (bbi) complete_lattice
begin
definition "\<Sqinter>(F :: 'a mtran set) \<equiv> \<Squnion>{g. \<forall>f \<in> F. g \<le> f}"
definition "\<top> :: 'a mtran \<equiv> \<Sqinter>{}"
definition "(F :: 'a mtran) \<sqinter> G \<equiv> \<Sqinter>{F, G}"
instance 
  apply (default, simp_all add: inf_mtran_def Inf_mtran_def top_mtran_def)
  by (transfer, auto intro: Sup_least Sup_upper Inf_greatest Inf_lower)+
end

text {* It doesn't form a distributivity lattice *}
instance mtran :: (bbi) complete_distrib_lattice
  apply default defer (* nitpick *) oops

text {* It forms a pre quantale on respect to function aplication, but not a full quantale *}

instance mtran :: (bbi) near_quantale_unital 
  by default (transfer, auto)

lemma mono_qSup_subdistl: "mono (f :: 'a :: complete_lattice \<Rightarrow> 'a) \<Longrightarrow> \<Squnion>((\<lambda>g. f o g) ` G) \<le> f \<circ> \<Squnion>G"
  by (rule Sup_least) (auto intro!: le_funI order_class.monoD[of "\<lambda>x. f x"] SUP_upper)

instance mtran :: (bbi) pre_quantale
  by default (transfer, simp only: mono_qSup_subdistl)

instance mtran :: (bbi) quantale_unital
  apply default
  apply transfer
  apply (rule le_funI)
  
  apply simp
  apply (rule SUP_upper)
  apply auto

  (* nitpick, it needs to be strict monotone *) oops

end
