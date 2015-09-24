theory AddPredicateTransformers
  imports MonoPredicateTransformers
begin

definition additive :: "('a :: bbi \<Rightarrow> 'b :: bbi) \<Rightarrow> bool" where
  "additive f \<equiv> \<forall>x y. f (x + y) = f x + f y"

definition comp_additive :: "('a :: bbi \<Rightarrow> 'b :: bbi) \<Rightarrow> bool" where
  "comp_additive f \<equiv> \<forall>X. f (\<Squnion>X) = \<Squnion>{f x | x. x \<in> X}"

lemma comp_add_addI: "comp_additive f \<Longrightarrow> additive f"
proof (auto simp: comp_additive_def additive_def)
  fix x y assume "\<forall>X. f (\<Squnion>X) = \<Squnion>{f x |x. x \<in> X}"
  hence "f (\<Squnion>{x, y}) = \<Squnion>{f z |z. z \<in> {x, y}}" by metis
  thus "f (x + y) = f x + f y"
    by (auto intro!: Sup_eqI) metis+
qed

lemma add_mono[dest?]: "additive F \<Longrightarrow> mono F"
  by (auto simp add: mono_def additive_def) (metis le_iff_sup)

lemma comp_add_mono[dest?]: "comp_additive F \<Longrightarrow> mono F"
  by (metis add_mono comp_add_addI)

text {* Closed operations *}

lemma comp_additive_skip [simp,intro]: "comp_additive id"
  by (simp add: comp_additive_def)

lemma comp_additive_comp_clos [intro]: "\<lbrakk>comp_additive (F :: 'a :: bbi \<Rightarrow> 'a); comp_additive (G :: 'a :: bbi \<Rightarrow> 'a)\<rbrakk> \<Longrightarrow> comp_additive (F o G)"
  by (auto simp: comp_additive_def intro!: Sup_eqI Sup_upper Sup_least) force

lemma comp_additive_abort [simp,intro]: "comp_additive \<bottom>"
  by (simp add: comp_additive_def)

lemma comp_additive_sup_clos [intro]: "\<lbrakk>comp_additive F; comp_additive G\<rbrakk> \<Longrightarrow> comp_additive (F + G)"
  apply (auto simp: comp_additive_def intro!: Sup_eqI[symmetric])
  apply (rule le_supI1, auto intro!: Sup_least Sup_upper)
  by (auto intro!: le_supI2 Sup_upper)

text {* Meet and top are not closed under complete additivity *}

lemma comp_additive_inf_clos [intro]: "\<lbrakk>comp_additive F; comp_additive G\<rbrakk> \<Longrightarrow> comp_additive (F \<sqinter> G)"
  (* nitpick *) oops

lemma comp_additive_magic [simp,intro]: "comp_additive \<top>"
  (* nitpick *) oops

lemma comp_additive_Sup_clos [intro]: "\<forall>f \<in> F. comp_additive f \<Longrightarrow> comp_additive (\<Squnion>F)"
proof (simp add: comp_additive_def, rule allI)
  fix X
  assume assm: "\<forall>f \<in> F. \<forall>X. f (\<Squnion>X) = \<Squnion>{f x |x. x \<in> X}"
  hence "(SUP f:F. f (\<Squnion>X)) = (SUP f:F. \<Squnion> {f x| x. x \<in> X})"
    by (auto intro: SUP_cong)
  also have "... = \<Squnion> {(SUP f:F. f x) | x. x \<in> X}"
    apply (auto intro!: Sup_eqI[symmetric])
    apply (rule SUP_mono)
    apply (rule_tac x=f in bexI)
    apply (rule Sup_upper)
    apply force
    apply simp
    apply (rule SUP_least)
    apply (rule Sup_least)
    apply auto
    by (metis SUP_upper dual_order.trans)
  finally show "(SUP f:F. f (\<Squnion>X)) = \<Squnion>{SUP f:F. f x |x. x \<in> X}"
    by auto
qed

text {* Type of additive predicate transformers *}

typedef 'a atran = "{F:: 'a :: bbi \<Rightarrow> 'a. comp_additive F}"
  by (rule_tac x=id in exI) (auto simp: comp_additive_def)
setup_lifting type_definition_atran

text {* Every additive predicate transformer is a monotonic one *}

lemma "\<forall>(F :: 'a :: bbi atran). \<exists>(G :: 'a mtran). Rep_mtran G = Rep_atran F"
  by transfer (auto intro: comp_add_mono)

text {* Morphism between additive to monotonic predicate transformers *}

lift_definition mptran :: "'a :: bbi atran \<Rightarrow> 'a mtran" is "\<lambda>F. F"
  by (metis comp_add_mono)

instantiation atran :: (bbi) bounded_semilattice_sup_bot
begin
lift_definition bot_atran :: "'a atran" is \<bottom> ..
lift_definition less_eq_atran:: "'a atran \<Rightarrow> 'a atran \<Rightarrow> bool" is "op \<le>" .
lift_definition less_atran :: "'a atran \<Rightarrow> 'a atran \<Rightarrow> bool" is "op <" .
lift_definition sup_atran :: "'a atran \<Rightarrow> 'a atran \<Rightarrow> 'a atran" is sup ..
instance
  by default (transfer, auto)+
end

text {* Complete additive predicate transformers form a complete join-semilattice*}

instantiation atran :: (bbi) Sup
begin
lift_definition Sup_atran :: "'a atran set \<Rightarrow> 'a atran" is Sup by auto
instance ..
end

text {* 
  All complete join semilattice for a complete lattice.
  Note that meet and top are different from the complete lattice formed by ptran
*}

instantiation atran :: (bbi) complete_lattice
begin

definition "\<Sqinter>(F :: 'a atran set) \<equiv> \<Squnion>{g. \<forall>f \<in> F. g \<le> f}"
definition "\<top> :: 'a atran \<equiv> \<Sqinter>{}"
definition "(F :: 'a atran) \<sqinter> G \<equiv> \<Sqinter>{F, G}"

instance 
  apply (default, simp_all add: inf_atran_def Inf_atran_def top_atran_def)
  by (transfer, auto intro: Sup_least Sup_upper Inf_greatest Inf_lower)+
end

text {*
  It forms a monoid
*}

instantiation atran :: (bbi) monoid_mult
begin
lift_definition one_atran :: "'a atran" is "id" ..
lift_definition times_atran :: "'a atran \<Rightarrow> 'a atran \<Rightarrow> 'a atran" is "op o" ..
instance 
  by default (transfer, auto)+
end

text {*
  It forms a Quantale
*}

instance atran :: (bbi) near_quantale
  by default (transfer, auto)

instance atran :: (bbi) near_quantale_unital ..

instance atran :: (bbi) pre_quantale
  apply (default, transfer, drule comp_add_mono)
  apply (rule mono_qSup_subdistl)
  by simp

instance atran :: (bbi) quantale
apply default
apply transfer
apply (simp add: comp_additive_def)
apply (rule le_funI)
apply simp
apply (unfold SUP_def)
apply (erule_tac x="((\<lambda>f. f xa) ` Y)" in allE) 
apply simp
apply (rule Sup_least)
apply (unfold SUP_def)
apply (rule Sup_upper)
by auto

instance atran :: (bbi) quantale_unital ..

end
