theory ConjPredicateTransformers
  imports MonoPredicateTransformers
begin

definition conjunctive :: "('a :: bbi \<Rightarrow> 'b :: bbi) \<Rightarrow> bool" where
  "conjunctive f \<equiv> \<forall>x y. f (x \<sqinter> y) = f x \<sqinter> f y"

definition comp_conjunctive :: "('a :: bbi \<Rightarrow> 'b :: bbi) \<Rightarrow> bool" where
  "comp_conjunctive f \<equiv> \<forall>X. f (\<Sqinter>X) = \<Sqinter>{f x | x. x \<in> X}"

lemma comp_conj_conjI: "comp_conjunctive f \<Longrightarrow> conjunctive f"
proof (auto simp: comp_conjunctive_def conjunctive_def)
  fix x y assume "\<forall>X. f (\<Sqinter>X) = \<Sqinter>{f x | x. x \<in> X}"
  hence "f (\<Sqinter>{x, y}) = \<Sqinter>{f z |z. z \<in> {x, y}}" by metis
  thus "f (x \<sqinter> y) = f x \<sqinter> f y"
    by (auto intro!: Inf_eqI) metis+
qed

lemma conj_mono[dest?]: "conjunctive F \<Longrightarrow> mono F"
  by (auto simp add: mono_def conjunctive_def) (metis le_iff_inf)

lemma conj_conj_mono[dest?]: "comp_conjunctive F \<Longrightarrow> mono F"
  by (auto intro: comp_conj_conjI conj_mono)

text {* Closed operations *}

lemma comp_conjunctive_skip [simp,intro]: "comp_conjunctive id"
  by (simp add: comp_conjunctive_def)

lemma comp_conjunctive_comp_clos [intro]: "\<lbrakk>comp_conjunctive (F :: 'a :: bbi \<Rightarrow> 'a); comp_conjunctive (G :: 'a :: bbi \<Rightarrow> 'a)\<rbrakk> \<Longrightarrow> comp_conjunctive (F o G)"
  by (auto simp: comp_conjunctive_def intro!: Inf_eqI Inf_lower Inf_greatest) force

lemma comp_conjunctive_magic [simp,intro]: "comp_conjunctive \<top>"
  by (simp add: comp_conjunctive_def)

lemma comp_conjunctive_inf_clos [intro]: "\<lbrakk>comp_conjunctive F; comp_conjunctive G\<rbrakk> \<Longrightarrow> comp_conjunctive (F \<sqinter> G)"
  apply (auto simp: comp_conjunctive_def intro!: Inf_eqI[symmetric])
  apply (rule le_infI1, auto intro!: Inf_lower Inf_greatest)
  by (auto intro!: le_infI2 Inf_lower)

text {* Meet and top are not closed under complete additivity *}

lemma comp_conjunctive_sup_clos [intro]: "\<lbrakk>comp_conjunctive F; comp_conjunctive G\<rbrakk> \<Longrightarrow> comp_conjunctive (F + G)"
  (* nitpick *) oops

lemma comp_conjunctive_abort [simp,intro]: "comp_conjunctive \<bottom>"
  (* nitpick *) oops

lemma comp_conjunctive_Inf_clos [intro]: "\<forall>f \<in> F. comp_conjunctive f \<Longrightarrow> comp_conjunctive (\<Sqinter>F)"
proof (simp add: comp_conjunctive_def, rule allI)
  fix X
  assume assm: "\<forall>f \<in> F. \<forall>X. f (\<Sqinter>X) = \<Sqinter>{f x |x. x \<in> X}"
  hence "(INF f:F. f (\<Sqinter>X)) = (INF f:F. \<Sqinter> {f x| x. x \<in> X})"
    by (auto intro: INF_cong)
  also have "... = \<Sqinter> {(INF f:F. f x) | x. x \<in> X}"
    apply (auto intro!: INF_eqI)
    apply (rule Inf_mono)
    apply auto
    apply (rule_tac x="(INF f:F. f x)" in exI)
    apply auto
    apply (rule INF_lower)
    apply simp
    apply (rule Inf_greatest)
    apply auto
    apply (rule INF_greatest)
    apply (subgoal_tac "\<Sqinter>{f x |x. x \<in> X} \<le> f xa")
    apply force
    apply (rule Inf_lower)
    by auto
  finally show "(INF f:F. f (\<Sqinter>X)) = \<Sqinter>{INF f:F. f x |x. x \<in> X}"
    by auto
qed

text {* Type of conjunctive predicate transformers *}

typedef 'a ctran = "{F:: 'a :: bbi \<Rightarrow> 'a. comp_conjunctive F}"
  by (rule_tac x=id in exI) (auto simp: comp_conjunctive_def)
setup_lifting type_definition_ctran

text {* Every conjunctive predicate transformer is a monotonic one *}

lemma "\<forall>(F :: 'a :: bbi ctran). \<exists>(G :: 'a mtran). Rep_mtran G = Rep_ctran F"
  by transfer (auto intro: conj_conj_mono)

text {* Morphism between conjunctive to monotonic predicate transformers *}

lift_definition mptran :: "'a :: bbi ctran \<Rightarrow> 'a mtran" is "\<lambda>F. F"
  by (metis conj_conj_mono)

text {* The order in the semilattice is inversed *}

instantiation ctran :: (bbi) bounded_semilattice_sup_bot
begin
lift_definition bot_ctran :: "'a ctran" is \<top> ..
lift_definition less_eq_ctran:: "'a ctran \<Rightarrow> 'a ctran \<Rightarrow> bool" is "op \<ge>" .
lift_definition less_ctran :: "'a ctran \<Rightarrow> 'a ctran \<Rightarrow> bool" is "op >" .
lift_definition sup_ctran :: "'a ctran \<Rightarrow> 'a ctran \<Rightarrow> 'a ctran" is inf ..
instance
  by default (transfer, auto)+
end

text {* Complete conjunctive predicate transformers form a complete join-semilattice*}

instantiation ctran :: (bbi) Sup
begin
lift_definition Sup_ctran :: "'a ctran set \<Rightarrow> 'a ctran" is Inf by auto
instance ..
end

text {* 
  All complete join semilattice for a complete lattice.
  Note that meet and top are different from the complete lattice formed by ptran
*}

instantiation ctran :: (bbi) complete_lattice
begin

definition "\<Sqinter>(F :: 'a ctran set) \<equiv> \<Squnion>{g. \<forall>f \<in> F. g \<le> f}"
definition "\<top> :: 'a ctran \<equiv> \<Sqinter>{}"
definition "(F :: 'a ctran) \<sqinter> G \<equiv> \<Sqinter>{F, G}"

instance 
  apply (default, simp_all add: inf_ctran_def Inf_ctran_def top_ctran_def)
  by (transfer, auto intro: Sup_least Sup_upper Inf_greatest Inf_lower)+
end

text {*
  It forms a monoid
*}

instantiation ctran :: (bbi) monoid_mult
begin
lift_definition one_ctran :: "'a ctran" is "id" ..
lift_definition times_ctran :: "'a ctran \<Rightarrow> 'a ctran \<Rightarrow> 'a ctran" is "op o" ..
instance 
  by default (transfer, auto)+
end

text {*
  It forms a Quantale
*}

instance ctran :: (bbi) near_quantale
  by default (transfer, auto)

instance ctran :: (bbi) near_quantale_unital ..

instance ctran :: (bbi) pre_quantale
  apply default
  apply transfer
  apply (rule le_funI)
  apply (simp add: comp_conjunctive_def)
  apply (unfold INF_def)
  apply (erule_tac x="((\<lambda>f. f xa) ` Y)" in allE) 
  apply simp
  apply (rule INF_greatest)
  apply (rule Inf_lower)
  by auto

instance ctran :: (bbi) quantale 
  apply default
  apply transfer
  apply (rule le_funI)
  apply (simp add: comp_conjunctive_def)
  apply (unfold INF_def)
  apply (erule_tac x="((\<lambda>f. f xa) ` Y)" in allE) 
  apply simp
  apply (rule Inf_greatest)
  apply (unfold INF_def)
  apply (rule Inf_lower)
  by auto

instance ctran :: (bbi) quantale_unital ..

end
