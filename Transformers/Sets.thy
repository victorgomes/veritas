theory Sets
  imports "../Algebra/PartialQuantales"
begin

section {* Resource Predicates *}

text {* A resource predicate is a set on a partial monoid. *}

text {* The powerset lifting of a partial semigroup form a quantale *}

instantiation "set" :: (partial_semigroup) near_quantale_pmult
begin
definition "P \<oplus> Q \<equiv> {x \<oplus> y | x y. x ## y \<and> x \<in> P \<and> y \<in> Q}"
definition "(P :: 'a set) ## Q \<equiv> True"
declare pmult_defined_set_def[simp]

lemma [simp]: "(P :: 'a set) ## Q \<oplus> R" 
  by (simp add: pmult_set_def)

lemma [simp]: "(P :: 'a set) \<oplus> Q ## R" 
  by (simp add: pmult_set_def)

instance
  apply (default, auto simp: pmult_set_def)
  apply (metis partial_semigroup_class.pmult_assoc partial_semigroup_class.pmult_def)
  by (metis partial_semigroup_class.pmult_assoc partial_semigroup_class.pmult_def)
end

instance "set" :: (partial_semigroup) pre_quantale_pmult
  by default (auto simp: pmult_set_def)

instance "set" :: (partial_semigroup) quantale_pmult
  by default (auto simp: pmult_set_def)

text {* Unit, commutativity and distributivity are also lifted. *}

instantiation "set" :: (partial_monoid) near_quantale_pmult_unital
begin
definition "1' \<equiv> {1'}"
instance
  by default (auto simp: pmult_set_def pmult_one_set_def pmult_oner pmult_onel)
end

instance "set" :: (partial_ab_semigroup) comm_quantale_pmult
  apply (default, auto simp: pmult_set_def)
  apply (metis pmult_ab_assoc pmult_def_eq)
  by (metis pmult_ab_assoc pmult_def_eq pmult_comm pmult_comm_def)+

instance "set" :: (partial_monoid) quantale_pmult_unital ..

instance "set" :: (partial_comm_monoid) comm_quantale_pmult_unital ..

instance "set" :: (partial_semigroup) distrib_quantale_pmult ..

instance "set" :: (partial_comm_monoid) distrib_comm_quantale_pmult_unital ..

end
