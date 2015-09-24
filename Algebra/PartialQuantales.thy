theory PartialQuantales
  imports PartialMonoid Quantale_Sup
begin

notation pmult_one ("1'")

text {*
  Quantales with \<Squnion> distributivity
*}

class partial_near_quantale = complete_lattice + partial_semigroup +
  assumes partial_qSup_distr: "\<forall>y \<in> Y. y ## x \<Longrightarrow> \<Squnion> Y * x = \<Squnion> ((\<lambda>y. y * x) ` Y)"

class partial_pre_quantale = partial_near_quantale +
  assumes partial_qSup_subdistl:  "\<forall>y \<in> Y. x ## y \<Longrightarrow> \<Squnion> ((\<lambda>y. x * y) ` Y) \<le> x * \<Squnion> Y"

class partial_quantale = partial_pre_quantale +
  assumes partial_qSup_supdistl: "\<forall>y \<in> Y. x ## y \<Longrightarrow> x * \<Squnion> Y \<le> \<Squnion> ((\<lambda>y. x * y) ` Y)" 
begin

lemma partial_qSup_distl: "\<forall>y \<in> Y. x ## y \<Longrightarrow> x * \<Squnion> Y = \<Squnion> ((\<lambda>y. x * y) ` Y)"
  by (metis antisym_conv partial_qSup_subdistl partial_qSup_supdistl)

end

(* Quantale with different signature, derived from partial mult *)
class near_quantale_pmult = partial_near_quantale + totality
begin
sublocale Sup_pmult!: near_quantale_Sup _ _ _ _ _ _ _ _ pmult
  apply (default, metis pmult_assoc totality)
  by (metis partial_qSup_distr totality)
end

class near_quantale_pmult_unital = near_quantale_pmult + partial_monoid
begin
sublocale Sup_pmult!: near_quantale_Sup_unital "1'" "op *" 
  by default (simp_all add: pmult_onel pmult_oner)

end

class pre_quantale_pmult = partial_pre_quantale + totality
begin
subclass near_quantale_pmult ..
sublocale Sup_pmult!: pre_quantale_Sup  _ _ _ _ _ _ _ _ pmult
  by default (metis partial_qSup_subdistl totality)
end

class quantale_pmult = partial_quantale + totality
begin
subclass pre_quantale_pmult ..
sublocale Sup_pmult!: quantale_Sup _ _ _ _ _ _ _ _ pmult
  by default (metis partial_qSup_supdistl totality)
end

class quantale_pmult_unital = near_quantale_pmult_unital + quantale_pmult
begin
sublocale Sup_pmult!: quantale_Sup_unital "1'" "op *" ..
end

class comm_quantale_pmult = quantale_pmult + partial_ab_semigroup
class comm_quantale_pmult_unital = quantale_pmult_unital + comm_quantale_pmult
class distrib_quantale_pmult = quantale_pmult + complete_distrib_lattice
class distrib_comm_quantale_pmult_unital = distrib_quantale_pmult + comm_quantale_pmult_unital

end
