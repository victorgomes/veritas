theory PredicateTransformers
  imports "../Algebra/BBI"
begin

no_notation plus (infixl "+" 65)

text{* 
  Predicate transformers are functions from predicates to predicates, abstractly, from 
  commutative quantale unital to commutative quantale unital
*}

instantiation "fun" :: (quantale, quantale) quantale
begin

definition "F * G \<equiv> \<lambda>h. \<Squnion> {F f * G g | f g. h = f * g}"

lemma qmult_apply [simp, code]:
  "(F * G) h \<equiv>  \<Squnion> {F f * G g | f g. h = f * g}"
  by (simp add: times_fun_def)

lemma sup_distrib_left_fun: "(f * (g + h)) x = (f * g + f * h) x"
  by (subst qmult_apply, subst sup_apply, subst Sup.qdistl) simp

lemma sup_distrib_right_fun: "((f + g) * h) x = (f * h + g * h) x"
  by (subst qmult_apply, subst sup_apply, subst Sup.qdistr) simp

lemma qSup_distl_fun: "(f * \<Squnion>G) x = (\<Squnion>(op * f ` G)) x"
  apply (auto simp add: qSUP_distl intro!: antisym Sup_least SUP_mono)
  apply (metis (lifting, mono_tags) Sup_upper mem_Collect_eq)
  by (auto intro!: SUP_least Sup_mono) (metis SUP_upper)

lemma qSup_distr_fun: "(\<Squnion>G * f) x = (\<Squnion>((\<lambda>g. g * f) ` G)) x"
  apply (auto simp add: qSUP_distr intro!: antisym Sup_least SUP_mono)
  apply (metis (lifting, mono_tags) Sup_upper mem_Collect_eq)
  by (auto intro!: SUP_least Sup_mono) (metis SUP_upper)

lemma Sup_distl_assoc: "(f :: 'a \<Rightarrow> 'b) y * \<Squnion>{g y' * h z' |y' z' :: 'a. z = y' * z'} = \<Squnion>{f y * (g y' * h z') |y' z'. z = y' * z'}"
  by (auto simp only: Sup.Join_distl intro!: Sup.Join_eqI2)

lemma qSup_distr_assoc: "\<Squnion>{((f :: 'a \<Rightarrow> 'b) y * g y') | y y' :: 'a. z = (y * y')} * h z' = \<Squnion>{(f y * g y') * h z' | y y'. z = (y * y')}"
  by (auto simp only: qSup_distr intro: Sup.Join_eqI2)

lemma qmult_assoc_fun: "(f * (g * h)) x = ((f * g) * h) x"
proof -
  have "(f * (g * h)) x = \<Squnion> {\<Squnion> {(f y * g y') * h z' | y' z'. z = y' * z'} | y z. x = y * z}"
    by (simp add: Sup_distl_assoc mult.assoc)
  also have "... = \<Squnion> {(f y * g y') * h z' | y' z' y z. z = y' * z' \<and> x = y * z}"
    apply (rule antisym, rule Sup_least, safe, rule Sup_mono, auto, rule Sup_least, auto)
    apply (subgoal_tac "\<exists>ya z. y * (y' * z') = ya * z \<and> f y * g y' * h z' \<le> \<Squnion>{f ya * g y' * h z' |y' z'. z = y' * z'}")
    apply (smt Sup_upper2 mem_Collect_eq)
    by (smt Sup_le_iff dual_order.refl mem_Collect_eq)
  also have "... = \<Squnion> {(f y * g y') * h z' | z' y y'. x = y * (y' * z')}"
    by (auto intro: Sup.Join_eqI2)
  also have "... = \<Squnion> {(f y * g y') * h z' | z' y y'. x = (y * y') * z'}"
    by (metis mult.assoc)
  also have "... = \<Squnion> {(f y * g y') * h z' | z' y y' z. z = (y * y') \<and> x = z * z'}"
    by (auto intro: Sup.Join_eqI2)
  also have "... = \<Squnion>{ \<Squnion>{(f y * g y') * h z' | y y'. z = (y * y')} | z z'. x = z * z'}"
    apply (rule antisym, rule Sup_least, auto)  
    apply (subgoal_tac "\<exists>z z'a. y * y' * z' = z * z'a \<and> f y * g y' * h z' \<le> \<Squnion>{f y * g y' * h z'a |y y'. z = y * y'}")
    apply (smt Sup_upper2 mem_Collect_eq)
    apply (smt Sup_le_iff dual_order.refl mem_Collect_eq)
    by (rule Sup_least, safe, rule Sup_mono, auto)
  finally show ?thesis
    by (simp add: qSup_distr_assoc)
qed

instance
  apply default
  apply (rule ext, rule qmult_assoc_fun[symmetric])
  apply (rule ext, rule qSup_distr_fun)
  by (metis (lifting, mono_tags) qSup_distl_fun eq_iff le_funI)+
end

text {* Unit is also lifted *}

instantiation "fun" :: (quantale_unital, quantale_unital) quantale_unital
begin

definition
  "1 \<equiv> \<lambda>x. if x = 1 then 1 else \<bottom>"

lemma qunitl_fun[simp]: "(1 * f) x = f x"
  by (auto simp: one_fun_def intro!: Sup_eqI)

lemma qunitr_fun[simp]: "(f * 1) x = f x"
  by (auto simp: one_fun_def intro!: Sup_eqI)

instance
  by default  (auto intro: qunitr_fun qunitl_fun)

end

text {* Commutativity is also lifted *}

instance "fun" :: (comm_quantale, comm_quantale) comm_quantale
proof (default, simp_all add: mult.assoc, rule ext)
  fix f g :: "'a :: comm_quantale \<Rightarrow> 'b :: comm_quantale"
  fix x :: "'a :: comm_quantale"
  have "(f * g) x = \<Squnion> {f y * g z | y z. x = y * z}" by simp
  also have "... = \<Squnion> {g z * f y | z y. x = z * y}"
    by (auto intro!: Sup.Join_eqI2 mult.commute)
  finally show "(f * g) x = (g * f) x" by simp
qed

instance "fun" :: (comm_quantale_unital, comm_quantale_unital) comm_quantale_unital 
  by default auto

text {* Distributivity is also lifted *}

instance "fun" :: (distrib_quantale, distrib_quantale) distrib_quantale .. 

instance "fun" :: (distrib_comm_quantale_unital, distrib_comm_quantale_unital) distrib_comm_quantale_unital ..

text {* BBI *}

instance "fun" :: (bbi, bbi) bbi ..

end
