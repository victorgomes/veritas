theory Quantale
  imports "$AFP/Kleene_Algebra/Kleene_Algebra"
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 65) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)


no_notation
  star ("_\<^sup>\<star>" [101] 100)
  
class near_quantale = complete_lattice + semigroup_mult +
  assumes Sup_mult_distr: "\<Squnion>X \<cdot> y = (\<Squnion>x \<in> X. x \<cdot> y)"
begin

lemma Sup_mult_distr': "\<Squnion>{x. P(x)} \<cdot> y = \<Squnion>{x \<cdot> y |x. P(x)}"
  using Sup_mult_distr[of "{x. P(x)}"]
  by (metis Sup.SUP_def image_Collect) 

lemma mult_distr: "(x \<squnion> y) \<cdot> z = (x \<cdot> z) \<squnion> (y \<cdot> z)"
  using Sup_mult_distr[of "{x, y}"] by auto

sublocale ab_near_semiring "op \<squnion>"
  by default (simp_all add: sup.commute mult_distr sup_left_commute)

sublocale near_dioid "op \<squnion>"
  apply default
  apply auto
  apply (simp add: local.le_iff_sup)+
done

lemma mult_inf_subdistr: "(x \<sqinter> y) \<cdot> z \<le> (x \<cdot> z) \<sqinter> (y \<cdot> z)"
  by (metis local.inf.bounded_iff local.inf_le1 local.inf_le2 local.mult_isor)
  
lemma mult_Inf_subdistr: "\<Sqinter>X \<cdot> y \<le> (\<Sqinter>x \<in> X. x \<cdot> y)"
  by (metis INF_greatest Inf_lower mult_isor)


end

class pre_quantale = near_quantale +
  assumes Sup_mult_subdistl: "(\<Squnion>x \<in> X. y \<cdot> x) \<le> y \<cdot> \<Squnion>X"
begin

lemma mult_subdistl: "z \<cdot> x \<le> z \<cdot> (x \<squnion> y)"
  using Sup_mult_subdistl[of "{x, y}"] by auto

sublocale pre_dioid "op \<squnion>"
  by default (fact mult_subdistl)
  
lemma mult_inf_subdistl: "x \<cdot> (y \<sqinter> z) \<le> (x \<cdot> y) \<sqinter> (x \<cdot> z)"
  by (metis local.inf.bounded_iff local.inf_le1 local.inf_le2 local.mult_isol)
  
lemma mult_INF_subdistr: "y \<cdot> \<Sqinter>X \<le> (\<Sqinter>x \<in> X. y \<cdot> x)"
  by (metis INF_greatest Inf_lower mult_isol)
 
lemma mult_Inf_subdistr: "y \<cdot> \<Sqinter>X \<le> \<Sqinter>((\<lambda>x. y \<cdot> x) ` X)"
  by (auto simp: mult_INF_subdistr)

end

class quantale = near_quantale +
  assumes Sup_mult_distl: "y \<cdot> \<Squnion>X = (\<Squnion>x \<in> X. y \<cdot> x)"
begin

lemma Sup_mult_distl': "y \<cdot> \<Squnion>{x. P(x)} = \<Squnion>{y \<cdot> x | x. P(x)}"
  using Sup_mult_distl[of _ "{x. P(x)}"]
  by (metis Sup.SUP_def image_Collect)

lemma mult_distl: "x \<cdot> (y \<squnion> z) = (x \<cdot> y) \<squnion> (x \<cdot> z)"
  using Sup_mult_distl[of x "{y, z}"] by auto

subclass pre_quantale
  by default (force simp: Sup_mult_distl intro: antisym)

sublocale dioid "op \<squnion>"
  by default (simp_all add: mult_distr mult_distl)

end

class near_quantale_unital = near_quantale + monoid_mult
begin

lemma mult_annil [simp]: "\<bottom> \<cdot> x = \<bottom>"
  using Sup_mult_distr[of "{}"] by auto

sublocale near_dioid_one_zerol "op \<squnion>" _ _ \<bottom>
  by default auto

primrec iter :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "iter x 0 = 1"
| "iter x (Suc n) = iter x n \<cdot> x"

definition iteration :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100) where
  "x\<^sup>\<star> \<equiv> \<Sqinter>{y. 1 \<squnion> y \<cdot> x \<le> y}"

lemma iter_eq: "x\<^sup>\<star> = \<Squnion>{y. \<exists>n. y = iter x n}"
  apply (simp add: iteration_def)
  apply (rule antisym)
  defer
  apply (rule Sup_least)
  apply (rule Inf_greatest)
  apply clarsimp
  apply (induct_tac n)
  apply simp
  apply (metis local.iter.simps(2) local.mult_isor local.order_trans)
  apply (rule Inf_lower)
  apply auto
  apply (rule Sup_upper)
  apply clarsimp
  apply (rule_tac x=0 in exI)
  apply force
  apply (subst Sup_mult_distr')
  apply (rule Sup_mono)
  apply clarsimp
  apply (rule_tac x="iter x (Suc n)" in exI)
  apply clarsimp
  apply (rule_tac x="Suc n" in exI)
  apply clarsimp
done

lemma iter_mult: "x \<cdot> (iter x n) = (iter x n) \<cdot> x"
  apply (induct n)
  apply simp+
  apply (metis mult_assoc)
done

lemma iteration_ref: "1 \<le> x\<^sup>\<star>"
  unfolding iteration_def by (auto intro: Inf_greatest)

lemma iteration_1r: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  apply (auto simp: iteration_def Inf_Sup Sup_mult_distr intro!: Sup_upper SUP_least)
  by (metis local.mult_isor local.order_trans)
  
lemma iteration_unfoldr: "1 \<squnion> x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  by (metis iteration_1r iteration_ref local.le_sup_iff)

lemma iter_right_lfp: "lfp (\<lambda>x. 1 \<squnion> x \<cdot> y) = y\<^sup>\<star>"
  apply (rule antisym, metis iteration_unfoldr lfp_lowerbound)
  by (force simp: iteration_def intro!: Inf_lower lfp_greatest)
  
lemma iteration_inductr': "1 \<squnion> y \<cdot> x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  unfolding iteration_def using Inf_lower by auto
  
lemma iteration_inductr: "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  (* nitpick *) oops
  
lemma star_ext: "x \<le> x\<^sup>\<star>"
  unfolding iteration_def apply (auto intro!: Inf_greatest)
  by (metis local.dual_order.trans local.mult_isor local.mult_onel)

end

class pre_quantale_unital = pre_quantale + monoid_mult
begin

subclass near_quantale_unital ..

sublocale pre_dioid_one_zerol "op \<squnion>" _ _ \<bottom> ..

lemma iteration_inductr: "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  (* nitpick *) oops
  
lemma iteration_inductl: "z \<squnion> x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  apply (simp add: iter_eq Sup_mult_distr')
  apply (rule Sup_least)
  apply auto
  apply (induct_tac n)
  apply simp+
  by (metis iter_mult local.mult_isol mult_assoc order_trans)
  
end

class quantale_unital = quantale + monoid_mult
begin

subclass pre_quantale_unital ..

lemma mult_annir [simp]: "x \<cdot> \<bottom> = \<bottom>"
  using Sup_mult_distl[of x "{}"] by auto

sublocale dioid_one_zero "op \<squnion>" _ _ \<bottom>
  by default auto

lemma iteration_1l: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  apply (simp add: iter_eq Sup_mult_distl')
  apply (rule Sup_mono)
  apply auto
  apply (rule_tac x="iter x (Suc n)" in exI)
  apply auto
  apply (rule_tac x="Suc n" in exI)
  apply clarsimp
  apply (induct_tac n)
  apply simp+
  by (metis local.mult_isor mult_assoc)
  
lemma iteration_unfoldl: "1 \<squnion> x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis iteration_1l iteration_ref local.le_sup_iff)
  
lemma iteration_inductr: "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  apply (simp add: iter_eq Sup_mult_distl')
  apply (rule Sup_least)
  apply auto
  apply (induct_tac n)
  apply simp+
  by (metis local.mult_isor mult_assoc order_trans)
  
sublocale ka: kleene_algebra "op \<squnion>" _ _ \<bottom> _ _ iteration
  apply default
  apply (auto intro: iteration_inductl iteration_inductr iteration_1l iteration_ref)
done
  
lemma "\<forall>x y. x \<le> y \<longrightarrow> F x \<le> F y \<Longrightarrow> \<forall>p r. (F p) * r \<le> F (p * r) \<Longrightarrow> p \<le> F q \<longleftrightarrow> (\<forall>r. \<Squnion>{m. q * m \<le> r} \<le> \<Squnion>{m. p * m \<le> F r})"
  apply default
  apply (rule allI)
  apply (rule Sup_mono)  
  apply clarsimp
  apply (rule_tac x=a in exI)
  apply (rule conjI)
  apply (metis local.mult_isor local.order_trans)
  apply simp
  apply (erule_tac x=q in allE) back back
  apply (subgoal_tac "1 \<le> \<Squnion>{m. q \<cdot> m \<le> q}")
  apply (subgoal_tac "1 \<le> \<Squnion>{m. p \<cdot> m \<le> F q}")
  defer
  apply (metis local.dual_order.trans)
  apply (rule Sup_upper)
  apply clarsimp
  proof -
    assume "1 \<le> \<Squnion>{m. p \<cdot> m \<le> F q}"
    hence "p \<le> p * \<Squnion>{m. p \<cdot> m \<le> F q}"
      by (metis local.mult_1_right local.mult_isol_var local.order.refl)
    also have "... = \<Squnion>{p * m| m. p \<cdot> m \<le> F q}"
      apply (insert Sup_mult_distl[of p "{m. p \<cdot> m \<le> F q}"])
      apply auto
      by (metis Sup.Sup_image_eq image_Collect)
    also have "... \<le> F q"
      apply (rule Sup_least)
      by auto
    finally show "p \<le> F q" by metis
  qed

lemma "\<forall>x y. x \<le> y \<longrightarrow> F x \<le> F y \<Longrightarrow> \<forall>p q. p \<le> F q \<longleftrightarrow> (\<forall>r. \<Squnion>{m. q * m \<le> r} \<le> \<Squnion>{m. p * m \<le> F r}) \<Longrightarrow> (F p) * r \<le> F (p * r)"
  apply (erule_tac x="F p" in allE) back
  apply (erule_tac x=p in allE) back
  apply simp
  apply (erule_tac x="p*r" in allE) back
  apply (subgoal_tac "r \<le> \<Squnion>{m. p \<cdot> m \<le> p \<cdot> r}")
  apply (subgoal_tac "r \<le> \<Squnion>{m. F p \<cdot> m \<le> F (p \<cdot> r)}")
  defer
  apply (metis local.dual_order.trans)
  apply (rule Sup_upper)
  apply clarsimp
  proof -
    assume "r \<le> \<Squnion>{m. F p \<cdot> m \<le> F (p \<cdot> r)}"
    hence "F p * r \<le> F p * \<Squnion>{m. F p \<cdot> m \<le> F (p \<cdot> r)}"
      by (metis local.mult_isol_var local.order.refl)
    also have "... = \<Squnion>{F p * m | m. F p \<cdot> m \<le> F (p \<cdot> r)}"
      apply (insert Sup_mult_distl[of _ "{m. F p \<cdot> m \<le> F (p \<cdot> r)}"])
      apply auto
      by (metis Sup.Sup_image_eq image_Collect)
    also have "... \<le> F (p * r)"
      apply (rule Sup_least)
      by auto
    finally show "F p \<cdot> r \<le> F (p \<cdot> r)" by metis
  qed
end

class distrib_quantale = complete_distrib_lattice + quantale

class distrib_quantale_unital = distrib_quantale + quantale_unital

class comm_near_quantale = near_quantale + ab_semigroup_mult

class comm_pre_quantale = pre_quantale + ab_semigroup_mult

subclass (in comm_pre_quantale)  comm_near_quantale ..

class comm_quantale = quantale + ab_semigroup_mult

subclass (in comm_quantale) comm_pre_quantale ..

class comm_near_quantale_unital = near_quantale + comm_monoid_mult

subclass (in comm_near_quantale_unital) comm_near_quantale ..

subclass (in comm_near_quantale_unital) near_quantale_unital ..

class comm_pre_quantale_unital = pre_quantale + comm_monoid_mult

subclass (in comm_pre_quantale_unital) comm_near_quantale ..

subclass (in comm_pre_quantale_unital) near_quantale_unital ..

class comm_quantale_unital = quantale + comm_monoid_mult

subclass (in comm_quantale_unital) comm_near_quantale ..

subclass (in comm_quantale_unital) near_quantale_unital ..

class distrib_comm_quantale_unital = distrib_quantale + comm_quantale_unital

class boolean_quantale_unital = quantale_unital + complete_boolean_algebra

class boolean_comm_quantale_unital = boolean_quantale_unital + comm_quantale

end
