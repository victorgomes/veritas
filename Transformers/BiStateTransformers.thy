theory BiStateTransformers
  imports "../Algebra/PartialQuantales" "../Algebra/BBI"
begin

no_notation plus (infixl "+" 65)
no_notation pmult (infixl "*" 80)
no_notation pmult_one ("1")
notation pmult (infixl "\<oplus>" 80)
notation times (infixl "*" 70)
notation sup (infixl "+" 65)
notation inf (infixl "\<sqinter>" 70)
notation one_class.one ("1")

text {*
  We extend the state transformers to two dimensions (to accommodate store and heap)
*}

declare [[coercion_enabled]]
typedef ('a, 'b, 'c) bifun = "{f :: ('a \<times> 'b \<Rightarrow> 'c). True}" by auto
declare [[coercion Rep_bifun]]
setup_lifting type_definition_bifun

instantiation bifun :: (type, type, complete_lattice) bounded_lattice
begin
lift_definition bot_bifun :: "('a, 'b, 'c) bifun" is bot ..
lift_definition sup_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun" is sup ..
lift_definition top_bifun :: "('a, 'b, 'c) bifun" is top ..
lift_definition inf_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun" is inf ..
lift_definition less_eq_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun \<Rightarrow> bool" is less_eq .
lift_definition less_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun \<Rightarrow> bool" is less .
instance 
  by default (transfer, auto)+
end

instantiation bifun :: (type, type, complete_lattice) complete_lattice
begin
lift_definition Inf_bifun :: "('a, 'b, 'c) bifun set \<Rightarrow> ('a, 'b, 'c) bifun" is Inf ..
lift_definition Sup_bifun :: "('a, 'b, 'c) bifun set \<Rightarrow> ('a, 'b, 'c) bifun" is Sup ..
instance 
  by default (transfer, auto intro: Sup_least Sup_upper Inf_greatest Inf_lower)+
end

instance bifun :: (type, type, complete_distrib_lattice) complete_distrib_lattice
apply default
apply (unfold INF_def)
apply transfer
apply auto
apply (metis sup_Inf)
apply (unfold SUP_def)
apply transfer
apply auto
by (metis inf_Sup)


instantiation bifun :: (type, partial_semigroup, quantale) quantale
begin

lift_definition times_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun"
  is "\<lambda>f g (x, y). \<Squnion> {f (x, y1) * g (x, y2) | y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2}" ..

lemma ext_bifun [intro]: "(\<And>x y. Rep_bifun f (x, y) = Rep_bifun g (x, y)) \<Longrightarrow> (f :: ('a, 'b, 'c) bifun) = g"
  apply transfer
  by auto

lemma le_bifunI [intro]: "(\<And>x y. Rep_bifun f (x, y) \<le> Rep_bifun g (x, y)) \<Longrightarrow> f \<le> g"
  apply transfer
  by (metis PairE le_funI)

lemma qmult_bifun_apply [simp, code]:
  "((f :: ('a, 'b, 'c) bifun) * g) (x, y) = \<Squnion> {f (x, y1) * g (x, y2) | y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2}"
  by transfer auto

lemma sup_distrib_left_bifun: "((f :: ('a, 'b, 'c) bifun) * (g + h)) (x, y) = (f * g + f * h) (x, y)"
  apply transfer
  apply auto
  apply (subst Sup.qdistl)
  by simp

lemma sup_distrib_right_bifun: "(((f :: ('a, 'b, 'c) bifun) + g) * h) x = (f * h + g * h) x"
  apply transfer
  apply auto
  apply (subst Sup.qdistr)
  by simp

lemma qSup_distl_bifun: "((f :: ('a, 'b, 'c) bifun) * \<Squnion>G) x = (\<Squnion>(op * f ` G)) x"
  apply transfer
  apply (auto simp add: qSUP_distl intro!: antisym Sup_least SUP_mono)
  apply (rule_tac x=xa in bexI)
  apply (rule Sup_upper)
  apply auto
  apply (rule SUP_least)
  apply (rule Sup_mono)
  apply auto
  by (metis (mono_tags) SUP_upper)

lemma qSup_distr_bifun: "(\<Squnion>G * (f :: ('a, 'b, 'c) bifun)) x = (\<Squnion>((\<lambda>g. g * f) ` G)) x"
  apply transfer
  apply (auto simp add: qSUP_distr intro!: antisym Sup_least SUP_mono)
  apply (rule_tac x=xa in bexI)
  apply (rule Sup_upper)
  apply auto
  apply (rule SUP_least)
  apply (rule Sup_mono)
  apply auto
  by (metis (mono_tags) SUP_upper)

lemma Sup_distl_assoc_bifun: "(f :: ('a, 'b, 'c) bifun) (x, y1) * \<Squnion>{g (x, y2) * h (x, y3) |y2 y3. y = y2 \<oplus> y3 \<and> y2 ## y3} = \<Squnion>{f (x, y1) * (g (x, y2) * h (x, y3)) |y2 y3. y = y2 \<oplus> y3 \<and> y2 ## y3}"
  by (auto simp only: Sup.Join_distl intro: Sup.Join_eqI2)

lemma qSup_distr_assoc_bifun: "\<Squnion>{((f :: ('a, 'b, 'c) bifun) (x, y1) * g (x, y2)) | y1 y2. y = (y1 \<oplus> y2) \<and> y1 ## y2} * h (x, y3) = \<Squnion>{(f (x, y1) * g (x, y2)) * h (x, y3) | y1 y2. y = (y1 \<oplus> y2) \<and> y1 ## y2}"
  by (auto simp only: qSup_distr intro: Sup.Join_eqI2)

lemma qmult_assoc_bifun: "((f :: ('a, 'b, 'c) bifun) * (g * h)) (x, y) = ((f * g) * h) (x, y)"
proof simp
  have "\<Squnion>{f (x, y1) * \<Squnion>{g (x, y1) * h (x, y2a) |y1 y2a. y2 = y1 \<oplus> y2a \<and> y1 ## y2a} |y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2} =
    \<Squnion>{\<Squnion>{f (x, y1) * (g (x, y1a) * h (x, y2a)) |y1a y2a. y2 = y1a \<oplus> y2a \<and> y1a ## y2a} |y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2}"
    by (unfold Sup_distl_assoc_bifun) simp
  also have "... = \<Squnion>{\<Squnion>{(f (x, y1) * g (x, y1a)) * h (x, y2a) |y1a y2a. y2 = y1a \<oplus> y2a \<and> y1a ## y2a} |y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2}"
    by (subst mult.assoc) simp
  also have "... = \<Squnion>{(f (x, y1) * g (x, y1a)) * h (x, y2a) |y1a y2a y1 y2. y2 = y1a \<oplus> y2a \<and> y1a ## y2a \<and> y = y1 \<oplus> y2 \<and> y1 ## y2}"
    apply (rule antisym)
    apply (rule Sup_least)
    apply safe
    apply (rule Sup_mono)
    apply auto
    apply (rule Sup_least)
    apply auto
    apply transfer
    apply auto
    proof -
      fix y1a :: 'b and y2a :: 'b and y1 :: 'b and fa :: "'a \<times> 'b \<Rightarrow> 'c" and xa :: 'a and ga :: "'a \<times> 'b \<Rightarrow> 'c" and ha :: "'a \<times> 'b \<Rightarrow> 'c"
      assume a1: "y1a ## y2a"
      assume a2: "y1 ## y1a \<oplus> y2a"
      obtain sk\<^sub>8\<^sub>2 :: "'b \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b" and sk\<^sub>8\<^sub>1 :: "'b \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'b" where "\<exists>y1aa y2aa. fa (xa, y1) * ga (xa, y1a) * ha (xa, y2a) = fa (xa, y1) * ga (xa, y1aa) * ha (xa, y2aa) \<and> y1a \<oplus> y2a = y1aa \<oplus> y2aa \<and> y1aa ## y2aa" using a1 by blast
      hence "fa (xa, y1) * ga (xa, y1a) * ha (xa, y2a) \<le> \<Squnion>{fa (xa, y1) * ga (xa, y1aa) * ha (xa, y2aa) |y1aa y2aa. y1a \<oplus> y2a = y1aa \<oplus> y2aa \<and> y1aa ## y2aa}" by (simp add: Sup.Join_Collect_upper)
      then obtain sk\<^sub>7 :: "'c \<Rightarrow> 'b" and sk\<^sub>6 :: "'c \<Rightarrow> 'b" where "\<exists>x\<^sub>0\<ge>fa (xa, y1) * ga (xa, y1a) * ha (xa, y2a). x\<^sub>0 \<in> {\<Squnion>{fa (xa, y1b) * ga (xa, y1a) * ha (xa, y2a) |y1a y2a. y2 = y1a \<oplus> y2a \<and> y1a ## y2a} | y1b y2. y1 \<oplus> (y1a \<oplus> y2a) = y1b \<oplus> y2 \<and> y1b ## y2}" using a2 by blast
      thus "fa (xa, y1) * ga (xa, y1a) * ha (xa, y2a) \<le> \<Squnion>{\<Squnion>{fa (xa, y1b) * ga (xa, y1a) * ha (xa, y2a) |y1a y2a. y2 = y1a \<oplus> y2a \<and> y1a ## y2a} | y1b y2. y1 \<oplus> (y1a \<oplus> y2a) = y1b \<oplus> y2 \<and> y1b ## y2}" by (smt Sup_upper2) (* > 2 s, timed out *)
    qed
  also have "... = \<Squnion>{(f (x, y1) * g (x, y1a)) * h (x, y2a) |y1a y2a y1. y1a ## y2a \<and> y = y1 \<oplus> (y1a \<oplus> y2a) \<and> y1 ## (y1a \<oplus> y2a)}"
    by (auto intro: Sup.Join_eqI2)
  also have "... = \<Squnion>{(f (x, y1) * g (x, y1a)) * h (x, y2a) |y1a y2a y1. y1 ## y1a \<and> y = (y1 \<oplus> y1a) \<oplus> y2a \<and> (y1 \<oplus> y1a) ## y2a}"
    by (metis (erased, lifting) partial_semigroup_class.pmult_assoc partial_semigroup_class.pmult_def)
  also have "... = \<Squnion>{(f (x, y1) * g (x, y1a)) * h (x, y2) |y1a y2a y1 y2. y1 ## y1a \<and> y2a = y1 \<oplus> y1a \<and> y = y2a \<oplus> y2 \<and> y2a ## y2}"
    by (auto intro: Sup.Join_eqI2)
  also have "... = \<Squnion>{\<Squnion>{f (x, y1) * g (x, y1a) |y1 y1a. y2a = y1 \<oplus> y1a \<and> y1 ## y1a} * h (x, y2) |y2a y2. y = y2a \<oplus> y2 \<and> y2a ## y2}"
    apply (rule antisym)
    apply (rule Sup_least)
    apply auto
    defer
    apply (rule Sup_least)
    apply auto
    apply (subst qSup_distr_assoc_bifun)
    apply (rule Sup_mono)
    apply auto
    apply (subgoal_tac "\<exists>y2a y2b. y1 \<oplus> y1a \<oplus> y2 = y2a \<oplus> y2b \<and> y2a ## y2b \<and> f (x, y1) * g (x, y1a) * h (x, y2) \<le> \<Squnion>{f (x, y1) * g (x, y1a) |y1 y1a. y2a = y1 \<oplus> y1a \<and> y1 ## y1a} * h (x, y2b) ")
    apply (smt Sup_upper2 mem_Collect_eq)
    apply (subst qSup_distr_assoc_bifun)
    by (smt Sup_le_iff dual_order.refl mem_Collect_eq)
  finally show "\<Squnion>{f (x, y1) * \<Squnion>{g (x, y1) * h (x, y2a) |y1 y2a. y2 = y1 \<oplus> y2a \<and> y1 ## y2a} |y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2} =
                 \<Squnion>{\<Squnion>{f (x, y1a) * g (x, y2) |y1a y2. y1 = y1a \<oplus> y2 \<and> y1a ## y2} * h (x, y2) |y1 y2. y = y1 \<oplus> y2 \<and> y1 ## y2}"
   by auto
qed

instance
  apply default
  apply (rule ext_bifun,rule qmult_assoc_bifun[symmetric])
  apply (rule ext_bifun, rule qSup_distr_bifun)
  by (metis (lifting, mono_tags) qSup_distl_bifun eq_iff le_bifunI)+

end

text {* Unit is also lifted *}

instantiation bifun :: (type, partial_monoid, quantale_unital) quantale_unital
begin

lift_definition one_bifun :: "('a, 'b, 'c) bifun" is "\<lambda>(x, y). if y = 1' then 1 else \<bottom>" ..

lemma qunitl_bifun[simp]: "Rep_bifun (1 * f) (x, y) = Rep_bifun f (x, y)"
  apply transfer
  by (auto simp: pmult_onel one_bifun_def intro!: Sup_eqI)

lemma qunitr_bifun[simp]: "Rep_bifun (f * 1) (x, y) = Rep_bifun f (x, y)"
  apply transfer
  by (auto simp: pmult_oner one_bifun_def intro!: Sup_eqI)

instance
  by default (auto intro: qunitr_bifun qunitl_bifun)

end

text {* Commutativity is also lifted *}

instance bifun :: (type, partial_ab_semigroup, comm_quantale) comm_quantale
apply default
apply (rule ext_bifun)
apply transfer
by (auto simp: mult.commute intro: pmult_comm pmult_comm_def Sup.Join_eqI2)

instance bifun :: (type, partial_comm_monoid, comm_quantale_unital) comm_quantale_unital 
  by default auto

text {* Distributivity is also lifted *}

instance bifun :: (type, partial_semigroup, distrib_quantale) distrib_quantale ..

instance bifun :: (type, partial_comm_monoid, distrib_comm_quantale_unital) distrib_comm_quantale_unital ..

instantiation bifun :: (type, partial_comm_monoid, bbi) bbi
begin

lift_definition minus_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun"
  is "\<lambda>f g (x, y). f (x, y) - g (x, y)" ..
lift_definition uminus_bifun :: "('a, 'b, 'c) bifun \<Rightarrow> ('a, 'b, 'c) bifun" is "\<lambda>f (x, y). - f(x, y)" ..

instance
  apply default
  apply transfer
  apply (rule ext)
  apply auto
  apply (metis inf_compl_bot)
  apply transfer
  apply (rule ext)
  apply auto
  apply (metis sup_compl_top)
  apply transfer
  apply (rule ext)
  apply auto
  by (metis diff_eq)
end

end
