theory Abstract_Quantales
  imports Main
begin

no_notation 
  times (infixl "*" 70) and
  one_class.one ("1")

locale abs_complete_lattice = 
  fixes Join :: "'a set \<Rightarrow> 'a" ("\<Oplus>_" [900] 900)
  assumes Join_singleton: "\<Oplus>{x} = x"
  and Join_Union: "\<Oplus>{\<Oplus>x| x. x \<in> X} = \<Oplus>(\<Union>X)"
  and Join_limit: "(\<And>x. x \<in> A \<Longrightarrow> z = \<Oplus>{x, z}) \<Longrightarrow> z = \<Oplus> {z, \<Oplus> A}" 

context abs_complete_lattice begin

lemma Join_absorb: "x \<in> A \<Longrightarrow> \<Oplus>A = \<Oplus> {x, \<Oplus> A}"
proof -
  assume "x \<in> A"
  hence "\<Oplus>A = \<Oplus>(\<Union>{{x},A})"
    by auto (metis insert_absorb)
  also have "... = \<Oplus> {\<Oplus> {x}, \<Oplus> A}"
    by (subst Join_Union[symmetric]) (auto intro: cong[of "\<lambda>X.\<Oplus>X"])
  finally show ?thesis
    by (metis Join_singleton)
qed

lemma Join_simp1: "\<Oplus>{x, \<Oplus>{y, z}} = \<Oplus>{x, y, z}"
proof -
  have "\<Oplus>{x, \<Oplus>{y, z}} = \<Oplus>{\<Oplus>{x}, \<Oplus>{y, z}}"
    by (metis Join_singleton)
  also have "... = \<Oplus>(\<Union>{{x}, {y, z}})"
    by (subst Join_Union[symmetric]) (auto intro: cong[of "\<lambda>X.\<Oplus>X"])
  finally show ?thesis
    by (auto simp: insert_commute)
qed

lemma Join_simp2: "\<Oplus>{x, \<Oplus>A} = \<Oplus>{y. y = x \<or> y \<in> A}"
proof -
  have "\<Oplus>{x, \<Oplus>A} = \<Oplus>{\<Oplus>{x}, \<Oplus>A}"
    by (metis Join_singleton)
  also have "... = \<Oplus>(\<Union>{{x}, A})"
    by (subst Join_Union[symmetric]) (auto intro: cong[of "\<lambda>X.\<Oplus>X"])
  finally show ?thesis
    by auto (metis insert_compr)
qed

lemma Join_reduce1: "x = \<Oplus>{x, y, z} \<Longrightarrow> x = \<Oplus>{x, y}"
  by (metis Join_absorb insertI1 insert_commute)

lemma Join_reduce2: "x = \<Oplus>{x, y, z} \<Longrightarrow> x = \<Oplus>{x, z}"
  by (metis Join_reduce1 insert_commute)

lemma Join_trans: "y = \<Oplus>{x, y} \<Longrightarrow> z = \<Oplus>{y, z} \<Longrightarrow> z = \<Oplus>{x, z}"
  by (metis Join_simp1 insert_commute)

definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 70) where
  "x \<oplus> y \<equiv> \<Oplus> {x, y}"

definition less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 55) where
  "x \<sqsubseteq> y \<equiv> y = x \<oplus> y"

definition less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 55) where
  "x \<sqsubset> y \<equiv> x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x"

lemma less_le_not_le: "x \<sqsubset> y \<longleftrightarrow> (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
  by (simp add: less_eq_def less_def)

lemma order_refl [iff]: "x \<sqsubseteq> x"
  by (simp add: less_eq_def join_def Join_singleton)

lemma order_trans [trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  by (auto simp: less_eq_def join_def intro: Join_trans)

lemma antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
  by (auto simp: less_eq_def join_def insert_commute)

lemma less_var: "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
  apply (auto simp: less_def)
  by (metis antisym)

lemma ineq: "x \<noteq> y \<Longrightarrow> \<not> x \<sqsubseteq> y \<or> \<not> y \<sqsubseteq> x"
  by (metis antisym)

lemma less_eq_less: "x \<sqsubset> y \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: less_def)

definition Meet :: "'a set \<Rightarrow> 'a" ("\<Odot>_" [900] 900) where
  "\<Odot>A \<equiv> \<Oplus>{x. \<forall>y \<in> A. x \<sqsubseteq> y}"

definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 65) where
  "x \<odot> y \<equiv> \<Odot>{x, y}"

lemma meet_comm: "x \<odot> y = y \<odot> x"
  by (simp add: insert_commute meet_def)

lemma meet_le1 [simp]: "x \<odot> y \<sqsubseteq> x"
  by (auto simp add: meet_def Meet_def less_eq_def join_def insert_commute intro: Join_limit)

lemma meet_le2 [simp]: "x \<odot> y \<sqsubseteq> y"
  by (metis meet_comm meet_le1)

lemma meet_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<odot> z"
  by (auto simp add: meet_def Meet_def less_eq_def join_def insert_commute intro: Join_absorb)

lemma join_comm: "x \<oplus> y = y \<oplus> x"
  by (simp add: insert_commute join_def)

lemma join_ge1 [simp]: "x \<sqsubseteq> x \<oplus> y"
  by (auto simp add: less_eq_def join_def insert_commute intro: Join_absorb)

lemma join_ge2 [simp]: "y \<sqsubseteq> x \<oplus> y"
  by (metis join_comm join_ge1)

lemma join_least: "y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<oplus> z \<sqsubseteq> x"
  by (auto simp: less_eq_def join_def insert_commute intro: Join_limit)

definition top :: "'a" ("\<top>") where "top \<equiv> \<Odot>{}"

definition bot :: "'a" ("\<bottom>") where "bot \<equiv> \<Oplus>{}"

lemma top_greatest: "x \<sqsubseteq> \<top>"
  by (auto simp: top_def Meet_def less_eq_def join_def insert_commute intro: Join_absorb)

lemma bot_least: "\<bottom> \<sqsubseteq> x"
  by (auto simp: bot_def less_eq_def join_def insert_commute intro: Join_limit)

lemma Meet_lower: "x \<in> A \<Longrightarrow> \<Odot>A \<sqsubseteq> x"
  by (auto simp: Meet_def less_eq_def join_def insert_commute intro: Join_limit)

lemma Meet_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Odot>A"
  by (auto simp: Meet_def less_eq_def join_def intro: Join_absorb)

lemma Join_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Oplus>A"
  by (auto simp: less_eq_def join_def intro: Join_absorb)

lemma Join_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Oplus>A \<sqsubseteq> z"
  by (auto simp: less_eq_def join_def insert_commute intro: Join_limit)

lemma Join_Collect_upper: "P x \<Longrightarrow> x \<sqsubseteq> \<Oplus> Collect P"
  by (metis Join_upper mem_Collect_eq)

lemma Meet_Collect_lower: "P x \<Longrightarrow> \<Odot> Collect P \<sqsubseteq> x"
  by (metis Meet_lower mem_Collect_eq)

definition complements :: "'a \<Rightarrow> 'a set" where
  "complements x = {y. x \<oplus> y = \<top> \<and> x \<odot> y = \<bottom>}"

lemma complementsE1: "y \<in> complements x \<Longrightarrow> x \<oplus> y = \<top>"
  by (metis (lifting, mono_tags) complements_def mem_Collect_eq)

lemma complementsE2: "y \<in> complements x \<Longrightarrow> x \<odot> y = \<bottom>"
  by (metis (lifting, full_types) complements_def mem_Collect_eq)

lemma complementsI1: "\<lbrakk>x \<oplus> y = \<top>; x \<odot> y = \<bottom>\<rbrakk> \<Longrightarrow> y \<in> complements x"
  by (metis (lifting, full_types) complements_def mem_Collect_eq)

lemma complementsI2: "\<lbrakk>x \<oplus> y = \<top>; x \<odot> y = \<bottom>\<rbrakk> \<Longrightarrow> x \<in> complements y"
  by (metis complementsI1 join_comm meet_comm)

lemma pre_order [simp]: "class.preorder op \<sqsubseteq> op \<sqsubset>"
  by default (auto simp: less_le_not_le, metis order_trans)

lemma order [simp]: "class.order_axioms op \<sqsubseteq>"
  by default (metis antisym)
  
lemma semillatice_inf [simp]: "class.semilattice_inf_axioms op \<odot> op \<sqsubseteq>"
  by default (simp_all add: meet_greatest)

lemma semilattice_sup [simp]: "class.semilattice_sup_axioms op \<oplus> op \<sqsubseteq>"
  by default (simp_all add: join_least)

lemma order_bot [simp]: "class.order_bot_axioms \<bottom> op \<sqsubseteq>"
  by default (metis bot_least)

lemma order_top [simp]: "class.order_top_axioms op \<sqsubseteq> \<top>"
  by default (metis top_greatest)

lemma comp_lattice [simp]: "class.complete_lattice Meet Join meet less_eq less join bot top"
  apply (intro_locales, simp_all)
  by default (simp_all add: top_def bot_def Meet_lower Meet_greatest Join_upper Join_least)

lemma dual_comp_lattice: "class.complete_lattice Join Meet join (\<lambda>x y. y \<sqsubseteq> x) (\<lambda>x y. y \<sqsubset> x) meet top bot"
  by unfold_locales (simp_all add: less_le_not_le antisym top_def bot_def join_least meet_greatest
    Meet_lower Meet_greatest Join_upper Join_least, metis order_trans)

end

locale abs_distrib_complete_lattice = abs_complete_lattice +
  assumes join_Meet: "x \<oplus> \<Odot>Y = \<Odot>{x \<oplus> y | y. y \<in> Y}"
  and meet_Join: "x \<odot> \<Oplus>Y = \<Oplus>{x \<odot> y | y. y \<in> Y}"
begin

lemma meet_join: "x \<odot> (y \<oplus> z) = (x \<odot> y) \<oplus> (x \<odot> z)"
  apply (insert meet_Join[of x "{y, z}"])
  by (auto simp add: join_def intro: cong[of "\<lambda>X. \<Oplus>X"])

lemma join_meet: "x \<oplus> (y \<odot> z) = (x \<oplus> y) \<odot> (x \<oplus> z)"
  apply (insert join_Meet[of x "{y, z}"])
  by (auto simp: join_def meet_def intro!: cong[of "\<lambda>X. \<Odot>X"])

lemma compl_uniq_le: "\<lbrakk>y \<in> complements x; z \<in> complements x\<rbrakk> \<Longrightarrow> z \<sqsubseteq> y"
proof (auto simp: complements_def)
  assume hyp: "x \<oplus> y = \<top>" "x \<odot> y = \<bottom>" "x \<oplus> z = \<top>" "x \<odot> z = \<bottom>"
  have "y = y \<oplus> \<bottom>"
    by (metis Join_limit bot_def ex_in_conv join_def)
  also have "... = y \<oplus> (x \<odot> z)"
    by (metis hyp(4))
  also have "... = (y \<oplus> x) \<odot> (y \<oplus> z)"
    by (metis join_meet)
  also have "... = \<top> \<odot> (y \<oplus> z)"
    by (metis hyp(1) join_comm)
  finally show "z \<sqsubseteq> y"
    by (metis join_ge2 meet_greatest top_greatest)
qed

lemma compl_uniq: "\<lbrakk>y \<in> complements x; z \<in> complements x\<rbrakk> \<Longrightarrow> y = z"
  by (metis antisym compl_uniq_le)

definition compl :: "'a \<Rightarrow> 'a" ("-- _" [99] 100) where
  "-- x \<equiv> THE y. y \<in> complements x"

definition diff :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "--" 65) where
  "x -- y \<equiv> x \<oplus> (-- y)"

lemma distrib_lattice [simp]: "class.distrib_lattice_axioms op \<odot> op \<oplus>"
  by default (metis join_meet)

end
  

locale abs_near_quantale = abs_complete_lattice + semigroup +
  assumes Join_distr: "\<Oplus> Y * x = \<Oplus> ((\<lambda>y. y * x) ` Y)"

locale abs_pre_quantale = abs_near_quantale + 
  assumes Join_subdistl: "x * \<Oplus> Y = \<Oplus> {\<Oplus> ((\<lambda>y. x * y) ` Y), x * \<Oplus> Y}"

locale abs_near_quantale_unital = abs_near_quantale + monoid

locale abs_quantale = abs_pre_quantale + 
  assumes Join_supdistl: "\<Oplus> ((\<lambda>y. x * y) ` Y) = \<Oplus> {\<Oplus> ((\<lambda>y. x * y) ` Y), x * \<Oplus> Y}"

locale abs_quantale_unital = abs_quantale + monoid

locale abs_comm_quantale = abs_quantale + abel_semigroup

locale abs_comm_quantale_unital = abs_quantale + comm_monoid

context abs_near_quantale begin

lemma qdistr: "(x \<oplus> y) * z = (x * z) \<oplus> (y * z)"
  by (insert Join_distr[of "{x, y}"]) (simp add: join_def)

lemma qannir [simp]: "\<bottom>  *  x = \<bottom>"
  by (insert Join_distr[of "{}"]) (simp add: bot_def)

lemma qisor: "x \<sqsubseteq> y \<Longrightarrow> x  *  z \<sqsubseteq> y  *  z"
  by (metis less_eq_def qdistr)

lemma join_subdistr: "(x \<oplus> y)  *  z \<sqsubseteq> (x  *  z) \<oplus> (y  *  z)"
  by (metis order_refl qdistr)

lemma Meet_subdistr: "\<Odot>Y * x \<sqsubseteq> \<Odot>{y * x | y. y \<in> Y}"
  by (auto simp add: Meet_def Join_distr qisor intro!: Join_least Join_upper)

lemma Join_eqI2: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> \<Oplus>A = \<Oplus>B"
  by (metis subsetI subset_antisym)

lemma Meet_eqI2: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> \<Odot>A = \<Odot>B"
  by (metis subsetI subset_antisym)

end

context abs_near_quantale_unital begin

primrec qpower :: "'a \<Rightarrow> nat \<Rightarrow> 'a" ("_ power _" [101,99] 100) where
  "x power (0 :: nat) = (1 :: 'a)"
| "x power (Suc n) = x * x power n"

lemma qpower_add: "x power m * x power n = x power (plus m n)"
  by (induct m, simp_all) (metis assoc)

lemma qpower_comm: "x power n * x = x * x power n"
  by (metis add_Suc_right qpower.simps qpower_add right_neutral)

lemma qpower_inductr: "y * x \<sqsubseteq> y \<Longrightarrow> y * x power n \<sqsubseteq> y"
  by (induct n, auto) (metis assoc order_trans qisor)

definition qstar :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100) where
  "x\<^sup>\<star> \<equiv> \<Oplus> {y. \<exists>i. y = x power i}"

lemma qstar_distr: "x\<^sup>\<star> * y = \<Oplus> {z * y | z. \<exists>i. z = x power i}"
  by (auto simp: qstar_def Join_distr intro: Join_eqI2)

lemma qstar_ref [simp]: "(1 :: 'a) \<sqsubseteq> x\<^sup>\<star>"
  by (auto simp: qstar_def intro!: Join_upper exI[of _ 0])

lemma qstar_refi: "x power i \<sqsubseteq> x\<^sup>\<star>"
  by (auto simp add: qstar_def intro: Join_upper)

lemma qstar_unfoldr_var: "x\<^sup>\<star> * x \<sqsubseteq> x\<^sup>\<star>"
  by (subst qstar_def, auto simp: Join_distr qpower_comm intro!: Join_least) (metis qpower.simps(2) qstar_refi)

lemma qstar_unfoldr1: "1 \<oplus> (x\<^sup>\<star> * x) \<sqsubseteq> x\<^sup>\<star>"
  by (auto simp add: qstar_unfoldr_var intro: join_least)

lemma qstar_unfoldr2: "x\<^sup>\<star> \<sqsubseteq> 1 \<oplus> (x\<^sup>\<star> * x)"
  apply (subst qstar_def, auto intro!: Join_least, induct_tac i, auto)
  by (metis join_ge2 order_trans qpower_comm qisor qstar_refi)

lemma qstar_unfoldr: "1 \<oplus> (x\<^sup>\<star> * x) = x\<^sup>\<star>"
  by (metis antisym qstar_unfoldr1 qstar_unfoldr2)

end

context abs_pre_quantale begin

lemma Join_qsubdistl: "\<Oplus> ((\<lambda>y. x * y) ` Y) \<sqsubseteq> x * \<Oplus> Y"
  by (metis Join_subdistl join_def less_eq_def)

lemma qsubdistl: "(x * y) \<oplus> (x * z) \<sqsubseteq> x * (y \<oplus> z)"
  by (insert Join_qsubdistl[of _ "{y, z}"]) (simp add: join_def)

lemma qisol: "x \<sqsubseteq> y \<Longrightarrow> z * x \<sqsubseteq> z * y"
  by (metis antisym join_ge2 less_eq_def qsubdistl)

end

context abs_quantale begin

lemma Join_qsupdistl: "x * \<Oplus> Y \<sqsubseteq> \<Oplus> ((\<lambda>y. x * y) ` Y)"
  by (metis Join_subdistl Join_supdistl order_refl)

lemma Join_distl: "x * \<Oplus> Y = \<Oplus> ((\<lambda>y. x * y) ` Y)"
  by (metis Join_subdistl Join_supdistl)

lemma qsupdistl: "x * (y \<oplus> z) \<sqsubseteq> (x * y) \<oplus> (x * z)"
  by (insert Join_qsupdistl[of _ "{y, z}"]) (simp add: join_def)

lemma qdistl: "z * (x \<oplus> y) = (z * x) \<oplus> (z * y)"
  by (metis antisym qsubdistl qsupdistl)

lemma qannil [simp]: "x * \<bottom>  = \<bottom>"
  by (insert Join_distl[of _ "{}"]) (simp add: bot_def)

end

context abs_quantale_unital begin

sublocale abs_near_quantale_unital ..

lemma power_inductl: "x * y \<sqsubseteq> y \<Longrightarrow> x power n * y \<sqsubseteq> y"
  by (induct n, auto) (metis assoc qisol order_trans)

lemma qstar_distl: "x * y\<^sup>\<star> = \<Oplus>{x * z | z. \<exists>i. z = y power i}"
  by (auto simp: qstar_def Join_distl intro: Join_eqI2)

lemma qstar_unfoldl_var: "x * x\<^sup>\<star> \<sqsubseteq> x\<^sup>\<star>"
  by (subst qstar_def, auto simp: Join_distl qpower_comm intro!: Join_least) (metis qpower.simps(2) qstar_refi)

lemma qstar_unfoldl1: "1 \<oplus> (x * x\<^sup>\<star>) \<sqsubseteq> x\<^sup>\<star>"
  by (auto simp add: qstar_unfoldl_var intro: join_least)

lemma qstar_unfoldl2: "x\<^sup>\<star> \<sqsubseteq> 1 \<oplus> (x * x\<^sup>\<star>)"
  apply (subst qstar_def, auto intro!: Join_least, induct_tac i, auto)
  by (metis join_ge2 order_trans qisol qstar_refi)

lemma qstar_unfoldl: "1 \<oplus> (x * x\<^sup>\<star>) = x\<^sup>\<star>"
  by (metis antisym qstar_unfoldl1 qstar_unfoldl2)

lemma qstar_inductr: "y \<oplus> (x * w) \<sqsubseteq> w \<Longrightarrow> x\<^sup>\<star> * y \<sqsubseteq> w"
  apply (auto simp add: qstar_distr intro!: Join_least)
  apply (induct_tac i, auto)
  apply (metis join_ge1 order_trans)
  by (metis assoc join_ge2 order_trans qisol)

lemma qstar_inductl: "y \<oplus> (w * x) \<sqsubseteq> w \<Longrightarrow> y * x\<^sup>\<star> \<sqsubseteq> w"
  apply (auto simp add: qstar_distl intro!: Join_least)
  apply (induct_tac i, auto)
  apply (metis join_ge1 order_trans)
  apply (subst qpower_comm[symmetric])
  by (metis join_ge2 assoc order_trans qisor)

end

end
