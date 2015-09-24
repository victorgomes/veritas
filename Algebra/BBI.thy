theory BBI
  imports Quantale Fixpoint
begin

notation 
  times (infixl "*" 70) and
  sup (infixl "\<squnion>" 65) and
  inf (infixl "\<sqinter>" 70) and
  Sup ("\<Squnion>_" [900] 900) and
  Inf ("\<Sqinter>_" [900] 900) and
  top ("\<top>") and
  bot ("\<bottom>") and
  one_class.one ("1")

class bbi = comm_quantale_unital + complete_boolean_algebra
begin

lemma qiso: "\<lbrakk>x \<le> z; y \<le> w\<rbrakk> \<Longrightarrow> x * y \<le> z * w"
  by (metis Sup.qisol Sup.qisor dual_order.trans)

lemma qmeet_subdistr: "(x \<sqinter> y) * z \<le> (x * z) \<sqinter> (y * z)"
  by (metis Sup.qisor inf_le1 inf_le2 le_inf_iff)

lemma qmeet_subdistl: "x * (y \<sqinter> z) \<le> (x * y) \<sqinter> (x * z)"
  by (metis mult_commute qmeet_subdistr)

lemma "(x * z) \<sqinter> (y * z) \<le> (x \<sqinter> y) * z" 
  (* nitpick *) oops

lemma "x \<sqinter> (y * z) \<le> (x \<sqinter> y) * (x \<sqinter> z)" 
  (* nitpick *) oops

lemma "(x * y) \<sqinter> z \<le> (x \<sqinter> z) * (y \<sqinter> z)"
  (* nitpick *) oops

lemma "(x \<sqinter> y) * (x \<sqinter> z) \<le> x \<sqinter> (y * z)"
  (* nitpick *) oops

lemma sep_conj_topl: "x \<le> \<top> * x"
  by (metis mult_1_left Sup.qisor top_greatest)

lemma sep_conj_topr: "x \<le> x * \<top>"
  by (metis mult_1_right Sup.qisol top_greatest)

lemma sep_conj_top [simp]: "\<top> * \<top> = \<top>"
  by (metis sep_conj_topl top_le)

definition sep_impl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "-*" 55) where
  "(op -*) x \<equiv> THE f. endo_galois_connection ((op * x)) f"

lemma equality_by_ineq: "\<forall>x. x \<le> f \<longleftrightarrow> x \<le> g \<Longrightarrow> f = g"
  by (metis Sup.ineq order_refl)

lemma ex_sep_conj_conn: "\<exists>!x. endo_galois_connection (op * y) x"
  apply auto
  apply (fold endo_lower_adjoint_def)
  apply (subst endo_lower_is_jp)
  apply (simp add: endo_join_preserving_def)
  apply (metis Sup.SUP_def local.Sup.Join_distl)
  apply (unfold endo_galois_connection_def)
  apply (subgoal_tac "\<forall>b a. (a \<le> x b) = (a \<le> ya b)")
  prefer 2
  apply simp
  apply (rule ext)
  apply (erule_tac x=xa in allE) back back
  apply (rule equality_by_ineq)
  by simp

lemma sep_impl: "x * y \<le> z \<longleftrightarrow> x \<le> y -* z"
  apply (simp add: sep_impl_def)
  apply (rule the1I2 [of "endo_galois_connection (op * y)"])
  apply (metis ex_sep_conj_conn)
  by (metis endo_galois_connection_def mult_commute) 

lemma sep_implI1: "x * y \<le> z \<Longrightarrow> x \<le> y -* z"
  by (simp add: sep_impl)

lemma sep_implI2: "x * y \<le> z \<Longrightarrow> y \<le> x -* z"
  by (metis mult_commute sep_implI1)

lemma sep_implE1: "x \<le> y -* z \<Longrightarrow> x * y \<le> z"
  by (simp add: sep_impl)

lemma sep_implE2: "x \<le> y -* z \<Longrightarrow> y * x \<le> z"
  by (simp add: sep_impl mult_commute)

lemma sep_impl_isoE: "\<lbrakk>x \<le> y -* z; w \<le> y\<rbrakk> \<Longrightarrow> x * w \<le> z"
  by (metis dual_order.trans sep_implE1 sep_implI2)

lemma sep_impl_annil1: "y * ( y -* x) \<le> x"
  by (metis eq_refl sep_implE2)

lemma sep_impl_annil2: "(y -* x) * y \<le> x"
  by (metis mult_commute sep_impl_annil1)

lemma sep_impl_annir1: "y \<le> (x -* (x * y))"
  by (metis order_refl sep_implI2)

lemma sep_impl_annir2: "y \<le> (x -* (y * x))"
  by (metis mult_commute sep_impl_annir1)

lemma sep_impl_annir2_iso: "x * z \<le> x * (y -* (y * z))"
  by (metis order_refl qiso sep_impl_annir1)

lemma reynolds28: "\<lbrakk>x \<le> y -* z; x' \<le> z -* w\<rbrakk> \<Longrightarrow> x' * x \<le> y -* w"
  by (metis mult_assoc sep_implE1 sep_implI1 sep_impl_isoE) 

lemma sep_impl_cut: "(z -* y) * (y -* x) \<le> z -* x"
  by (metis order_refl reynolds28 mult_commute)

lemma sep_impl_iso: "\<lbrakk>x' \<le> x; y \<le> y'\<rbrakk> \<Longrightarrow> x -* y \<le> x' -* y'"
  by (metis (full_types) order_trans sep_implE1 sep_implI2 sep_impl_annil1)

lemma sep_impl_iso_var: "x \<le> y \<Longrightarrow> z -* x \<le> z -* y"
  by (metis order_refl sep_impl_iso) 

lemma sep_impl_antitone: "x \<le> y \<Longrightarrow> y -* z \<le> x -* z"
  by (metis eq_refl sep_impl_iso)  

lemma sep_impl_to_meet: "y * (y -* x) \<le> (y * \<top>) \<sqinter> x"
  by (metis le_inf_iff sep_impl_annil1 sep_impl_annir2 sep_impl_isoE top_greatest)

lemma sep_impl_top [simp]: "x -* \<top> = \<top>"
  by (metis sep_implI2 top_greatest top_le)

lemma sep_impl_top_x: "\<top> -* x \<le> x"
  by (metis order_trans sep_conj_topl sep_impl_annil1)

lemma sep_impl_bot [simp]: "\<bottom> -* x = \<top>"
  by (metis Sup.qannir bot_least sep_implI2 top_le)

lemma sep_impl_top_bot [simp]: "\<top> -* \<bottom> = \<bottom>"
  by (metis le_bot sep_impl_top_x)

lemma sep_impl_join_subdistr: "(x \<squnion> y) -* z \<le> (x -* z) \<squnion> (y -* z)"
  by (metis sep_impl_antitone sup.coboundedI1 sup_ge1)

lemma sep_impl_join_subdistl: "(x -* y) \<squnion> (x -* z) \<le> x -* (y \<squnion> z)"
  by (metis sep_impl_iso_var sup_ge1 sup_ge2 sup_least)

lemma sep_impl_meet_subdistr: "(x -* z) \<sqinter> (y -* z) \<le> (x \<sqinter> y) -* z"
  by (metis inf_le1 le_infI1 sep_impl_antitone)

lemma sep_impl_meet_subdistl: "x -* (y \<sqinter> z) \<le> (x -* y) \<sqinter> (x -* z)"
  by (metis inf_le1 inf_le2 le_infI sep_impl_iso_var)


(* Algebraic characterization of pure assertion by Dang *)
definition pure :: "'a \<Rightarrow> bool" where
  "pure x \<equiv> \<forall>y z. x * \<top> \<le> x \<and> (y * z) \<sqinter> x \<le> (y \<sqinter> x) * (z \<sqinter> x)"

lemma pure_top [simp]: "pure \<top>"
  by (metis inf_le1 inf_top_right pure_def top_greatest)

lemma pure_bot [simp]: "pure \<bottom>"
  by (metis Sup.qannir eq_refl inf_bot_left inf_commute pure_def)

lemma pure_upward_closure [simp]: "pure x \<Longrightarrow> x * \<top> = x"
  apply (rule antisym, metis pure_def)
  by (metis sep_conj_topr)

lemma pure_upward_closure_var: "pure x \<Longrightarrow> x * y \<le> x"
  by (metis (full_types) eq_refl pure_upward_closure qiso top_greatest)

lemma pure_meet_distl: "pure x \<Longrightarrow> (y * z) \<sqinter> x = (y \<sqinter> x) * (z \<sqinter> x)"
  apply (rule antisym, metis pure_def)
  by (metis inf_le1 inf_le2 le_inf_iff pure_upward_closure qiso top_greatest)

lemma pure_meet_distr: "pure x \<Longrightarrow> x \<sqinter> (y * z) = (x \<sqinter> y) * (x \<sqinter> z)"
  by (metis inf_commute pure_meet_distl)

lemma pure_downward_closure: "pure x \<Longrightarrow> x = (x \<sqinter> 1) * \<top>"
  by (metis inf.orderE inf_commute inf_top_left pure_meet_distl pure_upward_closure mult_commute qmeet_subdistl mult_1_right)

lemma pure_downward_closure_var: "pure x \<Longrightarrow> x * y = x \<sqinter> (y * \<top>)"
  by (metis inf_absorb2 inf_idem inf_top_right pure_meet_distr pure_upward_closure_var mult_commute)

lemma reynolds_pure1: "pure x \<Longrightarrow> x \<sqinter> y \<le> x * y"
proof -
  assume pure: "pure x"
  hence "x \<sqinter> y \<le> x \<sqinter> (y * \<top>)"
    by (metis (full_types) inf_mono order_refl mult_commute qiso mult_1_left top_greatest)
  thus ?thesis
  by (metis pure pure_downward_closure_var)
qed

lemma reynolds_pure2: "\<lbrakk>pure x; pure y\<rbrakk> \<Longrightarrow> x * y \<le> x \<sqinter> y"
  by (metis eq_refl pure_downward_closure_var pure_upward_closure)

lemma reynolds_pure2_corollary: "\<lbrakk>pure x; pure y\<rbrakk> \<Longrightarrow> x * y = x \<sqinter> y"
  by (metis dual_order.antisym reynolds_pure1 reynolds_pure2)

lemma pure_idem [simp]: "pure x \<Longrightarrow> x * x = x"
  by (metis inf_idem reynolds_pure2_corollary)

lemma reynolds_pure3: "pure y \<Longrightarrow> (x \<sqinter> y) * z = (x * z) \<sqinter> y"
  apply (rule antisym)
  apply (metis le_infI1 le_infI2 le_inf_iff pure_upward_closure_var sep_impl_annir2 sep_impl)
  by (metis dual_order.trans inf_le1 pure_meet_distl sep_implE2 sep_impl_annir1)

lemma pure_join_closure: "\<lbrakk>pure x; pure x'\<rbrakk> \<Longrightarrow> pure (x \<squnion> x')"
proof (subst pure_def, auto)
  fix y z assume px: "pure x" and py: "pure x'"
  thus "(x \<squnion> x') * \<top> \<le> x \<squnion> x'"
    by (metis Sup.qdistl eq_refl mult_commute pure_upward_closure)
  have "(x \<squnion> x') \<sqinter> (y * z) = (x \<sqinter> (y * z)) \<squnion> (x' \<sqinter> (y * z))"
    by (metis inf_sup_distrib2)
  also have "... \<le> ((x \<sqinter> y) * (x \<sqinter> z)) \<squnion> ((x' \<sqinter> y) * (x' \<sqinter> z))"
    by (metis pure_meet_distr px py sup.bounded_iff sup_ge1 sup_ge2)
  also have "... \<le> (((x \<squnion> x') \<sqinter> y) * ((x \<squnion> x') \<sqinter> z)) \<squnion> (((x \<squnion> x') \<sqinter> y) * ((x \<squnion> x') \<sqinter> z))"
    by (metis inf_mono qiso sup_ge1 sup_ge2 sup_idem sup_least)
  finally show "y * z \<sqinter> (x \<squnion> x') \<le> (y \<sqinter> (x \<squnion> x')) * (z \<sqinter> (x \<squnion> x'))"
    by (metis inf_commute sup_idem)
qed

lemma pure_meet_closure: "\<lbrakk>pure x; pure x'\<rbrakk> \<Longrightarrow> pure (x \<sqinter> x')"
proof (subst pure_def, auto)
  fix y z assume px: "pure x" and py: "pure x'"
  thus "(x \<sqinter> x') * \<top> \<le> x"
    by (metis inf_le1 pure_upward_closure reynolds_pure3)
  show "(x \<sqinter> x') * \<top> \<le> x'"
    by (metis inf_le2 py reynolds_pure3)
  show "y * z \<sqinter> (x \<sqinter> x') \<le> (y \<sqinter> (x \<sqinter> x')) * (z \<sqinter> (x \<sqinter> x'))"
    by (metis eq_iff inf_commute inf_left_commute pure_meet_distr px py)
qed

lemma pure_sep_conj_closure: "\<lbrakk>pure x; pure x'\<rbrakk> \<Longrightarrow> pure (x * x')"
  by (metis pure_meet_closure reynolds_pure2_corollary)

lemma pure_negation_closure: "pure x \<Longrightarrow> pure (-x)"
proof (subst pure_def, auto)
  fix y z assume px: "pure x"
  hence "(-x * \<top>) \<sqinter> x = \<bottom>"
    by (metis compl_inf_bot pure_bot pure_upward_closure reynolds_pure3)
  thus "- x * \<top> \<le> - x"
    by (metis compl_sup double_compl inf.orderI inf_sup_distrib1 inf_top_right sup_bot_left sup_compl_top)
  have "(y * z) \<sqinter> -x = ((y \<sqinter> x) * (z \<sqinter> x) \<squnion> (y \<sqinter> -x) * (z \<sqinter> x) \<squnion> (y \<sqinter> x) * (z \<sqinter> -x) \<squnion> (y \<sqinter> -x) * (z \<sqinter> -x)) \<sqinter> -x"
    by (metis inf_top_right sup_compl_top inf_sup_distrib1 Sup.qdistr Sup.qdistl sup_assoc sup_commute sup_left_commute)
  also have "... = (((y * z) \<sqinter> x) \<squnion> (y \<sqinter> -x) * (z \<sqinter> x) \<squnion> (y \<sqinter> x) * (z \<sqinter> -x) \<squnion> (y \<sqinter> -x) * (z \<sqinter> -x)) \<sqinter> -x"
    by (metis px reynolds_pure3 inf_absorb1 inf_le2 mult_commute)
  also have "... = (((y * z) \<sqinter> x) \<squnion> (((y \<sqinter> -x) * z) \<sqinter> x) \<squnion> (y \<sqinter> x) * (z \<sqinter> -x) \<squnion> (y \<sqinter> -x) * (z \<sqinter> -x)) \<sqinter> -x"
    by (metis px reynolds_pure3 mult_commute)
  also have "... = (((y * z) \<sqinter> x) \<squnion> (((y \<sqinter> -x) * z) \<sqinter> x) \<squnion> (((z \<sqinter> -x) * y) \<sqinter> x) \<squnion> (y \<sqinter> -x) * (z \<sqinter> -x)) \<sqinter> -x"
    by (metis px reynolds_pure3 mult_commute)
  finally show "y * z \<sqinter> - x \<le> (y \<sqinter> - x) * (z \<sqinter> - x)"
    by (metis inf_sup_distrib2 inf_assoc inf_compl_bot inf_bot_right sup_bot_left inf_le1)
qed

(* I couldn't prove nor disprove *)
lemma pure_sep_impl_closure: "\<lbrakk>pure p; pure q\<rbrakk> \<Longrightarrow> pure (p -* q)"
  apply (subst pure_def)
  apply auto
  apply (metis eq_refl pure_upward_closure reynolds28 mult_commute sep_impl_annir2)
  oops

lemma pure_annilation [simp]: "pure x \<Longrightarrow> x * (-x) = \<bottom>"
  by (metis inf_compl_bot pure_negation_closure reynolds_pure2_corollary)

lemma indirect_ineq: "(\<And>z. z \<le> x \<longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y"
  by (metis (hide_lams, mono_tags) order_refl)

lemma "x \<squnion> y = y \<Longrightarrow> x \<le> y"
  by (metis le_iff_sup)

lemma join_meet_galois: "x \<sqinter> z \<le> y \<longleftrightarrow> z \<le> -x \<squnion> y"
proof
  assume "x \<sqinter> z \<le> y"
  hence "-x \<squnion> (x \<sqinter> z) \<le> -x \<squnion> y"
    by (metis le_iff_sup sup_idem sup_mono)
  thus "z \<le> -x \<squnion> y"
    by (metis compl_sup_top inf_top_left sup.boundedE sup_commute sup_inf_distrib2)
next
  assume "z \<le> -x \<squnion> y"
  thus "x \<sqinter> z \<le> y"
    by (metis inf_mono order_refl inf_sup_distrib1 inf_compl_bot sup_bot_left le_inf_iff)
qed

(* Reynolds uses implication x \<rightarrow> y \<equiv> - x \<squnion> y *)

lemma reynolds_pure4: "pure x \<Longrightarrow> x -* y \<le> -x \<squnion> y"
  apply (rule indirect_ineq)
  apply (rule impI)
  apply (drule sep_implE1)
  apply (subgoal_tac "x \<sqinter> z \<le> y")
  apply (metis join_meet_galois)
  by (metis order_trans reynolds_pure1 mult_commute)

lemma reynolds_pure5: "\<lbrakk>pure x; pure y\<rbrakk> \<Longrightarrow> -x \<squnion> y \<le> x -* y"
  apply (rule indirect_ineq)
  apply (rule impI)
  apply (rule sep_implI1)
  apply (subst (asm) join_meet_galois[symmetric])
  by (metis pure_downward_closure_var pure_meet_distr qiso top_greatest pure_upward_closure mult_commute)

definition intuitionistic :: "'a \<Rightarrow> bool" where
  "intuitionistic x \<equiv> x * \<top> \<le> x"

lemma pure_is_intuitionistic: "pure x \<Longrightarrow> intuitionistic x"
  by (metis intuitionistic_def pure_def)

lemma intuitionistic_top [simp]: "intuitionistic \<top>"
  by (metis pure_is_intuitionistic pure_top)

lemma intuitionistic_bot [simp]: "intuitionistic \<bottom>"
  by (metis pure_bot pure_is_intuitionistic)

lemma intuitionistic_upward_closure [simp]: "intuitionistic x \<Longrightarrow> x * \<top> = x"
  by (metis dual_order.antisym intuitionistic_def sep_conj_topr)

lemma intuitionistic_upward_closure_var: "intuitionistic x \<Longrightarrow> x * y \<le> x"
  by (metis (full_types) eq_refl intuitionistic_upward_closure qiso top_greatest)

lemma intuitionistic_downward_closure: "intuitionistic x \<Longrightarrow> (x \<sqinter> I) * \<top> \<le> x"
  by (metis dual_order.trans intuitionistic_def le_infE qmeet_subdistr)

lemma intuitionistic_downward_closure_var: "intuitionistic x \<Longrightarrow> x * y \<le> x \<sqinter> (y * \<top>)"
  by (metis Sup.qisor intuitionistic_upward_closure_var le_infI mult_commute top_greatest)

lemma reynolds_intuitionistic2: "\<lbrakk>intuitionistic x; intuitionistic y\<rbrakk> \<Longrightarrow> x * y \<le> x \<sqinter> y"
  by (metis intuitionistic_upward_closure_var le_infI mult_commute)

lemma reynolds_intuitionistic3: "intuitionistic y \<Longrightarrow> (x \<sqinter> y) * z \<le> (x * z) \<sqinter> y"
  by (metis inf_idem inf_le2 intuitionistic_upward_closure le_inf_iff qiso top_greatest)

lemma intuitionistic_sep_conj_closure: "\<lbrakk>intuitionistic x; intuitionistic y\<rbrakk> \<Longrightarrow> intuitionistic (x * y)"
  by (metis eq_refl intuitionistic_def intuitionistic_upward_closure mult_assoc)

lemma intuitionistic_sep_impl_closure: "\<lbrakk>intuitionistic x; intuitionistic y\<rbrakk> \<Longrightarrow> intuitionistic (x -* y)"
  by (metis intuitionistic_def sep_implI2 sep_impl_cut top_le)

lemma intuitionistic_join_closure: "\<lbrakk>intuitionistic x; intuitionistic y\<rbrakk> \<Longrightarrow> intuitionistic (x \<squnion> y)"
  by (metis eq_refl intuitionistic_def intuitionistic_upward_closure Sup.qdistr)

lemma intuitionistic_meet_closure: "\<lbrakk>intuitionistic x; intuitionistic y\<rbrakk> \<Longrightarrow> intuitionistic (x \<sqinter> y)"
  by (metis intuitionistic_def intuitionistic_upward_closure qmeet_subdistr)

lemma intuitionistic_sep_conj_top: "intuitionistic (x * \<top>)"
  by (metis eq_refl intuitionistic_def mult_assoc sep_conj_top)

lemma intuitionistic_sep_impl_top: "intuitionistic (\<top> -* x)"
  by (metis intuitionistic_def mult_commute sep_impl_cut sep_impl_top)

lemma strongest_intuitionistic: "\<not> (\<exists>y. intuitionistic y \<and> y \<le> x * \<top> \<and> y \<noteq> x * \<top> \<and> x \<le> y)"
  by (metis intuitionistic_upward_closure Sup.qdistr sup.orderE sup_absorb2)

lemma weakest_intuitionistic: "\<not> (\<exists>y. intuitionistic y \<and> \<top> -* x \<le> y \<and> y \<noteq> \<top> -* x \<and> y \<le> x)"
  by (metis dual_order.antisym intuitionistic_upward_closure sep_impl)

lemma sep_Sup: "\<Squnion> {x * p | x. x \<in> X} = \<Squnion> X * p"
  apply (rule Sup_eqI)
  apply (smt Sup_upper eq_refl mem_Collect_eq qiso)
  apply (rule sep_implE1)
  by (metis (lifting, full_types) Sup_least mem_Collect_eq sep_implI1)

lemma sep_Sup2: "\<Squnion> {p * x | x. x \<in> X} = p * \<Squnion> X"
  apply (rule Sup_eqI)
  apply (smt Sup_upper eq_refl mem_Collect_eq qiso)
  apply (rule sep_implE2)
oops

definition precise :: "'a \<Rightarrow> bool" where
  "precise p \<equiv> \<forall>X. \<Sqinter> {x * p | x. x \<in> X} = \<Sqinter> X * p"

lemma precise_charac: "precise p \<Longrightarrow> \<Sqinter> {x * p | x. x \<in> X} = \<Sqinter> X * p"
  by (simp add: precise_def)

lemma "precise p \<Longrightarrow> p * \<top> = \<top>"
  apply (simp add: precise_def)
  apply (erule allE [of _ "{}"], auto)
  by (metis mult_commute)

lemma precise_distl: "precise p \<Longrightarrow> (x \<sqinter> y) * p = (x * p) \<sqinter> (y * p)"
  apply (simp add: precise_def)
  apply (erule_tac x="{x, y}" in allE)
  apply auto
  apply (subgoal_tac "\<Sqinter> {xa * p |xa. xa = x \<or> xa = y} = (x * p) \<sqinter> (y * p)")
  apply simp
  apply (rule Inf_eqI)
  by auto

lemma precise_distr: "precise p \<Longrightarrow> p * (x \<sqinter> y) = (p * x) \<sqinter> (p * y)"
  by (metis precise_distl mult_commute)

lemma precise_sep_conj_closure: "\<lbrakk>precise p; precise q\<rbrakk> \<Longrightarrow> precise (p * q)"
proof (subst precise_def, auto)
  fix X assume pp: "precise p" and pq: "precise q"
  have "\<Sqinter> {x * (p * q) |x. x \<in> X} = \<Sqinter> {x * q |x. x \<in> {y * p | y. y \<in> X}}"
    apply (subst mem_Collect_eq)
    by (metis mult_assoc)
  also have "... = \<Sqinter> {y * p | y. y \<in> X} * q"
    by (metis pq precise_charac [of q "{y * p | y. y \<in> X}"])
  finally show "\<Sqinter>{x * (p * q) |x. x \<in> X} = \<Sqinter>X * (p * q)"
    by (metis (lifting, no_types) pp precise_charac mult_assoc)
qed

lemma precise_meet_closure: "\<lbrakk>precise p; precise q\<rbrakk> \<Longrightarrow> precise (p \<sqinter> q)"
  (* nitpick *) oops

lemma precise_join_closure: "\<lbrakk>precise p; precise q\<rbrakk> \<Longrightarrow> precise (p \<squnion> q)"
  (* nitpick *) oops

lemma precise_subset_closure: "\<lbrakk>p \<le> q; precise q\<rbrakk> \<Longrightarrow> precise p"
  (* nitpick *) oops

lemma "\<forall>x \<in> X. intuitionistic x \<Longrightarrow> intuitionistic (\<Squnion> X)"
proof (unfold intuitionistic_def) 
  assume assm: "\<forall>x\<in>X. x * \<top> \<le> x"
  have "\<Squnion>X * \<top> = \<Squnion>{x * \<top> | x. x \<in> X}"
    by (metis sep_Sup)
  also have "... \<le> \<Squnion>X"
    apply (rule Sup_least, rule Sup_upper, auto)
    by (metis assm dual_order.antisym sep_conj_topr)
  finally show "\<Squnion>X * \<top> \<le> \<Squnion>X" .
qed 

lemma "\<forall>x \<in> X. intuitionistic x \<Longrightarrow> intuitionistic (\<Sqinter> X)"
  by (metis intuitionistic_def Inf_greatest Inf_lower dual_order.antisym qiso sep_conj_top sep_conj_topr)

end

end
