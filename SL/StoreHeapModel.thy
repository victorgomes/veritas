theory StoreHeapModel
  imports PredTrans
begin

type_synonym 'a stran = "'a \<times> heap \<Rightarrow> ('a \<times> heap) option"

definition valid_mem :: "'a option \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "in" 100) where
  "x in Q \<equiv> case x of None \<Rightarrow> False | Some y \<Rightarrow> y \<in> Q"

definition basic :: "'a stran \<Rightarrow> 'a ptran" ("\<langle>_\<rangle>") where
  "basic f Q \<equiv> {(s, h). f (s, h) in Q}"

definition assign :: "('v, 's) lval \<Rightarrow> ('s \<Rightarrow>'v) \<Rightarrow> 's ptran" where
  "assign u_upd t \<equiv> \<langle>\<lambda>(s, h). Some (u_upd (\<lambda>_. t s) s, h)\<rangle>"

definition lookup :: "(nat, 's) lval \<Rightarrow> 's nat_exp \<Rightarrow> 's ptran" where
  "lookup u_upd t \<equiv> \<langle>\<lambda>(s, h). if t s \<in> dom h
                              then Some (u_upd (\<lambda>_. the (h (t s))) s, h)
                              else None\<rangle>"

definition mutation :: "'s nat_exp \<Rightarrow> 's nat_exp \<Rightarrow> 's ptran" where
  "mutation e t \<equiv> \<langle>\<lambda>(s, h). if e s \<in> dom h
                            then Some (s, h(e s \<mapsto> t s))
                            else None\<rangle>"

definition alloc :: "(nat, 's) lval \<Rightarrow> 's nat_exp \<Rightarrow> 's ptran" where
  "alloc u_upd t \<equiv> \<langle>\<lambda>(s, h). let N = (SOME n. n \<notin> dom h) in
                    Some (u_upd (\<lambda>_. N) s, h ++ [N \<mapsto> t s])\<rangle>"

definition disposal :: "'s nat_exp \<Rightarrow> 's ptran" where
  "disposal e \<equiv> \<langle>\<lambda>(s, h). if e s \<in> dom h 
                         then Some (s, h(e s := None)) 
                         else None\<rangle>"

(***********************************************************************************************)

(* Monotonic *)

lemma mono_basic [mptran]: "mono (basic f)"
  apply (auto simp: mono_def basic_def valid_mem_def)
  apply (case_tac "f(a, b)")
  apply force+
done

lemma mono_assign [mptran]: "mono (assign u t)"
  by (auto simp: assign_def intro: mptran)

lemma mono_lookup [mptran]: "mono (lookup u t)"
  by (auto simp: lookup_def intro: mptran)

lemma mono_mutation [mptran]: "mono (mutation e t)"
  by (auto simp: mutation_def intro: mptran)

lemma mono_alloc [mptran]: "mono (alloc u t)"
  by (auto simp: alloc_def intro: mptran)

lemma mono_disposal [mptran]: "mono (disposal e)"
  by (auto simp: disposal_def intro: mptran)

(***********************************************************************************************)

(* Locality *)

definition basic_local :: "'a stran \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "basic_local f R \<equiv> \<forall>s h1 h2 Q. h1 \<bottom> h2 \<and> f (s, h1) in Q \<and> (s, h2) \<in> R \<longrightarrow> f(s, h1 ++ h2) in (Q * R)"

lemma local_eq: "local (basic f) R \<longleftrightarrow> basic_local f R"
  by (force simp: local_def basic_local_def basic_def sep_def)

lemma local_assign: "free_pred v R \<Longrightarrow> local (assign v t) R"
  by (force simp: subst_pred_def local_eq basic_local_def assign_def basic_def sep_def valid_mem_def)

lemma local_lookup [lptran]: "free_pred u R \<Longrightarrow> local (lookup u t) R"
  apply (auto simp: local_eq basic_local_def lookup_def basic_def sep_def valid_mem_def)
  apply (rule_tac x=h1 in exI)
  apply (rule_tac x=h2 in exI)
  apply (subgoal_tac "the ((h1 ++ h2) (t s)) = y")
  apply (force simp: subst_pred_def)
  by (simp add: heap_divider)

lemma local_mutation [lptran]: "local (mutation e t) R"
  apply (auto simp: local_eq basic_local_def mutation_def basic_def sep_def valid_mem_def)
  apply (rule_tac x="h1(e s \<mapsto> t s)" in exI)
  apply (rule_tac x=h2 in exI)
  apply auto
  apply (metis (no_types, lifting) dom_fun_upd fun_upd_triv map_add_comm map_add_upd option.distinct(1) ortho_def)
  apply (auto simp: ortho_def)
done

lemma "dom h \<noteq> UNIV \<Longrightarrow> \<exists>n. n \<notin> dom h"
  apply auto
done

lemma local_alloc [lptran]: "\<forall>h. \<exists>n. n \<notin> dom h \<Longrightarrow> local (alloc u t) R"
  apply (simp add: alloc_def local_eq basic_local_def)
  apply auto
oops

lemma local_disposal [lptran]: "local (disposal e) R"
  apply (simp add: disposal_def local_def ortho_def sep_def basic_def valid_mem_def)
  apply auto
  apply (erule_tac x="h1(e s := None)" in allE)
  apply auto 
  apply (erule_tac x="h2" in allE)
  apply auto
  apply (auto simp: map_add_def)
  apply (erule notE)
  apply (rule ext)
  apply auto
  apply (metis disjoint_iff_not_equal domI domIff fun_upd_apply option.case_eq_if)
  by (metis fun_upd_apply)

(***********************************************************************************************)

(* Separation Logic *)

lemma hl_basic [sl]: "P \<subseteq> {s. f s in Q} \<Longrightarrow> ht P (basic f) Q"
  by (auto simp: ht_def basic_def seq_def)

lemma hl_assign [sl]: "P \<subseteq> subst_pred Q z_upd t \<Longrightarrow> ht P (assign z_upd t) Q"
  by (auto simp: assign_def subst_pred_def valid_mem_def intro!: sl)

(* Mutation *)

lemma sl_mut_local [sl]: "ht (e \<mapsto> -) (mutation e e') (e \<mapsto> e')"
  by (auto simp: mutation_def valid_mem_def any_singleton_def singleton_def intro!: sl)

lemma sl_mut_local' [sl]: "ht (e \<mapsto> n) (mutation e e') (e \<mapsto> e')"
  by (auto simp: mutation_def valid_mem_def any_singleton_def singleton_def intro!: sl)

lemma sl_mut_global [sl]: "ht ((e \<mapsto> -) * r) (mutation e e') ((e \<mapsto> e') * r)"
  by (auto intro: sl lptran sl_frame)

lemma sl_mut_global' [sl]: "ht ((e \<mapsto> n) * r) (mutation e e') ((e \<mapsto> e') * r)"
  by (auto intro: sl lptran sl_frame)

lemma sl_mut: "ht ((e \<mapsto> -) * ((e \<mapsto> e') -* r)) (mutation e e') r"
  apply (rule hl_post[where Q'="(e \<mapsto> e') * ((e \<mapsto> e') -* r)"])
  by (auto simp: Assertions.bbi.sep_impl_annil1 intro!: sl_mut_global mptran)

lemma sl_mut_suc [sl]: "ht (v \<mapsto> a, b) (mutation (\<lambda>s. v s + 1) e) (v \<mapsto> a, e)"
  by (auto simp add: doublet_def intro: sl_frame2 lptran sl)

(* Allocation *)

lemma sl_alloc_local [sl]: "free u_upd e \<Longrightarrow> vars1 u_upd u \<Longrightarrow> ht emp (alloc u_upd e) (u \<mapsto> e)"
  apply (auto simp: alloc_def emp_def valid_mem_def singleton_def intro!: sl)
  apply (case_tac "let N = SOME n. True in Some (u_upd (\<lambda>_. N) a, [N \<mapsto> e a])")
  apply (metis option.distinct(1))
  apply (auto simp add: Let_unfold)
done

(* Disposal *)

lemma sl_dipose_local [sl]: "ht (e \<mapsto> -) (disposal e) (emp)"
  by (auto simp: disposal_def singleton_def valid_mem_def any_singleton_def emp_def intro!: sl)

lemma sl_disposal [sl]: "ht ((e \<mapsto> -) * r) (disposal e) r"
  by (subst bbi.mult_1[symmetric], (rule sl | rule lptran | rule sl_frame)+)

lemma sl_disposal_alt [sl]: "ht ((e \<mapsto> n) * r) (disposal e) r"
  apply (rule hl_pre)
  defer
  apply (rule sl_disposal)
  apply (rule bbi.qiso)
  by (auto simp: any_singleton_def singleton_def)

(* Lookup *)

lemma sl_lookup_local: "vars2 v_upd v v' \<Longrightarrow> vars3 v_upd v' \<Longrightarrow> free v_upd e \<Longrightarrow> 
    ht (e \<mapsto> v') (lookup v_upd e) ((v \<Midarrow> v') \<sqinter> (e \<mapsto> v'))"
  by (auto simp: lookup_def valid_mem_def singleton_def intro!: sl)

lemma sl_lookup_lkl: "vars1 v_upd v \<Longrightarrow> vars3 v_upd v'' \<Longrightarrow> free v_upd e \<Longrightarrow>
    ht ((v \<Midarrow> v') \<sqinter> (e \<mapsto> v'')) (lookup v_upd e) ((v \<Midarrow> v'') \<sqinter> (subst e v_upd v' \<mapsto> v))"
  by (auto simp: lookup_def valid_mem_def singleton_def intro!: sl)

lemma sl_lookup: "ht (EXS v'. (e \<mapsto> v') * ((e \<mapsto> v') -* (subst_pred r v_upd v'))) (lookup v_upd e) r"
  apply (auto simp: lookup_def intro!: sl)
  apply (subgoal_tac "(a, b) \<in> subst_pred r v_upd x")
  prefer 2
  using bbi.sep_impl_annil1 apply blast
  apply (auto simp: subst_pred_def)
  apply (clarsimp simp: valid_mem_def)
  prefer 2
  apply (clarsimp simp: valid_mem_def)
  apply (clarsimp simp: sep_def singleton_def)
  apply (rule_tac x="x a" in exI)
  apply (simp add: heap_divider)
  apply (subgoal_tac "y = x a")
  apply simp
  apply (clarsimp simp: sep_def singleton_def)
  apply auto
  by (simp add: domI ortho_def)

lemma sl_lookup': "ht (EXS v'. (e \<mapsto> $v') * ((e \<mapsto> $v') -* (subst_pred r v_upd $v'))) (lookup v_upd e) r"
  apply (auto simp: lookup_def intro!: sl)
  apply (subgoal_tac "(a, b) \<in> subst_pred r v_upd $x")
  prefer 2
  using bbi.sep_impl_annil1 apply blast
  apply (auto simp: subst_pred_def)
  apply (clarsimp simp: valid_mem_def)
  prefer 2
  apply (clarsimp simp: valid_mem_def)
  apply (clarsimp simp: sep_def singleton_def)
  apply (rule_tac x="x" in exI)
  apply (simp add: heap_divider)
  apply (subgoal_tac "y = x")
  apply simp
  apply (clarsimp simp: sep_def singleton_def)
  apply auto
  by (simp add: domI ortho_def)

lemma sl_lookup_alt: "ht (EXS v'. (e \<hookrightarrow> v') \<sqinter> (subst_pred r v_upd v')) (lookup v_upd e) r"
  apply (rule hl_pre)
  prefer 2
  apply (rule sl_lookup)
  apply (rule Collect_mono)
  apply (rule impI)
  apply (erule exE)
  apply (rule_tac x=xa in exI)
  apply (rule impE)
  prefer 2
  apply assumption
  prefer 2
  apply assumption
  apply (rule in_mono)
  apply (rule reynolds6)
done

lemma sl_lookup_alt' [sl]: "ht (EXS v'. (e \<hookrightarrow> $v') \<sqinter> (subst_pred r v_upd $v')) (lookup v_upd e) r"
  apply (rule hl_pre)
  prefer 2
  apply (rule sl_lookup)
  apply (rule Collect_mono)
  apply (rule impI)
  apply (erule exE)
  apply (rule_tac x="$xa" in exI)
  apply (rule impE)
  prefer 2
  apply assumption
  prefer 2
  apply assumption
  apply (rule in_mono)
  apply (rule reynolds6)
done

lemma sl_lookup_var: "p \<subseteq> (EXS v'. (e \<hookrightarrow> $v') \<sqinter> (subst_pred q v_upd $v')) \<Longrightarrow> ht p (lookup v_upd e) q"
  apply (rule hl_pre)
  apply assumption
  apply (rule sl_lookup_alt')
done

lemma lookup_suc_ref [sl]:"\<forall>x s. v (k_upd (\<lambda>_. x) s) = v s \<Longrightarrow> \<forall>x s. k (k_upd (\<lambda>_. x) s) = x \<Longrightarrow> 
  \<forall>x. subst_pred (R k) k_upd (\<lambda>_. x) = R (\<lambda>_. x) \<Longrightarrow> 
  ht (EXS x. (v \<mapsto> (\<lambda>_. a), (\<lambda>_. x)) * R (\<lambda>_. x)) (lookup k_upd (\<lambda>s. v s + 1)) ((v \<mapsto> (\<lambda>_. a), k) * R k)"
  apply (rule hl_classic)
  apply (rule mptran)+
  defer
  defer
  apply (rule sl_lookup_alt')
  defer
  apply (rule subset_refl)
  apply (rule mono_exs)
  apply (simp add: doublet_def)
  apply (rule conjI)
  apply (simp add: points_to_def)
  apply (metis (no_types, lifting) Assertions.bbi.intuitionistic_sep_conj_top Assertions.bbi.intuitionistic_sep_impl_closure Assertions.bbi.intuitionistic_top Assertions.bbi.sep_impl_annir2 Assertions.bbi.sep_impl_isoE Assertions.bbi.sep_impl_top_x Assertions.bbi.strongest_intuitionistic sep_comm top_greatest)
  apply (subst spred)+
  apply simp
done

lemma lookup_suc_ref':"\<forall>x s. v (k_upd (\<lambda>_. x) s) = v s \<Longrightarrow> \<forall>x s. k (k_upd (\<lambda>_. x) s) = x \<Longrightarrow> 
  \<forall>x. subst_pred (R k) k_upd (\<lambda>_. x) = R (\<lambda>_. x) \<Longrightarrow> 
  ht (EXS x. (v \<mapsto> (\<lambda>_. a), (\<lambda>_. x)) * R (\<lambda>_. x)) (lookup k_upd (\<lambda>s. v s + 1)) ((v \<mapsto> -) * (((\<lambda>s. v s + 1) \<mapsto> -) * R k))"
  apply (rule hl_classic)
  apply (rule mptran)+
  defer
  defer
  apply (rule sl_lookup_alt')
  defer
  apply (rule subset_refl)
  apply (rule mono_exs)
  apply (simp add: doublet_def)
  apply (rule conjI)
  apply (simp add: points_to_def)
  apply (metis (no_types, lifting) Assertions.bbi.intuitionistic_sep_conj_top Assertions.bbi.intuitionistic_sep_impl_closure Assertions.bbi.intuitionistic_top Assertions.bbi.sep_impl_annir2 Assertions.bbi.sep_impl_isoE Assertions.bbi.sep_impl_top_x Assertions.bbi.strongest_intuitionistic sep_comm top_greatest)
  apply (subst spred)+
  apply simp
  apply sep_auto
done

lemma lookup_suc_var_ref [sl]:"\<forall>x s. v (k_upd (\<lambda>_. x) s) = v s \<Longrightarrow> \<forall>x s. k (k_upd (\<lambda>_. x) s) = x \<Longrightarrow> 
  \<forall>x. subst_pred (R k) k_upd (\<lambda>_. x) = R (\<lambda>_. x) \<Longrightarrow> P \<le> (EXS x. (v \<mapsto> (\<lambda>_. a), (\<lambda>_. x)) * R (\<lambda>_. x)) \<Longrightarrow> 
  ht P (lookup k_upd (\<lambda>s. v s + 1)) ((v \<mapsto> -) * (((\<lambda>s. v s + 1) \<mapsto> -) * R k))"
  apply (rule hl_pre)
  defer
  apply (rule lookup_suc_ref')
  apply simp+
done

no_notation basic ("\<langle>_\<rangle>")

(***********************************************************************************************)

(* Hoare tactic *)

named_theorems hl_rules

method hoare_init uses simp = 
  ((subst simp | subst fst_conv | subst snd_conv)+)?

method hoare_step uses simp hl = 
  (hoare_init simp: simp, (assumption | rule subset_refl | rule mptran  | rule lptran | rule hl sl | rule allI | rule ballI | subst sep_assoc | rule hl_exs2))

method hoare_ind uses simp hl = 
  (hoare_step simp: simp hl: hl; (hoare_ind simp: simp hl: hl)?)+

method hoare uses simp hl = 
  (hoare_init simp: simp; (hoare_ind simp: simp hl: hl)?)

method hl_aux uses rule =
  (rule allI, rule rule; ((erule_tac x=u in allE)+, assumption))
  
end