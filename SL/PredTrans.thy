theory PredTrans
  imports Assertions
begin

type_synonym 'a ptran = "'a pred \<Rightarrow> 'a pred"

(* Commands in Predicate Transformer Semantics *)

definition abort :: "'a ptran" where
  "abort q \<equiv> bot"

definition magic :: "'a ptran" where
  "magic q \<equiv> top"

definition skip :: "'a ptran" where
  "skip \<equiv> id"

definition assumption :: "'a pred \<Rightarrow> 'a ptran" ("\<lfloor>_\<rfloor>" [50] 100) where
  "\<lfloor>p\<rfloor> \<equiv> \<lambda>q. -p \<squnion> q"

definition seq :: "'a ptran \<Rightarrow> 'a ptran \<Rightarrow> 'a ptran" (infixl ";" 65) where
  "seq \<equiv> op o"

definition cond :: "'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a ptran \<Rightarrow> 'a ptran" where
  "cond b F G \<equiv> (\<lfloor>b\<rfloor> o F) \<sqinter> (\<lfloor>-b\<rfloor> o G)"

primrec pow :: "'a ptran \<Rightarrow> nat \<Rightarrow> 'a ptran" where
  "pow F 0 = \<top>"
| "pow F (Suc n) = F o (pow F n)"

lemma iso_pow: "mono F \<Longrightarrow> F \<le> G \<Longrightarrow> pow F n \<le> pow G n"
  apply (induct n)
  apply simp
  apply auto
  apply (simp add: le_fun_def)
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (erule_tac x="pow G n x" in allE)
  apply (rule order_trans[rotated])
  apply assumption
  apply (rule monoE)
  apply assumption+
done

definition iteration :: "'a ptran \<Rightarrow> 'a ptran" ("_\<^sup>\<omega>" [999] 1000) where
  "F\<^sup>\<omega> \<equiv> \<Sqinter>{pow F n | n. True}"

lemma iso_iter: "mono F \<Longrightarrow> F \<le> G \<Longrightarrow> F\<^sup>\<omega> \<le> G\<^sup>\<omega>"
  apply (auto simp: iteration_def intro!: Inf_mono)
  apply (rule_tac x="pow F n" in exI)
  apply (auto intro: iso_pow)
done

definition while :: "'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a ptran" where
  "while b F \<equiv> (\<lfloor>b\<rfloor> o F)\<^sup>\<omega> o \<lfloor>-b\<rfloor>"

lemma iso_while: "mono F \<Longrightarrow> F \<le> G \<Longrightarrow> while b F \<le> while b G"
proof (auto simp: while_def)
  assume a: "F \<le> G" and "mono F"
  hence "mono (\<lfloor>b\<rfloor> \<circ> F)"
    by (auto simp: mono_def assumption_def)
  moreover have "\<lfloor>b\<rfloor> \<circ> F \<le> \<lfloor>b\<rfloor> \<circ> G"
    using a by (auto simp: assumption_def le_fun_def)
  ultimately have "(\<lfloor>b\<rfloor> \<circ> F)\<^sup>\<omega> \<le> (\<lfloor>b\<rfloor> \<circ> G)\<^sup>\<omega>"
    by (auto intro!: iso_iter)
  thus "(\<lfloor>b\<rfloor> \<circ> F)\<^sup>\<omega> \<circ> \<lfloor>- b\<rfloor> \<le> (\<lfloor>b\<rfloor> \<circ> G)\<^sup>\<omega> \<circ> \<lfloor>- b\<rfloor>"
    by (auto simp: le_fun_def)
qed

text {* Annotated programs for automatic verification *}

definition awhile :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a ptran" where
  "awhile i b x \<equiv> while b x"

definition apre :: "'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a ptran" where
  "apre p x \<equiv> x"

definition apost :: "'a ptran \<Rightarrow> 'a pred\<Rightarrow> 'a ptran" where
  "apost x q \<equiv> x; apre q skip"

definition aprog :: "'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a pred \<Rightarrow> 'a ptran" where
  "aprog p x q \<equiv> x"


(* Algebraic Structure *)

interpretation PT!: near_quantale_unital id "op o" Inf Sup inf less_eq less sup bot "top :: 'a ptran"
  by default auto

(* Commands are co-continue *)

definition cocontinuity :: "('a :: complete_lattice \<Rightarrow> 'a) \<Rightarrow> bool" where
  "cocontinuity f \<equiv> \<forall>X. \<Sqinter> (f ` X) = f (\<Sqinter> X)"

lemma cc_mono: "cocontinuity f \<Longrightarrow> mono f"
  by (simp add: Inf_continuity_mono cocontinuity_def monoI)  

named_theorems ccptran

lemma cc_eq: "cocontinuity f \<longleftrightarrow> (\<forall>X. f (\<Sqinter>X) = \<Sqinter>{f x | x. x \<in> X})"
  apply (auto simp: cocontinuity_def)
  apply (metis Collect_mem_eq Inf_image_eq image_Collect)
  by (metis Collect_mem_eq Inf_image_eq image_Collect)

lemma cc_top [ccptran]: "cocontinuity \<top>"
  by (auto simp: cocontinuity_def magic_def)

lemma cc_magic [ccptran]: "cocontinuity (magic)"
  by (auto simp: cocontinuity_def magic_def)

lemma cc_skip [ccptran]: "cocontinuity (skip)"
  by (auto simp: cocontinuity_def skip_def)

lemma cc_assumption [ccptran]: "cocontinuity (\<lfloor>p\<rfloor>)"
  by (auto simp: cocontinuity_def assumption_def)

lemma cc_apply [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity G \<Longrightarrow> cocontinuity (F o G)"
  by (auto simp: cc_eq cocontinuity_def intro!: Inf_eqI Inf_lower Inf_greatest) force

lemma cc_seq [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity G \<Longrightarrow> cocontinuity (F; G)"
  by (auto simp: seq_def intro!: ccptran)

lemma cc_inf [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity G \<Longrightarrow> cocontinuity (F \<sqinter> G)"
  apply (auto simp: cocontinuity_def)
  by (metis INF_inf_distrib)

lemma cc_cond [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity G \<Longrightarrow> cocontinuity (cond b F G)"
  by (auto simp: cond_def intro: ccptran)

lemma cc_pow [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (pow F n)"
  by (induct n) (auto intro: ccptran)

lemma cc_Inf [ccptran]: "\<forall>f \<in> F. cocontinuity f \<Longrightarrow> cocontinuity (\<Sqinter>F)"  
proof (simp add: cc_eq, rule allI)
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

lemma cc_iter [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (F\<^sup>\<omega>)"
  by (auto simp: iteration_def intro!: ccptran)

lemma cc_while [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (while b F)"
  by (auto simp: while_def intro: ccptran)

lemma cc_awhile [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (awhile i b F)"
  by (auto simp: awhile_def intro: ccptran)

lemma cc_apre [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (apre p F)"
  by (auto simp: apre_def intro: ccptran)

lemma cc_apost [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (apost F q)"
  by (auto simp: apost_def intro: ccptran)

lemma cc_aprog [ccptran]: "cocontinuity F \<Longrightarrow> cocontinuity (aprog p F q)"
  by (auto simp: aprog_def intro: ccptran)

(* Commands are monotone *)

named_theorems mptran

lemma mono_top [mptran]: "mono (\<top> :: 'a ptran)"
  by (auto intro: cc_mono ccptran)

lemma mono_magic [mptran]: "mono (magic)"
  by (auto simp: magic_def intro: cc_mono ccptran)

lemma mono_skip [mptran]: "mono (skip)"
  by (auto intro!: cc_mono ccptran)

lemma mono_assumption [mptran]: "mono (\<lfloor>p\<rfloor>)"
  by (auto intro!: cc_mono ccptran)

lemma mono_apply [mptran]: "mono F \<Longrightarrow> mono G \<Longrightarrow> mono (F o G)"
  by (auto simp: mono_def)

lemma mono_seq [mptran]: "mono F \<Longrightarrow> mono G \<Longrightarrow> mono (F; G)"
  by (auto simp: seq_def intro!: mptran)

lemma mono_inf [mptran]: "mono F \<Longrightarrow> mono G \<Longrightarrow> mono (F \<sqinter> G)"
  by (auto simp: mono_def le_infI1 le_infI2)

lemma mono_cond [mptran]: "mono F \<Longrightarrow> mono G \<Longrightarrow> mono (cond b F G)"
  by (auto simp: cond_def intro: mptran)

lemma mono_pow [mptran]: "mono F \<Longrightarrow> mono (pow F n)"
  by (induct n) (auto intro: mptran)

lemma mono_Inf [mptran]: "\<forall>(f :: 'a :: complete_lattice \<Rightarrow> 'a) \<in> F. mono f \<Longrightarrow> mono (\<Sqinter> F)"
  by (auto simp: order_class.mono_def, rule INF_mono) auto

lemma mono_iter [mptran]: "mono F \<Longrightarrow> mono (F\<^sup>\<omega>)"
  by (auto simp: iteration_def intro!: mptran)

lemma mono_while [mptran]: "mono F \<Longrightarrow> mono (while b F)"
  by (auto simp: while_def intro: mptran)

lemma mono_awhile [mptran]: "mono F \<Longrightarrow> mono (awhile i b F)"
  by (auto simp: awhile_def intro: mptran)

lemma mono_apre [mptran]: "mono F \<Longrightarrow> mono (apre p F)"
  by (auto simp: apre_def intro: mptran)

lemma mono_apost [mptran]: "mono F \<Longrightarrow> mono (apost F q)"
  by (auto simp: apost_def intro: mptran)

lemma mono_aprog [mptran]: "mono F \<Longrightarrow> mono (aprog p F q)"
  by (auto simp: aprog_def intro: mptran)

(* Locality *)

abbreviation local_pred :: "'a pred \<Rightarrow> bool" where
  "local_pred \<equiv> bbi.intuitionistic"

definition local :: "'a ptran \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "local F r \<equiv> \<forall>q. (F q) * r \<le> F (q * r)"

(* Commands are local *)

named_theorems lptran

lemma local_top [lptran]: "local \<top> r"
  by (auto simp: local_def)

lemma local_abort [lptran]: "local (abort) r"
  by (auto simp: local_def abort_def)

lemma local_magic [lptran]: "local (magic) r"
  by (auto simp: local_def magic_def)

lemma local_skip [lptran]: "local (skip) r"
  by (auto simp: local_def skip_def)

lemma local_assumption [lptran]: "local_pred (-p) \<Longrightarrow> local (\<lfloor>p\<rfloor>) r"
  apply (simp add: local_def assumption_def)
  using Assertions.bbi.intuitionistic_upward_closure_var bbi.Sup.qdistr by blast

lemma local_apply [lptran]: "mono F \<Longrightarrow> local F r \<Longrightarrow> local G r \<Longrightarrow> local (F o G) r"
proof (subst local_def, rule allI, simp)
  fix q assume assm: "mono F" "local F r" "local G r"
  hence "F (G q) * r \<le> F (G q * r)"
    by (simp add: local_def)
  also have "... \<le> F (G (q * r))"
    using assm by (simp add: local_def mono_def)
  finally show "F (G q) * r \<subseteq> F (G (q * r))"
    by (simp add: local_def)
qed

lemma local_seq [lptran]: "mono F \<Longrightarrow> local F r \<Longrightarrow> local G r \<Longrightarrow> local (F; G) r"
  by (auto simp: seq_def intro: lptran)

lemma local_inf [lptran]: "local F r \<Longrightarrow> local G r \<Longrightarrow> local (F \<sqinter> G) r"
  apply (auto simp: local_def)
  using Assertions.bbi.qmeet_subdistr apply blast
  using Assertions.bbi.qmeet_subdistr apply blast
done

lemma local_cond [lptran]: "local_pred b \<Longrightarrow> local_pred (-b) \<Longrightarrow> local F r \<Longrightarrow> local G r \<Longrightarrow> local (cond b F G) r"
  by (auto simp: cond_def intro!: ccptran mptran lptran)

lemma local_pow [lptran]: "mono F \<Longrightarrow> local F r \<Longrightarrow> local (pow F n) r"
  by (induct n) (auto intro: lptran)

lemma local_Inf [lptran]: "\<forall>f \<in> F. local f r \<Longrightarrow> local (\<Sqinter>F) r"
  apply (simp add: local_def, rule allI)
  apply (rule INF_greatest)
  apply auto
by (metis (no_types) INF_lower2 bbi.Sup.qisol order_refl sep_comm subsetCE)

lemma local_iter [lptran]: "mono F \<Longrightarrow> local F r \<Longrightarrow> local (F\<^sup>\<omega>) r"
  by (auto simp: iteration_def intro: lptran)

lemma local_while [lptran]: "local_pred b \<Longrightarrow> local_pred (-b) \<Longrightarrow> mono F \<Longrightarrow> local F r \<Longrightarrow> local (while b F) r"
  by (auto simp: while_def intro!: lptran mptran)

lemma local_awhile [lptran]: "mono F \<Longrightarrow> local_pred b \<Longrightarrow> local_pred (-b) \<Longrightarrow> local F r \<Longrightarrow> local (awhile i b F) r"
  by (auto simp: awhile_def intro!: lptran mptran)

lemma local_apre [lptran]: "local F r \<Longrightarrow> local (apre p F) r"
  by (auto simp: apre_def intro: lptran)

lemma local_apost [lptran]: "mono F \<Longrightarrow> local F r \<Longrightarrow> local (apost F q) r"
  by (auto simp: apost_def intro!: lptran)

lemma local_aprog [lptran]: "local F r \<Longrightarrow> local (aprog p F q) r"
  by (auto simp: aprog_def intro: lptran)

(* Separation logic *)

named_theorems sl

definition ht :: "'a pred \<Rightarrow> 'a ptran \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "ht p F q \<equiv> p \<le> F q"

lemma hl_skip [sl]: "p \<le> q \<Longrightarrow> ht p skip q"
  by (auto simp: ht_def skip_def)                              

lemma hl_apply [sl]: "mono F \<Longrightarrow> ht p F r \<Longrightarrow> ht r G q \<Longrightarrow> ht p (F o G) q"
  apply (simp add: ht_def mono_def seq_def)
  apply (rule order_trans)
  apply assumption
  apply (erule_tac x=r in allE)
  apply (erule_tac x="G q" in allE)
  by force

lemma hl_seq [sl]: "mono F \<Longrightarrow> ht p F r \<Longrightarrow> ht r G q \<Longrightarrow> ht p (F; G) q"
  by (auto simp: seq_def intro: sl)

lemma hl_asumption [sl]: "ht (b \<sqinter> p) F q \<Longrightarrow> ht p (\<lfloor>b\<rfloor> o F) q"
  by (simp add: ht_def seq_def assumption_def) blast

lemma hl_inf [sl]: "ht p F q \<Longrightarrow> ht p G q \<Longrightarrow> ht p (F \<sqinter> G) q"
  by (simp add: ht_def)

lemma hl_cond [sl]: "ht (b \<sqinter> p) F q \<Longrightarrow> ht (-b \<sqinter> p) G q \<Longrightarrow> ht p (cond b F G) q"
  by (auto simp: cond_def intro!: sl)

lemma "(F :: 'a ptran) \<le> F\<^sup>\<omega>"
  apply (auto simp: iteration_def)
  apply (rule Inf_greatest)
  apply auto
  apply (induct_tac n)
  apply (auto simp: le_fun_def)
oops

lemma hl_pow [sl]: "mono F \<Longrightarrow> p \<le> F p \<Longrightarrow> p \<le> pow F n p"
  apply (induct n)
  apply force
  apply simp
  apply (rule order_trans)
  apply assumption back
  apply (rule monoE)
  apply assumption+
done

lemma hl_iter [sl]: "mono F \<Longrightarrow> ht p F p \<Longrightarrow> ht p F\<^sup>\<omega> p"
  apply (simp add: ht_def iteration_def)
  apply (rule INF_greatest)
  apply auto
  using hl_pow by blast

lemma hl_while [sl]: "mono F \<Longrightarrow> ht (b \<sqinter> i) F i \<Longrightarrow> ht i (while b F) (-b \<sqinter> i)"
  apply (auto simp: while_def intro!: sl mptran)
  by (auto simp: ht_def assumption_def)

lemma sl_frame [sl]: "local F r \<Longrightarrow> ht p F q \<Longrightarrow> ht (p * r) F (q * r)"
  apply (auto simp: local_def ht_def)
  by (meson Assertions.bbi.sep_implE1 Assertions.bbi.sep_implI1 contra_subsetD dual_order.trans)

lemma sl_frame2 [sl]: "local F r \<Longrightarrow> ht p F q \<Longrightarrow> ht (r * p) F (r * q)"
sorry

text {* Weakening / Strengthening / Consequence Rules *}

lemma hl_pre: "P \<le> P' \<Longrightarrow> ht P' F Q \<Longrightarrow> ht P F Q"
  by (fastforce simp: ht_def)

lemma hl_post: "mono F \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P F Q' \<Longrightarrow> ht P F Q"
  by (meson hl_pre ht_def mono_def)

lemma hl_classic: "mono F \<Longrightarrow> P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' F Q' \<Longrightarrow> ht P F Q"
  by (rule hl_pre, assumption, rule hl_post, auto)

text {* Annotated programs *}

lemma hl_awhile [sl]: "mono F \<Longrightarrow> P \<subseteq> i \<Longrightarrow> -b \<inter> i \<subseteq> Q \<Longrightarrow> ht (b \<sqinter> i) F i \<Longrightarrow> ht P (awhile i b F) Q"
  by (rule hl_classic) (auto simp: awhile_def intro: mptran sl)
  
lemma hl_apre_classic [sl]: "P \<le> P' \<Longrightarrow> ht P' F Q \<Longrightarrow> ht P (apre P' F) Q"
  by (auto simp: apre_def intro: hl_pre)

lemma hl_apost_classic [sl]: "mono F \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P F Q' \<Longrightarrow> ht P (apost F Q') Q"
  by (auto simp: apost_def intro!: sl)
  
lemma hl_aprog_classic [sl]: "mono F \<Longrightarrow> P \<le> P' \<Longrightarrow> Q' \<le> Q \<Longrightarrow> ht P' F Q' \<Longrightarrow> ht P (aprog P' F Q') Q"
  by (auto simp: aprog_def intro: sl hl_classic)

lemma hl_exs: "(\<And>x. ht (P x) F Q) \<Longrightarrow> ht (EXS x. P x) F Q"
  by (auto simp: ht_def)

lemma hl_exs2: "mono F \<Longrightarrow> (\<forall>x . ht (P x) F (Q x)) \<Longrightarrow> ht (EXS x. P x) F (EXS x. Q x)"
  apply (auto simp: ht_def)
  apply (erule_tac x=x in allE)
  apply (erule monoE)
  apply (rule pred_exI2)
  apply force
done

lemma hl_exs3: "mono F \<Longrightarrow> (\<And>x . ht P F (Q x)) \<Longrightarrow> ht P F (EXS x. Q x)"
  apply (auto simp: ht_def)
  apply (erule monoE)
  apply (rule pred_exI2)
  apply force
done

end