theory Quantale_Tests
  imports Quantale "$AFP/KAT_and_DRA/SingleSorted/Test_Dioids"
begin

class quantales_tests = quantale + dioid_tests +
  assumes test_meet_closure: "test p \<Longrightarrow> test q \<Longrightarrow> test (p \<sqinter> q)"
begin

lemma test_meet: "test p \<Longrightarrow> test q \<Longrightarrow> p \<sqinter> q = p \<cdot> q"
  apply (auto simp: test_restrictl test_restrictr intro!: antisym)
  by (metis inf.boundedE test_meet_closure mult_inf_subdistr test_leq_mult_def_var test_mult_idem_var)

definition guards :: "('a \<times> 'a) set \<Rightarrow> 'a" where
  "guards GC \<equiv> \<Squnion>{b. \<exists>x. (b, x) \<in> GC \<and> test b}"

lemma test_guards: "test (guards GC)"
  sorry
  
definition comm :: "('a \<times> 'a) set \<Rightarrow> 'a" where
  "comm GC \<equiv> \<Squnion>{b \<cdot> x | b x. (b, x) \<in> GC \<and> test b}"

definition select :: "('a \<times> 'a) set \<Rightarrow> 'a" where
  "select GC \<equiv> comm GC"

lemma test_export_eq: "test p \<Longrightarrow> test b \<Longrightarrow> p\<cdot>b\<cdot>x \<le> b\<cdot>x\<cdot>q \<longleftrightarrow> p\<cdot>b\<cdot>x \<le> x\<cdot>q"
proof (default, metis local.order_trans local.test_restrictl mult_assoc)
  assume assm: "test p" "test b" "p\<cdot>b\<cdot>x \<le> x\<cdot>q"
  hence "p\<cdot>b\<cdot>x = b\<cdot>(p\<cdot>b\<cdot>x)"
    by (metis local.test_mult_comm_var local.test_mult_idem_var mult_assoc)
  also have "... \<le> b\<cdot>(x\<cdot>q)"
    by (simp add: assm(3) local.mult_isol)
  finally show "p \<cdot> b \<cdot> x \<le> b \<cdot> x \<cdot> q"
    by (simp add: mult_assoc)
qed

lemma "test p \<Longrightarrow> test q \<Longrightarrow> \<forall>b x. (b, x) \<in> GC \<and> test b \<longrightarrow> p\<cdot>b\<cdot>x \<le> x\<cdot>q \<Longrightarrow> p\<cdot>(select GC) \<le> (select GC)\<cdot>q"
proof (auto simp: select_def)
  assume assm: "test p" "\<forall>b x. (b, x) \<in> GC \<and> test b \<longrightarrow> p \<cdot> b \<cdot> x \<le> x \<cdot> q"
  hence a: "\<forall>b x. (b, x) \<in> GC \<and> test b \<longrightarrow> p \<cdot> (b \<cdot> x) \<le> b \<cdot> x \<cdot> q"
    by (auto simp: test_export_eq mult_assoc[symmetric])
  have "p \<cdot> (comm GC) = \<Squnion>{p \<cdot> (b \<cdot> x) |b x. (b, x) \<in> GC \<and> test b}"
    by (auto simp: comm_def Sup_mult_distl') (metis (no_types, lifting))
  also have "... \<le> \<Squnion>{b \<cdot> x \<cdot> q |b x. (b, x) \<in> GC \<and> test b}"
    apply (rule Sup_least)
    apply auto
    apply (rule Sup_upper2)
    apply auto
    using a apply auto
  done
  also have "... = comm GC \<cdot> q"
    by (auto simp: comm_def Sup_mult_distr') (metis (no_types, lifting))
  finally show "p \<cdot> comm GC \<le> comm GC \<cdot> q" .
qed
(*
definition repeat :: "('a \<times> 'a) set \<Rightarrow> 'a" where
  "repeat GC \<equiv> iteration (comm GC)"
*)

end

end
