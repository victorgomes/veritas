theory RKAT_Models
  imports RKAT "$AFP/KAT_and_DRA/SingleSorted/KAT_Models"
begin

definition rel_spec :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel"  where
  "rel_spec P Q \<equiv> Sup {X. P O X \<subseteq> X O Q}"

lemma rel_specD: "near_dioid_tests_zerol.test (\<lambda>x. Id \<inter> - x) P \<Longrightarrow> 
   near_dioid_tests_zerol.test (\<lambda>x. Id \<inter> - x) Q \<Longrightarrow>
   X \<le> rel_spec P Q \<Longrightarrow> P O X \<subseteq> X O Q"
(*
  apply (subst rel_kat.hoare_triple_def_var)
  apply auto
  apply (subgoal_tac "xa = y")
  prefer 2
  apply (metis rel_kat.test_absorb3 rel_kat.test_comp_add rel_kat.test_def rel_kat.test_restrictr pair_in_Id_conv subsetCE)
  apply simp
  apply (subgoal_tac "(y, z) \<in> rel_spec p q")
  prefer 2
  apply (metis subsetCE)
  apply (rule relcompI)
  apply assumption
  apply (auto simp: rel_spec_def)
  apply (subst (asm) rel_kat.hoare_triple_def_var) back
  apply auto
  apply (subgoal_tac "(y, z) \<in> p O xa")
  prefer 2
  apply force
  apply (subgoal_tac "(y, z) \<in> xa O q")
  prefer 2
  apply force
  apply (erule relcompE) back
  by (metis Id_O_R rel_kat.test_restrictr pair_in_Id_conv prod.inject subsetCE)
*)
sorry

abbreviation rel_not :: "'a rel \<Rightarrow> 'a rel" where
  "rel_not x \<equiv> Id \<inter> ( - x)"

interpretation rel_rkat: rkat "op \<union>" "op O" "Id :: 'a rel" "{}" "op \<subseteq>" "op \<subset>" rtrancl rel_not rel_spec
  apply (default, safe) 
  apply (clarsimp simp: rel_spec_def)
  apply (rule_tac x=x in exI)
  apply force
  apply (auto simp: rel_dioid_tests.test_def rel_spec_def)
  apply (subgoal_tac "xa = y")
  prefer 2
  apply blast
  apply simp
  apply (subgoal_tac "(y, z) \<in> \<Union>{X. p O X \<subseteq> X O q}")
  prefer 2
  apply blast
  apply (subgoal_tac "\<exists>X. (y, z) \<in> X \<and> p O X \<subseteq> X O q")
apply clarsimp

sorry

end
