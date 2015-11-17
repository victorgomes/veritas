theory RKAT_Models
  imports RKAT "$AFP/KAT_and_DRA/SingleSorted/KAT_Models"
begin

definition rel_spec :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel"  where
  "rel_spec P Q \<equiv> Sup {X. P O X \<subseteq> X O Q}"

abbreviation rel_not :: "'a rel \<Rightarrow> 'a rel" where
  "rel_not x \<equiv> Id \<inter> ( - x)"

lemma rel_spec1: "near_dioid_tests_zerol.test rel_not P \<Longrightarrow> 
   near_dioid_tests_zerol.test rel_not Q \<Longrightarrow>
   P O X \<subseteq> X O Q \<Longrightarrow> X \<le> rel_spec P Q"
   by (auto simp: rel_spec_def)

lemma rel_spec2: "near_dioid_tests_zerol.test rel_not P \<Longrightarrow> 
   near_dioid_tests_zerol.test rel_not Q \<Longrightarrow>
   X \<le> rel_spec P Q \<Longrightarrow> P O X \<subseteq> X O Q"
proof (simp add: rel_spec_def rel_dioid_tests.kat_eq2[symmetric])
  assume "X \<subseteq> \<Union>{X. (P O X) O (rel_not Q) = {}}"
  hence "(P O X) O (rel_not Q) \<subseteq> (P O \<Union>{X. (P O X) O (rel_not Q) = {}}) O (rel_not Q)"
    by (simp add: relcomp_mono)
  also have "... \<subseteq> \<Union>{(P O X)O (Id \<inter> - Q) | X. (P O X) O (rel_not Q) = {}} "
    by auto
  also have "... \<subseteq> {}"
    by auto
  finally show "(P O X) O (rel_not Q) = {}"
    by auto
qed

interpretation rel_rkat: rkat "op \<union>" "op O" "Id :: 'a rel" "{}" "op \<subseteq>" "op \<subset>" rtrancl rel_not rel_spec
  apply (default, default)
  apply (simp_all add: rel_spec1 rel_spec2)
done

end
