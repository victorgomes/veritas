theory LinkedList3
  imports Refinement
begin

definition exact :: "'s pred \<Rightarrow> bool" where
  "exact p \<equiv> \<forall>s h h'. (s, h) \<in> p \<and> (s, h') \<in> p \<longrightarrow> dom h = dom h'"

lemma "exact (<p>)"
  apply (unfold exact_def )
apply (unfold pure_pred_def)
apply (auto simp: emp_def sep_def)
done


lemma [spred]: "subst_pred <P> i_update j = <subst_pred_s P i_update j>"
  by (auto simp: subst_pred_def pure_pred_def emp_def)

lemma [sep_simps, simp]: "<{}> = bot"
  by (auto simp: pure_pred_def) 

lemma [sep_simps, simp]: "s \<in> (if P then UNIV else {}) = P"
  by auto

lemma hd_tl: "x \<noteq> [] \<Longrightarrow> rev x @ y = rev (tl x) @ (Cons (hd x) y)"
  apply (induct x)
  apply simp
  apply auto
done



schematic_lemma s_singleton: "(s, h) \<in> (i \<mapsto> j) \<Longrightarrow> (s, h) \<in> (i \<mapsto> (\<lambda>_.?x))"
  by (auto simp: singleton_def)

lemma cutE1: "(s, h) \<in> p * q \<Longrightarrow> (\<And>s h. (s, h) \<in> q \<Longrightarrow> (s, h) \<in> q') \<Longrightarrow> (s, h) \<in> p * q'"
  by (auto simp: sep_def)

lemma cutE1': "(s, h) \<in> p \<Longrightarrow> (q = emp) \<Longrightarrow> (s, h) \<in> p * q"
  by (auto simp: sep_def emp_def)

schematic_lemma llist_J: "(s, h) \<in> llist xa j \<Longrightarrow> (s, h) \<in> llist xa (\<lambda>_. ?x)"
  apply (induct xa arbitrary: x)
  apply (simp add: llist_empty pure_pred_def)
oops

lemma final: "(s, h) \<in> llist xs j \<Longrightarrow> (s, h) \<in> llist xs (\<lambda>_. j s)"
  apply (induct xs)
  apply (simp add: sep_simps pure_pred_def)
  apply (simp add: llist_simp2)
  apply auto

        apply (erule split_pure_sepE)
        apply (erule pred_exE')
        apply (rule_tac x=x in exI)
        apply (simp add: singleton_def doublet_def sep_def)
        apply (erule split_pure_sepE)
        apply simp
done
    
declare  Set.Diff_eq [sep_simps]

schematic_lemma test: "(s, h) \<in> (i \<mapsto> j) * q \<Longrightarrow> (s, h) \<in> (i \<mapsto> (\<lambda>_.?x)) * q"
  by (auto simp: sep_def singleton_def)


lemma cutE2: "(s, h) \<in> p * q \<Longrightarrow> (\<And>s h. (s, h) \<in> q \<Longrightarrow> (s, h) \<in> p' * q') \<Longrightarrow> (s, h) \<in> p' * (p * q')"
  apply (auto simp: sep_def ortho_def)
by (smt Int_commute Un_empty dom_map_add inf_sup_distrib1 map_add_assoc map_add_comm)
(*
lemma cutE3: "(s, h) \<in> p * q \<Longrightarrow> (\<And>s h. (s, h) \<in> p \<Longrightarrow> (s, h) \<in> p') \<Longrightarrow> (\<And>s h. (s, h) \<in> q \<Longrightarrow> (s, h) \<in> q') \<Longrightarrow> (s, h) \<in> p' * q'"
  sorry
*)
record rev_list =
  i :: nat
  j :: nat
  k :: nat


find_consts name: j_update

lemma "spec (llist xs i) (llist (rev xs) j) \<le> (
      assign j_update #0;
      while ({(s, h). i s \<noteq> 0}) 
        (
          lookup k_update (\<lambda>s. i s + 1);
          mutation (\<lambda>s. i s + 1) j;
          assign j_update i;
          assign i_update k
        )
      )"
proof -
  have "spec (llist xs i) (llist (rev xs) j) \<le>
      assign j_update #0; 
      (spec (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>) (llist (rev xs) j))"
      apply morgan
        apply sep_normal

        
        apply (rule subrelI)
        apply (rule Set.IntI)
        apply (erule Set.IntE)

        apply (erule pred_exE')+
        apply (erule split_pure_sepE)+

        apply (erule cutE1)+
        apply (erule cutE2)+


        apply (rule pred_exI')+
        apply (rule split_pure_sep')+

        apply simp_all
        
        apply (erule cutE1)+
        apply (erule cutE1')+
        apply (erule cutE2)+

        defer
            apply (erule cutE1)+
            apply (erule cutE1')+
            apply (erule cutE2)+
        defer
        
        apply sep_normal
        defer
          apply sep_normal

        apply auto
    done
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        (spec (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      apply morgan

      apply sep_normal

        apply (rule subrelI)+
        apply (rule Set.IntI)
        apply (erule Set.IntE)+

        apply (erule pred_exE')+
        apply (erule split_pure_sepE)+

        apply (erule cutE1)+
        apply (erule cutE2)+


        apply (rule pred_exI')+
        apply (rule split_pure_sep')+

        apply simp
        apply simp



      apply sep_normal
        apply (rule subrelI)+
        apply (rule Set.IntI)
        apply (erule Set.IntE)+

        apply (erule pred_exE')+
        apply (erule split_pure_sepE)+

        apply (erule cutE1)+
        apply (erule cutE2)+


        apply (rule pred_exI')+
        apply (rule split_pure_sep')+

        apply simp
        apply simp

      apply sep_normal

        apply (rule subrelI)+
        apply (rule Set.IntI)
        apply (erule Set.IntE)+

        apply (erule pred_exE')+
        apply (erule split_pure_sepE)+

        apply (erule cutE1)+
        apply (erule cutE2)+


        apply (rule pred_exI')+
        apply (rule split_pure_sep')+

        apply simp
        apply simp

        apply (rule split_pure_neg)
        apply (erule pred_exE')+
        apply (erule split_pure_sep_nostateE)
        apply simp
        apply (erule zero, simp)
        apply simp
      done
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        (spec (EXS A B a k. (i \<mapsto> #a, #k) * llist A #k * llist B j * <{s. rev xs = (rev (Cons a A)) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"

      apply morgan

      apply sep_normal
        apply (rule split_pure_sep)

        apply (erule not_zero, simp)
        apply sep_normal

        apply (erule pred_exE')+
        apply (erule split_pure_sepE)+

        apply (rule pred_exI')+

        apply (rule split_pure_sep')

        apply simp
        apply (rule hd_tl)
        apply simp

        apply assumption
      done
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        (spec (EXS A B a. (i \<mapsto> #a, k) * llist A k * llist B j * <{s. rev xs = (rev (Cons a A)) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"

      apply morgan
      apply simp
      apply simp
      apply sep_normal
      apply simp
    done
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        (spec (EXS A B a. (i \<mapsto> #a, j) * llist A k * llist B j * <{s. rev xs = (rev (Cons a A)) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
    by morgan
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        (spec (EXS A B a. llist A k * (i \<mapsto> #a, j) * llist B j * <{s. rev xs = (rev (Cons a A)) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
    apply morgan
      apply (rule mono_exs2)+
      apply sep_normal
         apply (rule split_pure_sep)
        apply (rule pred_exI')
        apply (rule split_pure_sep')
        apply simp
        apply simp       

        apply (erule cutE2 | erule cutE1 | assumption)+
      done

    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        (spec (EXS A B a. llist A k * llist (Cons a B) i * <{s. rev xs = (rev A) @ (Cons a B)}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      apply morgan
      apply (rule mono_exs2)+
      apply sep_normal
         apply (rule split_pure_sep)

         apply (subst exs[symmetric])+


        apply (rule split_pure_sep')
        apply simp
        apply simp   
        apply (erule cutE1)+

        apply (rule pred_exI')
        apply (rule test[where j=j])


        apply (erule cutE1_s)
        apply simp
thm final
        apply (simp add: final)
        apply (erule s_singleton)

        apply (erule cutE1_s)
          apply (assumption | erule cutE2 | erule cutE1)+
        sorry

    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        (spec (EXS A B. llist A k * llist B i * <{s. rev xs = (rev A) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      apply morgan

      apply sep_normal
         apply (rule split_pure_sep)
        apply (rule split_pure_conj)
        apply (erule pred_exE')+
        apply (erule split_pure_sep_nostateE)
        apply (rule pred_exI')+
        apply (rule split_pure_sep')
        apply simp
        apply simp

        apply sep_normal
         apply (rule split_pure_sep)
        apply (rule split_pure_conj)
        apply (erule pred_exE')+
        apply (erule split_pure_sep_nostateE)
        apply (rule pred_exI')+
        apply (rule split_pure_sep')
        apply simp
        apply simp
        
      done
    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        assign j_update i;
        (spec (EXS A B. llist A k * llist B j * <{s. rev xs = (rev A) @ B}> * <{s. j s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      apply morgan
      apply sep_normal
         apply (rule split_pure_sep)
        apply (rule split_pure_conj)
        apply (erule pred_exE')+
        apply (erule split_pure_sep_nostateE)
        apply (rule pred_exI')+
        apply (rule split_pure_sep')
        apply simp
        apply simp
      done
    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        assign j_update i;
        assign i_update k
      )"
      apply morgan
      apply sep_normal
         apply (rule split_pure_sep)
        apply (rule split_pure_conj)
        apply (erule pred_exE')+
        apply (erule split_pure_sep_nostateE)
        apply (rule pred_exI')+
        apply (rule split_pure_sep')
        apply simp
        apply simp
      done
    finally show ?thesis .
qed

end