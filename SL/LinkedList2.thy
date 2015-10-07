theory LinkedList2
  imports StoreHeapModel
begin

(*
lemma tt1: "subst_pred (P * Q) i_update j = (subst_pred P i_update j) * (subst_pred Q i_update j)"
  by (auto simp: subst_pred_def sep_def)

lemma tt0: "subst_pred (P \<inter> Q) i_update j = (subst_pred P i_update j) \<inter> (subst_pred Q i_update j)"
  by (auto simp: subst_pred_def sep_def)

lemma tt2: "subst_pred (EXS k. (P k)) i_update j = (EXS k. (subst_pred (P k) i_update j))"
  by (auto simp: subst_pred_def sep_def)

lemma tt3: "subst_pred (EXS k. (P k) * (Q k)) i_update j = (EXS k. (subst_pred (P k) i_update j) * (subst_pred (Q k) i_update j))"
  by (auto simp: subst_pred_def sep_def)

lemma subst_singleton: "subst_pred (x \<mapsto> y) i_update j = (subst x i_update j \<mapsto> subst y i_update j)"
  by (auto simp: subst_pred_def singleton_def)

lemma subst_any_singleton: "subst_pred (x \<mapsto> -) i_update j = (subst x i_update j \<mapsto> -)"
  by (auto simp: subst_pred_def any_singleton_def singleton_def)

lemma subst_doublet: "subst_pred (x \<mapsto> y, z) i_update j = (subst x i_update j \<mapsto> subst y i_update j, subst z i_update j)"
  apply (subst doublet_def)+
  apply (subst tt1)+
  apply (subst subst_singleton)+
  apply (simp add:)
done

*)


lemma [simp]: "i a = 0 \<Longrightarrow> (a, b) \<in> llist x i \<Longrightarrow> x = []"
  apply (induct x)
  apply simp
  apply (simp add: llist_simp2)
done

lemma subst_llist [spred]: "subst_pred (llist xs m) i_update j = llist xs (subst m i_update j)"
  apply (simp add: llist_def spred)
  apply (simp add: subst_pred_def)
done


lemma [simp]: "{(s, h). True} = \<top>"
  by auto

lemma [spred]: "subst_pred UNIV i_update j = UNIV"
  by (auto simp: subst_pred_def)

lemma "i a = 0  \<Longrightarrow> (a, b) \<in> list_seg x i (\<lambda>_. 0) \<Longrightarrow> x = []"
  apply (induct x arbitrary: a b)
  apply simp+
  apply (auto simp: sep_def doublet_def singleton_def ortho_def)
oops

record test =
  i :: nat
  j :: nat
  k :: nat

lemma "ht (list_seg (Cons x xs) i k)
    (
      lookup j_update (\<lambda>s. (i s) + 1);
      dispose i;
      dispose (\<lambda>s. i s + 1);
      assign i_update j
    )
    (list_seg xs i k)"
apply hoare 

apply (rule hl_classic[rotated 3])
apply (rule sl_lookup_global[where v=j])
prefer 6
apply sep_normal
apply (rule subrelI)
apply(erule tt5')
defer
apply clarsimp
apply assumption
prefer 4
apply sep_normal
apply (rule split_pure)
apply (rule pred_exI')+
apply sep_auto
apply (erule tt5')
defer
apply (erule tt5')
defer
apply sep_normal

apply 
apply simp
apply sep_normal
apply sep_aut

    



lemma "ht (llist xs i)(
      assign j_update #0;
      awhile (EXS as bs. (llist as i * llist bs j) * (#(rev xs) \<Midarrow> #((rev as) @ bs)))
        ({(s, h). i s \<noteq> 0}) 
        (
          lookup k_update (\<lambda>s. i s + 1);
          mutation (\<lambda>s. i s + 1) j;
          assign j_update i;
          assign i_update k
        )
      )(llist (rev xs) j)"
apply hoar
apply sep_auto
apply sep_auto
prefer 3



apply (rule hl_post[where Q' = "EXS x as bs. ((i \<mapsto> #x, j) * llist as k * llist bs j) \<sqinter> (#(rev xs) \<Midarrow> #((rev (x#as)) @ bs))"])
apply (rule mptran)+
apply sep_auto
defer

  apply (rule hl_seq)
  apply (rule mptran)+
defer
  apply (rule hl_awhile)
  apply (rule mptran)+
  apply (rule order_refl)

prefer 3

  apply (rule hl_pre)
  defer
  apply (rule hl_assign)
  apply (rule order_refl)

prefer 3
  apply (subst spred)+
  apply (rule order_trans)
prefer 2
  apply (rule pred_exI[where x=xs])
  apply (rule order_trans)
prefer 2
  apply (rule pred_exI[where x="[]"])
  apply (simp add: spred subst_pred_def )

  apply (subst Collect_neg_eq[symmetric])
  apply (subst Collect_conj_eq[symmetric])
  apply clarsimp
  apply (subgoal_tac "x=[]")
  apply (clarsimp simp: emp_def sep_def llist_def)
  apply (clarsimp simp: emp_def sep_def ortho_def)
  

  apply (rule hl_seq)
  apply (rule mptran)+
  apply (rule hl_seq)
  apply (rule mptran)+
  apply (rule hl_seq)
  apply (rule mptran)+

prefer 4
  apply (rule hl_assign)
  apply (subst spred)+
  apply (rule order_refl)
prefer 3
  apply (rule hl_assign)
  apply (subst spred)+
  apply (rule order_refl)

prefer 2
  apply (rule hl_post[where Q' = "EXS x as bs. ((i \<mapsto> #x, j) * llist as k * llist bs j) \<sqinter> (#(rev xs) \<Midarrow> #((rev (x#as)) @ bs))"])
  apply (rule mptran)+

  apply (simp add: subst_pred_def)
  apply clarsimp
  apply (rule_tac x=xa in exI)
  apply (rule_tac x="x#xb" in exI)
  defer

  apply (rule sl_mut)

apply (rule hl_pre)
defer
apply (rule sl_lookup)
defer
apply (subst spred)+
apply (simp add: subst_pred_def)
apply clarsimp


  

end