theory LinkedList3
  imports Refinement
begin


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
      by morgan (sep_auto, auto)
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        (spec (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      by morgan sep_auto+
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        (spec (EXS A B a k. (i \<mapsto> #a, #k) * llist A #k * llist B j * <{s. rev xs = (rev (Cons a A)) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      by morgan (sep_safe, sep_auto)
  also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        (spec (EXS A B a. (i \<mapsto> #a, k) * llist A k * llist B j * <{s. rev xs = (rev (Cons a A)) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      by morgan sep_auto+
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
    by morgan sep_auto
    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        (spec (EXS A B a. llist A k * llist (Cons a B) i * <{s. rev xs = (rev A) @ (Cons a B)}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      by morgan sep_auto
    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        (spec (EXS A B. llist A k * llist B i * <{s. rev xs = (rev A) @ B}> * <{s. i s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      by morgan sep_auto+
    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        assign j_update i;
        (spec (EXS A B. llist A k * llist B j * <{s. rev xs = (rev A) @ B}> * <{s. j s \<noteq> 0}>)
              (EXS A B. llist A i * llist B j * <{s. rev xs = (rev A) @ B}>))
      )"
      by morgan sep_auto
    also have "... \<le> 
      assign j_update #0; 
      while ({(s, h). i s \<noteq> 0})  (
        lookup k_update (\<lambda>s. i s + 1);
        mutation (\<lambda>s. i s + 1) j;
        assign j_update i;
        assign i_update k
      )"
      by morgan sep_auto
    finally show ?thesis .
qed


lemma "ht (llist xs i)(
      assign j_update #0;
      awhile (EXS as bs. (llist as i * llist bs j) * (<{s. rev xs = rev as @ bs}>))
        ({(s, h). i s \<noteq> 0}) 
        (
          lookup k_update (\<lambda>s. i s + 1);
          mutation (\<lambda>s. i s + 1) j;
          assign j_update i;
          assign i_update k
        )
      )(llist (rev xs) j)"
apply hoare
apply sep_auto
defer
apply sep_auto
apply sep_auto
defer
defer
apply sep_auto


end