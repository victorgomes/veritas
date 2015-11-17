theory ListReversal
  imports LinkedList Syntax
begin

record rev_list =
  i :: nat
  j :: nat
  k :: nat
 
no_notation pmult_one_class.pmult_one ("1")

lemma "\<lbrakk>llist xs i, llist (rev xs) j\<rbrakk> \<le>
      `j := 0;
      while `i \<noteq> 0 do 
        `k := @(`i + 1);
        @(`i + 1) := `j;
        `j := `i;
        `i := `k
      od"
proof -
  have "\<lbrakk>llist xs i, llist (rev xs) j\<rbrakk> \<le>
      `j := 0; 
      \<lbrakk>EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>, llist (rev xs) j\<rbrakk>"
      by morgan (sep_auto, auto)
  also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        \<lbrakk>EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle>,
         EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>\<rbrakk>
      od"
      by morgan sep_auto+
  also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        \<lbrakk>EXS A B a k. (i \<mapsto> $a, $k) * llist A $k * llist B j * \<langle>rev xs = (rev (a#A)) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle>,
         EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>\<rbrakk>
      od"
      by morgan (sep_safe, sep_auto)
  also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        `k := @(`i + 1);
        \<lbrakk>EXS A B a. (i \<mapsto> $a, k) * llist A k * llist B j * \<langle>rev xs = (rev (a#A)) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle>,
         EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>\<rbrakk>
      od"
      by morgan sep_auto+
  also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        `k := @(`i + 1);
        @(`i + 1) := `j;
        \<lbrakk>EXS A B a. (i \<mapsto> $a, j) * llist A k * llist B j * \<langle>rev xs = (rev (a#A)) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle>,
         EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>\<rbrakk>
      od"
    by morgan
    also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        `k := @(`i + 1);
        @(`i + 1) := `j;
        \<lbrakk>EXS A B. llist A k * llist B i * \<langle>rev xs = (rev A) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle>,
         EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>\<rbrakk>
      od"
      by morgan sep_auto+
    also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        `k := @(`i + 1);
        @(`i + 1) := `j;
        `j := `i;
        \<lbrakk>EXS A B. llist A k * llist B j * \<langle>rev xs = (rev A) @ B\<rangle> * \<langle>`j \<noteq> 0\<rangle>,
         EXS A B. llist A i * llist B j * \<langle>rev xs = (rev A) @ B\<rangle>\<rbrakk>
      od"
      by morgan sep_auto
    also have "... \<le> 
      `j := 0; 
      while `i \<noteq> 0 do 
        `k := @(`i + 1);
        @(`i + 1) := `j;
        `j := `i;
        `i := `k
      od"
      by morgan sep_auto
    finally show ?thesis .
qed


lemma "\<turnstile> \<lbrace> list_seg (x#xs) i k \<rbrace>
      `j := @(`i + 1);
      dispose `i;
      dispose (`i + 1);
      `i := `j
    \<lbrace> list_seg xs i k \<rbrace>"
 by hoare sep_auto+

lemma exsI: "(x, y) \<in> (EXS xa xb xc x. P x \<inter> Q xa xb xc x) \<Longrightarrow> (x, y) \<in> (EXS x. P x \<inter> (EXS xa xb xc. Q xa xb xc x))"
  by auto

lemma deallocI [intro]: "(x, y) \<in> {(s, h). i s \<noteq> 0} \<Longrightarrow>
              (x, y) \<in> llist xa i \<Longrightarrow>
              (x, y) \<in> (EXS x. ((\<lambda>s. i (s\<lparr>j := i s\<rparr>) + 1) \<mapsto> (\<lambda>s. x)) * true \<inter> (EXS xa xb xc. ((\<lambda>s. j (s\<lparr>j := i s, i := x\<rparr>)) \<mapsto> (\<lambda>s. xa)) * (((\<lambda>s. j (s\<lparr>j := i s, i := x\<rparr>) + 1) \<mapsto> (\<lambda>s. xb)) * llist xc (\<lambda>s. i (s\<lparr>j := i s, i := x\<rparr>)))))"
  apply (rule exsI)
  apply safe
  apply (drule llist_cons) back
  apply assumption
  apply auto
  apply (rule_tac x="hd xa" in exI)
  apply (rule_tac x=j in exI)
  apply (rule_tac x="tl xa" in exI)
  apply (rule_tac x=j in exI)
  apply auto
by (metis (no_types, lifting) bbi.Sup.qisol bbi.mult.left_commute contra_subsetD top_greatest)

lemma "\<turnstile> \<lbrace> llist xs i \<rbrace>
      while `i \<noteq> 0 
      inv EXS ys. llist ys i 
      do
        `j := `i;
        `i := @(`i + 1);
        dispose `j;
        dispose (`j + 1)
      od
    \<lbrace> emp \<rbrace>"
by hoare (sep_safe, (rule deallocI, auto | sep_auto))+

declare sl_frame [sl]

lemma "\<turnstile> \<lbrace> llist xs i \<rbrace>
      `j := 0;
      while `i \<noteq> 0 
      inv EXS as bs. (llist as i * llist bs j) * \<langle>rev xs = rev as @ bs\<rangle>
      do
        \<lbrace> EXS A B a k. (i \<mapsto> $a, $k) * llist A $k * llist B j * \<langle>rev xs = (rev (a#A)) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle> \<rbrace>
        `k := @(`i + 1); 
        @(`i + 1) := `j
        \<lbrace> EXS A B a. (i \<mapsto> $a, j) * llist A k * llist B j * \<langle>rev xs = (rev (a#A)) @ B\<rangle> * \<langle>`i \<noteq> 0\<rangle> \<rbrace>;
        `j := `i;
        `i := `k
      od
      \<lbrace> llist (rev xs) j \<rbrace>"
by (hoare; sep_safe) sep_auto+

end