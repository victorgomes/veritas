theory Separation_Semiring
  imports Domain_Semiring Range_Semiring
begin

no_notation
  fdiamond ("\<bar> _ \<rangle> _" [50,90] 95) and
  fbox ("\<bar> _ ] _" [50,90] 95) and
  bdiamond ("\<langle> _ \<bar> _" [50,90] 95) and
  bbox ("[ _ \<bar> _" [50,90] 95) and
  times (infixl "*" 70)

context antidomain_semiring
begin

definition fdia :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<bar>_\<rangle>_" [99, 99] 100) where
  "\<bar>x\<rangle>y = d(x\<cdot>y)"
  
definition fbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<bar>_]_" [99, 99] 100) where
  "\<bar>x]y = a( \<bar>x\<rangle> a(y) )"

lemma fbox_def_var: "\<bar>x]y = a(x\<cdot>a(y))"
  by (metis fdia_def fbox_def local.a_5)
  
sublocale fmodal: fmodal_semiring where fdiamond = fdia and fbox = fbox
  apply default
  apply (simp_all add: fdia_def fbox_def_var)
done
  
lemma fswap: "p = d(p) \<Longrightarrow> q = d(q) \<Longrightarrow> \<bar>x\<rangle>p \<le> \<bar>y]q \<longleftrightarrow> \<bar>y\<rangle>a(q) \<le> \<bar>x]a(p)"
  by (metis local.a_antitone local.antidomain_semiring_domain_def local.fmodal.fbox_fdia_de_morgan_1 local.fmodal.fdia_fbox_de_morgan_2)

end

interpretation rel: antidomain_semiring "op \<union>" "op O" Id "{}" "\<lambda>x. -(Id \<inter> x O UNIV) \<inter> Id" "op \<subseteq>" "op \<subset>"
apply default
apply auto
by (metis ComplI IdI Int_iff UNIV_I compl_inf relcomp.simps)

interpretation rel: antirange_semiring "op \<union>" "op O" Id "{}" "\<lambda>x. -(Id \<inter> UNIV O x) \<inter> Id" "op \<subseteq>" "op \<subset>"
apply default
apply auto
by (metis ComplI IdI Int_iff UNIV_I compl_inf relcomp.simps)

class sepconj =
  fixes sepconj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 80)
  and sepunit :: "'a" ("e")
  
class ss_domain = antidomain_semiring + sepconj +
  assumes d6: "d(d(x) * d(y)) = d(x) * d(y)"
  and d7: "d(x * (y * z)) = d((x * y) * z)"
  and d8: "d(x * (y + z)) = d(x * y) + d(x * z)"
  and d9: "d(x * y) = d(y * x)"
  and d10: "d(x * e) = d(x)"
  and d_loc: "d(x \<cdot> (y * z)) \<le> d(x\<cdot>y) * d(z)"
begin

lemma d_loc': "d p = p \<Longrightarrow> d q = q \<Longrightarrow> d(x \<cdot> (p * q)) \<le> d(x\<cdot>p) * q"
  by (metis local.d_loc)

lemma fdia_local: "d(p) = p \<Longrightarrow> d(q) = q \<Longrightarrow> \<bar>x\<rangle>(p * q) \<le> \<bar>x\<rangle>p * q"
  by (metis local.d_loc' local.fmodal.fdiamond_def)
  
lemma fbox_local: "\<lbrakk>p = d(p); q = d(q)\<rbrakk> \<Longrightarrow> \<bar>x]p * q \<le> \<bar>x](p * q)"
  (* nitpick *) oops

end

context antirange_semiring
begin

definition bdia :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<langle>_\<bar>_" [99, 99] 100) where
  "\<langle>x\<bar>y = r(y\<cdot>x)"
  
definition bbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("[_\<bar>_" [99, 99] 100) where
  "[x\<bar>y = ar( \<langle>x\<bar> ar(y) )"

lemma bbox_def_var: "[x\<bar>y = ar(ar(y)\<cdot>x)"
  by (metis bdia_def local.antirange_semiring_range_def local.bbox_def local.dual.a_closure local.dual.antidomain_semiring_domain_def)
  
sublocale bmodal: bmodal_semiring where bdiamond = bdia and bbox = bbox
  apply default
  apply (simp_all add: bdia_def bbox_def_var)
done

lemma bswap: "p = r(p) \<Longrightarrow> q = r(q) \<Longrightarrow> \<langle>x\<bar>p \<le> [y\<bar>q \<longleftrightarrow> \<langle>y\<bar>ar(q) \<le> [x\<bar>ar(p)"
  by (metis local.bmodal.dual.fbox_fdia local.bmodal.dual.fdia_fbox_de_morgan_2 local.bmodal.dual.fdia_simp_2 local.dual.a_antitone local.dual.antidomain_semiring_domain_def)

end

class ss_range = antirange_semiring + sepconj +
  assumes r6: "r(r(x) * r(y)) = r(x) * r(y)"
  and r7: "r(x * (y * z)) = r((x * y) * z)"
  and r8: "r(x * (y + z)) = r(x * y) + r(x * z)"
  and r9: "r(x * y) = r(y * x)"
  and r10: "r(x * e) = r(x)"
  and r_loc: "r((x * y) \<cdot> z) \<le> r(x\<cdot>z) * r(y)"
begin

lemma bdia_local: "r(p) = p \<Longrightarrow> r(q) = q \<Longrightarrow> \<langle>x\<bar>(p * q) \<le> \<langle>x\<bar>p * q"
  by (metis local.r_loc bdiamond_def)

end

class modal_semiring = antidomain_semiring + antirange_semiring +
  assumes domrange: "d(r(x))=r(x)"
  and rangedom: "r(d(x))=d(x)"
begin

lemma domrangefix: "d(x)=x \<longleftrightarrow> r(x)=x"
  by (metis domrange rangedom)

lemma box_diamond_galois_1: "\<lbrakk>p=d(p); q=d(q)\<rbrakk> \<Longrightarrow> (\<langle>x\<bar>p \<le> q \<longleftrightarrow> p \<le> \<bar>x]q)"
  by (metis domrangefix fbox_demodalisation3 rdemodalisation3)
  
lemma box_diamond_galois_2: "\<lbrakk>p=d(p); q=d(q)\<rbrakk> \<Longrightarrow> ( \<bar>x\<rangle>p \<le> q \<longleftrightarrow> p \<le> [x\<bar>q)"
  by (metis domrangefix bbox_demodalisation3 fdemodalisation3)

lemma diamond_conjugation_var_1: "\<lbrakk>p=d(p); q=d(q)\<rbrakk> \<Longrightarrow>( \<bar>x\<rangle>q \<le> a(p) \<longleftrightarrow> \<langle>x\<bar>p \<le> a(q))"
  by (smt a_closure a_export antidomain_semiring_domain_def box_diamond_galois_1 domain_1 fbox_def fdia_fbox less_eq_def)

lemma diamond_conjugation: "\<lbrakk>p=d(p); q=d(q)\<rbrakk> \<Longrightarrow> (p\<cdot>( \<bar>x\<rangle>q) = 0 \<longleftrightarrow> q\<cdot>(\<langle>x\<bar>p) = 0)" 
  by (metis diamond_conjugation_var_1 fdia_simp_2 bdia_simp_2 domrange d_d_zero dom_el_comm)

lemma box_conjugation:  "\<lbrakk>p=d(p); q=d(q)\<rbrakk> \<Longrightarrow> (p \<le> [x\<bar>a(q) \<longleftrightarrow> q \<le> \<bar>x]a(p))"
  by (metis box_diamond_galois_2 a_closure diamond_conjugation_var_1  box_diamond_galois_1 antidomain_semiring_domain_def)

lemma box_diamond_cancellation_1:  "p=d(p)  \<Longrightarrow>  p \<le> \<bar>x](\<langle>x\<bar>p)"
  by (metis bdiamond_def box_diamond_galois_1 domrange order_refl)

lemma box_diamond_cancellation_2:  "p=d(p)  \<Longrightarrow>  p \<le> [x\<bar>( \<bar>x\<rangle>p)"
  by (metis box_diamond_galois_2 domain_invol fdiamond_def order_refl)

lemma box_diamond_cancellation_3:  "q=d(q) \<Longrightarrow> \<bar>x\<rangle>([x\<bar>q) \<le> q"
  by (metis ar_closure box_diamond_galois_2 domrangefix dual.fbox_fdia order_refl)

lemma box_diamond_cancellation_4:  "q=d(q) \<Longrightarrow> \<langle>x\<bar>( \<bar>x]q) \<le> q"
  by (metis a_closure box_diamond_galois_1 fbox_def order_refl) 
  
lemma antidomran: "d(x) = x \<Longrightarrow> a(x) = ar(x)"
  by (metis local.a_gla local.antidomain_semiring_domain_def local.antirange_semiring_range_def local.antisym_conv local.ar1 local.ar_gla local.domrange local.rangedom)  

end

interpretation rel: modal_semiring "op \<union>" "op O" Id "{}" "\<lambda>x. -(Id \<inter> x O UNIV) \<inter> Id" "op \<subseteq>" "op \<subset>" "\<lambda>x. -(Id \<inter> UNIV O x) \<inter> Id"
  apply default
  apply (subst rel.antidomain_semiring_domain_def)
  apply (subst rel.antirange_semiring_range_def)+
  prefer 2
  apply (subst rel.antidomain_semiring_domain_def)+
  apply (subst rel.antirange_semiring_range_def)
  apply force
  apply fastforce
done


class modal_separation_semiring = modal_semiring + ss_domain + ss_range 
begin

lemma dsep_isol: "d(y) \<le> d(z) \<Longrightarrow> d(x) * d(y) \<le> d(x) * d(z)"
proof (simp add: less_eq_def)
  assume assms: "d y + d z = d z"
  have "d x * d y + d x * d z = d (d x * d y) + d(d x * d z)"
    by (metis d6)
  also have "... = d (d x * (d y + d z))"
    by (metis d8)
  also have "... = d (d x * d z)"
    by (metis assms)
  finally show "d x * d y + d x * d z = d x * d z"
    by (metis d6)
qed

lemma dsep_isor: "d(x) \<le> d(y) \<Longrightarrow> d(x) * d(z) \<le> d(y) * d(z)"
  using dsep_isol local.d6 local.d9 by smt
  
lemma dsep_isol_var: "p=d(p) \<Longrightarrow> q=d(q) \<Longrightarrow> s=d(s) \<Longrightarrow> p \<le> q \<Longrightarrow> s * p \<le> s * q"
  by (metis dsep_isol)

lemma dsep_isor_var: "p=d(p) \<Longrightarrow> q=d(q) \<Longrightarrow> s=d(s) \<Longrightarrow> p \<le> q \<Longrightarrow> p * s \<le> q * s"
  by (metis dsep_isor)

lemma d_sepconj: "d(p) = p \<Longrightarrow> d(q) = q \<Longrightarrow> d(p * q) = p * q"
  by (metis local.d6)
  
lemma fbox_local: "\<lbrakk>p = d(p); q = d(q)\<rbrakk> \<Longrightarrow> \<bar>x]p * q \<le> \<bar>x](p * q)"
proof -
  assume tests:"p = d(p)" "q = d(q)"
  hence "\<langle>x\<bar>(\<bar>x]p * q) \<le> \<langle>x\<bar>(\<bar>x]p) * q"
    by (metis bdia_local local.fmodal.fbox_simp_2 domrangefix)
  moreover have "\<langle>x\<bar>(\<bar>x]p) \<le> p"
    by (metis local.box_diamond_cancellation_4 tests(1))
  ultimately have "\<langle>x\<bar>(\<bar>x]p * q) \<le> p * q"
    apply (subst tests(1))
    apply (rule dual_order.trans)
    using tests apply (auto intro!: dsep_isor_var)
    by (metis local.antirange_semiring_range_def local.bmodal.dual.fdia_simp_2 local.domrangefix local.dual.antidomain_semiring_domain_def)
  thus ?thesis
    by (metis local.box_diamond_galois_1 local.d6 local.fmodal.fbox_simp_2 tests(1) tests(2))
qed

lemma bbox_local: "\<lbrakk>p = d(p); q = d(q)\<rbrakk> \<Longrightarrow> [x\<bar>p * q \<le> [x\<bar>(p * q)"
proof -
  assume tests:"p = d(p)" "q = d(q)"
  hence "\<bar>x\<rangle>([x\<bar>p * q) \<le> \<bar>x\<rangle>([x\<bar>p) * q"
    by (metis local.d_loc local.fmodal.fdiamond_def)
  moreover have "\<bar>x\<rangle>([x\<bar>p) \<le> p"
    by (metis local.box_diamond_cancellation_3 tests(1))
  ultimately have "\<bar>x\<rangle>([x\<bar>p * q) \<le> p * q"
    apply (subst tests(1))
    apply (rule dual_order.trans)
    using tests apply (auto intro!: dsep_isor_var)
    by (metis local.fmodal.fdia_simp_2)
  thus ?thesis
    by (metis d_sepconj local.antirange_semiring_range_def local.bmodal.dual.fbox_fdia local.box_diamond_galois_2 local.domrangefix local.dual.a_closure local.dual.antidomain_semiring_domain_def tests(1) tests(2))
qed

end

end
