section {* A PDL Textbook Exercise *}

context fmodal_kleene_algebra
begin

definition T :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<leadsto>_\<leadsto>_" [61,61,61] 60)
  where "p\<leadsto>x\<leadsto>q = a(p)+\<bar>x]d(q)"

lemma T_d: "d(p\<leadsto>x\<leadsto>q) = p\<leadsto>x\<leadsto>q"
  by (metis a_closure fbox_simp_2 d5 T_def)

lemma T_p: "d(p)\<cdot>(p\<leadsto>x\<leadsto>q) = d(p)\<cdot>\<bar>x]d(q)"
  by (metis T_def distl a_comp_1 add_zerol)

lemma T_a: "a(p)\<cdot>(p\<leadsto>x\<leadsto>q) = a(p)"
  by (metis T_def a_closure domain_absorption_1 fbox_simp_2)

lemma T_seq: "(p\<leadsto>x\<leadsto>q)\<cdot>\<bar>x](q\<leadsto>y\<leadsto>s) \<le> p\<leadsto>x\<cdot>y\<leadsto>s"
proof -
  have "(p\<leadsto>x\<leadsto>q)\<cdot>\<bar>x](q\<leadsto>y\<leadsto>s) \<le> a(p)+\<bar>x](d(q)\<cdot>(q\<leadsto>y\<leadsto>s))"
    by (smt distr fbox_simp_2 dom_subid mult_oner add_iso mult_isol fbox_add1 domain_invol T_def T_d)
  thus ?thesis
    by (smt T_p dom_subid mult_onel fbox_iso mult_isor add_iso fbox_simp add_comm fbox_simp_2 dom_mult_closed fbox_mult T_def order_trans)
qed

lemma T_square: "(p\<leadsto>x\<leadsto>q)\<cdot>\<bar>x](q\<leadsto>x\<leadsto>p) \<le> p\<leadsto>x\<cdot>x\<leadsto>p"
  by (metis T_seq)

lemma T_segerberg: "\<bar>x\<^sup>\<star>]d(p) = d(p)\<cdot>\<bar>x\<^sup>\<star>](p\<leadsto>x\<leadsto>p)"
  by (metis fbox_segerberg T_def add_comm)

lemma lookahead: "\<bar>x\<^sup>\<star>](d(p)\<cdot>\<bar>x]d(p)) = \<bar>x\<^sup>\<star>]d(p)"
  by (metis fbox_add1 fbox_simp_2 fbox_mult domain_invol fbox_add2 add_lub add_ub eq_iff star_1l star_slide_var)

lemma alternation: "\<bar>(x\<cdot>x)\<^sup>\<star>](d(p)\<cdot>(q\<leadsto>x\<leadsto>p))\<cdot>\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>](d(q)\<cdot>(p\<leadsto>x\<leadsto>q)) = d(p)\<cdot>\<bar>x\<^sup>\<star>]((p\<leadsto>x\<leadsto>q)\<cdot>(q\<leadsto>x\<leadsto>p))"
proof -
  have "d(p)\<cdot>\<bar>x\<^sup>\<star>]((p\<leadsto>x\<leadsto>q)\<cdot>(q\<leadsto>x\<leadsto>p)) = d(p)\<cdot>(\<bar>(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q)\<cdot>(q\<leadsto>x\<leadsto>p))\<cdot>\<bar>(x\<cdot>x)\<^sup>\<star>]\<bar>x]((p\<leadsto>x\<leadsto>q)\<cdot>(q\<leadsto>x\<leadsto>p)))"
    by (smt meyer_1 mult_onel distr fbox_add2 fbox_simp star_slide fbox_mult)
  also have "\<dots> = d(p)\<cdot>\<bar>(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q)\<cdot>\<bar>x](q\<leadsto>x\<leadsto>p)\<cdot>(q\<leadsto>x\<leadsto>p)\<cdot>\<bar>x](p\<leadsto>x\<leadsto>q))"
    by (smt T_d dom_el_comm dom_mult_closed fbox_add1 fbox_simp_2 mult_assoc)
  also have "\<dots> = d(p)\<cdot>\<bar>(x\<cdot>x)\<^sup>\<star>](p\<leadsto>x\<cdot>x\<leadsto>p)\<cdot>\<bar>(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q)\<cdot>\<bar>x](q\<leadsto>x\<leadsto>p)\<cdot>(q\<leadsto>x\<leadsto>p)\<cdot>\<bar>x](p\<leadsto>x\<leadsto>q))"
    by (smt domain_order T_seq fbox_simp_2 dom_mult_closed mult_assoc dom_el_comm T_d fbox_add1)
  also have "\<dots> = \<bar>(x\<cdot>x)\<^sup>\<star>]d(p)\<cdot>\<bar>(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q)\<cdot>\<bar>x](q\<leadsto>x\<leadsto>p)\<cdot>(q\<leadsto>x\<leadsto>p)\<cdot>\<bar>x](p\<leadsto>x\<leadsto>q))"
    by (metis T_segerberg)
  also have "\<dots> = \<bar>(x\<cdot>x)\<^sup>\<star>](d(p)\<cdot>(q\<leadsto>x\<leadsto>p)\<cdot>(\<bar>x]d(q)\<cdot>\<bar>x](q\<leadsto>x\<leadsto>p)\<cdot>\<bar>x](p\<leadsto>x\<leadsto>q)))"
    by (smt fbox_add1 mult_assoc domain_invol fbox_simp_2 dom_mult_closed T_d T_p dom_el_comm)
  also have "\<dots> = \<bar>(x\<cdot>x)\<^sup>\<star>](d(p)\<cdot>\<bar>x\<cdot>x]d(p))\<cdot>\<bar>(x\<cdot>x)\<^sup>\<star>]((q\<leadsto>x\<leadsto>p)\<cdot>\<bar>x](d(q)\<cdot>(p\<leadsto>x\<leadsto>q)))"
    by (smt fbox_add1 fbox_simp_2 a_closure d5 domain_invol dom_mult_closed T_d T_p dom_el_comm mult_assoc fbox_mult)
  finally show ?thesis
    by (smt lookahead fbox_add1 fbox_simp_2 domain_invol dom_mult_closed mult_assoc fbox_mult star_slide T_d)
qed

lemma meyer: "\<bar>(x\<cdot>x)\<^sup>\<star>]d(p)\<cdot>\<bar>x\<cdot>(x\<cdot>x)\<^sup>\<star>]a(p) = d(p)\<cdot>\<bar>x\<^sup>\<star>]((p\<leadsto>x\<leadsto>a(p))\<cdot>(a(p)\<leadsto>x\<leadsto>p))"
  by (metis alternation antidomain_semiring_domain_def T_a a_closure)

lemma segerberg_again: "\<bar>x\<^sup>\<star>]d(p) = d(p)\<cdot>\<bar>x\<^sup>\<star>](p\<leadsto>x\<leadsto>p)"
  by (smt T_d dom_el_idemp alternation fbox_add2 meyer_1 mult_onel distr T_p lookahead)

