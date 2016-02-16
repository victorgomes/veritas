theory PredTrans
  imports Syntax "../Algebra/KAD/Modal_Kleene_Algebra"
begin

definition a_rel :: "'a rel \<Rightarrow> 'a rel" where
  "a_rel P \<equiv> {(y, y) | y. \<forall>x. (x, y) \<notin> P}"

definition st :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "st R x \<equiv> {y. (x, y) \<in> R}"

definition dia_rel :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "dia_rel R X \<equiv> Id_on (\<Union>{st R x | x. x \<in> snd ` X})"

definition box_rel :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "box_rel R Y \<equiv> Id_on {x. Id_on (st R x) \<subseteq>  Y}"

interpretation rel_kad: antirange_kleene_algebra "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>" rtrancl a_rel
  apply default
  apply (auto simp: a_rel_def)
done

interpretation rel_kad: bdiamond_semiring dia_rel "op \<union>" "op O" Id "{}" a_rel "op \<subseteq>" "op \<subset>"
  apply default
  apply (auto simp: st_def a_rel_def rel_kad.antirange_semiring_range_def box_rel_def dia_rel_def)
  apply force
  apply force
done

interpretation rel_kad: bmodal_semiring box_rel dia_rel "op \<union>" "op O" Id "{}" a_rel "op \<subseteq>" "op \<subset>"
  apply default
  apply (clarsimp simp: box_rel_def a_rel_def st_def)
  apply auto
sorry


named_theorems wlp_rules
  
lemma pt_awhile [wlp_rules]: "Id_on (b \<inter> i) \<le> box_rel R (Id_on i) \<Longrightarrow> p \<le> Id_on i \<Longrightarrow> Id_on (-b \<inter> i) \<le> q \<Longrightarrow> p \<le> box_rel (awhile i b R) q"
  apply (simp add: awhile_def cwhile_def)
sorry

thm rel_kad.bbox_mult
lemma pt_seq [wlp_rules]: "p \<subseteq> box_rel R (box_rel S q) \<Longrightarrow> p \<subseteq> box_rel (R; S) q"
  apply (simp add: seq_def rel_kad.bbox_mult)
  apply (auto simp: box_rel_def st_def)
sorry

lemma pt_graph: "P \<subseteq> {s. f s \<in> Q} \<Longrightarrow> \<lfloor>P\<rfloor> \<subseteq> box_rel (\<langle>f\<rangle>) (\<lfloor>Q\<rfloor>)"
  by (force simp: box_rel_def graph_def st_def)

lemma pt_assign: "P \<subseteq> subst Q u t \<Longrightarrow> \<lfloor>P\<rfloor> \<subseteq> box_rel (assign u t) (\<lfloor>Q\<rfloor>)"
  by (auto simp add: assign_def intro!: pt_graph)

lemma pt_base [wlp_rules]: "P \<subseteq> Q \<Longrightarrow> \<lfloor>P\<rfloor> \<subseteq> \<lfloor>Q\<rfloor>"
  by auto

lemma pt_induct [wlp_rules]: "Id_on p \<subseteq> F (Id_on (subst Q u t)) \<Longrightarrow> mono F \<Longrightarrow> (Id_on p) \<subseteq> F (box_rel (assign u t) (\<lfloor>Q\<rfloor>))"
  by (meson monoE pt_assign subset_eq)

declare mono_id [intro]

lemma [intro]: "mono (box_rel R)"
  by (force simp: mono_def box_rel_def st_def)

lemma [intro]: "mono F \<Longrightarrow> mono (\<lambda>a. box_rel R (F a))"
  by (force simp: mono_def box_rel_def st_def)

record state =
  x :: nat
  y :: nat
  z :: nat

lemma "Id_on ({s. x s = xo \<and> y s = yo}) \<le> box_rel 
  (
    while `y \<noteq> 0
    inv gcd `x `y = gcd xo yo
    do
      (`z := `y;
      `y := `x mod `y);
      `x := `z
    od
   ) (Id_on ({s. x s = gcd xo yo}))"
   apply (rule wlp_rules)+
   by auto (metis gcd_red_nat)

end