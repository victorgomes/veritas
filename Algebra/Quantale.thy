theory Quantale
  imports Abstract_Quantales
begin

no_notation 
  times (infixl "*" 70) and
  plus (infixl "+" 65) 
  
notation 
  sup (infixl "+" 65) and
  inf (infixl "\<sqinter>" 70) and
  Sup ("\<Squnion>_" [900] 900) and
  Inf ("\<Sqinter>_" [900] 900) and
  top ("\<top>") and
  bot ("\<bottom>") and
  times (infixl "\<cdot>" 70) 

sublocale complete_lattice \<subseteq> Sup!: abs_complete_lattice Sup
  where [simp]: "abs_complete_lattice.join Sup = op +"
    and [simp]: "abs_complete_lattice.less_eq Sup = op \<le>"
    and [simp]: "abs_complete_lattice.less Sup = op <"
    and [simp]: "abs_complete_lattice.Meet Sup = Inf"
    and [simp]: "abs_complete_lattice.meet Sup = op \<sqinter>"
    and [simp]: "abs_complete_lattice.top Sup = \<top>"
    and [simp]: "abs_complete_lattice.bot Sup = \<bottom>"
proof -
  show "abs_complete_lattice Sup"
    apply unfold_locales
    apply (metis Sup_atLeastAtMost atLeastAtMost_singleton order_refl)
    apply (auto simp: Sup_le_iff intro!: Sup_eqI Sup_least)
    apply (metis (no_types) Sup_upper UnionI)
    by (metis Sup_least le_iff_sup sup.orderE)
  then interpret cl: abs_complete_lattice Sup .
  show "cl.join = op +"
    by (default, default) (simp add: cl.join_def)
  show [simp]: "cl.less_eq = op \<le>"
    apply (default, default)
    by (auto simp add: cl.less_eq_def cl.join_def le_iff_sup)
  show "cl.less = op <"
    apply (default, default)
    by (auto simp add: less_le_not_le cl.less_def)
  show [simp]: "cl.Meet = Inf"
    by default (auto simp add: cl.Meet_def Inf_Sup)
  show "cl.meet = op \<sqinter>"
    by (default, default) (simp add: cl.meet_def)
  show "cl.top = \<top>"
    by (simp add: cl.top_def)
  show "cl.bot = \<bottom>"
    by (simp add: cl.bot_def)
qed

class near_quantale = complete_lattice + semigroup_mult +
  assumes qSup_distr: "\<Squnion> Y \<cdot> x = \<Squnion> ((\<lambda>y. y \<cdot> x) ` Y)"
begin

lemma qSup_distr': "\<Squnion>{x. P(x)} \<cdot> y = \<Squnion>{x \<cdot> y |x. P(x)}"
  using qSup_distr[of "{x. P(x)}"]
  by (metis image_Collect)

end

class near_quantale_unital = near_quantale + monoid_mult

class pre_quantale = near_quantale + 
  assumes qSup_subdistl: "\<Squnion> ((\<lambda>y. x \<cdot> y) ` Y) \<le> x \<cdot> \<Squnion> Y"

class quantale = pre_quantale + 
  assumes qSup_supdistl: "x \<cdot> \<Squnion> Y \<le> \<Squnion> ((\<lambda>y. x \<cdot> y) ` Y)"

class quantale_unital = quantale + monoid_mult

(* Instantiation of quantales *)

sublocale near_quantale \<subseteq> Sup!: abs_near_quantale Sup "op \<cdot>"
  where "abs_complete_lattice.join Sup = op +"
    and "abs_complete_lattice.less_eq Sup = op \<le>"
    and "abs_complete_lattice.less Sup = op <"
    and "abs_complete_lattice.Meet Sup = Inf"
    and "abs_complete_lattice.meet Sup = op \<sqinter>"
    and "abs_complete_lattice.top Sup = \<top>"
    and "abs_complete_lattice.bot Sup = \<bottom>"
  by (unfold_locales, auto) (metis qSup_distr Sup_image_eq)

sublocale near_quantale_unital \<subseteq> Sup!: abs_near_quantale_unital Sup "op \<cdot>" one
  where "abs_complete_lattice.join Sup = op +"
    and "abs_complete_lattice.less_eq Sup = op \<le>"
    and "abs_complete_lattice.less Sup = op <"
    and "abs_complete_lattice.Meet Sup = Inf"
    and "abs_complete_lattice.meet Sup = op \<sqinter>"
    and "abs_complete_lattice.top Sup = \<top>"
    and "abs_complete_lattice.bot Sup = \<bottom>"
  by unfold_locales auto

sublocale pre_quantale \<subseteq> Sup!: abs_pre_quantale Sup "op \<cdot>"
  where "abs_complete_lattice.join Sup = op +"
    and "abs_complete_lattice.less_eq Sup = op \<le>"
    and "abs_complete_lattice.less Sup = op <"
    and "abs_complete_lattice.Meet Sup = Inf"
    and "abs_complete_lattice.meet Sup = op \<sqinter>"
    and "abs_complete_lattice.top Sup = \<top>"
    and "abs_complete_lattice.bot Sup = \<bottom>"
  apply unfold_locales
  apply (auto intro: Sup_eqI Sup_least)
  by (metis Sup.Sup_image_eq local.Sup.less_eq_def local.qSup_subdistl)

sublocale quantale \<subseteq> Sup!: abs_quantale Sup "op \<cdot>"
  where "abs_complete_lattice.join Sup = op +"
    and "abs_complete_lattice.less_eq Sup = op \<le>"
    and "abs_complete_lattice.less Sup = op <"
    and "abs_complete_lattice.Meet Sup = Inf"
    and "abs_complete_lattice.meet Sup = op \<sqinter>"
    and "abs_complete_lattice.top Sup = \<top>"
    and "abs_complete_lattice.bot Sup = \<bottom>"
  apply unfold_locales
  apply (auto intro: Sup_eqI Sup_least)
  by (metis qSup_supdistl le_iff_sup sup_commute Sup.Sup_image_eq)

sublocale quantale_unital \<subseteq> Sup!: abs_quantale_unital Sup "op \<cdot>" one
  where "abs_complete_lattice.join Sup = op +"
    and "abs_complete_lattice.less_eq Sup = op \<le>"
    and "abs_complete_lattice.less Sup = op <"
    and "abs_complete_lattice.Meet Sup = Inf"
    and "abs_complete_lattice.meet Sup = op \<sqinter>"
    and "abs_complete_lattice.top Sup = \<top>"
    and "abs_complete_lattice.bot Sup = \<bottom>"
  by unfold_locales auto

context near_quantale begin

lemma qSUP_distr: "(SUP y:Y. f y) \<cdot> x = (SUP y: Y. f y \<cdot> x)"
  by (unfold SUP_def qSup_distr image_image) simp

end

context quantale begin

lemma qSUP_distl: "x \<cdot> (SUP y:Y. f y) = (SUP y: Y. x \<cdot> f y)"
  by (unfold SUP_def Sup.Join_distl image_image) simp

lemma qSUP_distl': "y \<cdot> \<Squnion>{x. P(x)} = \<Squnion>{y \<cdot> x | x. P(x)}"
  using qSUP_distl[of _ "{x. P(x)}"]
  by (simp add: image_Collect local.Sup.Join_distl)

lemma qSUP_distl2': "x \<cdot> \<Squnion>{y \<cdot> z | y z. P y z} = \<Squnion>{x \<cdot> (y \<cdot> z) | y z. P y z}"
  using qSUP_distl[of _ "{y \<cdot> z | y z. P y z}"]
  apply (simp add: image_Collect local.Sup.Join_distl)
  by (metis (full_types))

lemma qSUP_merge_ineq: "\<Squnion> {f x \<cdot> g y | x y. P x \<and> Q y} \<le> \<Squnion> {\<Squnion> {f x \<cdot> g y | x. P x} | y. Q y}"
proof (rule Sup_least, auto)
  fix xa y assume "P xa" "Q y"
  hence "\<exists>u. (\<exists>x. f xa \<cdot> g y = f x \<cdot> g u \<and> P x) \<and> Q u" by blast
  hence "\<exists>u. Q u \<and> f xa \<cdot> g y \<in> {f x \<cdot> g u |x. P x}" by blast
  hence "\<exists>B. (\<exists>y. \<Squnion>B = \<Squnion>{f x \<cdot> g y |x. P x} \<and> Q y) \<and> f xa \<cdot> g y \<in> B" by blast
  hence "\<exists>B. \<Squnion>B \<le> \<Squnion>{\<Squnion>{f x \<cdot> g y |x. P x} |y. Q y} \<and> f xa \<cdot> g y \<in> B"
    using Sup.Join_Collect_upper by (metis (lifting, mono_tags))
  thus "f xa \<cdot> g y \<le> \<Squnion>{\<Squnion>{f x \<cdot> g y |x. P x} |y. Q y}"
    using Sup_le_iff by blast
qed

lemma qSUP_merge: "\<Squnion> {\<Squnion> {f x \<cdot> g y | x. P x} | y. Q y} = \<Squnion> {f x \<cdot> g y | x y. P x \<and> Q y}"
  apply (rule antisym, rule Sup_least, safe)
  by (rule Sup_mono, auto simp add: qSUP_merge_ineq)

lemma Sup_sum_le1: "\<Squnion> {f a b + g a b | a b. P a b} \<le> \<Squnion>{f a b | a b. P a b} + \<Squnion>{g a b | a b. P a b}"
proof (rule Sup_least, safe)
  fix a b assume assm: "P a b"
  have "f a b \<le> \<Squnion>{f a b | a b. P a b}" and "g a b \<le> \<Squnion>{g a b | a b. P a b}"
    apply (rule Sup_upper) using assm apply blast
    apply (rule Sup_upper) using assm by blast
  thus "f a b + g a b \<le> \<Squnion>{f a b |a b. P a b} + \<Squnion>{g a b |a b. P a b}"
    by (metis (lifting, no_types) sup_mono)
qed

lemma Sup_sum_le2: "\<Squnion>{f a b | a b. P a b} + \<Squnion>{g a b | a b. P a b} \<le> \<Squnion> {f a b + g a b | a b. P a b}"
proof (subst Sup_union_distrib[symmetric], rule Sup_least, auto)
  fix a b assume assm: "P a b"
  have "f a b + g a b \<le> \<Squnion> {f a b + g a b | a b. P a b}"
    apply (rule Sup_upper) using assm by blast
  thus "f a b \<le> \<Squnion> {f a b + g a b | a b. P a b}" and "g a b \<le> \<Squnion> {f a b + g a b | a b. P a b}"
    by auto
qed

lemma Sup_sum [iff]: "\<Squnion> {f a b + g a b | a b. P a b} = \<Squnion>{f a b | a b. P a b} + \<Squnion>{g a b | a b. P a b}"
  by (rule antisym) (metis Sup_sum_le1, metis Sup_sum_le2)

lemma Sup_sum_same_set[iff]:" \<Squnion> {a + b | a b. a \<in> A \<and> b \<in> A} = \<Squnion>A + \<Squnion>A"
proof -
  have "\<Squnion> {a + b | a b. a \<in> A \<and> b \<in> A} = \<Squnion>{a | a b. a \<in> A \<and> b \<in> A} + \<Squnion>{b | a b. a \<in> A \<and> b \<in> A}"
    by simp
  also have "... = \<Squnion>A + \<Squnion>A"
    by (rule antisym) (rule sup.mono, (rule Sup_subset_mono, force)+)+
  finally show ?thesis .
qed

end

class comm_quantale = quantale + ab_semigroup_mult
class comm_quantale_unital = comm_quantale + comm_monoid_mult
begin
subclass quantale_unital ..
end
class distrib_quantale = quantale + complete_distrib_lattice
class distrib_quantale_unital = distrib_quantale + quantale_unital
class distrib_comm_quantale = comm_quantale + distrib_quantale
class distrib_comm_quantale_unital = comm_quantale_unital + distrib_quantale

end
