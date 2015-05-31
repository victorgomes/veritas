theory Examples
  imports "../Syntax"
begin

lemma hl_ret: "\<forall>s. ht P R {t. (z_update (\<lambda>_. y t) s) \<in> Q} \<Longrightarrow> ht P (block id R (\<lambda>s t. s) (\<lambda>s t. `z := y t)) Q"
apply (rule hl_block)
prefer 3
apply (rule allI)+
apply (rule hl_to_rel)
apply (rule subset_refl)
apply auto
done

lemma hl_no_changes: "\<forall>s m. Q \<subseteq> {t. (z_update (\<lambda>_. m) t) \<in> Q} \<Longrightarrow> ht Q (block id R (\<lambda>s t. s) (\<lambda>s t. `z := y t)) Q"
by (force simp: block_def ht_def seq_def dyn_def to_rel_def)


record state =
    x :: nat
    y :: nat
    z :: nat
    
lemma swap:
  "\<turnstile> \<lbrace>`x = xo \<and> `y = yo \<rbrace>
      `z := `x;
      `x := `y;
      `y := `z
   \<lbrace>`x = yo \<and> `y = xo\<rbrace>"
   by hoare auto

lemma "\<turnstile> \<lbrace> `x = n \<rbrace> 
  local `x := `x + 1 in
    `x := 2;
    `y := `x + 1
  end 
  \<lbrace> `x = n \<and> `y = 3 \<rbrace>"
  by hoare auto

lemma "\<turnstile> \<lbrace> `x = u \<rbrace> local `x in R end \<lbrace> `x = u \<rbrace>"
  apply (rule hl_block[where P'="\<lambda>s. {t. x s = u}" and R="\<lambda>s s'. {t. x t = u}"])
  apply auto
  by hoare

definition proc :: "'s rel \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> 's rel \<times> ('s \<Rightarrow> 'v)" where
  "proc R v \<equiv> (R, v)"

definition "MAX xo yo \<equiv> 
      proc (`x := xo;
      `y := yo;
      \<lbrace> `x = xo \<and> `y = yo \<rbrace>
      if `x \<ge> `y then
        `y := `x
      else
        `y := `y
      fi) y"

lemma maximum: 
  "\<turnstile> \<lbrace> `x = u \<and> `y = v \<rbrace> `z := call (MAX xo yo) \<lbrace> `z = max xo yo \<and> `x = u \<and> `y = v \<rbrace>"
  unfolding MAX_def proc_def
apply (rule hl_split)
apply (rule hl_ret)
apply simp
apply hoare
apply (rule hl_apre)
apply hoare
apply auto
apply (rule hl_no_changes)
apply force
done

lemma maximum: 
  "\<turnstile> \<lbrace> `x = u \<rbrace> block id (MAX xo yo) (\<lambda>s t. s) (\<lambda>s t. `z := y t) \<lbrace> `x = u \<and> `z = max xo yo \<rbrace>"
  unfolding MAX_def
thm hl_ret
apply (rule hl_split)
defer
apply (rule hl_ret)

apply simp
apply (rule allI)
apply hoare
apply (rule hl_apre)
apply hoare
apply auto
apply (rule hl_no_changes)
apply auto
apply simp
apply (rule hl_seq)
apply (rule hl_seq)
apply (rule hl_cond_tac)
prefer 4
apply (rule hl_to_rel)
apply (rule subset_refl)
prefer 3
apply (rule hl_to_rel)
apply (rule subset_refl)
apply (rule subset_refl)
apply clarify
apply simp

apply hoare
apply auto



lemma swap_annotated:
  "\<turnstile> \<lbrace>`x = xo \<and> `y = yo \<rbrace>
      `z := `x;
      \<lbrace> `x = xo \<and> `y = yo \<and> `z = xo \<rbrace>
      `x := `y;
      \<lbrace> `x = yo \<and> `y = yo \<and> `z = xo \<rbrace>
      `y := `z
   \<lbrace>`x = yo \<and> `y = xo\<rbrace>"
apply hoare
apply auto
done

primrec fact :: "nat \<Rightarrow> nat" where
  "fact 0 = 1"
| "fact (Suc n) = (Suc n) * fact n"


lemma fact: "\<turnstile> \<lbrace> True \<rbrace>
  `x := 0;
  `y := 1;
  while `x \<noteq> xo
  inv `y = fact `x
  do
    `x := `x + 1;
    `y := `y * `x
  od
  \<lbrace> `y = fact xo \<rbrace>"
  by hoare auto

lemma fact_rec: "\<forall>xo. \<turnstile> \<lbrace> (xo = `x) \<rbrace>
  rec Fact in
    if `x = 0 then
      `y := 1
    else
      `x := `x - 1;
      \<lbrace> xo = `x + 1 \<rbrace>
      Fact;
      `x := `x + 1;
      `y := `y \<cdot> `x
    fi
  end
  \<lbrace> xo = `x \<rbrace>"
apply (rule hl_rec2)
prefer 2
apply hoare
apply force
prefer 2
apply (rule hl_apre)
apply (rule subset_refl)
apply simp
apply (rule hl_apre3[where P="\<lambda>xo. {s. xo = Suc (x s)}"])
apply assumption
apply simp
apply force

sorry



apply (erule_tac x="x sa - 1" in allE)
apply hoare_step
defer
defer
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply simp
prefer 3
apply simp
apply clarsimp
apply assumption
apply auto
defer
apply (rule hl_2[where P'="\<lambda>z u. {s. z = x s}" and Q'="\<lambda>z u. {s. z = x s}"])
apply clarsimp
apply clarsimp
apply (rule allI)
prefer 2
apply clarsimp


apply assumption
apply clarsimp
apply force


apply hoare_step
defer
apply hoare_step
prefer 3
apply hoare_step
apply hoare_step
apply force
prefer 2
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply hoare_step
apply simp_all
apply (rule hl_conseq)
apply hoare_step
apply clarsimp
prefer 2
apply hoare_step
apply hoare_step
apply (rule conjI)
apply (subgoal_tac "s \<in> {s. xo = Suc (x s)}")
apply force
apply assumption
apply clarsimp
apply (subst mem_Collect_eq)




lemma "local `x := t in skip end = a" oops

lemma [simp]: "ht P R <UNIV>"
  apply (auto simp: ht_def seq_def)
done

lemma "P \<subseteq> UNIV" oops

declare [[simp_trace]]
lemma maximum2: 
  "\<turnstile> \<lbrace> `x = xo \<rbrace> `x := 2; local `x in MAX end \<lbrace> `x = xo \<rbrace>"
unfolding MAX_def
apply hoare
apply force
apply safe
apply force
apply clarsimp
apply auto

apply (rule allI)
apply (subst mem_Collect_eq)
apply (rule subset_refl)

apply simp
apply auto
apply (auto simp: ht_def seq_def)
apply (rule subset_refl)

apply (subst mem_Collect_eq)
apply (rule allI)
apply simp
apply auto
apply (unfold ht_def seq_def)
apply simp
apply auto
apply (auto simp: ht_def)

lemma maximum2: 
  "\<turnstile> \<lbrace> `x = xo \<and> `y = yo\<rbrace> local `x := `x in (block id MAX (\<lambda>s t. s) (\<lambda>s t. \<langle>\<lambda>v. v \<lparr> z := y t \<rparr>\<rangle>)) end \<lbrace> `z = max xo yo \<and> `x = xo \<rbrace>"
  unfolding MAX_def apply hoare
  apply simp
  apply (rule allI)
  apply (subst Collect_mem_eq)
apply (rule subset_refl)


lemma euclids:
  "\<turnstile> \<lbrace>`x = xo \<and> `y = yo\<rbrace> 
    while `y \<noteq> 0
    inv gcd `x `y = gcd xo yo
    do 
      `z := `y;
      `y := `x mod `y;
      `x := `z
    od 
    \<lbrace>gcd xo yo = `x\<rbrace>"
  by (hoare, auto) (metis gcd_red_nat)

record div_state = state +
  q :: nat
  r :: nat

lemma div: 
  "\<turnstile> \<lbrace> `x \<ge> 0 \<rbrace>
    `q :=  0; `r := `x;
    while `y \<le> `r
    inv `x = `q * `y + `r \<and> `r \<ge> 0
    do
      `q := `q + 1;
      `r := `r - `y
    od
  \<lbrace> `x = `q * `y + `r \<and> `r \<ge> 0 \<and> `r < `y \<rbrace>"
  by hoare auto



hide_const x y z q r

lemma extend_euclid_invariant:
  assumes "(a' :: int)\<cdot>m + b'\<cdot>n = c" "a\<cdot>m + b\<cdot>n = d" "c = q\<cdot>d + r"
  shows "(a' - q\<cdot>a)\<cdot>m + (b'- q\<cdot>b)\<cdot>n = r"
proof -
  have "(a' - q\<cdot>a)\<cdot>m + (b'- q\<cdot>b)\<cdot>n = a'\<cdot>m - q\<cdot>a\<cdot>m + b'\<cdot>n - q\<cdot>b\<cdot>n"
    by (metis add.left_commute int_distrib(3) uminus_add_conv_diff)
  also have "... = a'\<cdot>m + b'\<cdot>n - q\<cdot>(a\<cdot>m + b\<cdot>n)"
    proof -
      have "\<And>u. u = d \<longrightarrow> u - b \<cdot> n = a \<cdot> m" by (simp add: assms(2) diff_eq_eq)
      hence "c - d \<cdot> q + b \<cdot> (n \<cdot> q) = c - a \<cdot> (m \<cdot> q)" by (metis diff_add_eq diff_diff_eq2 int_distrib(3) mult.assoc mult.commute)
      thus "a' \<cdot> m - q \<cdot> a \<cdot> m + b' \<cdot> n - q \<cdot> b \<cdot> n = a' \<cdot> m + b' \<cdot> n - q \<cdot> (a \<cdot> m + b \<cdot> n)" by (metis (no_types) assms(1) assms(2) diff_add_eq diff_eq_eq mult.commute mult.left_commute)
    qed
  finally show ?thesis
    by (simp add: assms(1) assms(2) assms(3))
qed


record extended_euclid_state = 
  a :: int
  b :: int
  a':: int
  b':: int
  c :: int
  d :: int
  r :: int
  q :: int
  t :: int

(* Solve linear diophantine equations *)

lemma extended_euclid: "\<turnstile> \<lbrace> True \<rbrace>
    `b := 1;
    `a':= 1;
    `b' := 0;
    `a := 0;
    `c := m;
    `d := n;
    `q := `c div `d;
    `r := `c mod `d;
    while `r \<noteq> 0
    inv
      `a'\<cdot>m + `b'\<cdot>n = `c \<and> `a\<cdot>m + `b\<cdot>n = `d \<and> `c = `q\<cdot>`d + `r
    do
      `c := `d;
      `d := `r;
      `t := `a';
      `a' := `a;
      `a := `t - `q\<cdot>`a;
      `t := `b';
      `b' := `b;
      `b := `t - `q\<cdot>`b;
      `q := `c div `d;
      `r := `c mod `d
    od
  \<lbrace> `a\<cdot>m + `b\<cdot>n = `d  \<rbrace>"
  by (hoare, auto) (metis extend_euclid_invariant)

hide_const a b a' b' c d r q t

end
