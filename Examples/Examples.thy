theory Examples
  imports "../Syntax"
begin

record state =
    x :: nat
    y :: nat
    z :: nat

lemma swap:
  "\<turnstile> \<lbrace>`x = xo \<and> `y = yo \<rbrace>
      `z := `x ;
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
  by (hoare first: hl_split) auto

lemma "\<turnstile> \<lbrace> `x = u \<rbrace> local `x := t in R end \<lbrace> `x = u \<rbrace>"
  by hoare auto

definition "MAX xo yo \<equiv> begin 
    local `x := `xo in
      `y := `yo;
      if `x \<ge> `y then
        `y := `x
      fi
    end
    return `y
  end"

lemma "\<turnstile> \<lbrace> True \<rbrace> proc (MAX \<guillemotleft>xo\<guillemotright> \<guillemotleft>yo\<guillemotright>) \<lbrace> `y \<ge> xo \<and> `y \<ge> yo \<rbrace>"
  by (hoare simp: MAX_def) auto

lemma "\<turnstile> \<lbrace> `x = xo \<rbrace> `z := call (MAX \<guillemotleft>xo\<guillemotright> \<guillemotleft>yo\<guillemotright>) \<lbrace> `x = xo \<rbrace>"
  apply (hoare_step simp: MAX_def, simp)
  by hoare auto

lemma "\<turnstile> \<lbrace> `y = yo \<rbrace> `z := call (MAX \<guillemotleft>xo\<guillemotright> \<guillemotleft>yo\<guillemotright>) \<lbrace> `y = yo \<rbrace>"
  by (hoare simp: MAX_def) auto

lemma "\<turnstile> \<lbrace> `y = yo \<rbrace> `z := call (MAX \<guillemotleft>xo\<guillemotright> \<guillemotleft>yo\<guillemotright>) \<lbrace> `y = yo \<and> `z \<ge> xo \<and> `z \<ge> yo \<rbrace>"
  by (hoare simp: MAX_def first: hl_split) auto

lemma swap_annotated:
  "\<turnstile> \<lbrace>`x = xo \<and> `y = yo \<rbrace>
      `z := `x;
      \<lbrace> `x = xo \<and> `y = yo \<and> `z = xo \<rbrace>
      `x := `y;
      \<lbrace> `x = yo \<and> `y = yo \<and> `z = xo \<rbrace>
      `y := `z
   \<lbrace>`x = yo \<and> `y = xo\<rbrace>"
  by (hoare hl: hl_apre_classic) auto

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
  lfp (\<lambda>Fact xo.
    if `x = 0 then
      `y := 1
    else
      `x := `x - 1;
      \<lbrace> xo = `x + 1 \<and> `x > 0 \<rbrace>
      (Fact xo);
      `x := `x + 1;
      `y := `y \<cdot> `x
    fi
  ) xo
  \<lbrace> xo = `x \<rbrace>"
thm hl_rec[where P="\<lambda>z. {s. z = x s}" and Q="\<lambda>z. {s. z = x s}"]
oops

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
  using assms int_distrib(2) 
  by (auto simp: int_distrib(3))

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
  by hoare (auto simp: extend_euclid_invariant)

hide_const a b a' b' c d r q t

type_synonym 'a array = "(nat \<Rightarrow> 'a) \<times> nat"

abbreviation array :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" where "array \<equiv> fst"
abbreviation len :: "'a array \<Rightarrow> nat" where "len \<equiv> snd"

fun sum_to :: "nat array \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_to (f, _) 0 = undefined"
| "sum_to (f, n) (Suc 0) = (if n > 0 then f 0 else undefined)"
| "sum_to (f, n) (Suc m) = (if n > m then f m + sum_to (f, n) m else undefined)"

record state_sum =
  s :: nat
  i :: nat

lemma "\<turnstile> \<lbrace> len a > 0 \<rbrace> 
    `s := array a 0;
    for `i := 0 to len a
    inv `s = sum_to a `i \<and> `i \<le> len a
    do
      `s := `s + (array a `i)
    od  
    \<lbrace> `s = sum_to a (len a) \<rbrace>"
apply hoare
apply auto
apply (case_tac a)
apply auto
apply (case_tac "b > i x")
apply auto
prefer 3
apply (case_tac a)
apply force
apply (case_tac a)
apply auto
apply (case_tac a)
apply auto
apply force


apply clarsimp
apply (subst card_UN_disjoint[symmetric])
apply (rule antisym)
prefer 3
apply (case_tac a)
apply auto
apply (case_tac a)
apply auto


apply simp
apply force
apply force
apply simp
apply (subst Collect_neg_eq[symmetric])
apply (subst linorder_not_le)
apply simp
apply auto
apply hoare_step
apply hoare_step
defer
defer
apply hoare_step
apply hoare_step
defer
apply hoare_step
apply hoare_step
apply hoare_step
prefer 2
apply force
apply simp
apply hoare
apply simp
apply force
apply clarsimp
apply auto

end
