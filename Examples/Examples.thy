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

record sum_state = 
  s :: nat
  i :: nat

lemma array_sum: "\<turnstile> \<lbrace> True \<rbrace>
        `i := 0;
        `s := 0;
        while `i < N
        inv `s = array_sum a 1 (`i) \<and> `i \<le> N
        do
          `i := `i + 1;
          `s := `s + a(`i)
        od
      \<lbrace> `s = array_sum a 1 N \<rbrace>"
    by hoare auto

hide_const s i

record power_state =
  b:: nat
  i :: nat
  n :: nat

lemma power:
  "\<turnstile> \<lbrace> `n \<ge> 1 \<rbrace>
    `i := 1;
    `b := a;
    while `i < `n
    inv `b = a ^ `i \<and> `i \<le> `n
    do
      `b := `b * a;
      `i := `i + 1
    od
  \<lbrace> `b = a ^ `n \<rbrace>"
  by hoare auto

lemma "\<turnstile> \<lbrace> `n \<ge> 1 \<rbrace> 
    `b := a;
    for `i := 1 to `n do
      `b := `b * a
    od  
    \<lbrace> `b = a ^ `n \<rbrace>"
    by hoare auto

hide_const i b n

record ls_state =
  i :: nat
  j :: nat
  n :: nat

lemma linear_search: 
  "\<turnstile> \<lbrace> True \<rbrace>
    `i := 1;
    while `i \<le> N
    inv (\<forall>k. 1 \<le> k \<and> k < `i \<longrightarrow> a(k) \<noteq> m) \<or> (a(`j) = m)
    do
      if a(`i) = m then
        `j := `i
      fi;
      `i := `i + 1
    od
  \<lbrace> (\<forall>k. 1 \<le> k \<and> k \<le> N \<longrightarrow> a(k) \<noteq> m) \<or> (a(`j) = m) \<rbrace>" 
  apply (hoare, auto)
  using less_SucE by blast

lemma "\<turnstile> \<lbrace> `n \<ge> 1 \<rbrace> 
    `j := 1;
    for `i := 1 to `n do
      if a(`i) = m then
        `j := `i
      fi
    od
  \<lbrace> (\<forall>k. 1 \<le> k \<and> k < `n \<longrightarrow> a(k) \<noteq> m) \<or> (a(`j) = m) \<rbrace>" 
  apply (hoare, auto)
  using less_SucE by blast

hide_const i j n

record 'a :: order bubble =
  i :: nat
  j :: nat
  k :: nat
  a :: "'a array"

lemma bubble: 
  "\<turnstile> \<lbrace> True \<rbrace>
    `i := n;
    while `i > 0
    inv array_sorted (`a) (`i + 1) (n - `i) \<and> `i \<le> n
    do
      `j := 1;
      while `j < `i
      inv (\<forall>k. 1 \<le> k \<and> k \<le> `j \<longrightarrow> `a(k) \<le> `a(`j)) \<and> `i \<le> n \<and> `i > 0
        \<and> array_sorted (`a) (`i + 1) (n - `i)  \<and>
      (\<forall>k. 1 \<le> k \<and> k \<le> `i \<longrightarrow> `a k \<le> `a (`i + 1))
      do
        if `a(`j) > `a(`j + 1) then
          `k := `a(`j);
          `a(`j) := `a(`j + 1);
          `a(`j + 1) := `k
        fi;
        `j := `j + 1
      od;
      `i := `i - 1
    od
  \<lbrace> array_sorted (`a) 1 n \<rbrace>"
  apply hoare
oops


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

hide_const a x y z q r

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
