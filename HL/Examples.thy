theory Examples
  imports Syntax
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
  by hoare_split auto

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
  by (hoare_split simp: MAX_def) auto

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
          `s := `s + a<`i>
        od
      \<lbrace> `s = array_sum a 1 N \<rbrace>"
    by hoare auto

hide_const s i

record power_state =
  b:: nat
  i :: nat
  n :: nat

lemma power:
  "\<turnstile> \<lbrace> True \<rbrace>
    `i := 0;
    `b := 1;
    while `i < `n
    inv `b = a ^ `i \<and> `i \<le> `n
    do
      `b := `b * a;
      `i := `i + 1
    od
  \<lbrace> `b = a ^ `n \<rbrace>"
  by hoare auto

lemma power': "\<turnstile> \<lbrace> True \<rbrace> 
    `b := 1;
    for `i := 0 to `n do
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
  "\<turnstile> \<lbrace> `n > 0 \<rbrace>
    `i := 1;
    while `i < `n
    inv ((\<forall>k. 1 \<le> k \<and> k < `i \<longrightarrow> a(k) \<noteq> m) \<or> (a(`j) = m)) \<and> (`i \<le> `n)
    do
      if a(`i) = m then
        `j := `i
      fi;
      `i := `i + 1
    od
  \<lbrace> (\<forall>k. 1 \<le> k \<and> k < `n \<longrightarrow> a(k) \<noteq> m) \<or> (a(`j) = m) \<rbrace>" 
  apply (hoare, auto)
  using less_SucE by blast

lemma linear_search': "\<turnstile> \<lbrace> `n > 0 \<rbrace> 
    for `i := 1 to `n do
      if a(`i) = m then
        `j := `i
      fi
    od
  \<lbrace> (\<forall>k. 1 \<le> k \<and> k < `n \<longrightarrow> a(k) \<noteq> m) \<or> (a(`j) = m) \<rbrace>" 
  apply (hoare, auto)
  using less_SucE by blast


lemma linear_search'': 
  "\<turnstile> \<lbrace> `n > 0 \<rbrace>
    `i := 1;
    `j := 0;
    while `i < `n
    inv (if \<forall>k. 1 \<le> k \<and> k < `i \<longrightarrow> a(k) \<noteq> m then `j = 0 else (a(`j) = m))  \<and> (`i \<le> `n)
    do
      if a(`i) = m then
        `j := `i
      fi;
      `i := `i + 1
    od
  \<lbrace> if (\<forall>k. 1 \<le> k \<and> k < `n \<longrightarrow> a(k) \<noteq> m) then `j = 0 else (a(`j) = m) \<rbrace>" 
  apply hoare
  apply auto
  using le_less_linear apply blast
  using le_less_linear apply blast
  using less_SucE by blast

hide_const i j n
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
    `y := `y \<cdot> `x
  od
  \<lbrace> `y = fact xo \<rbrace>"
  by hoare auto

lemma fact_rec: "\<forall>xo. \<turnstile> \<lbrace> xo = `x \<rbrace>
  rec Fact in
    if `x = 0 then
      `y := 1
    else
      `x := `x - 1;
      \<lbrace>xo. xo = `x + 1\<rbrace>
      Fact;
      `x := `x + 1;
      `y := `y \<cdot> `x
    fi
  end
  \<lbrace> xo = `x \<and> `y = fact `x \<rbrace>"
  by hoare auto

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

end
