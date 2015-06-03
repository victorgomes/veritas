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
  apply (rule hl_split)
  by (hoare, auto)+

lemma "\<turnstile> \<lbrace> `x = u \<rbrace> local `x := t in R end \<lbrace> `x = u \<rbrace>"
  by hoare auto

definition "MAX xo yo \<equiv> begin 
    `x := `xo;
    `y := `yo;
    if `x \<ge> `y then
      `y := `x
    fi
    return `y
  end"

lemma "\<turnstile> \<lbrace> True \<rbrace> proc (MAX \<guillemotleft>xo\<guillemotright> \<guillemotleft>yo\<guillemotright>) \<lbrace> `y \<ge> xo \<and> `y \<ge> yo \<rbrace>"
  by (hoare simp: MAX_def) auto

lemma "\<turnstile> \<lbrace> True \<rbrace> `z := call (MAX \<guillemotleft>xo\<guillemotright> \<guillemotleft>yo\<guillemotright>) \<lbrace> `z \<ge> xo \<and> `z \<ge> yo \<rbrace>"
  by (hoare simp: MAX_def) auto

lemma swap_annotated:
  "\<turnstile> \<lbrace>`x = xo \<and> `y = yo \<rbrace>
      `z := `x;
      \<lbrace> `x = xo \<and> `y = yo \<and> `z = xo \<rbrace>
      `x := `y;
      \<lbrace> `x = yo \<and> `y = yo \<and> `z = xo \<rbrace>
      `y := `z
   \<lbrace>`x = yo \<and> `y = xo\<rbrace>"
  by (hoare hl_rules: hl_apre_classic) auto

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
