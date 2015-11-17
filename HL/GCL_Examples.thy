theory GCL_Examples
  imports GCL_Syntax
begin

record euclids =
  x :: nat
  y :: nat

lemma euclids: "\<turnstile> \<lbrace> `x = xo \<and> `y = yo \<rbrace>
    inv gcd xo yo = gcd `x `y
    do [
      `x > `y \<rightarrow> `x := `x - `y,
      `x < `y \<rightarrow> `y := `y - `x
    ] od
  \<lbrace> `x = gcd xo yo \<and> `x = `y \<rbrace>"
  apply hoare
  using gcd_diff1_nat gcd_nat.commute by auto

hide_const x y

record max =
  x :: nat
  y :: nat
  z :: nat

lemma max: "\<turnstile> \<lbrace> True \<rbrace>
    if [
      `x \<ge> `y \<rightarrow> `z := `x,
      `y \<ge> `x \<rightarrow> `z := `y
    ] fi
  \<lbrace> `z = max `x `y \<rbrace>"
  by hoare auto
  
hide_const x y z

record handshake_state = pc_state +
  x :: bool
  y :: bool
  c :: bool

lemma "\<turnstile> \<lbrace> \<not>`c \<rbrace>
    inv (
      (`pcX = 0 \<longrightarrow> `x \<longrightarrow> \<not> `c) \<and>
      (`pcX = 1 \<longrightarrow> (`x \<longrightarrow> \<not> `c) \<and> (`y \<longrightarrow> `c)) \<and>
      (`pcX = 2 \<longrightarrow> `y \<longrightarrow> `c) \<and>
      (`pcX = 3 \<longrightarrow> `c) \<and>
      (`pcX = 4 \<longrightarrow> `x \<and> `c) \<and>      
      
      (`pcY \<le> 1 \<longrightarrow> \<not> `c) \<and>
      (`pcY = 1 \<longrightarrow> `x \<longrightarrow> `pcX > 1) \<and>
      (`pcY \<ge> 2 \<longrightarrow> `c) \<and>
      (`pcY = 4 \<longrightarrow> `y \<and> `c) \<and>

      (`pcX = 2 \<and> `pcY = 2 \<longrightarrow> `x \<or> `y) \<and> 
      (`pcX \<le> 1 \<longrightarrow> `pcY \<le> 2) \<and>
      (`pcY \<le> 1 \<longrightarrow> `pcX \<le> 2)
    )
    0 =: `y := False ;;
    1 =: `x := True ;;
    2 =: wait `y ;;
    3 =: `x := True
      \<parallel>
    0 =: `x := False ;;
    1 =: `y := True; `c := True ;;
    2 =: wait `x ;;
    3 =: `y := True; `c := True
  \<lbrace> `x \<and> `y \<and> `c \<rbrace>"
  apply transform
apply hoare
by force+

hide_const x y c x

record mutual_incl_protocol = pc_state +
  x :: int
  y :: int
  c :: bool

lemma "\<turnstile> \<lbrace> `x = 0 \<and> `y = 0 \<and> `c \<rbrace>
    inv ( 
      (`x \<le> `y) \<and> (`y \<le> `x + 1) \<and>

      (`pcX \<le> 1 \<longrightarrow>  `c \<and> (`x = `y)) \<and>
      (`pcX = 2 \<longrightarrow> \<not>`c \<or> (`x + 1 = `y)) \<and>
      (`pcX = 3 \<longrightarrow> `c \<and> (`x + 1 = `y)) \<and>

      (`pcY \<le> 1 \<longrightarrow> `c \<or> (`x = `y)) \<and>
      (`pcY = 2 \<longrightarrow> \<not>`c \<and> (`x = `y)) \<and>
      (`pcY = 3 \<longrightarrow> \<not>`c \<and> (`x + 1 = `y))
    )
    0 =: while True do
            (* Critical Section 1 *)
           1 =: `c := False ;;
           2 =: wait `c ;;
           3 =: `x := `x + 1
         od
      \<parallel>
    0 =: while True do
           1 =: wait (\<not> `c) ;;
            (* Critical Section 2 *)
           2 =: `y := `y + 1 ;;
           3 =: `c := True
         od
  \<lbrace> True \<rbrace>"
  apply transform
  apply hoare
  by force+

lemma "\<turnstile> \<lbrace> `x = 0 \<and> `y = 0 \<and> `c \<rbrace>
    inv ( 
      (`x \<le> `y) \<and> (`y \<le> `x + 1) \<and>
      (`pcX \<le> 1 \<longrightarrow>  `c \<and> (`x = `y)) \<and>
      (`pcX = 2 \<longrightarrow> \<not>`c \<or> (`x + 1 = `y)) \<and>
      (`pcX = 3 \<longrightarrow> `c \<and> (`x + 1 = `y)) \<and>
      (`pcY \<le> 1 \<longrightarrow> `c \<or> (`x = `y)) \<and>
      (`pcY = 2 \<longrightarrow> \<not>`c \<and> (`x = `y)) \<and>
      (`pcY = 3 \<longrightarrow> \<not>`c \<and> (`x + 1 = `y))
    )
    0 =: while `x = `y  do
            (* Critical Section 1 *)
           1 =: `c := False ;;
           2 =: wait `c ;;
           3 =: `x := `x + 1
         od
      \<parallel>
    0 =: while `x = `y do
           1 =: wait (\<not> `c) ;;
            (* Critical Section 2 *)
           2 =: `y := `y + 1 ;;
           3 =: `c := True
         od
  \<lbrace> True \<rbrace>"
  apply transform
  apply hoare
  by force+

hide_const x y pcX pcY c

end