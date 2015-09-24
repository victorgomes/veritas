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
      (`pcX = 2 \<and> `pcY = 2 \<longrightarrow> `x \<or> `y) \<and>

      (`pcX = 1 \<longrightarrow> \<not>`y \<or> `c) \<and>
      (`pcX = 2 \<longrightarrow> \<not>`y \<or> `c) \<and>
      (`pcX = 3 \<longrightarrow> `y) \<and>
      (`pcX = 4 \<longrightarrow> `x \<and> `y) \<and>
      
      (`pcY = 0 \<longrightarrow> \<not>`c) \<and>
      (`pcY = 2 \<longrightarrow> `c) \<and>
      (`pcY \<ge> 3 \<longrightarrow> `x) \<and>
      (`pcY \<ge> 4 \<longrightarrow> `c)
      
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
  apply (rule hl_seq)+
  apply (rule hl_arepeat_induct)
  apply (rule subset_refl)
  apply clarsimp
defer
  prefer 2
  apply (rule hl_assign)
  apply (rule subset_refl)
  prefer 2
  apply (rule hl_assign)
defer

  apply (rule hl_alt_base | rule hl_alt_induct)+
  apply hoare

  apply force
  apply hoare
  apply force
  apply hoare
  apply force
  apply hoare
  apply force
  apply hoare
  apply force
  apply hoare
  apply force
  apply hoare
  apply clarsimp
  apply hoare
  apply clarsimp

  apply (case_tac "pcX xa = Suc (Suc (Suc (Suc 0)))")
  apply clarsimp
defer
  apply clarsimp
  apply (case_tac "pcY xa = Suc (Suc (Suc (Suc 0)))")
  apply clarsimp
  defer
  apply clarsimp
  apply simp
apply force


defer
defer
defer
defer
defer
defer
defer
  apply hoare
  apply clarsimp

lemma
pcY xa = Suc (Suc (Suc 0)) \<Longrightarrow> pcX xa = Suc (Suc (Suc (Suc 0))) \<Longrightarrow> x xa
pcX x = Suc (Suc (Suc 0)) \<Longrightarrow> pcY x = Suc (Suc (Suc (Suc 0))) \<Longrightarrow> y x \<and> c x

  apply hoare
  apply clarsimp
  apply force

  apply hoare
  apply force

  apply hoare
  apply force

  apply hoare
  apply force

  apply hoare
  apply force

  apply hoare
  apply simp
  apply clarsimp
prefer 2
apply clarsimp


lemma "\<turnstile> \<lbrace> \<not>`c \<rbrace>
    inv (
      
      (`pcX = 0 \<longrightarrow> `pcY = Suc (Suc (Suc (Suc 0))) \<longrightarrow> `y \<longrightarrow> \<not> `c) \<and>

      (`pcY = Suc (Suc 0) \<longrightarrow> `x \<longrightarrow> `c \<longrightarrow> 0 < `pcX) \<and>
      (`pcY = Suc (Suc (Suc 0)) \<longrightarrow> `x \<longrightarrow> `c \<longrightarrow> 0 < `pcX) \<and>

      (`pcX = 1 \<longrightarrow> \<not>`y \<or> `c) \<and>
      (`pcX = 2 \<longrightarrow> \<not>`y \<or> `c) \<and>
      (`pcX = 3 \<longrightarrow> `c) \<and>
      (`pcX = 4 \<longrightarrow> `x \<and> `c) \<and>

      (`pcX = 2 \<and> `pcY = 2 \<longrightarrow> `x \<or> `y) \<and>
      
      (`pcY = 0 \<longrightarrow> \<not> `c) \<and>
      (`pcY = 1 \<longrightarrow> \<not> `c) \<and>
      (`pcY = 2 \<longrightarrow> `c) \<and>
      (`pcY = 3 \<longrightarrow> `x \<and> `c) \<and>

      (`pcY = 4 \<longrightarrow> `y \<and> `c)
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
  apply (rule hl_seq)+
  apply (rule hl_arepeat_induct)
  apply (rule subset_refl)
  apply force
  prefer 2
  apply (rule hl_assign)
  apply (rule subset_refl)
  prefer 2
  apply (rule hl_assign)
defer


  apply (rule hl_alt_base | rule hl_alt_induct)+
  apply hoare
  apply force


  apply hoare
  apply clarsimp

  apply hoare
  apply clarsimp
  apply force

  apply hoare
  apply force

  apply hoare
  apply force

  apply hoare
  apply force

  apply hoare
  apply force

  apply hoare
  apply simp
  apply clarsimp
prefer 2
apply clarsimp





apply forc
apply fore

apply clarsimp
apply force
apply force
apply force
apply force

apply clarsimp
apply clarsimp
apply force



hide_const x y c x

record write_protocol = pc_state +
  w :: bool
  r :: bool
  f :: int
  g :: int
  y :: int
  x :: int
  c :: nat

lemma "\<turnstile> \<lbrace> `w \<and> \<not>`r \<and> `f = 0 \<and> `g = 0 \<and> `y \<le> 0 \<and> `y < `x \<and> `pcX = 0 \<and> `pcY = 0 \<rbrace>
    inv ( 
      (`g < `f \<or> `w) \<and> (`y \<le> `f) \<and> (`g \<le> `f) \<and>
      (`pcX = 0 \<or> `pcX = 1 \<or> `pcX = 2 \<or> `pcX = 3) \<and>
      (`pcY \<in> {0,1,2,3}) \<and>
      (`pcX \<le> 1 \<longrightarrow> `y \<le> `f) \<and>
      (`pcX = 2 \<longrightarrow> `g < `f) \<and>
      (`pcY = 0 \<longrightarrow> `y < `x \<or> `r) \<and>
      (`pcY = 1 \<longrightarrow> `g < `f \<or> `w) \<and>
      (`pcY = 2 \<longrightarrow> `y < `f \<or> `w) \<and>
      (`pcY = 3 \<longrightarrow> `y < `f \<or> `r)
    )
    0 =: while True do
           1 =: await `c > 0 then `f := `f + 1; `w := False end ;;
           2 =: `g := `g + 1; `w := True; `c := `c - 1
         od
      \<parallel>
    0 =: while `y < `x do
           1 =: `y := `g ;;
           2 =: `r := `w ;;
           3 =: `x := `f
         od
  \<lbrace> `r \<and> `c = 0 \<rbrace>"
apply transform
apply hoare
apply force
apply force
apply force
apply force
defer
apply force
apply force
apply force
apply force
apply force
apply force
apply clarsimp
oops

hide_const w r f g x y c

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