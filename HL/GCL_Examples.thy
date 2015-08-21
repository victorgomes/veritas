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
end