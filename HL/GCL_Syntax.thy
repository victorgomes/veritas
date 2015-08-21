theory GCL_Syntax
  imports GCL Syntax
begin

no_notation comp_op ("n_" [90] 91)
  and test_operator  ("t_" [100] 101)
  and floor ("\<lfloor>_\<rfloor>")
  and ceiling ("\<lceil>_\<rceil>")
  and Set.image (infixr "`" 90)
  and residual_r (infixr "\<rightarrow>" 60)

(* Classical GCL *)

syntax
  "_gc" :: "'a set \<Rightarrow> 'a rel \<Rightarrow> ('a set \<times> 'a rel)" ("_ \<rightarrow> _" [50, 50] 0)
  "_alt" :: "('a set \<times> 'a rel) list \<Rightarrow> 'a rel" ("(0if// /  _ //fi)" [60] 61)
  "_arepeat" :: "'a set \<Rightarrow> ('a set \<times> 'a rel) list \<Rightarrow> 'a rel" ("(0inv _ //do// /  _ //od)" [50, 60] 61)

translations
  "b \<rightarrow> x" == "(_assert b, x)"
  "if xs fi" == "CONST alt xs"
  "inv i do xs od" == "CONST arepeat (_assert i) xs"

(* Concurrency by GCL *)

no_syntax 
  "_cond" :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0if _ then//  _//else//  _//fi)" [0,0,0] 62)
  "_while"      :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel"             ("(0while  _//do  _//od)" [0, 0] 62)

syntax
  "_Atomic" :: "nat \<Rightarrow> 'a rel \<Rightarrow> 'a lprog" ("_ =: _" [61, 61] 61)
  "_Seq"    :: "'a lprog \<Rightarrow> 'a lprog \<Rightarrow> 'a lprog" (infixl ";;" 61)
  "_If"     :: "nat \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0_ =: if _ then//  _//else//  _//fi)" [0,0,0] 62)
  "_While"  :: "nat \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel"             ("(0while  _//do  _//od)" [0, 0] 62)
  "_par"    :: "'a pc_state_scheme lprog \<Rightarrow> 'a pc_state_scheme lprog \<Rightarrow> 'a pc_state_scheme rel" ("(0 _//\<parallel>// _)" 55)

translations
  "k =: x"                      == "CONST Atomic k x"
  "x;; y"                       == "CONST Seq x y"
  "k =: if b then x else y fi"  == "CONST GCL.If k b x y"
  "k =: while b do x od"        == "CONST Loop k (_assert b) x"
  "x \<parallel> y"                       == "CONST par x y"

record state = pc_state +
  x :: nat

lemma "\<turnstile> \<lbrace> True \<rbrace> k =: `x := 1 \<parallel> k =: `x := 1 \<lbrace> True \<rbrace>"
  apply (unfold par_def)
  apply simp
oops
end