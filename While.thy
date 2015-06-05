theory While
  imports Main
begin

text {* Simple while programming language based on relations *}

text {* Relations below the identity form tests *}

notation Id_on ("\<lfloor>_\<rfloor>" 100) 

text {* Variables *}

type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"
type_synonym ('v, 's) var = "('v, 's) lval \<times> ('v, 's) rval"

abbreviation upd_var :: "('v, 's) var \<Rightarrow> ('v, 's) lval" ("upd _" 100) where "upd_var \<equiv> fst"
abbreviation val_var :: "('v, 's) var \<Rightarrow> ('v, 's) rval" ("val _" 100) where "val_var \<equiv> snd"

text {* Arrays *}
(*
type_synonym 'a array = "'a list"
*)
text {* Commands *}

definition abort :: "'s rel" ("abort") where "abort \<equiv> {}"

definition skip :: "'s rel" ("skip") where "skip \<equiv> Id" 

definition graph :: "('s \<Rightarrow> 's) \<Rightarrow> 's rel" ("\<langle>_\<rangle>" 100) where
  "\<langle>f\<rangle> \<equiv> {(s, f s) | s. True}"

definition subst :: "'s set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's set" where
  "subst P u_upd t \<equiv> Collect (\<lambda>s. u_upd (\<lambda>_. t s) s \<in> P)"

definition assign :: "('v, 's) lval \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> 's rel" where
  "assign u_upd t \<equiv> \<langle>\<lambda>s. u_upd (\<lambda>_. t s) s\<rangle>"

definition seq :: "'s rel \<Rightarrow> 's rel \<Rightarrow> 's rel" (infixr ";" 60) where
  "seq \<equiv> relcomp"

definition cond :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "cond b x y \<equiv> (\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>-b\<rfloor>;y)"

definition cwhile :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "cwhile b x \<equiv> (\<lfloor>b\<rfloor>;x)\<^sup>*; \<lfloor>-b\<rfloor>"

definition cfor :: "('v :: {order, plus, one}, 's) var \<Rightarrow> ('v, 's) rval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "cfor j n m x \<equiv> assign (upd j) n; cwhile {s. (val j) s \<le> m s} (x; assign (upd j) (\<lambda>s. (val j) s + 1))"

definition dyn :: "('s \<Rightarrow> 's rel) \<Rightarrow> 's rel" ("\<lceil>_\<rceil>" 100) where
  "\<lceil>g\<rceil> \<equiv> {(s, s'). (s, s') \<in> g s}"

definition block :: "'s rel \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's rel" where
  "block x ret \<equiv> \<lceil>\<lambda>s. x; \<langle>ret s\<rangle>\<rceil>"

definition loc_block :: "('v, 's) var \<Rightarrow> ('v, 's) rval \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "loc_block z t x \<equiv> (block (\<langle>\<lambda>s. (upd z) (\<lambda>_. t s) s\<rangle>; x) (\<lambda>s. (upd z) (\<lambda>_. (val z) s)))"

type_synonym ('v, 's) func = "('s rel \<times> ('v, 's) var)"

abbreviation fun_block :: "'s rel \<Rightarrow> ('v, 's) var \<Rightarrow> ('v, 's) func" where
  "fun_block R y \<equiv> (R, y)"

abbreviation proc_block :: "('v, 's) func \<Rightarrow> 's rel" ("proc _" 100) where "proc_block \<equiv> fst"
abbreviation ret_var :: "('v, 's) func \<Rightarrow> ('v, 's) var" ("ret _" 100) where "ret_var \<equiv> snd"

definition fun_call :: "('v, 's) lval \<Rightarrow> ('v, 's) func \<Rightarrow> 's rel" where
  "fun_call u_upd F \<equiv> let y = ret F in 
      block (proc F) (\<lambda>s t. (upd y) (\<lambda>_. snd y s) (u_upd (\<lambda>_. snd y t) t))"
  
text {* Annotated programs for automatic verification *}

definition awhile :: "'s set \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "awhile i b x \<equiv> cwhile b x"

definition afor :: "'s set  \<Rightarrow> ('v :: {order, plus, one}, 's) var \<Rightarrow> ('v, 's) rval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "afor i j n m x \<equiv> cfor j n m x"

definition apre :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "apre p x \<equiv> x"

definition apost :: "'s rel \<Rightarrow> 's set\<Rightarrow> 's rel" where
  "apost x q \<equiv> x; apre q skip"

definition aprog :: "'s set\<Rightarrow> 's rel \<Rightarrow> 's set\<Rightarrow> 's rel" where
  "aprog p x q \<equiv> x"


end
