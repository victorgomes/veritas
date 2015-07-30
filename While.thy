section {* While Programming Language *}

theory While
  imports Main
begin

text {* Simple while programming language based on relations *}

text {* Relations below the identity form tests *}

notation Id_on ("\<lfloor>_\<rfloor>" 100) 

text {* Variables *}

text {* 
  The following convention on types are used:
  - 's for store, a record of variables
  - 'h for heap, a partial function from nat to nat
  - 'a for state, the pair of 's and 'h or error state
  - 'v for the value of a variable
  The types are instantiated later on, and are usually generic.
*}

type_synonym ('s, 'h) state = "('s \<times> 'h) option"

text {* The left value of a variable is an update function. *}
type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"

text {* The right value of a variable is a retrieve function. *}
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"

text {* A variable is then a pair of left and right values, satisfying some properties. *}
type_synonym ('v, 's) var = "('v, 's) lval \<times> ('v, 's) rval"

abbreviation upd_var :: "('v, 'a) var \<Rightarrow> ('v, 'a) lval" ("upd _" 100) where "upd_var \<equiv> fst"
abbreviation val_var :: "('v, 'a) var \<Rightarrow> ('v, 'a) rval" ("val _" 100) where "val_var \<equiv> snd"

definition consistent_var :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "consistent_var u_upd u \<equiv> \<forall>s. u_upd (\<lambda>_. u s) s = s"

definition consistent_var2 :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> bool" where
  "consistent_var2 u_upd u \<equiv> \<forall>t. consistent_var u_upd t \<longrightarrow> u = t"

text {* Commands *}

definition abort :: "'a rel" ("abort") where "abort \<equiv> {}"

definition skip :: "'a rel" ("skip") where "skip \<equiv> Id" 

definition graph :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a rel" ("\<langle>_\<rangle>" 100) where
  "\<langle>f\<rangle> \<equiv> {(\<sigma>, f \<sigma>) | \<sigma>. True}"

abbreviation on_store :: "('s \<Rightarrow> 's) \<Rightarrow> ('s \<times> 'h) \<Rightarrow> ('s \<times> 'h)" where
  "on_store f \<equiv> \<lambda>(s, h). (f s, h)"

abbreviation on_heap :: "('h \<Rightarrow> 'h) \<Rightarrow> ('s \<times> 'h) \<Rightarrow> ('s \<times> 'h)" where
  "on_heap f \<equiv> \<lambda>(s, h). (s, f h)"

definition subst :: "('s, 'h) state set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('s, 'h) state set" where
  "subst P u_upd t \<equiv> Collect (\<lambda>\<sigma>. (case \<sigma> of Some (s, h) \<Rightarrow> Some (u_upd (\<lambda>_. t s) s, h) | None \<Rightarrow> None) \<in> P)"

definition assign :: "('v, 's) lval \<Rightarrow> ('s \<Rightarrow>'v) \<Rightarrow> ('s, 'h) state rel" where
  "assign u_upd t \<equiv> \<langle>\<lambda>\<sigma>. case \<sigma> of Some (s, h) \<Rightarrow> Some (u_upd (\<lambda>_. t s) s, h) | None \<Rightarrow> None\<rangle>"

definition seq :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" (infixr ";" 60) where
  "seq \<equiv> relcomp"

definition cond :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "cond b x y \<equiv> (\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>-b\<rfloor>;y)"

definition cwhile :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "cwhile b x \<equiv> (\<lfloor>b\<rfloor>;x)\<^sup>*; \<lfloor>-b\<rfloor>"

(*
definition cfor :: "('v :: {linorder, plus, one}, 'a) var \<Rightarrow> ('v, 'a) rval \<Rightarrow> ('v, 'a) var \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "cfor j n m x \<equiv> assign (upd j) n; cwhile {s. (val j) s < (val m) s} (x; assign (upd j) (\<lambda>s. (val j) s + 1))"
*)

definition dyn :: "('a \<Rightarrow> 'a rel) \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>" 100) where
  "\<lceil>g\<rceil> \<equiv> {(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> g \<sigma>}"

definition block :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a rel" where
  "block x ret \<equiv> \<lceil>\<lambda>\<sigma>. x; \<langle>ret \<sigma>\<rangle>\<rceil>"

(*
definition loc_block :: "('v, 'a) var \<Rightarrow> ('v, 'a) rval \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "loc_block z t x \<equiv> (block (\<langle>\<lambda>s. (upd z) (\<lambda>_. t s) s\<rangle>; x) (\<lambda>s. (upd z) (\<lambda>_. (val z) s)))"

type_synonym ('v, 'a) func = "('a rel \<times> ('v, 'a) var)"

abbreviation fun_block :: "'a rel \<Rightarrow> ('v, 'a) var \<Rightarrow> ('v, 'a) func" where
  "fun_block R y \<equiv> (R, y)"

abbreviation proc_block :: "('v, 'a) func \<Rightarrow> 'a rel" ("proc _" 100) where "proc_block \<equiv> fst"
abbreviation ret_var :: "('v, 'a) func \<Rightarrow> ('v, 'a) var" ("ret _" 100) where "ret_var \<equiv> snd"

definition fun_call :: "('v, 'a) lval \<Rightarrow> ('v, 'a) func \<Rightarrow> 'a rel" where
  "fun_call u_upd F \<equiv> let y = ret F in 
      block (proc F) (\<lambda>s t. (upd y) (\<lambda>_. snd y s) (u_upd (\<lambda>_. snd y t) t))"
 *)

text {* Annotated programs for automatic verification *}

definition awhile :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "awhile i b x \<equiv> cwhile b x"

(*
definition afor :: "'a set  \<Rightarrow> ('v :: {order, plus, one}, 'a) var \<Rightarrow> ('v, 'a) rval \<Rightarrow> ('v, 'a) rval \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "afor i j n m x \<equiv> cfor j n m x"
*)

definition apre :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "apre p x \<equiv> x"

definition apost :: "'a rel \<Rightarrow> 'a set\<Rightarrow> 'a rel" where
  "apost x q \<equiv> x; apre q skip"

definition aprog :: "'a set\<Rightarrow> 'a rel \<Rightarrow> 'a set\<Rightarrow> 'a rel" where
  "aprog p x q \<equiv> x"


end
