theory While
  imports Main
begin

text {* We define a simple while programming language based on relations *}

text {* 
  Programs are modelled as relations using a standard while programming language:
  S ::= abort | skip | \<langle>f\<rangle> | \<lceil>g\<rceil> | S; S' | if b then S else S' fi | while b do S od,
  where f is a state transformer
*}

notation Id_on ("\<lfloor>_\<rfloor>" 100) (* relations below the identity form tests *)  

type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"
type_synonym ('v, 's) var = "('v, 's) lval \<times> ('v, 's) rval"

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

definition dyn :: "('s \<Rightarrow> 's rel) \<Rightarrow> 's rel" ("\<lceil>_\<rceil>" 100) where
  "\<lceil>g\<rceil> \<equiv> {(s, s'). (s, s') \<in> g s}"

definition block :: "'s rel \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's rel" where
  "block x ret \<equiv> \<lceil>\<lambda>s. x; \<langle>ret s\<rangle>\<rceil>"

definition loc_block :: "('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "loc_block z_upd z t x \<equiv> (block (\<langle>\<lambda>s. z_upd (\<lambda>_. t s) s\<rangle>; x) (\<lambda>s. z_upd (\<lambda>_. z s)))"

type_synonym ('v, 's) func = "('s rel \<times> ('v, 's) rval)"

abbreviation fun_block :: "'s rel \<Rightarrow> ('v, 's) rval \<Rightarrow> ('v, 's) func" where
  "fun_block R y \<equiv> (R, y)"

abbreviation proc_block :: "('v, 's) func \<Rightarrow> 's rel" ("proc _") where
  "proc_block \<equiv> fst"

definition fun_call :: "('v, 's) lval \<Rightarrow> ('v, 's) func \<Rightarrow> 's rel" where
  "fun_call u_upd F \<equiv> block (fst F) (\<lambda>s t. u_upd (\<lambda>_. snd F t) t)"
  
text {* Annotated programs for automatic verification *}

definition awhile :: "'s set \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "awhile i b x \<equiv> cwhile b x"

definition apre :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "apre p x \<equiv> x"

definition apost :: "'s rel \<Rightarrow> 's set\<Rightarrow> 's rel" where
  "apost x q \<equiv> x; apre q skip"

definition aprog :: "'s set\<Rightarrow> 's rel \<Rightarrow> 's set\<Rightarrow> 's rel" where
  "aprog p x q \<equiv> x"


end
