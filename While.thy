theory While
  imports Main
begin

text {* We define a simple while programming language based on relations *}

text {* 
  Programs are modelled as relations using a standard while programming language:
  S ::= abort | skip | basic f | S; S' | if b then S else S' fi | while b do S od,
  where f is a state transformer
*}

notation Id_on ("\<lfloor>_\<rfloor>" 100) (* relations below the identity form tests *)  

definition abort :: "'s rel" ("abort") where "abort \<equiv> {}"

definition skip :: "'s rel" ("skip") where "skip \<equiv> Id" 

definition torel :: "('s \<Rightarrow> 's) \<Rightarrow> 's rel" ("\<langle>_\<rangle>" 100) where
  "\<langle>f\<rangle> \<equiv> {(s, f s) | s. True}"

definition seq :: "'s rel \<Rightarrow> 's rel \<Rightarrow> 's rel" (infixr ";" 60) where
  "seq \<equiv> relcomp"

definition cond :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "cond p x y \<equiv> (\<lfloor>p\<rfloor>;x) \<union> (\<lfloor>-p\<rfloor>;y)"

definition while :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "while p x \<equiv> (\<lfloor>p\<rfloor>;x)\<^sup>*; \<lfloor>-p\<rfloor>"

definition block :: "('s \<Rightarrow> 's) \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "block f x \<equiv> \<langle>f\<rangle>; x"

text {* Annotated programs for automatic verification *}

definition awhile :: "('b \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "awhile i p x \<equiv> while p x"

definition apre :: "('b \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "apre p x \<equiv> x"

definition apost :: "'s rel \<Rightarrow> ('b \<Rightarrow> 's set) \<Rightarrow> 's rel" where
  "apost x q \<equiv> x; apre q skip"

definition aprog :: "('b \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> ('b \<Rightarrow> 's set) \<Rightarrow> 's rel" where
  "aprog p x q \<equiv> x"

end
