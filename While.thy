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

definition abort :: "'s rel" ("abort") where "abort \<equiv> {}"

definition skip :: "'s rel" ("skip") where "skip \<equiv> Id" 

definition to_rel :: "('s \<Rightarrow> 's) \<Rightarrow> 's rel" ("\<langle>_\<rangle>" 100) where
  "\<langle>f\<rangle> \<equiv> {(s, f s) | s. True}"

definition seq :: "'s rel \<Rightarrow> 's rel \<Rightarrow> 's rel" (infixr ";" 60) where
  "seq \<equiv> relcomp"

definition cond :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "cond b x y \<equiv> (\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>-b\<rfloor>;y)"

definition while :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "while b x \<equiv> (\<lfloor>b\<rfloor>;x)\<^sup>*; \<lfloor>-b\<rfloor>"

definition dyn :: "('s \<Rightarrow> 's rel) \<Rightarrow> 's rel" ("\<lceil>_\<rceil>" 100) where
  "\<lceil>g\<rceil> \<equiv> {(s, s'). (s, s') \<in> g s}"
  
definition block :: "('s \<Rightarrow> 's) \<Rightarrow> 's rel \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's rel) \<Rightarrow> 's rel" where
  "block init x ret c \<equiv> \<lceil>\<lambda>s. \<langle>init\<rangle>; x; \<lceil>\<lambda>t. \<langle>ret s\<rangle>; c s t\<rceil> \<rceil>"
  
text {* Annotated programs for automatic verification *}

definition awhile :: "('v \<Rightarrow> 's set) \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "awhile i b x \<equiv> while b x"

definition apre :: "('v \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "apre p x \<equiv> x"

definition apost :: "'s rel \<Rightarrow> ('v \<Rightarrow> 's set) \<Rightarrow> 's rel" where
  "apost x q \<equiv> x; apre q skip"

definition aprog :: "('v \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> ('v \<Rightarrow> 's set) \<Rightarrow> 's rel" where
  "aprog p x q \<equiv> x"

text {* Lift tests to assertions *}

definition assert :: "'a set \<Rightarrow> 'v \<Rightarrow> 'a set" ("<_>") where
  "<b> \<equiv> \<lambda>_. b"

end
