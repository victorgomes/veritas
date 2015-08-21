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
  - 'a for state, the pair of 's and 'h or error state
  - 'v for the value of a variable
  The types are instantiated later on, and are usually generic.
*}

text {* The left value of a variable is an update function. *}
type_synonym ('v, 's) lval = "('v \<Rightarrow> 'v) \<Rightarrow> 's \<Rightarrow> 's"

text {* The right value of a variable is a retrieve function. *}
type_synonym ('v, 's) rval = "'s \<Rightarrow> 'v"

text {* A variable is then a pair of left and right values, satisfying some properties. *}
type_synonym ('v, 's) var = "('v, 's) lval \<times> ('v, 's) rval"

abbreviation upd :: "('v, 'a) var \<Rightarrow> ('v, 'a) lval" where "upd \<equiv> fst"
abbreviation val :: "('v, 'a) var \<Rightarrow> ('v, 'a) rval" where "val \<equiv> snd"

text {* Commands *}

definition abort :: "'a rel" ("abort") where "abort \<equiv> {}"

definition skip :: "'a rel" ("skip") where "skip \<equiv> Id" 

definition graph :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a rel" ("\<langle>_\<rangle>" 100) where
  "\<langle>f\<rangle> \<equiv> {(s, f s) | s. True}"

definition subst :: "'s set \<Rightarrow> ('v, 's) lval \<Rightarrow> ('v, 's) rval \<Rightarrow> 's set" where
  "subst P u_upd t \<equiv> Collect (\<lambda>s. (u_upd (\<lambda>_. t s) s) \<in> P)"

definition assign :: "('v, 's) lval \<Rightarrow> ('s \<Rightarrow>'v) \<Rightarrow> 's rel" where
  "assign u_upd t \<equiv> \<langle>\<lambda>s. u_upd (\<lambda>_. t s) s\<rangle>"

definition seq :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" (infixr ";" 60) where
  "seq \<equiv> relcomp"

definition cond :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "cond b x y \<equiv> (Id_on b;x) \<union> (Id_on (-b);y)"

definition cwhile :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "cwhile b x \<equiv> ((Id_on b);x)\<^sup>*; (Id_on (-b))"

definition cfor :: "('v :: {linorder, plus, one}, 'a) var \<Rightarrow> ('v, 'a) rval \<Rightarrow> ('v, 'a) var \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "cfor j n m x \<equiv> assign (upd j) n; cwhile {s. (val j) s < (val m) s} (x; assign (upd j) (\<lambda>s. (val j) s + 1))"

definition dyn :: "('a \<Rightarrow> 'a rel) \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>" 100) where
  "\<lceil>g\<rceil> \<equiv> {(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> g \<sigma>}"

definition block :: "'a rel \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a rel" where
  "block x ret \<equiv> \<lceil>\<lambda>\<sigma>. x; \<langle>ret \<sigma>\<rangle>\<rceil>"


definition loc_block :: "('v, 's) var \<Rightarrow> ('v, 's) rval \<Rightarrow> 's rel \<Rightarrow> 's rel" where
  "loc_block z t x \<equiv> (block (\<langle>\<lambda>s. (upd z) (\<lambda>_. t s) s\<rangle>; x) (\<lambda>s. (upd z) (\<lambda>_. (val z) s)))"

type_synonym ('v, 'a) func = "('a rel \<times> ('v, 'a) var)"

abbreviation fun_block :: "'a rel \<Rightarrow> ('v, 'a) var \<Rightarrow> ('v, 'a) func" where
  "fun_block R y \<equiv> (R, y)"

abbreviation proc_block :: "('v, 'a) func \<Rightarrow> 'a rel" ("proc _" 100) where "proc_block \<equiv> fst"
abbreviation ret_var :: "('v, 'a) func \<Rightarrow> ('v, 'a) var" ("ret _" 100) where "ret_var \<equiv> snd"

definition fun_call :: "('v, 'a) lval \<Rightarrow> ('v, 'a) func \<Rightarrow> 'a rel" where
  "fun_call u_upd F \<equiv> let y = ret F in 
      block (proc F) (\<lambda>s t. (upd y) (\<lambda>_. snd y s) (u_upd (\<lambda>_. snd y t) t))"

text {* Annotated programs for automatic verification *}

definition awhile :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "awhile i b x \<equiv> cwhile b x"

definition afor :: "'a set \<Rightarrow> ('v :: {linorder, plus, one}, 'a) var \<Rightarrow> ('v, 'a) rval \<Rightarrow> ('v, 'a) var \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "afor i j n m x \<equiv> cfor j n m x"

definition apre :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "apre p x \<equiv> x"

definition apre_aux :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "apre_aux p x \<equiv> x"

definition apost :: "'a rel \<Rightarrow> 'a set\<Rightarrow> 'a rel" where
  "apost x q \<equiv> x; apre q skip"

definition apost_aux :: "'a rel \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> 'a rel" where
  "apost_aux x q \<equiv> x; apre_aux q skip"

definition aprog :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" where
  "aprog p x q \<equiv> x"

definition aprog_aux :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'a rel \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> 'a rel" where
  "aprog_aux p x q \<equiv> x"



(***********************************************************************************************)

text {* Monotonicity rules *}

named_theorems mono_rules

lemma mono_id [mono_rules]: "mono (\<lambda>f. f)"
  by (auto simp: mono_def)  

lemma mono_abort [mono_rules]: "mono (\<lambda>f. abort)"
  by (auto simp: mono_def)  

lemma mono_skip [mono_rules]: "mono (\<lambda>f. skip)"
  by (auto simp: mono_def)  

lemma mono_test [mono_rules]: "mono (\<lambda>f. \<lfloor>b\<rfloor>)"
  by (auto simp: mono_def)  

lemma mono_assign [mono_rules]: "mono (\<lambda>f. assign v m)"
  by (auto simp: mono_def)  

lemma mono_dyn [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. \<lceil>R f\<rceil>)"
  apply (auto simp: mono_def dyn_def)
  by (meson le_fun_def subsetCE)

lemma mono_seq [mono_rules]: "mono R \<Longrightarrow> mono S \<Longrightarrow> mono (\<lambda>f. R f; S f)"
  by (force simp: mono_def seq_def) 

lemma mono_cond [mono_rules]: "mono R \<Longrightarrow> mono S \<Longrightarrow> mono (\<lambda>f. cond b (R f) (S f))"
  by (fastforce simp: mono_def cond_def seq_def)

lemma mono_iter [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. (R f)\<^sup>*)"
  by (clarsimp simp: mono_def) (meson rtrancl_mono subsetCE)
  
lemma mono_cwhile [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. cwhile b (R f))"
  by (auto simp: cwhile_def intro!: mono_rules)

lemma mono_cfor [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. cfor j n m (R f))"
  by (auto simp: cfor_def intro!: mono_rules)

lemma mono_awhile [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. awhile i b (R f))"
  by (auto simp: awhile_def intro!: mono_rules)

lemma mono_afor [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. afor i j n m (R f))"
  by (auto simp: afor_def intro!: mono_rules)

lemma mono_apre [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. apre p (R f))"
  by (auto simp: apre_def)

lemma mono_apre_aux [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. apre_aux p (R f))"
  by (auto simp: apre_aux_def)

lemma mono_apost [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. apost (R f) q)"
  by (auto simp: apost_def intro!: mono_rules)

lemma mono_apost_aux [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. apost_aux (R f) q)"
  by (auto simp: apost_aux_def intro!: mono_rules)

lemma mono_aprog [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. aprog p (R f) q)"
  by (auto simp: aprog_def)

lemma mono_aprog_aux [mono_rules]: "mono R \<Longrightarrow> mono (\<lambda>f. aprog_aux p (R f) q)"
  by (auto simp: aprog_aux_def)

end
