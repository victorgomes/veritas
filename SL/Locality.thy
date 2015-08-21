theory Locality
  imports "../Algebra/PartialMonoid"
begin

text {*
  We define a separation algebra on a set of pair, where the first
  component contains no algebraic structure and the second is
  a partial commutative monoid.
*}

text {* Notation *}

no_notation times (infixl "*" 70)
  and pmult_defined (infix "##" 55)

(*********************************************************************************************)

abbreviation univ_pred :: "'a set" ("\<top>") where "\<top> \<equiv> UNIV"
abbreviation fault_pred :: "'a set option" ("\<bottom>") where "\<bottom> \<equiv> None"
abbreviation some_pred :: "'a \<Rightarrow> 'a option" ("<_>") where "<P> \<equiv> Some P"

type_synonym ('a, 'b) state = "('a \<times> 'b) option"
type_synonym ('a, 'b) pred = "('a \<times> 'b) set"
type_synonym ('a, 'b) pred_bot = "('a \<times> 'b) set option"
type_synonym 'b hpred = "'b set"
type_synonym 'b hpred_bot = "'b set option"

abbreviation fault_state :: "('a, 'b) state" ("fault") where "fault \<equiv> None"
abbreviation some_state :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) state" ("<_, _>") where "<s, h> \<equiv> Some (s, h)"

(*********************************************************************************************)

text {* Locality is defined on the abstract concept of separation algebra *}

locale locality  = partial_comm_monoid sep_add sep_def sep_unit
  for sep_add :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<bullet>" 70)
    and sep_def :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "##" 50)
    and sep_unit :: 'b ("emp")
begin

text {* Sub state relation *}

definition substate :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "x \<preceq> y \<equiv> \<exists>z. x ## z \<and> y = x \<bullet> z"

lemma substate_trans: "x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
  using local.pmult_ab1 local.pmult_assoc substate_def by fastforce

text {* Predicate about the heap *}

definition sep_hset :: "'b hpred \<Rightarrow> 'b hpred \<Rightarrow> 'b hpred" (infixl "*\<^sup>h" 75) where
  "P *\<^sup>h Q = { h \<bullet> h' | h h' . h ## h' \<and> h \<in> P \<and> h' \<in> Q}"

fun sepbot_hset :: "'b hpred_bot \<Rightarrow> 'b hpred_bot \<Rightarrow> 'b hpred_bot" (infixl "*\<^sup>h\<^sub>\<bottom>" 75) where
  "<P> *\<^sup>h\<^sub>\<bottom> <Q> = <{ h \<bullet> h' | h h' . h ## h' \<and> h \<in> P \<and> h' \<in> Q}>"
| "p *\<^sup>h\<^sub>\<bottom> \<bottom> = \<bottom>"
| "\<bottom> *\<^sup>h\<^sub>\<bottom> q = \<bottom>"

definition EMPH :: "'b hpred_bot" where "EMPH \<equiv> <{emp}>"

fun leq_hset :: "'b hpred_bot \<Rightarrow> 'b hpred_bot \<Rightarrow> bool" (infixl "\<subseteq>\<^sup>h\<^sub>\<bottom>" 50) where
  "<P> \<subseteq>\<^sup>h\<^sub>\<bottom> <Q> \<longleftrightarrow> P \<subseteq> Q"
| "p \<subseteq>\<^sup>h\<^sub>\<bottom> \<bottom> \<longleftrightarrow> True"
| "\<bottom> \<subseteq>\<^sup>h\<^sub>\<bottom> q \<longleftrightarrow> q = \<bottom>"

definition le_hset :: "'b hpred_bot \<Rightarrow> 'b hpred_bot \<Rightarrow> bool" (infixl "\<subset>\<^sup>h\<^sub>\<bottom>" 50) where
  "P \<subset>\<^sup>h\<^sub>\<bottom> Q \<equiv> P \<subseteq>\<^sup>h\<^sub>\<bottom> Q \<and> P \<noteq> Q"

(* TODO: interpret sep_hset as a quantale *)

lemma sepbot_hset_botl [simp]: "\<bottom> *\<^sup>h\<^sub>\<bottom> Q = \<bottom>"
  using sepbot_hset.elims by auto

lemma sepbot_hset_eqbot [iff]:"P *\<^sup>h\<^sub>\<bottom> <Q> = \<bottom> \<longleftrightarrow> P = \<bottom>"
  by (cases P) auto

lemma leq_hset_refl [intro]: "P \<subseteq>\<^sup>h\<^sub>\<bottom> P"
  by (cases P) auto

lemma leq_hset_eqbot [simp]: "\<bottom> \<subseteq>\<^sup>h\<^sub>\<bottom> Q \<longleftrightarrow> Q = \<bottom>"
  by (cases Q) auto


(*********************************************************************************************)

text {* Safety and Framing properties on Relations *}

definition safe :: "('a, 'b) state rel \<Rightarrow> bool" where
  "safe R \<equiv> \<forall>s h h'. (<s, h>, fault) \<notin> R \<and> h \<preceq> h' \<longrightarrow> (<s, h'>, fault) \<notin> R"

definition frame :: "('a, 'b) state rel \<Rightarrow> bool" where
  "frame R \<equiv> \<forall>s ho h dh s' h'. 
              (<s, ho>, fault) \<notin> R \<and>
              ho ## dh \<and> 
              h = ho \<bullet> dh \<and>                    
              (<s, h>, <s', h'>) \<in> R
              \<longrightarrow> (\<exists>ho'. ho' ## dh \<and> h' = ho' \<bullet> dh \<and> (<s, ho>, <s', ho'>) \<in> R)" 

lemma "frame R \<longleftrightarrow> (\<forall>s ho h1 h' s'. (<s, ho>, fault) \<notin> R \<and> ho ## h1 \<and> (<s, ho \<bullet> h1>, <s', h'>) \<in> R \<longrightarrow> (\<exists>ho'. ho' ## h1 \<and> (<s, ho>, <s', ho'>) \<in> R \<and> h' = ho' \<bullet> h1))"
  apply (auto simp: frame_def)
apply force+
done

lemma safe_var: "safe R \<longleftrightarrow> (\<forall>s h h'. (<s, h'>, fault) \<in> R \<longrightarrow> h \<preceq> h' \<longrightarrow> (<s, h>, fault) \<in> R)" 
  by (auto simp: safe_def)

lemma safe2: "safe R \<longleftrightarrow> (\<forall>s h h'. (<s, h>, fault) \<notin> R \<and> h ## h' \<longrightarrow> (<s, h \<bullet> h'>, fault) \<notin> R)" 
  by (auto simp: safe_var substate_def)

lemma "\<forall>R \<in> PR. safe R \<Longrightarrow> safe (\<Union>PR)"
  by (auto simp: safe_def)

lemma "\<forall>R \<in> PR. frame R \<Longrightarrow> frame (\<Union>PR)"
  by (clarsimp simp: frame_def) meson

lemma "safe R \<Longrightarrow> safe S \<Longrightarrow> safe (R \<union> S)"
  by (auto simp: safe_def)

lemma "safe R \<Longrightarrow> safe S \<Longrightarrow> safe (R \<inter> S)"
  by (auto simp: safe_def)

lemma "safe R \<Longrightarrow> safe (R\<^sup>*)"
  apply (auto simp: safe_def)
  (* nitpick *) oops

lemma "frame R \<Longrightarrow> frame S \<Longrightarrow> frame (R \<union> S)"
  apply (auto simp: frame_def)
  apply blast+
done

lemma "frame R \<Longrightarrow> frame S \<Longrightarrow> frame (R \<inter> S)"
  apply (auto simp: frame_def)
  (* nitpick *) oops

lemma "frame R \<Longrightarrow> frame (R\<^sup>*)"
  apply (auto simp: frame_def)
  (* nitpick *) oops

lemma "safe R \<Longrightarrow> frame R \<Longrightarrow> safe (R\<^sup>*)"
  apply (auto simp: safe_def frame_def substate_def)
  (* nitpick *) oops

definition from_test :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) state rel" where
  "from_test P \<equiv> {(<s, h>, <s, h>) | s h. (s, h) \<in> P}" 

definition precise' :: "'b set \<Rightarrow> bool" where
  "precise' P \<equiv> \<forall>h. \<exists>h'. h' \<preceq> h \<longrightarrow> h' \<in> P"

lemma "precise' {h}"
  apply (auto simp: precise'_def substate_def)
done

definition precise :: "('a \<times> 'b) set \<Rightarrow> bool" where
  "precise P \<equiv> \<forall>(s :: 'a) h. \<exists>h'. h' \<preceq> h \<longrightarrow> h' \<in> (snd ` P)"

lemma "precise {(s, h)}"
  by (auto simp: precise_def)
  


lemma "safe (from_test P)"
  by (auto simp: safe_var from_test_def) 

lemma "precise P \<Longrightarrow> frame (from_test P)"
  apply (auto simp: frame_def from_test_def precise_def substate_def)
  apply (erule_tac x=so in allE)
  apply auto
oops
  

(*********************************************************************************************)

text {* State Transformer *}

definition stran :: "('a, 'b) state rel \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pred_bot" ("\<langle>_\<rangle>") where
  "\<langle>R\<rangle> s h \<equiv> if (<s, h>, fault) \<in> R then \<bottom> else <{(s', h'). (<s, h>, <s', h'>) \<in> R}>"

lemma non_fault_eq: "\<exists>P. \<langle>R\<rangle> s h = <P> \<longleftrightarrow> (<s, h>, fault) \<notin> R"
  by (clarsimp simp: stran_def)

lemma non_faultD [dest]: "\<langle>R\<rangle> s h = <P> \<Longrightarrow> (<s, h>, fault) \<notin> R"
  by (clarsimp simp: stran_def)

lemma fault_eq: "\<langle>R\<rangle> s h = \<bottom> \<longleftrightarrow> (<s, h>, fault) \<in> R"
  by (auto simp: stran_def)

lemma safeD1: "safe R \<Longrightarrow> (<s, h'>, fault) \<in> R \<Longrightarrow> h \<preceq> h' \<Longrightarrow> (<s, h>, fault) \<in> R"
  using safe_def by fastforce

lemma safeD2: "safe R \<Longrightarrow> h ## h' \<Longrightarrow> \<langle>R\<rangle> s (h \<bullet> h') = \<bottom> \<Longrightarrow> \<langle>R\<rangle> s h = \<bottom>"
  by (meson fault_eq substate_def safe_def)

primrec image_bot :: "('c \<Rightarrow> 'd) \<Rightarrow> 'c set option \<Rightarrow> 'd set option" (infixr "``" 90) where
  "f `` \<bottom> = \<bottom>"
| "f `` <A> = <{y. \<exists>x\<in>A. y = f x}>"

abbreviation hproj :: "('a, 'b) pred \<Rightarrow> 'b hpred" ("_\<downharpoonright>\<^sup>h" [1000] 999) where
  "P\<downharpoonright>\<^sup>h \<equiv> snd ` P"

lemma hprojI [intro]: "(s, h) \<in> P \<Longrightarrow>  h \<in> P\<downharpoonright>\<^sup>h"
  by (simp add: rev_image_eqI)

abbreviation hproj_bot :: "('a, 'b) pred_bot \<Rightarrow> 'b hpred_bot" ("_\<downharpoonright>\<^sup>h\<^sub>\<bottom>" [1000] 999) where
  "P\<downharpoonright>\<^sup>h\<^sub>\<bottom> \<equiv> snd `` P"

lemma hproj_bot: "f = \<bottom> \<Longrightarrow> (f)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = \<bottom>"
  by auto

lemma hproj_some [simp]: "f = <P> \<Longrightarrow> (f)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <P\<downharpoonright>\<^sup>h >"
  by auto

lemma safeD2_hproj: "safe R \<Longrightarrow> h ## h' \<Longrightarrow> (\<langle>R\<rangle> s (h \<bullet> h'))\<downharpoonright>\<^sup>h\<^sub>\<bottom> = \<bottom> \<Longrightarrow> (\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = \<bottom>"
  by (metis (no_types, lifting) image_bot.simps(2) option.distinct(1) safeD2 stran_def)

lemma non_faultD_hproj [dest]: "(\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <P> \<Longrightarrow> (<s, h>, fault) \<notin> R"
  by (clarsimp simp: stran_def)

lemma stran_hproj_eq: "(\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <H> \<Longrightarrow> h' \<in> H \<longleftrightarrow> (\<exists>s'. (<s, h>, <s', h'>) \<in> R)"
  apply (clarsimp simp: stran_def)
  apply (case_tac "(<s, h>, fault) \<in> R")
  apply auto
done

lemma stran1: "(\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <H> \<Longrightarrow> \<exists>s' h'. h' \<in> H \<longrightarrow> (<s, h>, <s', h'>) \<in> R"
  by (auto simp: stran_hproj_eq)

lemma stran2: "(\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <H> \<Longrightarrow> h' \<in> H \<Longrightarrow> \<exists>s'. (<s, h>, <s', h'>) \<in> R"
  by (auto simp: stran_hproj_eq)

lemma stran3: "(\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <H> \<Longrightarrow> (<s, h>, <s', h'>) \<in> R \<Longrightarrow> h' \<in> H"
  by (auto simp: stran_hproj_eq)

text {* Locality -- State Transformer *}


definition local :: "('a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pred_bot) \<Rightarrow> bool" where
  "local f \<equiv> \<forall>s h h'. h ## h' \<longrightarrow> (f s (h \<bullet> h'))\<downharpoonright>\<^sup>h\<^sub>\<bottom> \<subseteq>\<^sup>h\<^sub>\<bottom> (f s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> *\<^sup>h\<^sub>\<bottom> <{h'}>"


theorem sf_local: "safe R \<Longrightarrow> frame R \<Longrightarrow> local \<langle>R\<rangle>"
  apply (clarsimp simp: local_def)
  apply (case_tac "(\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom>")
  -- None
    apply clarsimp
  -- Some
    apply clarsimp
    apply (case_tac "(\<langle>R\<rangle> s (h \<bullet> h'))\<downharpoonright>\<^sup>h\<^sub>\<bottom>")
    -- None
      apply (clarsimp simp: safeD2_hproj)
    -- Some
      apply (clarsimp simp: frame_def)
      apply (meson stran2 stran3 non_faultD_hproj) 
done

theorem local_safe: "local \<langle>R\<rangle> \<Longrightarrow> safe R"
  apply (clarsimp simp: local_def safe_def substate_def stran_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=z in allE)
  apply clarsimp
done
                                                                                                                           
lemma local_frame1: "P \<subseteq> {h \<bullet> dh |h. h ## dh \<and> h \<in> Q }\<Longrightarrow> h \<in> P \<Longrightarrow> \<exists>h'. h = h' \<bullet> dh \<and> h' ## dh \<and> h' \<in> Q"
  by auto

lemma local_frame2: "(<s, h>, \<sigma>') \<in> R \<Longrightarrow> (\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <P> \<Longrightarrow> (<s, h>, None) \<notin> R  \<Longrightarrow> \<exists>s' h'. \<sigma>' = <s', h'> \<and> h' \<in> P"
  apply (cases \<sigma>')
  apply clarsimp
  apply (case_tac a)
  by (simp add: stran3)

theorem local_frame: "local \<langle>R\<rangle> \<Longrightarrow> frame R"
  apply (clarsimp simp: frame_def local_def)
(* nitpick
  apply (erule_tac x=so in allE)
  apply (erule_tac x=ho in allE)
  apply (erule_tac x=dh in allE)
  apply clarsimp
  apply (case_tac "(\<langle>R\<rangle> so (ho \<bullet> dh))\<downharpoonright>\<^sup>h\<^sub>\<bottom>")
  -- None 
    using fault_eq apply fastforc
  -- Some 
    apply clarsimp
    apply (case_tac "(\<langle>R\<rangle> so ho)\<downharpoonright>\<^sup>h\<^sub>\<bottom> *\<^sup>h\<^sub>\<bottom> <{dh}>")
    -- None
      apply (simp add: stran_def)
    -- Some
      apply clarsimp
      apply (case_tac "(\<langle>R\<rangle> so ho)\<downharpoonright>\<^sup>h\<^sub>\<bottom>")
      -- None
        apply clarsimp
      -- Some
        apply (clarsimp simp add: stran_hproj_eq)
        apply (subgoal_tac "h' \<in> a")
        apply blast
        apply (simp add: stran3)
done *)
oops

text {* Predicate (Assertion) Level *}

definition sep :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" (infixl "*" 75) where
  "P * Q \<equiv> {(s, h \<bullet> h') | s h h' .  h ## h' \<and> (s, h) \<in> P \<and> (s, h') \<in> Q}"

lemma mono_star: "P \<le> Q \<Longrightarrow> P * R \<le> Q * R"
  by (auto simp: sep_def)

(* TODO: sep forms a quantale *)

definition ptran :: "('a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pred_bot) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set" ("\<lbrakk>_\<rbrakk>") where
  "\<lbrakk>f\<rbrakk> Q \<equiv> {(s, h). case f s h of \<bottom> \<Rightarrow> False | <Q'> \<Rightarrow> Q' \<subseteq> Q }"

definition up_proj :: "('a, 'b) pred \<Rightarrow> ('a, 'b) pred" ("_\<up>" [1000] 999) where
  "P\<up> \<equiv> \<top> \<times> snd ` P"

definition Local :: "(('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set) \<Rightarrow> bool" where
  "Local F \<equiv> \<forall>P Q. (F P) * Q \<le> F (P\<up> * Q\<up>)"


lemma ptranD: "(s, h) \<in> \<lbrakk>\<langle>R\<rangle>\<rbrakk> Q  \<Longrightarrow> (<s, h>, <s', h'>) \<in> R \<Longrightarrow> (s', h') \<in> Q"
  apply (clarsimp simp: ptran_def stran_def)
  apply (case_tac "(<s, h>, fault) \<in> R")
  apply auto
done

lemma Local_stran_bot: "Local \<lbrakk>f\<rbrakk> \<Longrightarrow> h ## h' \<Longrightarrow> f s (h \<bullet> h') = \<bottom> \<Longrightarrow> f s h = \<bottom>"
  apply (clarsimp simp: Local_def)
  apply (erule_tac x="the (f s h)" in allE)
  apply (erule_tac x="{(s, h')}" in allE)
  apply (case_tac "f s h")
  apply (clarsimp simp: ptran_def)
  apply (subgoal_tac "the (f s h) = a")
  apply (force simp: ptran_def sep_def)
  apply force
done

lemma Local_stran_bot2: "Local \<lbrakk>\<langle>R\<rangle>\<rbrakk> \<Longrightarrow> h ## h' \<Longrightarrow> (\<langle>R\<rangle> s (h \<bullet> h'))\<downharpoonright>\<^sup>h\<^sub>\<bottom> = \<bottom> \<Longrightarrow> (\<langle>R\<rangle> s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = \<bottom>"
  apply (clarsimp simp: stran_def sep_def ptran_def Local_def)
  apply (erule_tac x="{\<sigma>'. (<s, h>, <\<sigma>'>) \<in> R}" in allE)
  apply (erule_tac x="{(s, h')}" in allE)
  apply clarsimp
  apply (case_tac " (<s, h \<bullet> h'>, fault) \<in> R")
  apply force
  apply clarsimp
done

lemma stran_ptran: "f s h = <S> \<Longrightarrow> (s, h) \<in> \<lbrakk>f\<rbrakk> S"
  by (clarsimp simp: stran_def ptran_def)

lemma stran_ptran_eq2: "f s h = <S> \<Longrightarrow> S \<subseteq> S' \<longleftrightarrow> (s, h) \<in> \<lbrakk>f\<rbrakk> S'"
  apply (clarsimp simp: stran_def ptran_def)
done

lemma stran_ptran_eq: "(f s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> \<subseteq>\<^sup>h\<^sub>\<bottom> <H> \<longleftrightarrow> (s, h) \<in> \<lbrakk>f\<rbrakk> (\<top>\<times>H)"
  apply (clarsimp simp: stran_def ptran_def)
  apply (case_tac "f s h")
  apply auto
done

lemma stran_ptranD [dest]: "(f s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> = <H> \<Longrightarrow> (s, h) \<in> \<lbrakk>f\<rbrakk> (\<top>\<times>H)"
  using stran_ptran_eq by force

lemma sep_heap_only[simp]: "\<top>\<times>H * \<top>\<times>H' = \<top>\<times>{h \<bullet> h' |h h'. h ## h' \<and> h \<in> H \<and> h' \<in> H'}"
  by (auto simp: sep_def)

theorem Local_local: "Local \<lbrakk>f\<rbrakk> \<Longrightarrow> local f"
  apply (clarsimp simp: local_def up_proj_def)
  apply (case_tac "(f s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> *\<^sup>h\<^sub>\<bottom> <{h'}>")
  -- None 
    apply clarsimp
  -- Some 
    apply (clarsimp simp: stran_ptran_eq)
    apply (case_tac "(f s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom>")
    -- None
    apply clarsimp
    -- Some
    apply (clarsimp simp: Local_def up_proj_def)
    apply (erule_tac x="\<top>\<times>aa" in allE)
    apply (erule_tac x="\<top>\<times>{h'}" in allE) 
    using sep_def apply fastforce
done


lemma local_Local_bot: "local f \<Longrightarrow> (a, b) \<in> \<lbrakk>f\<rbrakk> P * Q \<Longrightarrow> f a b = \<bottom> \<Longrightarrow> (a, b) \<in> \<lbrakk>f\<rbrakk> (\<top> \<times> {h \<bullet> h' |h h'. h ## h' \<and> h \<in> P\<downharpoonright>\<^sup>h \<and> h' \<in> Q\<downharpoonright>\<^sup>h})"
  apply (clarsimp simp: ptran_def sep_def local_def)
  apply (erule_tac x=a in allE)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=h' in allE)
  apply clarsimp
  apply (case_tac "f a h")
  apply auto
done

theorem local_Local: "local f  \<Longrightarrow> Local \<lbrakk>f\<rbrakk>"
  apply (clarsimp simp: Local_def)
  apply (case_tac "f a b")
  -- None
    apply (simp add: local_Local_bot up_proj_def)
  -- Some
    apply (rename_tac P')
    apply (subst stran_ptran_eq2[symmetric])
    apply assumption
    apply (default, case_tac x, clarsimp)
    apply (clarsimp simp: local_def)
    apply (rename_tac s h F s' h')
    apply (subgoal_tac "\<exists>h1 h2 F1. h = h1 \<bullet> h2 \<and> h1 ## h2 \<and> f s h1 = <F1> \<and> F1 \<subseteq> P \<and> h2 \<in> snd ` Q")
      apply clarsimp
      apply (erule_tac x=s in allE)
      apply (erule_tac x=h1 in allE)
      apply (erule_tac x=b in allE)
      apply clarsimp
      apply (subgoal_tac "h' \<in> {y. \<exists>x\<in>F. y = snd x}")
        apply (subgoal_tac "h' \<in> {h \<bullet> b |h. h ## b \<and> (\<exists>x\<in>F1. h = snd x)}")
        apply (clarsimp simp: up_proj_def)
        apply (rule_tac x=bb in exI)
        apply (rule_tac x=b in exI)
        apply (force simp: sep_def)
        apply force
      apply force
    apply (clarsimp simp: sep_def)
    apply (rule_tac x=ha in exI)
    apply (rule_tac x=h'a in exI)
    apply clarsimp
    apply (case_tac "f s ha")
    -- None 
      apply (clarsimp simp add: ptran_def)
    -- Some
    apply (subst (asm) stran_ptran_eq2[symmetric])
    apply assumption
    apply force
done

definition about_heap :: "('a \<times> 'b) set \<Rightarrow> bool" where
  "about_heap P \<equiv> P = P\<up>"

lemma frame_rule: "Local F \<Longrightarrow> about_heap Q \<Longrightarrow> about_heap R \<Longrightarrow> P \<le> F Q \<Longrightarrow> P * R \<le> F (Q * R)"
  apply (simp add: about_heap_def Local_def)
  by (metis dual_order.trans mono_star)

definition to_prog :: "('a, 'b) pred \<Rightarrow> ('a, 'b) state rel" where
  "to_prog P \<equiv> {(<p>, <p>) | p. p \<in> P}"

fun pred_bot_leq :: "('a, 'b) pred_bot \<Rightarrow> ('a, 'b) pred_bot \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "<P> \<sqsubseteq> <Q> \<longleftrightarrow> P \<subseteq> Q"
| "\<bottom> \<sqsubseteq> Q \<longleftrightarrow> Q = \<bottom>"
| "P \<sqsubseteq> \<bottom> \<longleftrightarrow> False"

fun sepbot_set :: "('a, 'b) pred_bot \<Rightarrow> ('a, 'b) pred_bot \<Rightarrow> ('a, 'b) pred_bot" (infixl "*\<^sub>\<bottom>" 75) where
  "<P> *\<^sub>\<bottom> <Q> = <P * Q>"
| "p *\<^sub>\<bottom> \<bottom> = \<bottom>"
| "\<bottom> *\<^sub>\<bottom> q = \<bottom>"

definition local2 :: "('a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pred_bot) \<Rightarrow> bool" where
  "local2 f \<equiv> \<forall>s h h'. h ## h' \<longrightarrow> (f s (h \<bullet> h')) \<sqsubseteq> (f s h) *\<^sub>\<bottom> <\<top>\<times>{h'}>"

lemma "local2 f \<Longrightarrow> local f"
  apply (auto simp: local_def local2_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=h' in allE)
  apply clarsimp
  apply (case_tac "(f s (h \<bullet> h'))\<downharpoonright>\<^sup>h\<^sub>\<bottom>")
  apply clarsimp
  apply (metis hproj_some option.distinct(1) option.exhaust pred_bot_leq.elims(2) sepbot_set.simps(1))
  apply clarsimp
  apply (case_tac "(f s h)\<downharpoonright>\<^sup>h\<^sub>\<bottom> *\<^sup>h\<^sub>\<bottom> <{h'}>")
  apply clarsimp
  apply clarsimp
  apply (case_tac "(f s (h \<bullet> h'))")
  apply clarsimp
  apply (case_tac "f s h *\<^sub>\<bottom> <\<top> \<times> {h'}>")
  apply clarsimp
  apply clarsimp
  apply (case_tac "(f s h)")
  apply clarsimp
  apply clarsimp
  apply (clarsimp simp: sep_def)
  apply force
done

lemma "local2 \<langle>R\<rangle> \<Longrightarrow> frame R"
  apply (clarsimp simp: frame_def local2_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=ho in allE)
  apply (erule_tac x=dh in allE)
  apply clarsimp
  apply (case_tac "(\<langle>R\<rangle> s (ho \<bullet> dh))")
  -- None 
    using fault_eq apply fastforce
  -- Some 
    apply clarsimp
    apply (case_tac "\<langle>R\<rangle> s ho *\<^sub>\<bottom> <\<top> \<times> {dh}>")
    -- None
      apply (simp add: stran_def)
    -- Some
      apply clarsimp
      apply (case_tac "(\<langle>R\<rangle> s ho)")
      -- None
        apply clarsimp
      -- Some
        apply (clarsimp simp add: sep_def)
by (smt Pair_inject mem_Collect_eq old.prod.case option.inject ptranD stran_def stran_ptran_eq2)

lemma "local2 f \<Longrightarrow> \<forall>P Q. (\<lbrakk>f\<rbrakk> P) * Q \<le> \<lbrakk>f\<rbrakk> (P * Q\<up>)"
  apply (clarsimp simp: )
  apply (case_tac "f a b")
  -- None
    apply (clarsimp simp add: up_proj_def sep_def ptran_def)
      apply (case_tac "f a h")
      apply clarsimp
      apply clarsimp
      apply (metis local2_def option.distinct(1) pred_bot_leq.elims(2) sepbot_set.simps(1))
  -- Some
    apply (rename_tac P')
    apply (subst stran_ptran_eq2[symmetric])
    apply assumption
    apply (default, case_tac x, clarsimp)
    apply (clarsimp simp: local2_def)
    apply (rename_tac s h F s' h')
    apply (clarsimp simp: ptran_def sep_def)
      apply (case_tac "f s ha")
      apply clarsimp
      apply clarsimp
      apply (erule_tac x=s in allE)
      apply (erule_tac x=ha in allE)
      apply (erule_tac x=h'a in allE)
      apply (clarsimp simp: sep_def up_proj_def)
by fastforce
      
lemma "local2 f \<Longrightarrow> \<forall>P Q. (\<lbrakk>f\<rbrakk> P) * Q \<le> \<lbrakk>f\<rbrakk> (P * Q)"
nitpick oops


lemma "(\<forall>(s, h) \<in> P. \<langle>R\<rangle> s h \<sqsubseteq> <Q>) \<Longrightarrow> to_prog P O R \<le> R O to_prog Q"
apply (clarsimp simp: to_prog_def)
apply (rule relcompI)
apply assumption
apply clarsimp
apply (erule_tac x="(aa, ba)" in ballE)
apply (clarsimp simp: stran_def)
apply (case_tac "(<aa, ba>, fault) \<in> R")
apply clarsimp
apply clarsimp
apply (case_tac z)
apply clarsimp
apply clarsimp
apply force
by force

lemma "to_prog P O R \<le> R O to_prog Q \<Longrightarrow> (\<forall>(s, h) \<in> P. \<langle>R\<rangle> s h \<sqsubseteq> <Q>)"
apply auto
apply (clarsimp simp: stran_def)
apply (case_tac "(<a, b>, fault) \<notin> R")
apply clarsimp
apply (clarsimp simp: to_prog_def)
apply force
apply clarsimp
apply (clarsimp simp: to_prog_def)
apply force
done

end

end