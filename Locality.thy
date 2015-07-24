theory Locality
  imports "Algebra/PartialMonoid" While
begin

no_notation times (infixl "*" 70)

type_synonym heap = "nat \<Rightarrow> nat option"

definition ortho :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 55)
  where "h1 \<bottom> h2 \<equiv> dom h1 \<inter> dom h2 = {}"

(*********************************************************************************************)

text {* State Level *}

type_synonym 's state = "('s \<times> heap) option"

abbreviation fault_state :: "'s state" ("fault") where "fault \<equiv> None"
abbreviation some_state :: "'s \<Rightarrow> heap \<Rightarrow> 's state" ("<_, _>") where "<s, h> \<equiv> Some (s, h)"

definition state_def :: "'s state \<Rightarrow> 's state \<Rightarrow> bool" (infix "##" 50) where
  "\<sigma> ## \<sigma>' \<equiv> case \<sigma> of fault \<Rightarrow> False
                     | <s, h> \<Rightarrow> (case \<sigma>' of fault \<Rightarrow> False
                                          | <s', h'> \<Rightarrow> s = s' \<and> h \<bottom> h')"

definition state_sep :: "'s state \<Rightarrow> 's state \<Rightarrow> 's state" (infixl "\<bullet>" 70) where
  "\<sigma> \<bullet> \<sigma>' \<equiv> case \<sigma> of fault \<Rightarrow> fault
                    | <s, h> \<Rightarrow> (case \<sigma>' of fault \<Rightarrow> fault
                                         | <s', h'> \<Rightarrow> (if s = s' \<and> h \<bottom> h' then <s, h ++ h'> else fault))"

definition state_leq :: "'s state \<Rightarrow> 's state \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "\<sigma> \<preceq> \<sigma>' \<equiv> \<exists>\<delta>. \<sigma> ## \<delta> \<and> \<sigma>' = \<sigma> \<bullet> \<delta>"

interpretation state: partial_ab_semigroup state_sep state_def
  apply default
  apply (auto simp: state_def_def state_sep_def)
    apply (case_tac x, auto)
    apply (case_tac y, auto)
    apply (case_tac z, auto simp: ortho_def)
  apply auto
    apply (case_tac x, auto)
    apply (case_tac y, force)
    apply (case_tac z, auto simp: ortho_def)
  apply auto
    apply (case_tac x, auto)
    apply (case_tac y, auto)
    apply (case_tac z, auto)
  apply (auto simp: ortho_def)
    apply (case_tac x, auto)
  apply (case_tac y, auto simp: ortho_def)
    apply (case_tac x, auto)
    apply (case_tac y, auto simp: ortho_def map_add_comm)
  apply auto
done

lemma state_leq_sep1: "\<sigma> ## \<sigma>' \<Longrightarrow> \<sigma> \<preceq> \<sigma> \<bullet> \<sigma>'"
  by (auto simp add: state_sep_def state_def_def state_leq_def)

lemma state_leq_sep2: "\<sigma> ## \<sigma>' \<Longrightarrow> \<sigma>' \<preceq> \<sigma> \<bullet> \<sigma>'"
  using state.pmult_comm state.pmult_comm_def state_leq_def by blast

lemma state_leq_fault1 [simp]: "\<not> fault \<preceq> \<sigma>"
  by (auto simp: state_leq_def state_def_def)

lemma state_leq_fault2 [simp]: "\<not> \<sigma> \<preceq> fault"
  by (auto simp: state_leq_def state_def_def state_sep_def split: option.split)

lemma state_defD [dest]: "\<sigma> ## \<sigma>' \<Longrightarrow> \<exists>s h h'. \<sigma> = Some (s, h) \<and> \<sigma>' = Some (s, h') \<and> h \<bottom> h'"
  apply (auto simp: state_def_def)
  apply (cases \<sigma>)
  apply auto
  apply (cases \<sigma>')
  apply auto
done

lemma state_non_fault1 [simp]: "\<sigma> ## \<sigma>' \<Longrightarrow> \<sigma> \<noteq> fault"
  by auto

lemma state_non_fault2 [simp]: "\<sigma> ## \<sigma>' \<Longrightarrow> \<sigma>' \<noteq> fault"
  by auto

lemma state_sep_non_fault1 [simp]: "\<sigma> ## \<sigma>' \<Longrightarrow> \<sigma> \<bullet> \<sigma>' \<noteq> fault"
  by (auto simp: state_sep_def)

lemma state_sep_non_fault2 [simp]: "\<sigma> ## \<sigma>' \<Longrightarrow> \<sigma>' \<bullet> \<sigma> \<noteq> fault"
  using state.pmult_comm_def state_sep_non_fault1 by blast

lemma state_sep_unfold: "<s, h> = \<delta> \<bullet> <s', h'> \<Longrightarrow> \<exists>dh. h = dh ++ h' \<and> dh \<bottom> h' \<and> s = s' \<and> \<delta> = <s, dh>"
  apply (auto simp: state_sep_def)
  apply (cases \<delta>)
  -- None apply clarsimp
  -- Some 
    apply clarsimp 
    apply (case_tac "a = s' \<and> b \<bottom> h'")
    apply auto
done

(*********************************************************************************************)

text {* Predicate (Assertion) Level *}

type_synonym 's pred = "('s \<times> heap) set option"

abbreviation fault_pred :: "'s pred" ("Fault") where "Fault \<equiv> None"
abbreviation some_pred :: "'a \<Rightarrow> 'a option" ("<_>") where "<P> \<equiv> Some P"
                               

definition sep_conj :: "'s pred \<Rightarrow> 's pred \<Rightarrow> 's pred" (infixl "*" 75) where
  "P * Q \<equiv> case P of Fault \<Rightarrow> None 
                | <p> \<Rightarrow> (case Q of Fault \<Rightarrow> Fault 
                               | <q> \<Rightarrow> <{(s, h ++ h') | s s' h h' . s = s' \<and> h \<bottom> h' \<and> (s, h) \<in> p \<and> (s', h') \<in> q}>)"

definition emp :: "'s pred" where "emp \<equiv> <{(s, h) | s h. h = Map.empty}>"

definition pred_leq :: "'s pred \<Rightarrow> 's pred \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50) where
  "P \<sqsubseteq> Q \<equiv> case P of Fault \<Rightarrow> Q = Fault
                    | <p> \<Rightarrow> (case Q of Fault \<Rightarrow> True
                                     | <q> \<Rightarrow> p \<le> q)"

definition pred_le :: "'s pred \<Rightarrow> 's pred \<Rightarrow> bool" (infixl "\<sqsubset>" 50) where
  "P \<sqsubset> Q \<equiv> P \<sqsubseteq> Q \<and> P \<noteq> Q"

interpretation pred: monoid sep_conj emp
  apply default
  apply (auto simp: sep_conj_def emp_def)
    apply (case_tac a, auto)
    apply (case_tac b, auto)
    apply (case_tac c, auto simp: ortho_def)
    apply (metis (no_types, lifting) Un_empty dom_map_add inf_sup_distrib1 inf_sup_distrib2 map_add_assoc)
  apply (metis (no_types, lifting) Un_empty dom_map_add inf_sup_distrib1 inf_sup_distrib2 map_add_assoc)
  apply (case_tac a, auto simp: ortho_def)
  apply (case_tac a, auto simp: ortho_def)
done

lemma Fault_annir [simp]: "P * Fault = Fault"
  apply (auto simp: sep_conj_def)
  apply (cases P)
  apply auto
done

lemma Fault_annil [simp]: "Fault * P = Fault"
  by (auto simp: sep_conj_def)

lemma FaultI1:"P * <q> = Fault \<Longrightarrow> P = Fault"
  apply (clarsimp simp: sep_conj_def)
  by (cases P) auto

lemma FaultI2:"<p> * Q = Fault \<Longrightarrow> Q = Fault"
  apply (clarsimp simp: sep_conj_def)
  by (cases Q) auto

interpretation order pred_leq pred_le
  apply default
  apply (auto simp: pred_leq_def pred_le_def)
    apply (case_tac x, auto)
  apply (case_tac y, auto)
  apply (case_tac x, auto)
    apply (case_tac x, auto)
    apply (case_tac y, auto)
  apply (case_tac z, auto)
    apply (case_tac x, auto)
  apply (case_tac y, auto)
done

(*********************************************************************************************)

text {* Safety and Framing properties on Relations *}

definition safe :: "'s state rel \<Rightarrow> bool" where
  "safe R \<equiv> \<forall>\<sigma> \<sigma>'. (\<sigma>, None) \<notin> R \<and> \<sigma> \<preceq> \<sigma>' \<longrightarrow> (\<sigma>', None) \<notin> R"

definition frame :: "'s state rel \<Rightarrow> bool" where
  "frame R \<equiv> \<forall>\<sigma>o \<sigma> \<sigma>1 \<sigma>'. (\<sigma>o, None) \<notin> R \<and> \<sigma>o ## \<sigma>1 \<and> \<sigma> = \<sigma>o \<bullet> \<sigma>1 \<and> (\<sigma>, \<sigma>') \<in> R \<longrightarrow> (\<exists>\<sigma>o'. \<sigma>' = \<sigma>o' \<bullet> \<sigma>1 \<and> (\<sigma>o, \<sigma>o') \<in> R)" 

lemma safe_fault: "safe R \<Longrightarrow> (\<sigma>o, fault) \<notin> R \<Longrightarrow> \<sigma>o ## \<sigma>1 \<Longrightarrow> (\<sigma>o \<bullet> \<sigma>1, fault) \<notin> R"
  using safe_def state_leq_sep1 by blast

(*********************************************************************************************)

text {* State Transformer *}

definition func :: "'s state rel \<Rightarrow> 's state \<Rightarrow> 's pred" ("\<langle>_\<rangle>" [50] 1000) where
  "func R \<sigma> \<equiv> case \<sigma> of fault \<Rightarrow> Fault | 
                  <(s, h)> \<Rightarrow> (if (\<sigma>, fault) \<in> R then Fault 
                                                else <{(s', h') | s' h'. (<s, h>, <s', h'>) \<in> R}>)"

lemma func_faultD [dest]: "(\<sigma>, fault) \<in> R \<Longrightarrow> \<langle>R\<rangle> \<sigma> = Fault"
  by (auto simp: func_def split: option.split)

lemma func_non_FaultD [dest]: "\<langle>R\<rangle> \<sigma> \<noteq> Fault \<Longrightarrow> (\<sigma>, fault) \<notin> R"
  by (meson func_faultD)

lemma func_fault_eq [simp]: "\<sigma> \<noteq> fault \<Longrightarrow> \<langle>R\<rangle> \<sigma> = Fault \<longleftrightarrow> (\<sigma>, fault) \<in> R"
  by (auto simp: func_def split: option.split)

lemma func_some: "\<langle>R\<rangle> \<sigma> = <S> \<Longrightarrow> \<sigma>' \<in> S \<Longrightarrow> (\<sigma>, <\<sigma>'>) \<in> R"
  apply (auto simp: func_def)
  apply (cases \<sigma>)
  apply auto
  apply (case_tac "(<a, b>, fault) \<in> R")
  apply auto
done

lemma func_some2: "\<langle>R\<rangle> <s, h> = <S> \<Longrightarrow> (<s, h>, <s', h'>) \<in> R \<Longrightarrow> (s', h') \<in> S"
  apply (auto simp: func_def)
  apply (case_tac "(<s, h>, fault) \<in> R")
  apply auto
done



(*********************************************************************************************)

text {* Locality -- State Transformer *}

definition local :: "('s state \<Rightarrow> 's pred) \<Rightarrow> bool" where
  "local f \<equiv> \<forall>\<sigma> \<sigma>'. \<sigma> ## \<sigma>' \<longrightarrow> f (\<sigma> \<bullet> \<sigma>') \<sqsubseteq> (f \<sigma>) * <{the \<sigma>'}>"

lemma frame_local_Fault: "safe R \<Longrightarrow> \<sigma> ## \<sigma>' \<Longrightarrow> \<langle>R\<rangle> (\<sigma> \<bullet> \<sigma>') = Fault \<Longrightarrow> \<langle>R\<rangle> \<sigma> * <{the \<sigma>'}> = Fault"
  by clarsimp (metis Fault_annil func_non_FaultD safe_def state_leq_sep1)

lemma frame_local_Some: "safe R \<Longrightarrow> frame R \<Longrightarrow> \<sigma> ## \<sigma>' \<Longrightarrow> \<langle>R\<rangle> (\<sigma> \<bullet> \<sigma>') = <P> \<Longrightarrow> \<langle>R\<rangle> \<sigma> * <{the \<sigma>'}> = <Q> \<Longrightarrow> P \<subseteq> Q"
  apply (clarsimp simp: frame_def sep_conj_def)
  apply (cases "\<langle>R\<rangle> \<sigma>")
  -- None apply clarsimp
  -- Some 
    apply (frule state_defD)
    apply clarsimp
    apply (erule_tac x="<s, h>" in allE)
    apply (erule_tac x="<s, h'>" in allE)
    apply (erule_tac x="<a, b>" in allE)
    using func_some func_some2 state_sep_unfold apply fastforce
done   

lemma rel_local: "safe R \<Longrightarrow> frame R \<Longrightarrow> local \<langle>R\<rangle>"
  apply (clarsimp simp: local_def pred_leq_def)
  apply (case_tac "\<langle>R\<rangle> (\<sigma> \<bullet> \<sigma>')") 
  -- None apply (clarsimp simp: option.case_eq_if frame_local_Fault)
  -- Some 
    apply (case_tac "\<langle>R\<rangle> \<sigma> * Some {the \<sigma>'}")
    -- None apply clarsimp
    -- Some apply (clarsimp simp: frame_local_Some)
done

lemma local_rel_safe: "local \<langle>R\<rangle> \<Longrightarrow> safe R"
  apply (clarsimp simp: safe_def local_def state_leq_def)
  apply (drule func_faultD)
  by (metis (mono_tags, lifting) FaultI1 func_fault_eq option.case_eq_if pred_leq_def state_non_fault1)
  
lemma local_rel_frame1: "P \<subseteq> {(s, h ++ dh) |h. h \<bottom> dh \<and> (s, h) \<in> Q} \<Longrightarrow> (s, h) \<in> P \<Longrightarrow> \<exists>h'. h = h' ++ dh \<and> h' \<bottom> dh \<and> (s, h') \<in> Q"
  by auto

lemma local_rel_frame2: "(<s, h>, \<sigma>') \<in> R \<Longrightarrow> \<langle>R\<rangle> <s, h> = <P> \<Longrightarrow> (<s, h>, None) \<notin> R  \<Longrightarrow> \<exists>s' h'. \<sigma>' = <s', h'> \<and> (s', h') \<in> P"
  apply (cases \<sigma>')
  apply clarsimp
  apply (case_tac a)
  by (simp add: func_some2)

lemma local_rel_frame: "local \<langle>R\<rangle> \<Longrightarrow> frame R"
  apply (clarsimp simp: frame_def local_def pred_leq_def)
  apply (erule_tac x=\<sigma>o in allE)
  apply (erule_tac x=\<sigma>1 in allE)
  apply clarsimp
  apply (case_tac "\<langle>R\<rangle> (\<sigma>o \<bullet> \<sigma>1)")
  -- None 
    apply clarsimp
    using FaultI1 func_fault_eq apply blast
  -- Some 
    apply clarsimp
    apply (case_tac "\<langle>R\<rangle> \<sigma>o * Some {the \<sigma>1}")
    -- None 
      apply clarsimp
      using FaultI1 func_fault_eq apply blast
    -- Some
      apply clarsimp
      apply (clarsimp simp: sep_conj_def)
      apply (case_tac "\<langle>R\<rangle> \<sigma>o")
      -- None
        apply clarsimp
      -- Some
        apply (drule state_defD)
        apply clarsimp
        apply (rename_tac P Q s h h')
        apply (clarsimp simp: state_sep_def )
        apply (drule_tac local_rel_frame2)
        apply assumption
        apply (clarsimp simp add: func_faultD)
        apply clarsimp
        apply (subgoal_tac "s' = s")
          prefer 2
          apply blast
        apply clarsimp
        apply (drule local_rel_frame1)
        apply assumption
        apply clarsimp
        apply (rule_tac x="Some (s, h'b)" in exI)
        apply (auto simp add: func_some)
done

lemma local_frame_safe_eq: "local \<langle>R\<rangle> \<longleftrightarrow> safe R \<and> frame R"
  using local_rel_frame local_rel_safe rel_local by blast

lemma safe_assign: "safe (assign u_upd t)"
  apply (clarsimp simp: safe_def assign_def graph_def)
  apply (case_tac \<sigma>)
  --None apply clarsimp
  -- Some
    apply clarsimp
    apply (case_tac \<sigma>')
    apply auto
done



lemma "frame (assign u_upd t)"
  apply (auto simp: frame_def)
  apply (frule state_defD)
  apply clarsimp
  apply (case_tac \<sigma>')
  -- None
    apply (clarsimp simp add: safe_assign safe_fault)
  -- Some
    apply clarsimp
    apply (clarsimp simp: assign_def graph_def)
    apply (case_tac "<s, h> \<bullet> <s, h'>")
    apply clarsimp
    apply clarsimp









end