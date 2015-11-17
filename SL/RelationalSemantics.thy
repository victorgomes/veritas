theory RelationalSemantics
  imports StoreHeapModel
begin

no_notation pleq (infix "\<sqsubseteq>" 50)

type_synonym 'a state = "('a \<times> heap) option"

definition pred :: "'a pred \<Rightarrow> 'a state set" where
  "pred P = {Some x | x. x \<in> P}"

lemma predE [elim!]: "x \<in> pred P \<Longrightarrow> (\<And>a b. x = Some (a, b) \<Longrightarrow> (a, b) \<in> P \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto simp: pred_def)

lemma predI [intro!]: "x \<in> P \<Longrightarrow> Some x \<in> pred P"
  apply (auto simp: pred_def )
  apply (rule_tac x="fst x" in exI)
  apply (rule_tac x="snd x" in exI)
  by auto

definition stran :: "'a state rel \<Rightarrow> ('a \<times> heap) \<Rightarrow> 'a pred option" where
  "stran R a \<equiv> if (Some a, None) \<in> R then None else Some {b. (Some a, Some b) \<in> R}"

lemma stranD: "stran R a = Some P \<Longrightarrow> b \<in> P \<Longrightarrow> (Some a, Some b) \<in> R"
  apply (auto simp: stran_def)
  apply (case_tac "(Some a, None) \<in> R")
  apply auto
done

lemma stranD2: "stran R a = Some P \<Longrightarrow> (Some a, Some b) \<in> R \<Longrightarrow> b \<in> P"
  apply (auto simp: stran_def)
  apply (case_tac "(Some a, None) \<in> R")
  apply auto
done

lemma stran_none: "stran R a = None \<longleftrightarrow> (Some a, None) \<in> R"
  by (auto simp: stran_def)

lemma stran_some: "stran R a = Some P \<Longrightarrow> (Some a, None) \<notin> R"
  by (auto simp: stran_def)

definition valid_subset :: "'a set option \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "\<sqsubseteq>" 100) where
  "P \<sqsubseteq> Q \<equiv> case P of None \<Rightarrow> False | Some P' \<Rightarrow> P' \<subseteq> Q"

lemma stranE2 [elim!]: "stran R a \<sqsubseteq> Q \<Longrightarrow> ((Some a, None) \<notin> R \<Longrightarrow> \<forall>b. (Some a, Some b) \<in> R \<longrightarrow> b \<in> Q \<Longrightarrow> G) \<Longrightarrow> G"
  apply (auto simp: stran_def valid_subset_def valid_mem_def)
  apply (case_tac "(Some a, None) \<in> R")
  apply simp
  apply auto
done

lemma stranI [intro!]: "(Some a, None) \<notin> R \<Longrightarrow> (\<And>b. (Some a, Some b) \<in> R \<Longrightarrow> b \<in> Q) \<Longrightarrow> stran R a \<sqsubseteq> Q"
  by (auto simp: stran_def valid_subset_def)

definition ptran :: "'a state rel \<Rightarrow> 'a ptran" where
  "ptran R Q = {a. stran R a \<sqsubseteq> Q}"

lemma [simp]: "(a, b) \<in> R O (Id_on Q) \<longleftrightarrow> (a, b) \<in> R \<and> b \<in> Q"
  by auto

lemma "P \<le> ptran R Q \<Longrightarrow> (Id_on (pred P)) O R \<le> R O (Id_on (pred Q))"
  apply (clarsimp simp: ptran_def)
  by (case_tac z) auto


lemma "(Id_on (pred P)) O R \<le> R O (Id_on (pred Q)) \<Longrightarrow> P \<le> ptran R Q"
  by (auto simp: ptran_def)

fun sep_bot :: "'a pred option \<Rightarrow> 'a pred option \<Rightarrow> 'a pred option" (infixl "*\<^sub>h" 75) where
  "(Some P) *\<^sub>h (Some Q) = Some (P * Q)"
| "P *\<^sub>h None = None"
| "None *\<^sub>h Q = None"

fun leq_bot :: "'a pred option \<Rightarrow> 'a pred option \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>h" 50) where
  "Some P \<sqsubseteq>\<^sub>h Some Q \<longleftrightarrow> P \<subseteq> Q"
| "p \<sqsubseteq>\<^sub>h None \<longleftrightarrow> True"
| "None \<sqsubseteq>\<^sub>h q \<longleftrightarrow> q = None"

definition stran_local :: "('a \<times> heap \<Rightarrow> 'a pred option) \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "stran_local f R \<equiv> \<forall>s h h'. h \<bottom> h' \<and> (s, h') \<in> R \<longrightarrow> f (s, (h ++ h')) \<sqsubseteq>\<^sub>h (f (s, h)) *\<^sub>h (Some R)"

lemma subseteqE: "P \<subseteq> Q \<Longrightarrow> (\<forall>x. x \<in> P \<longrightarrow> x \<in> Q \<Longrightarrow> R) \<Longrightarrow> R"
by auto

lemma "local (ptran R) A \<Longrightarrow> stran_local (stran R) A"
  apply (auto simp: stran_local_def ptran_def local_def)
  apply (case_tac "stran R (s, h)")
  apply simp
  apply simp
  apply (erule_tac x=a in allE)
  apply (erule subseteqE)
  apply (erule_tac x="(s, h ++ h')" in allE)
  apply (subgoal_tac "(s, h ++ h') \<in> {aa. stran R aa \<sqsubseteq> a} * A")
  prefer 2
  apply (clarsimp simp: sep_def valid_subset_def)
  apply force
  apply auto
  apply (case_tac "stran R (s, h ++ h')")
  apply (simp add: stran_def)
  apply auto
  apply (erule_tac x="ab" in allE)
  apply (erule_tac x="b" in allE)
  apply (drule stranD) back
  apply assumption
  apply auto
done

lemma "stran_local (stran R) A \<Longrightarrow> local (ptran R) A"
  apply (auto simp: stran_local_def local_def sep_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=h1 in allE)
  apply (erule_tac x=h2 in allE)
  apply auto
  apply (case_tac "stran R (s, h1)")
  apply (clarsimp simp: ptran_def valid_subset_def)
  apply simp
  apply (case_tac "stran R (s, h1 ++ h2)")
  apply simp
  apply (auto simp: ptran_def valid_subset_def sep_def)
  apply (erule subseteqE) back
  apply (erule_tac x="(ab, b)" in allE)
  apply auto
done

text {* Safety and Framing properties on Relations *}

definition substate :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<preceq>" 50) where
  "h \<preceq> h' \<equiv> \<exists>dh. h \<bottom> dh \<and> h' = h ++ dh"

definition safe :: "'a state rel \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "safe R A \<equiv> \<forall>s h dh. (Some (s, h), None) \<notin> R \<and> h \<bottom> dh \<and> (s, dh) \<in> A \<longrightarrow> (Some (s, h ++ dh), None) \<notin> R"

definition frame :: "('a \<times> heap) option rel \<Rightarrow> 'a pred \<Rightarrow> bool" where
  "frame R A \<equiv> \<forall>so ho h dh s' h'. 
              (Some (so, ho), None) \<notin> R \<and>
              ho \<bottom> dh \<and> 
              h = ho ++ dh \<and> (so, dh) \<in> A \<and>
              (Some (so, h), Some (s', h')) \<in> R
              \<longrightarrow> (\<exists>ho' dh'. ho' \<bottom> dh' \<and> h' = ho' ++ dh' \<and> (Some (so, ho), Some (s', ho')) \<in> R \<and> (s', dh') \<in> A)" 

lemma "stran_local (stran R) A \<Longrightarrow> safe R A"
  apply (auto simp: stran_local_def safe_def)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=dh in allE)
  apply (case_tac "stran R (s, h)")
  apply auto
  apply (clarsimp simp: stran_def)+
done


lemma heap_cut: "h1 \<bottom> h2 \<Longrightarrow> h1 \<bottom> h3 \<Longrightarrow> h1 ++ h2 = h1 ++ h3 \<Longrightarrow> h2 = h3"
  apply (auto simp: ortho_def map_add_def fun_eq_iff)
  apply (erule_tac x=x in allE)
  apply (case_tac "h2 x")
  apply auto
  apply (case_tac "h3 x")
  apply auto
  apply (case_tac "h3 x")
  apply auto
done

  

lemma "stran_local (stran R) A \<Longrightarrow> frame R A"
  apply (auto simp: stran_local_def frame_def)
  apply (erule_tac x=so in allE)
  apply (erule_tac x=ho in allE)
  apply (erule_tac x=dh in allE)
  apply auto
  apply (case_tac "stran R (so, ho)")
  apply auto
  apply (simp add: stran_def)
  apply (case_tac "stran R (so, ho ++ dh)")
  apply (simp add: stran_def)
  apply auto
  apply (auto simp: sep_def)
  apply (frule stranD2) back
  apply assumption

  apply (erule subseteqE)
  apply (erule_tac x="(s', h')" in allE)
  apply auto
  apply (rule_tac x=h1 in exI)
  apply (rule_tac x=h2 in exI)
  apply clarsimp
  using stranD apply blast
done

lemma "safe R A \<Longrightarrow> frame R A \<Longrightarrow> stran_local (stran R) A"
  apply (auto simp: stran_local_def)
  apply (case_tac "stran R (s, h)")
  apply simp_all
  apply (case_tac "stran R (s, h ++ h')")
  apply simp_all
  apply (simp add: stran_none safe_def)
  apply (drule stran_some)
  apply (erule_tac x=s in allE)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=h' in allE)
  apply clarsimp

  apply (rule subrelI)
  apply (frule stranD) back
  apply assumption
  apply (simp add: frame_def)

  apply (erule_tac x=s in allE)
  apply (erule_tac x=h in allE)
  apply (erule_tac x=h' in allE)
  apply clarsimp
  apply (erule_tac x=x in allE)
  apply (erule_tac x=y in allE)
  apply clarsimp
  apply (frule stran_some)
  apply clarsimp
  apply (simp add: sep_def)
  apply (rule_tac x=ho' in exI)
  apply (rule_tac x=dh' in exI)                  
  apply auto
  apply (drule stranD2)
apply assumption
by auto

lemma "ptran R Q = {a. \<forall>b. if (Some a, None) \<notin> R then (Some a, Some b) \<in> R \<longrightarrow> b \<in> Q else False}"
  by (auto simp: ptran_def)

lemma "(\<exists>a. P \<longleftrightarrow> Q a) \<longleftrightarrow> (P \<longleftrightarrow> (\<exists>a. Q a))"
apply auto
oops

lemma "(Some a, None) \<notin> R \<Longrightarrow> a \<notin> ptran R Q \<longleftrightarrow> (\<exists>b. (Some a, Some b) \<in> R \<and> b \<notin> Q)"
by (auto simp: ptran_def)

end