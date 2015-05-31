theory VCG
  imports "$ISABELLE_HOME/src/HOL/Eisbach/Eisbach" Syntax
begin

declare assert_def [simp]

lemma subset_refl_tac: "\<forall>u. Q u \<subseteq> Q u"
  by auto

lemma hl_awhile_tac: "\<forall>u. P u \<subseteq> i u \<Longrightarrow> \<forall>u. -b \<inter> i u \<subseteq> Q u \<Longrightarrow> ht (<b> \<sqinter> i) x i \<Longrightarrow> ht P (awhile i b x) Q"
  by (force intro!: hl_awhile le_funI)

named_theorems hl_rules

declare hl_abort [hl_rules]
  and hl_skip [hl_rules]
  and hl_to_rel [hl_rules] 
  and hl_seq [hl_rules]
  and hl_cond [hl_rules]
  and hl_dyn2 [hl_rules]
  and hl_awhile_tac [hl_rules]




no_notation
  Set.image (infixr "`" 90)



end
