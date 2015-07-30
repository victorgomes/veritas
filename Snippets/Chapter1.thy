theory Chapter1
  imports Main
begin


text_raw {*\DefineSnippet{class:dioid}{*}
class dioid = semiring +
  assumes add_idem [simp]: "x + x = x"
text_raw {*}%EndSnippet*}

context dioid begin

no_notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
no_notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

no_notation less  ("(_/ < _)" [51, 51] 50)

text_raw {*\DefineSnippet{def:leq}{*}
definition leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<le>" 50) where
  "x \<le> y \<equiv> x + y = y"
text_raw {*}%EndSnippet*}

text_raw {*\DefineSnippet{def:le}{*}
definition le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "<" 50) where
  "x < y \<equiv> x \<le> y \<and> x \<noteq> y"
text_raw {*}%EndSnippet*}

sublocale order "op \<le>" "op <"
apply default
 text {*
 \DefineSnippet{goals:order}{
    @{goals [display]}
 }%EndSnippet
 *}
 text {*
 \DefineSnippet{subgoals:order}{
    @{subgoals [display]}
 }%EndSnippet
 *}
oops

text_raw {*\DefineSnippet{sl:order}{*}
sublocale order "op \<le>" "op <"
proof
  fix x y
  show "(x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)"
    by (auto simp: le_def leq_def add_commute)
next
  fix x
  show "x \<le> x"
    by (simp add: leq_def)
next
  fix x y z
  assume "x \<le> y" and "y \<le> z"
  thus "x \<le> z"
    by (metis add_assoc leq_def)
next
  fix x y
  assume "x \<le> y" and "y \<le> x"
  thus "x = y"
    by (auto simp: leq_def add_commute)
qed
text_raw {*}%EndSnippet*}

no_notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
no_notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

text_raw {*\DefineSnippet{sl:sup}{*}
sublocale semilattice_sup "op +" "op \<le>" "op <" 
proof
  fix x y
  show "x \<le> x + y"
    by (metis leq_def add_assoc add_idem)
  show "y \<le> x + y"
    by (metis leq_def add_idem add.left_commute)
next
  fix x y z
  assume "y \<le> x" and "z \<le> x"
  thus "y + z \<le> x"
    by (simp add: add_assoc leq_def)
qed
text_raw {*}%EndSnippet*}

lemma my_thm : "x + x = x + (x + x)"
  by simp

lemma my_thm2 : "x + x = x + (x + x)"
proof -
  have "x + (x + x) = x + x"
    by simp
  also have "... = x"
    by simp
  finally show ?thesis
    by simp
qed

 text {*
 \DefineSnippet{mythm1}{
    @{prf [display] my_thm}
 }%EndSnippet
 *}

 text {*
 \DefineSnippet{mythm2}{
    @{prf [display] my_thm2}
 }%EndSnippet
 *}


end
end