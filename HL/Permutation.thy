theory Permutation
  imports Main
begin

(* Some theorems about permutation were copied from HOL/HOL-NSA-Examples/Permutation *)
inductive perm :: "'a list => 'a list => bool"  ("_ <~~> _"  [50, 50] 50) 
where
  Nil [intro!]: "[] <~~> []"
| swap [intro!]: "y # x # l <~~> x # y # l"
| Cons [intro!]: "xs <~~> ys ==> z # xs <~~> z # ys"
| trans [intro]: "xs <~~> ys ==> ys <~~> zs ==> xs <~~> zs"

lemma perm_refl [iff]: "l <~~> l"
  by (induct l) auto

lemma [simp]: "sorted (take (Suc 0) A)"
  by (induct A) auto

lemma xperm_empty_imp: "[] <~~> ys ==> ys = []"
  by (induct xs == "[]::'a list" ys pred: perm) simp_all

lemma perm_length: "xs <~~> ys ==> length xs = length ys"
  by (induct pred: perm) simp_all

lemma perm_sym: "xs <~~> ys ==> ys <~~> xs"
  by (induct pred: perm) auto

lemma perm_append_Cons: "a # xs @ ys <~~> xs @ a # ys"
  by (induct xs) auto

lemma perm_append_swap: "xs @ ys <~~> ys @ xs"
  apply (induct xs)
    apply simp_all
  apply (blast intro: perm_append_Cons)
  done

lemma perm_append_single: "a # xs <~~> xs @ [a]"
  by (rule perm.trans [OF _ perm_append_swap]) simp

lemma perm_rev: "rev xs <~~> xs"
  apply (induct xs)
   apply simp_all
  apply (blast intro!: perm_append_single intro: perm_sym)
  done

lemma perm_append1: "xs <~~> ys ==> l @ xs <~~> l @ ys"
  by (induct l) auto

lemma perm_append2: "xs <~~> ys ==> xs @ l <~~> ys @ l"
  by (blast intro!: perm_append_swap perm_append1)

lemma perm_swap: "xs @ y # x # ys <~~> xs @ x # y # ys"
  apply (induct xs)
  by auto

end
