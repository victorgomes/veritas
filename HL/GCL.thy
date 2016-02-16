theory GCL
  imports VCG
begin

(* Semantics *)

primrec guards :: "('a set \<times> 'a rel) list \<Rightarrow> 'a set" ("\<G> _" [1000] 1000) where
  "guards [] = {}"
| "guards (x#xs) = fst x \<union> guards xs"

primrec gc :: "('a set \<times> 'a rel) list \<Rightarrow> 'a rel" ("\<C> _" [1000] 1000) where
  "gc [] = {}"
| "gc (x#xs) = (\<lfloor>fst x\<rfloor> O (snd x)) \<union> gc xs"

lemma guarded_restrictl_var [simp]: "\<lfloor>b \<union> c\<rfloor>; ((\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>c\<rfloor>;y)) = (\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>c\<rfloor>;y)"
  by (force simp: seq_def)

lemma guarded_restrictl: "\<lfloor>\<G> x\<rfloor>; y \<le> y"
  by (auto simp: guards_def seq_def)

lemma gc_induct [simp]: "\<lfloor>\<G> x\<rfloor>; \<C> x = \<C> x"
  by (induct x) (force simp: seq_def)+

definition alt :: "('a set \<times> 'a rel) list \<Rightarrow> 'a rel" where
  "alt x \<equiv> (\<C> x)"

lemma [simp]: "alt [(b, x), (-b, skip)] = cond b x skip"
  by (auto simp add: alt_def cond_def skip_def seq_def)

lemma [simp]: "alt [(b, x), (-b, y)] = cond b x y"
  by (force simp add: alt_def cond_def skip_def seq_def)

lemma [simp]: "alt [] = abort"
  by (auto simp: alt_def abort_def seq_def)

lemma [simp]: "alt [({}, x)] = abort"
  by (force simp: alt_def abort_def seq_def)

lemma [simp]: "alt [(UNIV, x)] = x"
  by (auto simp: alt_def skip_def seq_def)

definition repeat :: "('a set \<times> 'a rel) list \<Rightarrow> 'a rel" where
  "repeat x \<equiv> (\<C> x)\<^sup>*;\<lfloor>-(\<G> x)\<rfloor>"

lemma [simp]: "repeat [(b, x)] = cwhile b x"
  by (simp add: repeat_def cwhile_def seq_def)

lemma "repeat [(b, x), (-b, y)] = abort"
  by (auto simp: repeat_def abort_def seq_def)

lemma [simp]: "repeat [] = skip"
  by (auto simp: repeat_def seq_def skip_def)

lemma [simp]: "repeat [({}, x)] = skip"
  by (auto simp: repeat_def seq_def skip_def)

lemma [simp]: "repeat [(UNIV, x)] = abort"
  by (auto simp: repeat_def abort_def seq_def)

lemma [simp]: "repeat [(b, x), (c, y)] = cwhile (\<G> [(b, x), (c, y)]) (\<C> [(b, x), (c, y)])"
  apply (simp add: repeat_def cwhile_def seq_def) oops

lemma [simp]: "repeat [(b, x), (c, y)] = cwhile (b \<union> c) ((\<lfloor>b\<rfloor>;x) \<union> (\<lfloor>c\<rfloor>;y))"
  apply (unfold cwhile_def)
  apply (subst guarded_restrictl_var)
  apply (clarsimp simp: seq_def repeat_def)
done

lemma repeat_while_eq: "repeat x = cwhile (\<G> x) (\<C> x)"
  by (simp add: repeat_def cwhile_def)

(* Hoare logic *)

lemma hl_simple_alt: "ht p y q \<Longrightarrow> ht p x q \<Longrightarrow> ht p (x \<union> y) q"
  by (force simp: ht_def seq_def)

lemma hl_alt_base [hl_rules]: "ht (p \<inter> b) x q \<Longrightarrow> ht p (alt [(b, x)]) q"
  by (auto simp: ht_def seq_def alt_def)

lemma hl_alt_induct [hl_rules]: "ht p (alt xs) q \<Longrightarrow> ht (p \<inter> b) x q \<Longrightarrow> ht p (alt ((b, x) # xs)) q"
  by (auto simp: ht_def seq_def alt_def) force+

definition arepeat :: "'a set \<Rightarrow> ('a set \<times> 'a rel) list \<Rightarrow> 'a rel" where
  "arepeat i x \<equiv> repeat x" 

lemma hl_repeat: "ht ((\<G> x) \<inter> i) (\<C> x) i \<Longrightarrow> ht i (repeat x) (- (\<G> x) \<inter> i)"
  by (auto simp: repeat_while_eq intro: hl_while)

lemma hl_repeat_induct: "ht ((\<G> x) \<inter> i) (alt x) i \<Longrightarrow> ht i (repeat x) (- (\<G> x) \<inter> i)"
  by (auto simp: alt_def intro: hl_repeat)

lemma hl_arepeat:
  "p \<subseteq> i \<Longrightarrow> - (\<G> x) \<inter> i \<subseteq> q \<Longrightarrow> ht ((\<G> x) \<inter> i) (\<C> x) i \<Longrightarrow> ht p (arepeat i x) q"
  by (rule hl_classic) (auto simp: arepeat_def intro: hl_repeat)

lemma hl_arepeat_induct [hl_rules]:
  "p \<subseteq> i \<Longrightarrow> - (\<G> x) \<inter> i \<subseteq> q \<Longrightarrow> ht ((\<G> x) \<inter> i) (alt x) i \<Longrightarrow> ht p (arepeat i x) q"
  by (auto simp: alt_def intro: hl_arepeat)

lemma hl_gc [hl_rules]: "ht q' x q \<Longrightarrow> p \<inter> b \<subseteq> q' \<Longrightarrow> ht p (\<lfloor>b\<rfloor> O x) q"
  by (force simp: ht_def seq_def)

(* Concurrency by Non determinism *)

datatype 'a lprog = Atomic nat "'a rel"
  | Seq "'a lprog" "'a lprog"
  | If nat "'a set" "'a lprog" "'a lprog"
  | Loop nat "'a set" "'a lprog"
  | Await nat "'a set" "'a rel"

primrec first :: "'a lprog \<Rightarrow> nat" where
  "first (Atomic k a) = k"
| "first (Seq x y) = first x"
| "first (If k b x y) = k"
| "first (Loop k b x) = k"
| "first (Await k b a) = k"

primrec last :: "'a lprog \<Rightarrow> nat" where
  "last (Atomic k a) = k"
| "last (Seq x y) = last y"
| "last (If k b x y) = last y"
| "last (Loop k b x) = last x"
| "last (Await k b a) = k"

primrec T :: "'a lprog \<Rightarrow> nat \<Rightarrow> (nat, 'a) var \<Rightarrow> ('a set \<times> 'a rel) list" where
  "T (Atomic k R) c pc = [({s. val pc s = k}, R; assign (upd pc) (\<lambda>_. c))]"
| "T (Seq x y) c pc = T x (first y) pc @ T y c pc"
| "T (If k b x y) c pc = ({s. val pc s = k} \<inter> b, assign (upd pc) (\<lambda>_. first x))
    # ({s. val pc s = k} - b, assign (upd pc) (\<lambda>_. first y))
    # T x c pc @ T y c pc"
| "T (Loop k b x) c pc = ({s. val pc s = k} \<inter> b, assign (upd pc) (\<lambda>_. first x))
    # ({s. val pc s = k} - b, assign (upd pc) (\<lambda>_. c))
    # T x k pc"
| "T (Await k b R) c pc = [({s. val pc s = k} \<inter> b, R; assign (upd pc) (\<lambda>_. c))]"


primrec pc_set :: "nat \<Rightarrow> nat set" where
  "pc_set 0 = {0}"
| "pc_set (Suc m) = {Suc m} \<union> pc_set m"

declare Num.numeral_2_eq_2 [simp]
  Num.numeral_3_eq_3 [simp]

lemma [simp]: "4 = Suc (Suc (Suc (Suc 0)))"
   by arith

record pc_state =
  pcX :: nat
  pcY :: nat

definition par :: "'a pc_state_scheme lprog \<Rightarrow> 'a pc_state_scheme lprog \<Rightarrow> 'a pc_state_scheme rel" where
  "par x y \<equiv> (assign pcX_update (\<lambda>_. 0)); (assign pcY_update (\<lambda>_. 0));
          repeat ((T x (last x + 1) (pcX_update, pcX) @ T y (last y + 1) (pcY_update, pcY)))"

definition apar :: "'a pc_state_scheme set \<Rightarrow> 'a pc_state_scheme lprog \<Rightarrow> 'a pc_state_scheme lprog \<Rightarrow> 'a pc_state_scheme rel" where
  "apar i x y \<equiv> (assign pcX_update (\<lambda>_. 0)); (assign pcY_update (\<lambda>_. 0));
          arepeat ({s. pcX s \<in> pc_set (Suc (last x)) \<and> pcY s \<in> pc_set (Suc (last y))} \<inter> i) ((T x (last x + 1) (pcX_update, pcX) @ T y (last y + 1) (pcY_update, pcY)))"

lemma post_inv_par: "ht p (apar ({s. pcX s = last x + 1 \<and> pcY s = last y + 1 \<longrightarrow> s \<in> q}) x y) q \<Longrightarrow> ht p (par x y) q"
  by (auto simp: apar_def arepeat_def par_def)

lemma post_inv_apar: "ht p (apar (i \<inter> {s. pcX s = last x + 1 \<and> pcY s = last y + 1 \<longrightarrow> s \<in> q}) x y) q \<Longrightarrow> ht p (apar i x y) q"
  by (auto simp: apar_def arepeat_def)

method transform uses simp = 
  ((rule post_inv_par | rule post_inv_apar), simp add: apar_def par_def)
end