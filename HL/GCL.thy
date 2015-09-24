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
(*
          alt [({s. pcX s = last x + 1 \<and> pcY s = last y + 1}, skip)]"
*)
(*
syntax
  "_repeat_od_inv" :: "'a set \<Rightarrow> ('a set \<times> 'a rel) list \<Rightarrow> 'a rel" ("(0inv _ //repeat// /  _ //od)" [0, 0] 61)

translations
  "inv i repeat c" == "CONST ann_repeat_od c i"



record handshake_state =
  pcX :: nat
  pcY :: nat
  x :: bool
  y :: bool
  c :: bool



lemma "\<turnstile> \<lbrace> \<not> `x \<and> \<not> `y \<and> \<not> `c \<and> `pcX = 0 \<and> `pcY = 0 \<rbrace>
    inv {s.
      (pcX s \<le> 1 \<longrightarrow> \<not> x s) \<and>
      (pcY s \<le> 1 \<longrightarrow> \<not> c s) \<and>
      (pcX s \<le> 2 \<longrightarrow> \<not> y s \<or> c s) \<and>
      (pcX s \<ge> 3 \<longrightarrow> y s \<and> c s) \<and>
      (pcY s \<ge> 3 \<longrightarrow> x s) \<and>
      (pcX s \<in> {0,1,2,3,4}) \<and>
      (pcY s \<in> {0,1,2,3,4}) \<and>
      (pcX s = 2 \<and> pcY s = 2 \<longrightarrow> x s \<or> y s) \<and>
      (pcX s = 4 \<longrightarrow> x s) \<and>
      (pcY s = 4 \<longrightarrow> y s \<and> c s)
    }
    repeat [
      {s. pcX s = 0} \<mapsto> `y := False; `pcX := 1,
      {s. pcX s = 1} \<mapsto> `x := True; `pcX := 2,
      {s. pcX s = 2 \<and> y s} \<mapsto> `pcX := 3,
      {s. pcX s = 3} \<mapsto> `x := True; `pcX := 4, 

      {s. pcY s = 0} \<mapsto> `x := False; `pcY := 1,
      {s. pcY s = 1} \<mapsto> `y := True; `c := True; `pcY := 2,
      {s. pcY s = 2 \<and> x s} \<mapsto> `pcY := 3,
      {s. pcY s = 3} \<mapsto> `y := True; `c := True; `pcY := 4  
    ]
  \<lbrace> `pcX = 4 \<and> `pcY = 4 \<and> `x \<and> `y \<and> `c \<rbrace>"
apply (rule hoare_repeat_od_inv_tactic) 
apply force
apply force
apply auto
apply hoare
apply force+
done

hide_const pcX pcY x y c

record write_protocol =
  w :: bool
  r :: bool
  f :: int
  g :: int
  y :: int
  x :: int
  pcX :: nat
  pcY :: nat
  c :: nat

lemma "\<turnstile> \<lbrace> `w \<and> \<not>`r \<and> `f = 0 \<and> `g = 0 \<and> `y \<le> 0 \<and> `y < `x \<and> `pcX = 0 \<and> `pcY = 0 \<rbrace>
    inv {s. 
      (g s < f s \<or> w s) \<and> (y s \<le> f s) \<and> (g s \<le> f s) \<and>
      (pcX s = 0 \<or> pcX s = 1) \<and>
      (pcY s \<in> {0,1,2,3}) \<and>
      (pcX s = 0 \<longrightarrow> y s \<le> f s) \<and>
      (pcX s = 1 \<longrightarrow> g s < f s) \<and>
      (pcY s = 0 \<longrightarrow> y s < x s \<or> r s) \<and>
      (pcY s = 1 \<longrightarrow> g s < f s \<or> w s) \<and>
      (pcY s = 2 \<longrightarrow> y s < f s \<or> w s) \<and>
      (pcY s = 3 \<longrightarrow> y s < f s \<or> r s)
    }
    repeat [
      {s. pcX s = 0 \<and> c s > 0 } \<mapsto> `f := `f + 1; `w := False; `pcX := 1,
      {s. pcX s = 1 } \<mapsto> `g := `g + 1; `w := True; `pcX := 0; `c := `c - 1,

      {s. \<not> (x s \<le> y s) \<and> pcY s = 0 } \<mapsto> `pcY := 1,
      {s. pcY s = 1 } \<mapsto> `y := `g;  `pcY := 2,
      {s. pcY s = 2 } \<mapsto> `r := `w; `pcY := 3,
      {s. pcY s = 3 } \<mapsto>  `x := `f; `pcY := 0
    ]
  \<lbrace> `r \<and> `c = 0 \<and> `pcX = 0 \<and> `pcY = 0 \<rbrace>"
apply (rule hoare_repeat_od_inv_tactic) 
apply force
apply force
apply auto
apply hoare
apply force+
done


hide_const w r f g x y pcX pcY c

record mutual_incl_protocol =
  x :: int
  y :: int
  pcX :: nat
  pcY :: nat
  c :: bool

lemma "\<turnstile> \<lbrace> `x = 0 \<and> `y = 0 \<and> `c \<and> `pcX = 0 \<and> `pcY = 0 \<and> n > 0 \<rbrace>
    inv {s. 
      (x s \<le> y s) \<and> (y s \<le> x s + 1) \<and>
      (pcX s \<in> {0,1,2}) \<and>
      (pcY s \<in> {0,1,2}) \<and>
      (pcX s = 0 \<longrightarrow>  c s \<and> (x s = y s)) \<and>
      (pcX s = 1 \<longrightarrow> \<not>c s \<or> (x s + 1 = y s)) \<and>
      (pcX s = 2 \<longrightarrow> c s \<and> (x s + 1 = y s)) \<and>
      (pcY s = 0 \<longrightarrow> c s \<or> (x s = y s)) \<and>
      (pcY s = 1 \<longrightarrow> \<not>c s \<and> (x s = y s)) \<and>
      (pcY s = 2 \<longrightarrow> \<not>c s \<and> (x s + 1 = y s)) \<and>
      (\<not> c s \<and> (y s < n \<longrightarrow> c s) \<longrightarrow> pcX s = 1 \<longrightarrow> pcY s = 0 \<longrightarrow> x s \<noteq> y s)
    }
    repeat [
      {s. pcX s = 0 \<and> x s < n } \<mapsto> `c := False; `pcX := 1,
      {s. pcX s = 1 \<and> c s } \<mapsto> `pcX := 2,
      {s. pcX s = 2 } \<mapsto> `x := `x + 1; `pcX := 0,

      {s. pcY s = 0 \<and> y s < n \<and> \<not>c s } \<mapsto> `pcY := 1,
      {s. pcY s = 1 } \<mapsto> `y := `y + 1; `pcY := 2,
      {s. pcY s = 2 } \<mapsto> `c := True; `pcY := 0
    ]
  \<lbrace> `x = `y \<and> `pcX = 0 \<and> `pcY = 0 \<rbrace>"
apply (rule hoare_repeat_od_inv_tactic) 
apply force
apply force
apply auto
apply hoare
apply force+
done

hide_const x y pcX pcY c
*)
end