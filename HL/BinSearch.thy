theory BinSearch
  imports Syntax
begin

hide_const first last sorted 

definition sorted :: "'a :: linorder array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "sorted a i j \<equiv> \<forall>x y. i \<le> x \<and> x \<le> y \<and> y \<le> j \<longrightarrow> a<x> \<le> a<y>"

lemma sorted_section1: "sorted a f l \<Longrightarrow> f \<le> m \<Longrightarrow> m < l \<Longrightarrow> a<m> < v \<Longrightarrow> (\<exists>x \<in> \<lbrace>Suc m, l\<rbrace>. a<x> = v) \<longleftrightarrow> (\<exists>x \<in>\<lbrace>f, l\<rbrace>. a<x> = v)"
  apply (auto simp: sorted_def interval_def)
  apply (rule_tac x=x in exI)
  apply clarsimp
  apply (metis leD less_imp_le_nat not_less_eq_eq)
done

lemma sorted_section2: "sorted a f l \<Longrightarrow> f \<le> m \<Longrightarrow> m \<le> l \<Longrightarrow> v \<le> a<m> \<Longrightarrow> (\<exists>x \<in> \<lbrace>f, m\<rbrace>. a<x> = v) \<longleftrightarrow> (\<exists>x \<in> \<lbrace>f, l\<rbrace>. a<x> = v)"
  apply (auto simp: sorted_def interval_def)
  by (meson eq_iff nat_le_linear)

record state =
  first :: nat
  mid :: nat
  last :: nat

abbreviation f :: "nat \<times> nat \<Rightarrow> nat" where "f \<equiv> fst"
abbreviation l :: "nat \<times> nat \<Rightarrow> nat" where "l \<equiv> snd"

lemma "\<forall>u. \<turnstile> \<lbrace> (f u = `first \<and> l u = `last \<and> `first \<le> `last \<and> sorted a `first `last) \<rbrace>
  rec BinSearch in 
    `mid := (`first + `last) div 2;
    if `first \<noteq> `last then
      if a<`mid> < v then
        `first := `mid + 1;
        \<lbrace> u. (f u + l u) div 2 + 1 = `first \<and> l u = `last \<and> `first \<le> `last \<and> sorted a `first `last
          \<and> sorted a (f u) (l u) \<and> a<(f u + l u) div 2> < v \<rbrace>
        BinSearch
        \<lbrace> (f u + l u) div 2 + 1 \<le> `mid \<and> `mid \<le> l u \<and> (a<`mid> = v \<longleftrightarrow> (\<exists>x \<in> \<lbrace>(f u + l u) div 2 + 1, l u\<rbrace>. a<x> = v))
          \<and> sorted a (f u) (l u) \<and> a<(f u + l u) div 2> < v \<rbrace>
      else 
        if a<`mid> > v then
          `last := `mid;
          \<lbrace> u. (f u = `first \<and> (f u + l u) div 2 = `last \<and> `first \<le> `last \<and> sorted a `first `last 
            \<and> sorted a (f u) (l u) \<and> v < a<(f u + l u) div 2> ) \<rbrace>
          BinSearch
          \<lbrace> f u \<le> `mid \<and> `mid \<le> (f u + l u) div 2 \<and> (a<`mid> = v \<longleftrightarrow> (\<exists>x \<in> \<lbrace>f u, (f u + l u) div 2\<rbrace>. a<x> = v))
            \<and> sorted a (f u) (l u) \<and> v < a<(f u + l u) div 2> \<rbrace>
        fi
      fi
    fi
    end
  \<lbrace> f u \<le> `mid \<and> `mid \<le> l u \<and> (a<`mid> = v \<longleftrightarrow> (\<exists>x \<in> \<lbrace>f u, l u\<rbrace>. a<x> = v)) \<rbrace>"
apply hoare
apply force
apply clarsimp
apply (rule conjI)
apply force
apply (rule sorted_section1)
apply simp+
apply force
apply clarsimp
apply (rule conjI)
apply simp
apply (rule sorted_section2)
apply simp+
apply clarsimp
apply (auto simp: sorted_def interval_def)
apply (rule_tac x="(first xa + last xa) div 2" in exI)
apply force
done

end
