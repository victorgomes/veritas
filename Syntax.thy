theory Syntax
  imports Hoare
begin

(* Syntax of the While language *)

syntax
  "_quote" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" ("`_" [1000] 1000) 
  "_subst" :: "'a set \<Rightarrow> 'b \<Rightarrow> idt \<Rightarrow> 'a set" ("_[_'/`_]" [1000] 999)
  "_assign" :: "idt \<Rightarrow> 'b \<Rightarrow> 'a rel" ("(`_ :=/ _)" [0, 65] 62)
  "_cond" :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("(0if _ then//  _//else//  _//fi)" [0,0,0] 62)
  "_cond_skip" :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("(0if _//then _//fi)" [0,0] 62)
  "_while" :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("(0while  _//do  _//od)" [0, 0] 62)
  "_awhile" :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("(0while _//inv  _//do _//od)" [0, 0, 0] 62)

ML {*
fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
    | quote_tr ts = raise TERM ("quote_tr", ts)
*}

parse_translation {*
  [(@{syntax_const "_quote"}, K quote_tr)]
*}

translations
  "p [t/`u]" == "CONST Collect \<guillemotleft> `(_update_name u (\<lambda>_. t)) \<in> p \<guillemotright>"
  "`u := t" => "CONST to_rel \<guillemotleft>`(_update_name u (\<lambda>_. t))\<guillemotright>"
  "if b then x else y fi" => "CONST cond (CONST Collect \<guillemotleft>b\<guillemotright>) x y"
  "if b then x fi" == "if b then x else skip fi"
  "while b inv i do x od" => "CONST awhile (CONST Collect \<guillemotleft>i\<guillemotright>) (CONST Collect \<guillemotleft>b\<guillemotright>) x"
  
  
(* Syntax of Hoare logic *)

syntax
  "_ht" :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> bool" ("\<turnstile> \<lbrace> _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)
translations
  "\<turnstile> \<lbrace> p \<rbrace> x \<lbrace> q \<rbrace>" == "CONST ht (%_. CONST Collect \<guillemotleft>p\<guillemotright>) x (%_. CONST Collect \<guillemotleft>q\<guillemotright>)"
  
record test = 
  i :: nat
  j :: nat
  
lemma "\<turnstile> \<lbrace> True \<rbrace> block (\<lambda>s. s\<lparr>i := j s\<rparr>) {} (\<lambda>s t. t\<lparr> i := i s\<rparr>) (\<lambda>s t. skip) \<lbrace> True \<rbrace>"
end
