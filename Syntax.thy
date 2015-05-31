theory Syntax
  imports Hoare
begin

(* Syntax of the While language *)

syntax
  "_quote" :: "'a \<Rightarrow> ('s \<Rightarrow> 'a)" ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('s \<Rightarrow> 'a) \<Rightarrow> 's" ("`_" [1000] 1000) 
  "_quote2" :: "'a \<Rightarrow> ('s \<Rightarrow> 'a)" ("(\<guillemotleft>2_\<guillemotright>)" [0] 1000)
  "_antiquote2" :: "('s \<Rightarrow> 'a) \<Rightarrow> 's" ("`2_" [1000] 1000)
  "_subst" :: "'s set \<Rightarrow> 'a \<Rightarrow> idt \<Rightarrow> 's set" ("_[_'/`_]" [1000] 999)
  "_assign" :: "idt \<Rightarrow> 'a \<Rightarrow> 's rel" ("(`_ :=/ _)" [0, 65] 62)
  "_cond" :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0if _ then//  _//else//  _//fi)" [0,0,0] 62)
  "_cond_skip" :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0if _//then _//fi)" [0,0] 62)
  "_while" :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0while  _//do  _//od)" [0, 0] 62)
  "_awhile" :: "'s set \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0while _//inv  _//do _//od)" [0, 0, 0] 62)
  "_awhile_aux" :: "'s set \<Rightarrow> 'v \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0while _//inv _. _//do _//od)" [0, 0, 0] 62)
  "_local" :: "idt \<Rightarrow> 'b \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("local `_ := _ in _ end" [0, 65, 55] 62)
  "_local2" :: "idt \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("local `_ in _ end" [0, 55] 62)
  "_locals" :: "idts \<Rightarrow> 's rel \<Rightarrow> 's rel" ("locals _ in _ end" [0, 55] 62)
  "_proc" :: "idt \<Rightarrow> 'a rel \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a rel" ("`_ := call _ `_ : _" [0, 65, 55] 62)
  "_rec" :: "'s rel \<Rightarrow> 's rel \<Rightarrow> 's rel" ("rec _ in _ end" [0, 55] 62)
  "_apre" :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel" ("\<lbrace> _ \<rbrace> _" [0, 62] 62)
  "_apre_aux" :: "'v \<Rightarrow> ('v \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> 's rel" ("\<lbrace> _ . _ \<rbrace> _" [0, 0, 62] 62)
  "_call" :: "idt \<Rightarrow> ('s rel \<times> ('s \<Rightarrow> 'v)) \<Rightarrow> 's rel" ("`_ := call _ " [0, 65] 62)

ML {*
fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
    | quote_tr ts = raise TERM ("quote_tr", ts)
fun quote2_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote2"} t
    | quote2_tr ts = raise TERM ("quote2_tr", ts)
*}

parse_translation {*
  [(@{syntax_const "_quote"}, K quote_tr), (@{syntax_const "_quote2"}, K quote2_tr)]
*}

abbreviation id2 :: "'s \<Rightarrow> 's \<Rightarrow> 's" where
  "id2 \<equiv> \<lambda>s t. s"

translations
  "p [t/`u]" == "CONST Collect \<guillemotleft> `(_update_name u (\<lambda>_. t)) \<in> p \<guillemotright>"
  "`u := t" => "CONST to_rel \<guillemotleft>`(_update_name u (\<lambda>_. t))\<guillemotright>"
  "if b then x else y fi" => "CONST cond (CONST Collect \<guillemotleft>b\<guillemotright>) x y"
  "if b then x fi" == "if b then x else skip fi"
  "while b inv i do x od" => "CONST awhile (CONST Collect \<guillemotleft>i\<guillemotright>) (CONST Collect \<guillemotleft>b\<guillemotright>) x"
  "while b inv u. i do x od" => "CONST awhile (%u. CONST Collect \<guillemotleft>i\<guillemotright>) (CONST Collect \<guillemotleft>b\<guillemotright>) x"
  "local `u := t in x end" => "CONST block (CONST id) (`u := t; x) (\<guillemotleft>2 \<guillemotleft>`(_update_name u (\<lambda>_. `2 u))\<guillemotright> \<guillemotright>) (\<guillemotleft>2 \<guillemotleft> skip \<guillemotright>\<guillemotright>)"
  "local `u in x end" => "CONST block (CONST id) x (\<guillemotleft>2 \<guillemotleft>`(_update_name u (\<lambda>_. `2 u))\<guillemotright> \<guillemotright>) (\<guillemotleft>2 \<guillemotleft> skip \<guillemotright>\<guillemotright>)"
  "\<lbrace> p \<rbrace> x" => "CONST apre (CONST Collect \<guillemotleft>p\<guillemotright>) x"
  "\<lbrace> u . p \<rbrace> x" => "CONST apre (CONST Collect \<guillemotleft>p\<guillemotright>) x"
  "rec f in x end" => "CONST lfp (%f. x)"
  " `z := call R" => "CONST block (CONST id) (CONST fst R) (CONST id2) (\<guillemotleft> \<guillemotleft>2 `z := `2 (CONST snd R) \<guillemotright>\<guillemotright>)"
  (*"`u := call R `v : t" => "CONST block (\<guillemotleft>`(_update_name v (\<lambda>_. t))\<guillemotright>) R (\<guillemotleft> \<guillemotleft>2 \<guillemotleft>`(_update_name v (\<lambda>_. `2 v))\<guillemotright> \<guillemotright> \<guillemotright>) (\<guillemotleft>2 \<guillemotleft> `u := `2 v \<guillemotright>\<guillemotright>)"
*)(* Syntax of Hoare logic *)

ML {*

fun update_name_tr (Free (x, T) :: ts) = list_comb (Free (suffix "_update" x, T), ts)
  | update_name_tr (Const (x, T) :: ts) = list_comb (Const (suffix "_update" x, T), ts)
  | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
      if Term_Position.is_position ty then list_comb (c $ update_name_tr [t] $ ty, ts)
      else
        list_comb (c $ update_name_tr [t] $
          (Lexicon.fun_type $
            (Lexicon.fun_type $ Lexicon.dummy_type $ ty) $ Lexicon.dummy_type), ts)
  | update_name_tr ts = raise TERM ("update_name_tr", ts);

fun vars_tr (Const (@{syntax_const "_idts"}, _) $ idt $ vars) = idt :: vars_tr vars
  | vars_tr t = [t];

fun local_tr [v, x] = Syntax.const @{const_syntax "block"} $ (Syntax.const @{const_syntax "id"})
                  $ x
                  $ quote2_tr [quote_tr [Syntax.const @{syntax_const "_antiquote"} $ update_name_tr [v, absdummy dummyT (Syntax.const @{syntax_const "_antiquote2"} $ v)]]]
                  $ quote2_tr [quote_tr [Syntax.const @{const_syntax "skip"}]]
 | local_tr ts = raise TERM ("local_tr", ts)

fun locals_tr' [] x = x
  | locals_tr' (v::vs) x = local_tr [v, locals_tr' vs x]

fun locals_tr [vars, x] =
    let val vs = vars_tr vars
    in locals_tr' vs x
    end
    | locals_tr ts = raise TERM ("locals_tr", ts)
*}

parse_translation {*
  [(@{syntax_const "_locals"}, K locals_tr)]
*}


syntax
  "_ht" :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's set \<Rightarrow> bool" ("\<turnstile> \<lbrace> _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)
  "_ht_aux" :: "'v \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's set \<Rightarrow> bool" ("\<turnstile> \<lbrace> _ . _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)

translations
  "\<turnstile> \<lbrace> p \<rbrace> x \<lbrace> q \<rbrace>" == "CONST ht (CONST Collect \<guillemotleft>p\<guillemotright>) x (CONST Collect \<guillemotleft>q\<guillemotright>)"
  "\<turnstile> \<lbrace> u . p \<rbrace> x \<lbrace> q \<rbrace>" => "\<forall>u. CONST ht (CONST Collect \<guillemotleft>p\<guillemotright>) x (CONST Collect \<guillemotleft>q\<guillemotright>)"



end
