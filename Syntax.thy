theory Syntax
  imports Hoare Array
begin

text {* 
  Programs are modelled as relations using a while programming language:
  S ::= abort 
      | skip 
      | \<langle>f\<rangle>                       (f is a state transformer)
      | \<lceil>g\<rceil>                       (g is function from state to relation)

      | x := t                    (assignment)
      | S; S' 
      | if b then S else S' fi 
      | while b do S od 

      | local x := t in S end   (local variable)
      | rec F in S end          (recursive procedures)
      | begin S end             (procedures)

      | x := call R             (assignment with a call to a function)

  R ::= begin S return y end    (functions)
*}
                                                                                                
syntax
  "_quote"      :: "'a \<Rightarrow> ('s \<Rightarrow> 'a)"                       ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote"  :: "('s \<Rightarrow> 'a) \<Rightarrow> 's"                       ("`_" [100] 1000) 

  "_subst"      :: "'s set \<Rightarrow> 'v \<Rightarrow> idt \<Rightarrow> 's set"          ("_[_'/`_]" [1000] 999)
  "_assign"     :: "idt \<Rightarrow> 'v \<Rightarrow> 's rel"                    ("(`_ :=/ _)" [0, 65] 62)
  "_asgn_array" :: "idt \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> 's rel"             ("(`_ (_) :=/ _)" [0, 0, 65] 62)

  "_cond"       :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel"   ("(0if _ then//  _//else//  _//fi)" [0,0,0] 62)
  "_cond_skip"  :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel"             ("(0if _//then _//fi)" [0,0] 62)
  "_while"      :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel"             ("(0while  _//do  _//od)" [0, 0] 62)
  "_awhile"     :: "'s set \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel"   ("(0while _//inv _//do// _//od)" [0, 0, 0] 62)

  "_for"        :: "idt \<Rightarrow> 'v \<Rightarrow> idt \<Rightarrow> 's rel \<Rightarrow> 's rel"    ("(0for `_ := _ to `_ do//  _//od)" [0, 65, 50, 0] 62)
  "_afor"        :: "idt \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel" ("(0for `_ := _ to _//inv _ //do  _//od)" [0, 0] 62)

  "_apre"       :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel"               ("\<lbrace> _ \<rbrace>// _" [0, 62] 62)
  "_apre_aux"   :: "'v \<Rightarrow> ('v \<Rightarrow> 's set) \<Rightarrow> 's rel \<Rightarrow> 's rel" ("\<lbrace> _ . _ \<rbrace> _" [0, 0, 62] 62)

  "_proc"       :: "'s rel \<Rightarrow> 's rel"                        ("begin// _//end")
  "_fun"        :: "'s rel \<Rightarrow> 'a \<Rightarrow> ('s rel \<times> 'a)"           ("begin// _// return `_//end")
  "_local"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a rel \<Rightarrow> 'a rel"           ("(0local `_ := _ in// _//end)" [0, 65, 55] 62)
  "_call"       :: "idt \<Rightarrow> ('s rel \<times> 'a) \<Rightarrow> 's rel"          ("`_ := call (0_) " [0, 65] 62)

  "_rec"        :: "'s rel \<Rightarrow> 's rel \<Rightarrow> 's rel"               ("(0rec _ in// _//end)" [0, 55] 62)

  "_ht"         :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's set \<Rightarrow> bool"       ("\<turnstile> \<lbrace> _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)
  "_ht_aux"     :: "'v \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's set \<Rightarrow> bool" ("\<turnstile> \<lbrace> _ . _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)



ML {*
  fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts)
*}

parse_translation {*
  [(@{syntax_const "_quote"}, K quote_tr)]
*}

translations
  "p [t/`u]"                == "_update_name u (\<lambda>_. t) \<in> p"
  "`u := t"                 == "CONST assign (_update_name u) \<guillemotleft>t\<guillemotright>"
  "`a(i) := t"              => "CONST assign (_update_name a) \<guillemotleft>(CONST fun_upd (`a) i t)\<guillemotright>"

  "if b then x else y fi"   => "CONST cond (CONST Collect \<guillemotleft>b\<guillemotright>) x y"
  "if b then x fi"          == "if b then x else skip fi"
  "while b do x od"         == "CONST cwhile (CONST Collect \<guillemotleft>b\<guillemotright>) x"
  "while b inv i do x od"   == "CONST awhile (CONST Collect \<guillemotleft>i\<guillemotright>) (CONST Collect \<guillemotleft>b\<guillemotright>) x"

  "for `i := n to `m do x od"=> "CONST cfor (CONST Pair (_update_name i) i) \<guillemotleft>n\<guillemotright> (CONST Pair (_update_name m) m) x"

  "\<lbrace> p \<rbrace> x"                 == "CONST apre (CONST Collect \<guillemotleft>p\<guillemotright>) x"
  "\<lbrace> u . p \<rbrace> x"             => "CONST apre (CONST Collect \<guillemotleft>p\<guillemotright>) x"

  "begin x end"             => "x"
  "begin x return `z end"   => "CONST fun_block x (CONST Pair (_update_name z) z)"
  "local `u := t in x end"  => "CONST loc_block (CONST Pair (_update_name u) u) \<guillemotleft>t\<guillemotright> x"
  "`z := call R"            => "CONST fun_call (_update_name z) R"

  "(rec f in x end) z"      => "CONST lfp (%f z. x z)"

  "\<turnstile> \<lbrace> p \<rbrace> x \<lbrace> q \<rbrace>"         => "CONST ht (CONST Collect \<guillemotleft>p\<guillemotright>) x (CONST Collect \<guillemotleft>q\<guillemotright>)"
  "\<turnstile> \<lbrace> u . p \<rbrace> x \<lbrace> q \<rbrace>"     => "\<forall>u. CONST ht (CONST Collect \<guillemotleft>p\<guillemotright>) x (CONST Collect \<guillemotleft>q\<guillemotright>)"
  

syntax ("" output)
  "_assert"    :: "'s \<Rightarrow> 's set"                             ("[_]" [0] 1000)
  "_seq"       :: "'s rel \<Rightarrow> 's rel \<Rightarrow> 'a rel"               ("_;// _" [59, 59] 60 )
  "_ht"        :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's set \<Rightarrow> bool"       ("\<turnstile> \<lbrace> _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)

ML {*
  fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | quote_tr' _ _ = raise Match;

  val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_assert"});

  fun subst_tr' (p :: x :: ts) = (quote_tr' (Syntax.const @{syntax_const "_subst"} $ p) ts) $ Syntax_Trans.update_name_tr' x
    | subst_tr' _ = raise Match;

  fun assign_tr' (x :: ts) =  quote_tr' (Syntax.const @{syntax_const "_assign"} $ Syntax_Trans.update_name_tr' x) ts
    | assign_tr' _ = raise Match;

  fun local_tr' [(Const _ $ _ $ x), t, y] = (quote_tr' (Syntax.const @{syntax_const "_local"} $ x) [t]) $ y
    | local_tr' _ = raise Match;

  fun call_tr' [z, f] = Syntax.const @{syntax_const "_call"} $ Syntax_Trans.update_name_tr' z $ f
    | call_tr' _ = raise Match;

  fun fun_tr' [x, (Const _ $ _ $ z)] = Syntax.const @{syntax_const "_fun"} $ x $ z
    | fun_tr' _ = raise Match;

  fun for_tr' [(Const _ $ _ $ i), n, (Const _ $ _ $ m), x] = (quote_tr' (Syntax.const @{syntax_const "_for"} $ i) [n]) $ m $ x
    | for_tr' _ = raise Match;

  fun print_tr' name [x, y, z] = Syntax.const name $ x $ y $ z
    | print_tr' name [x, y] = Syntax.const name $ x $ y
    | print_tr' name [x] = Syntax.const name $ x
    | print_tr' _ _ = raise Match;

*}

print_translation {*
  [
  (@{const_syntax Collect}, K assert_tr'),
  (@{const_syntax assign}, K assign_tr'),
  (@{const_syntax subst}, K subst_tr'),

  (@{const_syntax seq}, K (print_tr' @{syntax_const "_seq"})),
  (@{const_syntax cond}, K (print_tr' @{syntax_const "_cond"})),
  (@{const_syntax awhile}, K (print_tr' @{syntax_const "_awhile"})),

  (@{const_syntax apre}, K (print_tr' @{syntax_const "_apre"})),

  (@{const_syntax loc_block}, K local_tr'),
  (@{const_syntax cfor}, K for_tr'),
  (@{const_syntax fun_call}, K call_tr'),
  (@{const_syntax fun_block}, K fun_tr'),

  (@{const_syntax ht}, K (print_tr' @{syntax_const "_ht"}))
  ]
*}

(*

  "_local2"     :: "idt \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("local `_ in _ end" [0, 55] 62)
  "_locals"     :: "idts \<Rightarrow> 's rel \<Rightarrow> 's rel" ("locals _ in _ end" [0, 55] 62)

  "while b inv u. i do x od" => "CONST awhile (%u. CONST Collect \<guillemotleft>i\<guillemotright>) (CONST Collect \<guillemotleft>b\<guillemotright>) x"
  "local `u in x end" => "CONST block (CONST id) x (\<guillemotleft>2 \<guillemotleft>`(_update_name u (\<lambda>_. `2 u))\<guillemotright> \<guillemotright>) (\<guillemotleft>2 \<guillemotleft> skip \<guillemotright>\<guillemotright>)"

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

*)

end
