theory Syntax
  imports Refinement
begin

no_notation Set.image (infixr "`" 90)

text {* 
  S ::= abort 
      | skip 
      | cons e                     (allocation)
      | `x := t                     (assignment)
      | `x := @t                    (lookup)
      | @e := t                    (mutation)
      | dispose e                  (disposal)
      | S; S' 
      | if b then S else S' fi 
      | while b do S od 
*}

syntax
  "_quote"      :: "'a \<Rightarrow> ('s \<Rightarrow> 'a)"                       ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote"  :: "('s \<Rightarrow> 'a) \<Rightarrow> 's"                       ("`_" [1000] 1000)
  "_assert"     :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<times> 'h) set" 

  "_emp_assert" :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<times> 'h) set"         ("\<langle>_\<rangle>" [0] 100)

  "_subst"      :: "'s set \<Rightarrow> 'v \<Rightarrow> idt \<Rightarrow> 's set"          ("_[_'/`_]" [1000] 999)
  "_assign"     :: "idt \<Rightarrow> 'v \<Rightarrow> 's rel"                    ("(`_ :=/ _)" [0, 65] 62)

  "_alloc"      :: "idt \<Rightarrow> 'v \<Rightarrow> 's ptran"                  ("(`_ :=/ cons _)" [0, 65] 62)
  "_lookup"     :: "idt \<Rightarrow> 'v \<Rightarrow> 's ptran"                  ("(`_ :=/ @_)" [0, 65] 62)
  "_mutation"   :: "'v \<Rightarrow> 'v \<Rightarrow> 's ptran"                   ("(@_ :=/ _)" [0, 65] 62)
  "_disposal"   :: "'v \<Rightarrow> 's ptran"                         ("dispose _" [65] 62)


  "_cond"       :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel \<Rightarrow> 's rel"   ("(0if _ then//  _//else//  _//fi)" [0,0,0] 62)
  "_cond_skip"  :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel"             ("(0if _//then _//fi)" [0,0] 62)
  "_while"      :: "'s set \<Rightarrow> 's rel \<Rightarrow> 's rel"             ("(0while  _//do  _//od)" [0, 0] 62)
  "_awhile"     :: "'s set \<Rightarrow> 's set \<Rightarrow> 's rel \<Rightarrow> 's rel"   ("(0while _//inv _//do// _//od)" [0, 0, 0] 62)

  "_apre"       :: "('s \<times> heap) set \<Rightarrow> 's ptran \<Rightarrow> 's ptran"               ("\<lbrace> _ \<rbrace>// _" [0, 62] 62)
  "_apost"      :: "('s \<times> heap) set \<Rightarrow> 's ptran \<Rightarrow> 's ptran"               ("_ // \<lbrace> _ \<rbrace>" [62, 0] 62)


  "_ht"         :: "'s ptran \<Rightarrow> 's ptran \<Rightarrow> 's ptran \<Rightarrow> bool" ("\<turnstile> \<lbrace> _ \<rbrace>// _// \<lbrace> _ \<rbrace>" [0, 55, 0] 50)
  "_Spec"       :: "bool \<Rightarrow> bool \<Rightarrow> 'a"                       ("\<lbrakk>_,_\<rbrakk>" [10, 10] 100)

ML {*

  fun antiquote_tr name =
    let
      fun tr i ((t as Const (c, _)) $ u) =
            if c = name then tr i u $ Bound i
            else tr i t $ tr i u
        | tr i (t $ u) = tr i t $ tr i u
        | tr i (Abs (x, T, t)) = Abs (x, T, tr (i + 1) t)
        | tr _ a = a;
    in tr 0 end;
  
  fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts)

*}

parse_translation {*
  [(@{syntax_const "_quote"}, K quote_tr)]
*}

abbreviation (input) heapify :: "'a set \<Rightarrow> ('a \<times> 'b) set" where
  "heapify B \<equiv> {(s, h). s \<in> B}"

translations
  "_assert b"               => "CONST heapify (CONST Collect (\<guillemotleft>b\<guillemotright>))"
  "p [t/`u]"                == "_update_name u (\<lambda>_. t) \<in> p"

  "\<langle>P\<rangle>"                     => "CONST store_pred (CONST Collect (\<guillemotleft>P\<guillemotright>))"

  "`u := t"                 == "CONST assign (_update_name u) (_quote t)"
  "`u := cons t"            == "CONST alloc (_update_name u) (_quote t)"
  "`u := @t"                == "CONST lookup (_update_name u) (_quote t)"
  "@e := t"                 == "CONST mutation (_quote e) (_quote t)"
  "dispose t"               == "CONST disposal (_quote t)"

  "if b then x else y fi"   => "CONST cond (_assert b) x y"
  "if b then x fi"          == "if b then x else (CONST skip) fi"
  "while b do x od"         == "CONST cwhile (_assert b) x"
  "while b inv i do x od"   == "CONST awhile i (_assert b) x"

  "\<lbrakk>p, q\<rbrakk>"                   == "CONST spec p q" 
  "\<turnstile> \<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>"         == "CONST ht P x Q"

  "\<lbrace> P \<rbrace> x"                 == "CONST apre P x"
  "x \<lbrace> Q \<rbrace>"                 == "CONST apost x Q"
end