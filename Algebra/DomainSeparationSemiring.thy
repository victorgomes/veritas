theory DomainSeparationSemiring
  imports "KAD/Domain_Semiring"
begin

no_notation times (infixl "*" 70)

class dss_no_loc = antidomain_semiring +
  fixes sep :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 55)
  and e :: 'a
  assumes dss1: "d(d x * d y) = d x * d y"  
  and dss2: "d(x * (y * z)) = d ((x * y) * z)"  
  and dss3: "d(x * (y + z)) = d (x * y) + d (x * z)"  
  and dss4: "d(x * y) = d (y * x)"  
  and dss5: "d(x * e) = d x"  

class dss = dss_no_loc +
  assumes loc: "d(x \<cdot> (y * z)) \<le> d ((x \<cdot> y) * z)"  

end