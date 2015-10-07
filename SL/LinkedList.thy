theory LinkedList
  imports StoreHeapModel
begin

primrec llist :: "'a nat_exp \<Rightarrow> nat list \<Rightarrow> 'a pred" where
  "llist i [] = (i \<Midarrow> #0) \<sqinter> emp"
| "llist i (x#xs) = -(i \<Midarrow> #0) \<sqinter> (EXS k. i \<mapsto> j"

end