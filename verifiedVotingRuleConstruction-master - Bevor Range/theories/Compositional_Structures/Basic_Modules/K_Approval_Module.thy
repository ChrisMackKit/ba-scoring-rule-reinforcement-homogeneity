theory K_Approval_Module
imports Scoring_Module

begin

(*Vektor erstellen für k-approval. Erste Zahl ist größe des verbleibenden Vektors, 
zweite Zahl ist die Anzahl k*)
fun vector_k_approval:: "nat \<Rightarrow> nat \<Rightarrow> Vector" where
"vector_k_approval 0 m = []" |
"vector_k_approval (Suc(n)) 0 = 0 # vector_k_approval n 0" |
"vector_k_approval (Suc(n)) (Suc(m))= Suc(0) # (vector_k_approval n m) "

fun vector_A_k_approval:: "nat \<Rightarrow> 'a set \<Rightarrow> (nat) list" where
"vector_A_k_approval k A = vector_k_approval (card A) k"

definition one_approval :: "'a Electoral_Module" where
  "one_approval A p \<equiv> max_eliminator (scoring (vector_A_k_approval 1)) A p"

fun k_approval :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result" where
  "k_approval k A p = max_eliminator (scoring (vector_A_k_approval k)) A p"

end
