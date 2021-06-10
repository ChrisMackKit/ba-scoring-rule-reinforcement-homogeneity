theory Formula_1
imports Scoring_Module

begin
(*F1 Vektor*)
fun f1_alt:: "nat \<Rightarrow> Vector" where
"f1_alt 0 = []" |
"f1_alt (Suc(n)) = 0 # (f1_alt n)"

fun vector_formula :: "nat \<Rightarrow> Vector" where
"vector_formula n = (if n \<le> 10 then [25, 18, 15, 12, 10, 8, 6, 4, 2, 1] 
else ([25, 18, 15, 12, 10, 8, 6, 4, 2, 1] @ (f1_alt (n-10))))"

fun vector_A_f1:: "'a Vector_A" where
"vector_A_f1 A = vector_formula (card A)"

fun F1 :: "'a Electoral_Module" where
  "F1 A p vs= max_eliminator (scoring vector_A_f1) A p vs"

end