theory Eurovision_Module
imports Scoring_Module

begin
(*Eurovision Vektor*)
fun eu_alt:: "nat \<Rightarrow> Vector" where
"eu_alt 0 = []" |
"eu_alt (Suc(n)) = 0 # (eu_alt n)"

fun vector_eurovision :: "nat \<Rightarrow> Vector" where
"vector_eurovision n = (if n \<le> 10 then [12, 10, 8, 7, 6, 5, 4, 3, 2, 1] 
else ([12, 10, 8, 7, 6, 5, 4, 3, 2, 1] @ (eu_alt (n-10))))"

fun vector_A_euro:: "'a Vector_A" where
"vector_A_euro A = vector_eurovision (card A)"

fun euro :: "'a Electoral_Module" where
  "euro A p = max_eliminator (scoring vector_A_euro) A p"


end
