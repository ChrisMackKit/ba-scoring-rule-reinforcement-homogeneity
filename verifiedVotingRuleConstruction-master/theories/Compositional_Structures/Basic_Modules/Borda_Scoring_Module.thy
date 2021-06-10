theory Borda_Scoring_Module
imports Scoring_Module

begin
fun vec_borda:: "nat \<Rightarrow> Vector" where
"vec_borda n = rev (map nat [0..(int n-1)])"

fun vec_A_borda:: "'a Vector_A" where
"vec_A_borda A = vec_borda (card A)"

fun Borda_scoring :: "'a Electoral_Module" where
  "Borda_scoring A p vs = max_eliminator (scoring vec_A_borda) A p vs"
  
end
