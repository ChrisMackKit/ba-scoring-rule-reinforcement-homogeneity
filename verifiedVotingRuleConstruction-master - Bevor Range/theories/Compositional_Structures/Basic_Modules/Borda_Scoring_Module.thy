theory Borda_Scoring_Module
imports Scoring_Module

begin

fun vec_A_borda:: "'a Vector_A" where
"vec_A_borda A =  rev (map nat [0..int (card A)-1])"

fun Borda_scoring :: "'a Electoral_Module" where
  "Borda_scoring A p = max_eliminator (scoring vec_A_borda) A p"
  
end
