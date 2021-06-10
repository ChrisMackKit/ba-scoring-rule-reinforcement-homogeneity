theory NBA_Module
imports Scoring_Module

begin
(*MVP NBA Vote*)
fun mvp_alt:: "nat \<Rightarrow> Vector" where
"mvp_alt 0 = []" |
"mvp_alt (Suc(n)) = 0 # (mvp_alt n)"

fun vector_mvp :: "nat \<Rightarrow> Vector" where
"vector_mvp n = (if n \<le> 5 then [10, 7, 5, 3, 1] 
else ([10, 7, 5, 3, 1] @ (mvp_alt (n-5))))"

fun vector_A_mvp:: "'a Vector_A" where
"vector_A_mvp A = vector_mvp (card A)"

fun mvp :: "'a Electoral_Module" where
  "mvp A p vs= max_eliminator (scoring vector_A_mvp) A p vs"

end
