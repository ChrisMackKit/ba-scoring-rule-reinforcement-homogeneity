theory Anti_Plurality_Module
  imports Scoring_Module
          K_Approval_Module


begin

fun vector_anti_plurality:: "'a Vector_A" where
"vector_anti_plurality A = vector_k_approval (card A) ((card A) - 1)"

definition anti_plurality :: "'a Electoral_Module" where
  "anti_plurality A p = max_eliminator (scoring vector_anti_plurality) A p"

end