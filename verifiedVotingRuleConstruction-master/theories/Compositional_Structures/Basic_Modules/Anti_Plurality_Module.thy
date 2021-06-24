theory Anti_Plurality_Module
  imports Scoring_Module
          K_Approval_Module
          Formula_1_Module

begin

fun vector_anti_plurality:: "'a Vector_A" where
"vector_anti_plurality A = vector_k_approval (card A) ((card A) - 1)"

fun anti_plurality :: "'a Electoral_Module" where
  "anti_plurality A p vs= max_eliminator (scoring vector_anti_plurality) A p vs"


end