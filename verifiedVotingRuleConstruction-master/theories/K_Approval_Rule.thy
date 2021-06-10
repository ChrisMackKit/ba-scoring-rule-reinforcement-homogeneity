theory K_Approval_Rule
imports Scoring_Rules
        "Compositional_Structures/Basic_Modules/K_Approval_Module"
        "Compositional_Structures/Elect_Composition"

begin

lemma one_approval_elect:
  shows "electoral_module (elector one_approval)"
proof(unfold one_approval_def)
  show "electoral_module (elector (max_eliminator (scoring (vector_A_k_approval 1))))"
     using scoring_mod_A by blast 
qed

lemma k_approval_elect:
  shows "electoral_module (elector (k_approval k))"
proof(unfold k_approval.simps)
  show "electoral_module (elector (max_eliminator (scoring (vector_A_k_approval k))))"
    using scoring_mod_A by blast 
qed

lemma k_approval_hom:
  shows "homogeneity (elector (k_approval k))" unfolding k_approval.simps 
  using scoring_rules_homogeneity
  by blast

lemma k_approval_reinforcement:
  shows "reinforcement (elector (k_approval k))" unfolding k_approval.simps 
  using scoring_module_rein
  by blast

end
