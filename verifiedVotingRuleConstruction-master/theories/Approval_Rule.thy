theory Approval_Rule
  imports Scoring_Rules
          Range_Rules
        "Compositional_Structures/Basic_Modules/Approval_Module"
        "Compositional_Structures/Elect_Composition"

begin

lemma approval_elect:
  shows "electoral_module (elector range_scoring)"
proof(unfold range_scoring_def)
  show "electoral_module (elector (max_eliminator (range_score)))"
     using range_mod_A by blast 
 qed
(*
lemma approval_hom:
  shows "homogeneity (elector (max_eliminator approval_score))" unfolding range_score.simps 
  using range_rules_homogeneity approval_score.simps 
  by blast

lemma k_approval_reinforcement:
  shows "reinforcement (elector (max_eliminator approval_score))" unfolding range_score.simps 
  using range_module_rein
  by blast
*)
end