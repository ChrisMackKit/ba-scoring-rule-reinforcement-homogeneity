theory NBA_Rule
imports Scoring_Rules
        "Compositional_Structures/Basic_Modules/Scoring_Module"
        "Compositional_Structures/Basic_Modules/NBA_Module"
        "Compositional_Structures/Elect_Composition"

begin

lemma mvp_elect:
  shows "electoral_module (elector mvp)"
proof(unfold mvp.simps)
  show "electoral_module (elector (max_eliminator (scoring vector_A_mvp)))"
    using scoring_mod_A by blast 
qed


lemma mvp_hom:
  shows "homogeneity (elector mvp)" unfolding mvp.simps 
  using scoring_rules_homogeneity
  by blast

lemma mvp_reinforcement:
  shows "reinforcement_complete (elector mvp)" unfolding mvp.simps 
  using scoring_module_rein
  by blast

end
