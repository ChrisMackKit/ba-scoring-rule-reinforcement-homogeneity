theory Eurovision_Rule
imports Scoring_Rules
        "Compositional_Structures/Basic_Modules/Scoring_Module"
        "Compositional_Structures/Basic_Modules/Eurovision_Module"
        "Compositional_Structures/Elect_Composition"

begin


lemma euro_elect:
  shows "electoral_module (elector euro)"
proof(unfold euro.simps)
  show "electoral_module (elector (max_eliminator (scoring vector_A_euro)))"
    using scoring_mod_A by blast 
qed

lemma euro_hom:
  shows "homogeneity (elector euro)" unfolding euro.simps 
  using scoring_rules_homogeneity
  by blast

lemma euro_reinforcement:
  shows "reinforcement (elector euro)" unfolding euro.simps 
  using scoring_module_rein
  by blast

end
