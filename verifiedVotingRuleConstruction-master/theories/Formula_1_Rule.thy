theory Formula_1_Rule
  imports Scoring_Rules
          "Compositional_Structures/Basic_Modules/Scoring_Module"
          "Compositional_Structures/Basic_Modules/Formula_1"
          "Compositional_Structures/Elect_Composition"

begin

lemma f1_elect:
  shows "electoral_module (elector F1)"
proof(unfold F1.simps)
  show "electoral_module (elector (max_eliminator (scoring vector_A_f1)))"
    using scoring_mod_A by blast 
qed

lemma f1_hom:
  shows "homogeneity (elector F1)" unfolding F1.simps 
  using scoring_rules_homogeneity
  by blast

lemma f1_reinforcement:
  shows "reinforcement (elector F1)" unfolding F1.simps 
  using scoring_module_rein
  by blast

end