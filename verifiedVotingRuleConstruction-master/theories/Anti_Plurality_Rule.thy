theory Anti_Plurality_Rule
imports Scoring_Rules
        "Compositional_Structures/Basic_Modules/Anti_Plurality_Module"
        "Compositional_Structures/Elect_Composition"

begin

lemma anti_plurality_elect:
  shows "electoral_module (elector anti_plurality)"
proof(unfold anti_plurality.simps)
  show "electoral_module (elector (max_eliminator (scoring vector_anti_plurality)))"
     using scoring_mod_A by blast
qed

lemma anti_plurality_hom:
  shows "homogeneity (elector anti_plurality)" unfolding anti_plurality.simps
  using scoring_rules_homogeneity
  by blast

lemma anti_plurality_reinforcement:
  shows "reinforcement (elector anti_plurality)" unfolding anti_plurality.simps
  using scoring_module_rein
  by blast

end
