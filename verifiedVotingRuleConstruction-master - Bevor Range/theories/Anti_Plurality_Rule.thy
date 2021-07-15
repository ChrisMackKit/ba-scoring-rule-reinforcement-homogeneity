theory Anti_Plurality_Rule

imports Scoring_Rules
        "Compositional_Structures/Basic_Modules/Anti_Plurality_Module"
        "Compositional_Structures/Elect_Composition"
begin

subsection \<open>Definition\<close>

fun anti_Plurality_Rule :: "'a Electoral_Module" where
  "anti_Plurality_Rule A p = elector anti_plurality A p"

lemma Borda_scoring_elect:
  shows "electoral_module (elector anti_plurality)"
  proof(unfold anti_plurality_def)
  show "electoral_module (elector (max_eliminator (scoring vector_anti_plurality)))"
    using scoring_mod_A by blast 
qed

lemma borda_hom:
  shows "homogeneity (anti_Plurality_Rule)" unfolding anti_plurality_def anti_Plurality_Rule.simps
  using scoring_homogeneity elector_homogeneity by blast


lemma borda_reinforcement:
  shows "reinforcement (anti_Plurality_Rule)" unfolding anti_plurality_def anti_Plurality_Rule.simps
  using scoring_module_rein
  by blast

end
