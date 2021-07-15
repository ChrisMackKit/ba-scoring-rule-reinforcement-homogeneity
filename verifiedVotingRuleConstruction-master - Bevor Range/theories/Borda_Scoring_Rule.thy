theory Borda_Scoring_Rule

imports Scoring_Rules
        "Compositional_Structures/Basic_Modules/Borda_Scoring_Module"
        "Compositional_Structures/Elect_Composition"
begin

text
\<open>This is the Borda rule. On each ballot, each alternative is assigned a score
that depends on how many alternatives are ranked below. The sum of all such
scores for an alternative is hence called their Borda score. The alternative
with the highest Borda score is elected.\<close>

subsection \<open>Definition\<close>

fun borda_Scoring_Rule :: "'a Electoral_Module" where
  "borda_Scoring_Rule A p = elector Borda_scoring A p"

lemma Borda_scoring_elect:
  shows "electoral_module (elector Borda_scoring)"
  proof(unfold Borda_scoring.simps)
  show "electoral_module (elector (max_eliminator (scoring vec_A_borda)))"
    using scoring_mod_A by blast 
qed

lemma borda_hom:
  shows "homogeneity (borda_Scoring_Rule)" unfolding Borda_scoring.simps borda_Scoring_Rule.simps
  using scoring_homogeneity elector_homogeneity by blast


lemma borda_reinforcement:
  shows "reinforcement (borda_Scoring_Rule)" unfolding Borda_scoring.simps borda_Scoring_Rule.simps
  using scoring_module_rein
  by blast

end
