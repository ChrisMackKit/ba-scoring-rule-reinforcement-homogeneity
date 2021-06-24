(*  File:       Condorcet_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Condorcet Module\<close>

theory Condorcet_Module
  imports "Component_Types/Elimination_Module"
begin

text
\<open>This is the Condorcet module used by the Condorcet (voting) rule. The Condorcet
rule is a voting rule that implements the Condorcet criterion, i.e., it elects
the Condorcet winner if it exists, otherwise a tie remains between all
alternatives. The module implemented herein only rejects the alternatives not
elected by the voting rule, and defers the alternatives that would be elected
by the full voting rule.\<close>

subsection \<open>Definition\<close>

fun condorcet_score :: "'a Evaluation_Function" where
  "condorcet_score x A p vs =
    (if (condorcet_winner A p x) then 1 else 0)"

fun condorcet :: "'a Electoral_Module" where
  "condorcet A p vs = (max_eliminator condorcet_score) A p vs"

subsection \<open>Property\<close>

(* Condorcet score is Condorcet rating. *)
theorem condorcet_score_is_condorcet_rating: "condorcet_rating condorcet_score"
proof -
  have
    "\<forall>f.
      (\<not> condorcet_rating f \<longrightarrow>
          (\<exists>A rs a vs.
            condorcet_winner A rs a \<and>
              (\<exists>aa. \<not> f (aa::'a) A rs vs < f a A rs vs \<and> a \<noteq> aa \<and> aa \<in> A))) \<and>
        (condorcet_rating f \<longrightarrow>
          (\<forall>A rs a vs. condorcet_winner A rs a \<longrightarrow>
            (\<forall>aa. f aa A rs vs < f a A rs vs \<or> a = aa \<or> aa \<notin> A)))"
    unfolding condorcet_rating_def
    by (metis (mono_tags, hide_lams))
  thus ?thesis
    using cond_winner_unique condorcet_score.simps zero_less_one
    by (metis (no_types))
qed


theorem condorcet_is_dcc: "defer_condorcet_consistency condorcet"
  unfolding defer_condorcet_consistency_def electoral_module_def 
proof (safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  assume
    finA: "finite A" and
    profA: "profile A p" and
    vecA: "vector_pair A vs"
  have "well_formed A (max_eliminator condorcet_score A p vs)"
    using finA profA electoral_module_def max_elim_sound vecA
    by metis
  thus "well_formed A (condorcet A p vs)"
    by simp
next
(*
  show "\<And>A p w vs. condorcet_winner A p w \<Longrightarrow> finite A \<Longrightarrow> 
        condorcet A p vs = ({}, A - defer condorcet A p vs, {d \<in> A. condorcet_winner A p d})" sorry
*)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    vs :: "'a Pair_Vectors"
  assume
    cwin_w: "condorcet_winner A p w" and
    finA: "finite A" and
    vecA: "vector_pair A vs"
  (*show "condorcet_winner A p w \<Longrightarrow> finite A \<Longrightarrow> 
        condorcet A p vs = ({}, A - defer condorcet A p vs, {d \<in> A. condorcet_winner A p d})" sorry*)
  have max_cscore_dcc:
    "defer_condorcet_consistency (max_eliminator condorcet_score)"
    using cr_eval_imp_dcc_max_elim finA vecA
    by (simp add: condorcet_score_is_condorcet_rating)
  from defer_condorcet_consistency_def
  have
    "max_eliminator condorcet_score A p vs =
  ({},
  A - defer (max_eliminator condorcet_score) A p vs,
  {a \<in> A. condorcet_winner A p a})"
    using cwin_w finA max_cscore_dcc vecA 
    by (metis (no_types))
  thus
    "condorcet A p vs =
      ({},
       A - defer condorcet A p vs,
       {d \<in> A. condorcet_winner A p d})"
    by simp
qed

end
