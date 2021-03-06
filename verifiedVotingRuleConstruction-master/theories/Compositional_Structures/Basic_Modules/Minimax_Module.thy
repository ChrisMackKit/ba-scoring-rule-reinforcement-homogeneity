(*  File:       Minimax_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Minimax Module\<close>

theory Minimax_Module
  imports "Component_Types/Elimination_Module"
begin

text
\<open>This is the Minimax module used by the Minimax voting rule. The Minimax rule
elects the alternatives with the highest Minimax score. The module implemented
herein only rejects the alternatives not elected by the voting rule, and defers
the alternatives that would be elected by the full voting rule.\<close>

subsection \<open>Definition\<close>

fun minimax_score :: "'a Evaluation_Function" where
  "minimax_score x A p vs=
    Min {prefer_count p x y |y . y \<in> A-{x}}"

fun minimax :: "'a Electoral_Module" where
  "minimax A p vs = max_eliminator minimax_score A p vs"

subsection \<open>Lemma\<close>

lemma non_cond_winner_minimax_score:
  assumes
    prof: "profile A p" and
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  shows "minimax_score l A p vs \<le> prefer_count p l w"
proof -
  let
    ?set = "{prefer_count p l y |y . y \<in> A-{l}}" and
      ?lscore = "minimax_score l A p vs"
  have "finite A"
    using prof condorcet_winner.simps winner
    by metis
  hence "finite (A-{l})"
    using finite_Diff
    by simp
  hence finite: "finite ?set"
    by simp
  have "w \<in> A"
    using condorcet_winner.simps winner
    by metis
  hence 0: "w \<in> A-{l}"
    using l_neq_w
    by force
  hence not_empty: "?set \<noteq> {}"
    by blast
  (*from 0 not_empty, have 10 "prefer_count p l w \<in> ?set"
     by blast*)
  have "?lscore = Min ?set"
    by simp
  hence 1: "?lscore \<in> ?set \<and> (\<forall>p \<in> ?set. ?lscore \<le> p)"
    using local.finite not_empty Min_le Min_eq_iff
    by (metis (no_types, lifting))
  thus ?thesis
    using "0"
    by auto
qed

subsection \<open>Property\<close>

theorem minimax_score_cond_rating: "condorcet_rating minimax_score"
proof (unfold condorcet_rating_def minimax_score.simps prefer_count.simps, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    w :: "'a" and
    l :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w:"l \<noteq> w"
  show
    "Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
        y. y \<in> A - {l}} <
      Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
          y. y \<in> A - {w}}"
  proof (rule ccontr)
    assume
      "\<not> Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
          y. y \<in> A - {l}} <
        Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
            y. y \<in> A - {w}}"
    hence
      "Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r l))} |
          y. y \<in> A - {l}} \<ge>
        Min {card {i. i < length p \<and> (let r = (p!i) in (y \<preceq>\<^sub>r w))} |
            y. y \<in> A - {w}}"
      by linarith
    hence 000:
      "Min {prefer_count p l y |y . y \<in> A-{l}} \<ge>
        Min {prefer_count p w y |y . y \<in> A-{w}}"
      by auto
    have prof: "profile A p"
      using condorcet_winner.simps winner
      by metis
    from prof winner l_in_A l_neq_w
    have 100:
      "prefer_count p l w  \<ge> Min {prefer_count p l y |y . y \<in> A-{l}}"
      using non_cond_winner_minimax_score minimax_score.simps
      by fastforce 
    from l_in_A
    have l_in_A_without_w: "l \<in> A-{w}"
      by (simp add: l_neq_w)
    hence 2: "{prefer_count p w y |y . y \<in> A-{w}} \<noteq> {}"
      by blast
    have "finite (A-{w})"
      using prof condorcet_winner.simps winner finite_Diff
      by metis
    hence 3: "finite {prefer_count p w y |y . y \<in> A-{w}}"
      by simp
    from 2 3
    have 4:
      "\<exists> n \<in> A-{w} . prefer_count p w n =
        Min {prefer_count p w y |y . y \<in> A-{w}}"
      using Min_in
      by fastforce
    then obtain n where 200:
      "prefer_count p w n =
        Min {prefer_count p w y |y . y \<in> A-{w}}" and
      6: "n \<in> A-{w}"
      by metis
    hence n_in_A: "n \<in> A"
      using DiffE
      by metis
    from 6
    have n_neq_w: "n \<noteq> w"
      by auto
    from winner
    have w_in_A: "w \<in> A"
      by simp
    from 6 prof winner
    have 300: "prefer_count p w n > prefer_count p n w"
      by simp
    from 100 000 200
    have 400: "prefer_count p l w \<ge> prefer_count p w n"
      by linarith
    with prof n_in_A w_in_A l_in_A n_neq_w
         l_neq_w pref_count_sym
    have 700: "prefer_count p n w \<ge> prefer_count p w l"
      by metis
    have "prefer_count p l w > prefer_count p w l"
      using "300" "400" "700"
      by linarith
    hence "wins l p w"
      by simp
    thus False
      using condorcet_winner.simps l_in_A_without_w
            wins_antisym winner
      by metis
  qed
qed

theorem minimax_is_dcc: "defer_condorcet_consistency minimax"
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
  have "well_formed A (max_eliminator minimax_score A p vs)"
    using finA max_elim_sound par_comp_result_sound profA vecA
    by metis
  thus "well_formed A (minimax A p vs)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    w :: "'a"
  assume
    cwin_w: "condorcet_winner A p w" and
    finA: "finite A"
  have max_mmaxscore_dcc:
    "defer_condorcet_consistency (max_eliminator minimax_score)"
    using cr_eval_imp_dcc_max_elim finA
    by (simp add: minimax_score_cond_rating)
  with defer_condorcet_consistency_def
  have
    "max_eliminator minimax_score A p vs =
      ({},
       A - defer (max_eliminator minimax_score) A p vs,
       {a \<in> A. condorcet_winner A p a})"
    using cwin_w finA sorry
    (*by (metis (no_types))*)
  thus
    "minimax A p vs=
      ({},
       A - defer minimax A p vs,
       {d \<in> A. condorcet_winner A p d})"
    by simp
qed

end
