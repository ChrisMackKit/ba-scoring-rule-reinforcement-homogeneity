(*  File:       Elimination_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Elimination Module\<close>

theory Elimination_Module
  imports Evaluation_Function
          Electoral_Module
begin

text
\<open>This is the elimination module. It rejects a set of alternatives only if these
are not all alternatives. The alternatives potentially to be rejected are put
in a so-called elimination set. These are all alternatives that score below
a preset threshold value that depends on the specific voting rule.\<close>

subsection \<open>Definition\<close>

type_synonym Threshold_Value = nat

type_synonym Threshold_Relation = "nat \<Rightarrow> nat \<Rightarrow> bool"

type_synonym 'a Electoral_Set = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a set"

fun elimination_set :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 'a Electoral_Set" where
 "elimination_set e t r A p vs = {a \<in> A . r (e a A p vs) t }"

fun elimination_module :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            Threshold_Relation \<Rightarrow> 'a Electoral_Module" where
  "elimination_module e t r A p vs =
      (if (elimination_set e t r A p vs) \<noteq> A
        then ({}, (elimination_set e t r A p vs), A - (elimination_set e t r A p vs))
        else ({},{},A))"

subsection \<open>Common Eliminators\<close>

fun less_eliminator :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module" where
  "less_eliminator e t A p vs = elimination_module e t (<) A p vs"

fun max_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "max_eliminator e A p vs =
    less_eliminator e (Max {e x A p vs | x. x \<in> A}) A p vs"

fun leq_eliminator :: "'a Evaluation_Function \<Rightarrow> Threshold_Value \<Rightarrow>
                            'a Electoral_Module" where
  "leq_eliminator e t A p vs = elimination_module e t (\<le>) A p vs"

fun min_eliminator :: "'a Evaluation_Function \<Rightarrow> 'a Electoral_Module" where
  "min_eliminator e A p vs =
    leq_eliminator e (Min {e x A p vs | x. x \<in> A}) A p vs"

fun average :: "'a Evaluation_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow>
                    Threshold_Value" where
  "average e A p vs = (\<Sum>x \<in> A. e x A p vs) div (card A)"

fun less_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "less_average_eliminator e A p vs = less_eliminator e (average e A p vs) A p vs"

fun leq_average_eliminator :: "'a Evaluation_Function \<Rightarrow>
                                'a Electoral_Module" where
  "leq_average_eliminator e A p vs = leq_eliminator e (average e A p vs) A p vs"

subsection \<open>Soundness\<close>

lemma elim_mod_sound[simp]: "electoral_module (elimination_module e t r)"
proof (unfold electoral_module_def, safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  have "set_equals_partition A (elimination_module e t r A p vs)"
    by auto
  thus "well_formed A (elimination_module e t r A p vs)"
    by simp
qed

lemma less_elim_sound[simp]: "electoral_module (less_eliminator e t)"
  unfolding electoral_module_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  show
    "{a \<in> A. e a A p vs < t} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p vs < t} \<union> A = A"
    by safe
qed

lemma leq_elim_sound[simp]: "electoral_module (leq_eliminator e t)"
  unfolding electoral_module_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  show
    "{a \<in> A. e a A p vs \<le> t} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p vs \<le> t} \<union> A = A"
    by safe
qed

lemma max_elim_sound[simp]: "electoral_module (max_eliminator e)"
  unfolding electoral_module_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  show
    "{a \<in> A. e a A p vs < Max {e x A p vs |x. x \<in> A}} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p vs < Max {e x A p vs |x. x \<in> A}} \<union> A = A"
    by safe
qed

lemma min_elim_sound[simp]: "electoral_module (min_eliminator e)"
  unfolding electoral_module_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs:: "'a Pair_Vectors"
  show
    "{a \<in> A. e a A p vs \<le> Min {e x A p vs |x. x \<in> A}} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p vs \<le> Min {e x A p vs |x. x \<in> A}} \<union> A = A"
    by safe
qed

lemma less_avg_elim_sound[simp]: "electoral_module (less_average_eliminator e)"
  unfolding electoral_module_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs:: "'a Pair_Vectors"
  show
    "{a \<in> A. e a A p vs < (\<Sum>x\<in>A. e x A p vs) div card A} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p vs < (\<Sum>x\<in>A. e x A p vs) div card A} \<union> A = A"
    by safe
qed

lemma leq_avg_elim_sound[simp]: "electoral_module (leq_average_eliminator e)"
  unfolding electoral_module_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs:: "'a Pair_Vectors"
  show
    "{a \<in> A. e a A p vs\<le> (\<Sum>x\<in>A. e x A p vs) div card A} \<noteq> A \<longrightarrow>
      {a \<in> A. e a A p vs\<le> (\<Sum>x\<in>A. e x A p vs) div card A} \<union> A = A"
    by safe
qed

subsection \<open>Non-Electing\<close>

lemma elim_mod_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (elimination_module e t r )"
  by (simp add: non_electing_def)

lemma less_elim_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (less_eliminator e t)"
  using elim_mod_non_electing profile less_elim_sound
  by (simp add: non_electing_def)

lemma leq_elim_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (leq_eliminator e t)"
proof -
  have "non_electing (elimination_module e t (\<le>))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma max_elim_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (max_eliminator e)"
proof -
  have "non_electing (elimination_module e t (<))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma min_elim_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (min_eliminator e)"
proof -
  have "non_electing (elimination_module e t (<))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma less_avg_elim_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (less_average_eliminator e)"
proof -
  have "non_electing (elimination_module e t (<))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

lemma leq_avg_elim_non_electing:
  assumes profile: "finite_profile A p" and vectors: "finite_pair_vectors A p vs"
  shows "non_electing (leq_average_eliminator e)"
proof -
  have "non_electing (elimination_module e t (\<le>))"
    by (simp add: non_electing_def)
  thus ?thesis
    by (simp add: non_electing_def)
qed

subsection \<open>Inference Rules\<close>

(*** If the used evaluation function is Condorcet rating,
     max-eliminator is Condorcet compatible. ***)
theorem cr_eval_imp_ccomp_max_elim[simp]:
  assumes
    profile: "finite_profile A p" and
    rating: "condorcet_rating e" and 
    vectors: "finite_pair_vectors A p vs"
  shows
    "condorcet_compatibility (max_eliminator e)"
  unfolding condorcet_compatibility_def
proof (auto)
  have f1:
    "\<And>A p w x vs. condorcet_winner A p w \<Longrightarrow>
      finite A \<Longrightarrow> w \<in> A \<Longrightarrow> e w A p vs < Max {e x A p vs |x. x \<in> A} \<Longrightarrow>
        x \<in> A \<Longrightarrow> e x A p vs < Max {e x A p vs |x. x \<in> A}"
    using rating
    by (simp add: cond_winner_imp_max_eval_val)
  thus
    "\<And>A p w x vs.
      profile A p \<Longrightarrow> w \<in> A \<Longrightarrow>
        \<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)} \<Longrightarrow>
              finite A \<Longrightarrow> e w A p vs< Max {e x A p vs| x. x \<in> A} \<Longrightarrow>
                x \<in> A \<Longrightarrow> e x A p vs< Max {e x A p vs| x. x \<in> A}"
    by simp
qed

lemma cr_eval_imp_dcc_max_elim_helper1:
  assumes
    f_prof: "finite_profile A p" and
    rating: "condorcet_rating e" and
    winner: "condorcet_winner A p w" and 
    vectors: "finite_pair_vectors A p vs"
  shows "elimination_set e (Max {e x A p vs | x. x \<in> A}) (<) A p vs = A - {w}"
proof (safe, simp_all, safe)
  assume
    w_in_A: "w \<in> A" and
    max: "e w A p vs< Max {e x A p vs|x. x \<in> A}"
  show "False"
    using cond_winner_imp_max_eval_val
          rating winner f_prof max
    by fastforce
next
  fix
    x :: "'a"
  assume
    x_in_A: "x \<in> A" and
    not_max: "\<not> e x A p vs< Max {e y A p vs|y. y \<in> A}"
  show "x = w"
    using non_cond_winner_not_max_eval x_in_A
          rating winner f_prof not_max vectors
    by (metis (mono_tags, lifting))
qed

(*
  If the used evaluation function is Condorcet rating, max-eliminator
  is defer-Condorcet-consistent.
*)
theorem cr_eval_imp_dcc_max_elim[simp]:
  assumes rating: "condorcet_rating e"
  shows "defer_condorcet_consistency (max_eliminator e)"
  unfolding defer_condorcet_consistency_def
proof (safe, simp)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    w :: "'a"
  assume
    winner: "condorcet_winner A p w" and
    finite: "finite A" and
    vectors: "vector_pair A p vs"
  let ?trsh = "(Max {e y A p vs| y. y \<in> A})"
  show
    "max_eliminator e A p vs=
      ({},
        A - defer (max_eliminator e) A p vs,
        {a \<in> A. condorcet_winner A p a})"
  proof (cases "elimination_set e (?trsh) (<) A p vs \<noteq> A")
    case True
    have profile: "finite_profile A p"
      using winner
      by simp
    with rating winner have 0:
      "(elimination_set e ?trsh (<) A p vs) = A - {w}"
      using cr_eval_imp_dcc_max_elim_helper1 profile vectors
      by (metis (mono_tags, lifting)) 
    have
      "max_eliminator e A p vs=
        ({},
          (elimination_set e ?trsh (<) A p vs),
          A - (elimination_set e ?trsh (<) A p vs))"
      using True
      by simp
    also have "... = ({}, A - {w}, A - (A - {w}))"
      using "0"
      by presburger
    also have "... = ({}, A - {w}, {w})"
      using winner
      by auto
    also have "... = ({},A - defer (max_eliminator e) A p vs, {w})"
      using calculation
      by auto
    also have
      "... =
        ({},
          A - defer (max_eliminator e) A p vs,
          {d \<in> A. condorcet_winner A p d})"
      using cond_winner_unique3 winner Collect_cong
      by (metis (no_types, lifting))
    finally show ?thesis
      using finite winner
      by metis
  next
    case False
    thus ?thesis
    proof -
      have f1:
        "finite A \<and> profile A p \<and> w \<in> A \<and> (\<forall>a. a \<notin> A - {w} \<or> wins w p a)"
        using winner
        by auto
      hence
        "?trsh = e w A p vs"
        using rating winner
        by (simp add: cond_winner_imp_max_eval_val)
      hence False
        using f1 False
        by auto
      thus ?thesis
        by simp
    qed
  qed
qed

end
