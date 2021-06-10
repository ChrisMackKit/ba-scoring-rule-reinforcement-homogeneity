(*  File:       Maximum_Parallel_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Maximum Parallel Composition\<close>

theory Maximum_Parallel_Composition
  imports "Basic_Modules/Component_Types/Maximum_Aggregator"
          Parallel_Composition
begin

text
\<open>This is a family of parallel compositions. It composes a new electoral module
from two electoral modules combined with the maximum aggregator. Therein, the
two modules each make a decision and then a partition is returned where every
alternative receives the maximum result of the two input partitions. This means
that, if any alternative is elected by at least one of the modules, then it
gets elected, if any non-elected alternative is deferred by at least one of the
modules, then it gets deferred, only alternatives rejected by both modules get
rejected.\<close>

subsection \<open>Definition\<close>

fun maximum_parallel_composition :: "'a Electoral_Module \<Rightarrow>
        'a Electoral_Module \<Rightarrow> 'a Electoral_Module" where
  "maximum_parallel_composition m n =
    (let a = max_aggregator in (m \<parallel>\<^sub>a n))"

abbreviation max_parallel :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" (infix "\<parallel>\<^sub>\<up>" 50) where
  "m \<parallel>\<^sub>\<up> n == maximum_parallel_composition m n"

subsection \<open>Soundness\<close>

theorem max_par_comp_sound:
  assumes
    mod_m: "electoral_module m" and
    mod_n: "electoral_module n"
  shows "electoral_module (m \<parallel>\<^sub>\<up> n)"
  using mod_m mod_n
  by simp

subsection \<open>Lemmata\<close>

lemma max_agg_eq_result:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    in_A: "x \<in> A"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p vs x \<or>
      mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p vs x"
proof cases
  assume a1: "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p vs"
    have mod_contains_inst:
      "\<forall>p_mod q_mod a_set prof a vs.
        mod_contains_result p_mod q_mod a_set prof vs (a::'a) =
          (electoral_module p_mod \<and> electoral_module q_mod \<and>
            finite a_set \<and> profile a_set prof \<and> a \<in> a_set \<and> finite_pair_vectors a_set prof vs \<and>
            (a \<notin> elect p_mod a_set prof vs \<or> a \<in> elect q_mod a_set prof vs) \<and>
            (a \<notin> reject p_mod a_set prof vs \<or> a \<in> reject q_mod a_set prof vs) \<and>
            (a \<notin> defer p_mod a_set prof vs \<or> a \<in> defer q_mod a_set prof vs))"
      by (simp add: mod_contains_result_def)
  have module_mn: "electoral_module (m \<parallel>\<^sub>\<up> n)"
    by (simp add: module_m module_n)
  have not_defer_mn: "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p vs"
    using module_mn IntI a1 empty_iff f_prof result_disj f_vec
    by (metis (no_types))
  have not_reject_mn: "x \<notin> reject (m \<parallel>\<^sub>\<up> n) A p vs"
    using module_mn IntI a1 empty_iff f_prof result_disj f_vec
    by (metis (no_types))
  from a1 have
    "let (e1, r1, d1) = m A p vs;
        (e2, r2, d2) = n A p vs in
      x \<in> e1 \<union> e2"
    by auto
  hence union_mn: "x \<in> (elect m A p vs) \<union> (elect n A p vs)"
    by auto
  thus ?thesis
    using f_prof in_A module_m module_mn module_n
          not_defer_mn not_reject_mn union_mn
          mod_contains_inst f_vec
      by blast
next
  assume not_a1: "x \<notin> elect (m \<parallel>\<^sub>\<up> n) A p vs"
  thus ?thesis
  proof cases
    assume x_in_def: "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p vs"
    thus ?thesis
    proof (safe)
      assume not_mod_cont_mn:
        "\<not> mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p vs x"
      have par_emod:
        "\<forall>f g.
          (electoral_module (f::'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Result) \<and>
            electoral_module g) \<longrightarrow>
              electoral_module (f \<parallel>\<^sub>\<up> g)"
        using max_par_comp_sound
        by blast
      hence "electoral_module (m \<parallel>\<^sub>\<up> n)"
        using module_m module_n
        by blast
      hence max_par_emod:
        "electoral_module (m \<parallel>\<^sub>max_aggregator n)"
        by simp
      have set_intersect:
        "\<forall>(a::'a) A B. (a \<in> A \<inter> B) = (a \<in> A \<and> a \<in> B)"
        by blast
      obtain
        s_func :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Result) \<Rightarrow> 'a set" and
        p_func :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow>  'a Result) \<Rightarrow> 'a Profile" and
        vs_func :: "('a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow>  'a Result) \<Rightarrow> 'a Pair_Vectors" where
        well_f:
        "\<forall>f.
          (\<not> electoral_module f \<or>
            (\<forall>A prof vs. (finite A \<and> profile A prof) \<longrightarrow> well_formed A (f A prof vs))) \<and>
          (electoral_module f \<or> finite (s_func f) \<and> profile (s_func f) (p_func f) \<and> 
          vector_pair (s_func f) (p_func f) (vs_func f) \<and>
            \<not> well_formed (s_func f) (f (s_func f) (p_func f) (vs_func f)))"
        using electoral_module_def
        (*by moura*) sorry
      hence wf_n: "well_formed A (n A p vs)"
        using f_prof module_n
        by blast
      have wf_m: "well_formed A (m A p vs)"
        using well_f f_prof module_m
        by blast
      have a_exists: "\<forall>(a::'a). a \<notin> {}"
        by blast
      have e_mod_par:
        "electoral_module (m \<parallel>\<^sub>\<up> n)"
        using par_emod module_m module_n
        by blast
      hence "electoral_module (m \<parallel>\<^sub>max_aggregator n)"
        by simp
      hence result_disj_max:
        "elect (m \<parallel>\<^sub>max_aggregator n) A p vs \<inter> reject (m \<parallel>\<^sub>max_aggregator n) A p vs = {} \<and>
          elect (m \<parallel>\<^sub>max_aggregator n) A p vs \<inter> defer (m \<parallel>\<^sub>max_aggregator n) A p vs = {} \<and>
          reject (m \<parallel>\<^sub>max_aggregator n) A p vs \<inter> defer (m \<parallel>\<^sub>max_aggregator n) A p vs = {}"
        using f_prof result_disj f_vec
        by metis
      have x_not_elect:
        "x \<notin> elect (m \<parallel>\<^sub>max_aggregator n) A p vs"
        using result_disj_max x_in_def
        by force
      have result_m:
        "(elect m A p vs, reject m A p vs, defer m A p vs) = m A p vs"
        by auto
      have result_n:
        "(elect n A p vs, reject n A p vs, defer n A p vs) = n A p vs"
        by auto
      have max_pq:
        "\<forall>(A::'a set) p q.
          elect_r (max_aggregator A p q) = elect_r p \<union> elect_r q"
        by force
      have
        "x \<notin> elect (m \<parallel>\<^sub>max_aggregator n) A p vs"
        using x_not_elect
        by blast
      with max_pq
      have "x \<notin> elect m A p vs \<union> elect n A p vs"
        by (simp add: max_pq)
      hence x_not_elect_mn:
        "x \<notin> elect m A p vs \<and> x \<notin> elect n A p vs"
        by blast
      have x_not_mpar_rej:
        "x \<notin> reject (m \<parallel>\<^sub>max_aggregator n) A p vs"
        using result_disj_max x_in_def
        by fastforce
      hence x_not_par_rej:
        "x \<notin> reject (m \<parallel>\<^sub>\<up> n) A p vs"
        by auto
      have mod_cont_res_fg:
        "\<forall>f g A prof (a::'a) vs.
          mod_contains_result f g A prof vs a =
            (electoral_module f \<and> electoral_module g \<and>
              finite A \<and> profile A prof \<and> a \<in> A \<and> vector_pair A prof vs \<and>
                (a \<notin> elect f A prof vs \<or> a \<in> elect g A prof vs) \<and>
                (a \<notin> reject f A prof vs \<or> a \<in> reject g A prof vs) \<and>
                (a \<notin> defer f A prof vs \<or> a \<in> defer g A prof vs))"
        using mod_contains_result_def by fastforce
      have max_agg_res:
        "max_aggregator A (elect m A p vs, reject m A p vs, defer m A p vs)
          (elect n A p vs, reject n A p vs, defer n A p vs) = (m \<parallel>\<^sub>max_aggregator n) A p vs"
        by simp
      have well_f_max:
        "\<forall>r2 r1 e2 e1 d2 d1 A.
          well_formed A (e1, r1, d1) \<and> well_formed A (e2, r2, d2) \<longrightarrow>
            reject_r (max_aggregator A (e1, r1, d1) (e2, r2, d2)) = r1 \<inter> r2"
        using max_agg_rej_set
        by metis
      have e_mod_disj:
        "\<forall>f (A::'a set) prof vs.
          (electoral_module f \<and> finite (A::'a set) \<and> profile A prof \<and> vector_pair A prof vs) \<longrightarrow>
            elect f A prof vs \<union> reject f A prof vs \<union> defer f A prof vs = A"
        using result_presv_alts
        by blast
      hence e_mod_disj_n:
        "elect n A p vs \<union> reject n A p vs \<union> defer n A p vs = A"
        using f_prof module_n f_vec
        by metis
      have
        "\<forall>f g A prof (a::'a) vs.
          mod_contains_result f g A prof vs a =
            (electoral_module f \<and> electoral_module g \<and>
              finite A \<and> profile A prof \<and> a \<in> A \<and> vector_pair A prof vs \<and>
              (a \<notin> elect f A prof vs \<or> a \<in> elect g A prof vs) \<and>
              (a \<notin> reject f A prof vs \<or> a \<in> reject g A prof vs) \<and>
              (a \<notin> defer f A prof vs \<or> a \<in> defer g A prof vs))" 
        using mod_contains_result_def by fastforce 
      with e_mod_disj_n
      have "x \<in> reject n A p vs"
        using e_mod_par f_prof in_A module_n not_mod_cont_mn
              x_not_elect x_not_elect_mn x_not_mpar_rej f_vec
        by auto
      hence "x \<notin> reject m A p vs"
        using well_f_max max_agg_res result_m result_n
              set_intersect wf_m wf_n x_not_mpar_rej
        by (metis (no_types))
      with max_agg_res
      have
        "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p vs \<or> x \<in> defer m A p vs"
          using e_mod_disj f_prof in_A module_m x_not_elect_mn f_vec
          by blast
      with x_not_mpar_rej
      show "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p vs x"
        using mod_cont_res_fg x_not_par_rej e_mod_par f_prof
              in_A module_m x_not_elect f_vec
        by auto
    qed
  next
    assume not_a2: "x \<notin> defer (m \<parallel>\<^sub>\<up> n) A p vs"
    have el_rej_defer:
      "(elect m A p vs, reject m A p vs, defer m A p vs) = m A p vs"
      by auto
    from not_a1 not_a2 have a3:
      "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p vs"
      using electoral_mod_defer_elem in_A module_m module_n
            f_prof max_par_comp_sound f_vec
      by metis
    hence
      "case snd (m A p vs) of (Aa, Ab) \<Rightarrow>
        case n A p vs of (Ac, Ad, Ae) \<Rightarrow>
          x \<in> reject_r
            (max_aggregator A
              (elect m A p vs, Aa, Ab) (Ac, Ad, Ae))"
      using el_rej_defer
      by force
    hence
      "let (e1, r1, d1) = m A p vs;
          (e2, r2, d2) = n A p vs in
        x \<in> fst (snd (max_aggregator A
          (e1, r1, d1) (e2, r2, d2)))"
      by (simp add: case_prod_unfold)
    hence
      "let (e1, r1, d1) = m A p vs;
          (e2, r2, d2) = n A p vs in
        x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
      by simp
    hence
      "x \<notin> elect m A p vs \<union> (defer n A p vs \<union> defer m A p vs)"
      by force
    thus ?thesis
      using mod_contains_result_comm mod_contains_result_def Un_iff
            a3 f_prof in_A module_m module_n max_par_comp_sound f_vec
      by (metis (no_types))
  qed
qed

lemma max_agg_rej_iff_both_reject:
  assumes
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n"
  shows
    "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p vs \<longleftrightarrow>
      (x \<in> reject m A p vs \<and> x \<in> reject n A p vs)"
proof
  assume a: "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p vs"
  hence
    "case n A p vs of (Aa, Ab, Ac) \<Rightarrow>
      x \<in> reject_r (max_aggregator A
        (elect m A p vs, reject m A p vs, defer m A p vs) (Aa, Ab, Ac))"
    by auto
  hence
    "case snd (m A p vs) of (Aa, Ab) \<Rightarrow>
      case n A p vs of (Ac, Ad, Ae) \<Rightarrow>
        x \<in> reject_r (max_aggregator A
          (elect m A p vs, Aa, Ab) (Ac, Ad, Ae))"
    by force
  with a have
    "let (e1, r1, d1) = m A p vs;
          (e2, r2, d2) = n A p vs in
      x \<in> fst (snd (max_aggregator A (e1, r1, d1) (e2, r2, d2)))"
    by (simp add: prod.case_eq_if)
  hence
    "let (e1, r1, d1) = m A p vs;
        (e2, r2, d2) = n A p vs in
      x \<in> A - (e1 \<union> e2 \<union> d1 \<union> d2)"
    by simp
  hence
    "x \<in> A - (elect m A p vs \<union> elect n A p vs \<union> defer m A p vs \<union> defer n A p vs)"
    by auto
  thus "x \<in> reject m A p vs \<and> x \<in> reject n A p vs"
    using Diff_iff Un_iff electoral_mod_defer_elem
          f_prof module_m module_n f_vec
    by metis
next
  assume a: "x \<in> reject m A p vs \<and> x \<in> reject n A p vs"
  hence
    "x \<notin> elect m A p vs \<and> x \<notin> defer m A p vs \<and>
      x \<notin> elect n A p vs \<and> x \<notin> defer n A p vs"
    using IntI empty_iff module_m module_n f_prof result_disj f_vec
    by metis
  thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p vs"
    using DiffD1 a f_prof max_agg_eq_result module_m module_n
          mod_contains_result_comm mod_contains_result_def
          reject_not_elec_or_def f_vec
      by (metis (no_types))
qed

lemma max_agg_rej1:
  assumes
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p vs"
  shows
    "mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p vs x"
  unfolding mod_contains_result_def
proof (safe)
  show "electoral_module m"
    using module_m
    by simp
next
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "profile A p"
    using f_prof
    by simp
next
  show "vector_pair A p vs"
    using f_vec
    by simp
next
  show "x \<in> A"
    using f_prof module_n reject_in_alts rejected f_vec
    by blast
next
  assume
    x_in_elect: "x \<in> elect m A p vs"
  hence x_not_reject:
    "x \<notin> reject m A p vs"
    using disjoint_iff_not_equal f_prof module_m result_disj f_vec
    by metis
  have rej_in_A:
    "reject n A p vs \<subseteq> A"
    using f_prof module_n f_vec
    by (simp add: reject_in_alts)
  have x_in_A: "x \<in> A"
    using rej_in_A in_mono rejected
    by metis
  with x_in_elect x_not_reject
  show "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p vs"
    using f_prof max_agg_eq_result module_m module_n rejected
          max_agg_rej_iff_both_reject mod_contains_result_comm
          mod_contains_result_def f_vec
      by metis
next
  assume "x \<in> reject m A p vs"
  hence
    "x \<in> reject m A p vs \<and> x \<in> reject n A p vs"
    using rejected
    by simp
  thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p vs "
    using f_prof max_agg_rej_iff_both_reject module_m module_n f_vec
    by (metis (no_types))
next
  assume x_in_defer: "x \<in> defer m A p vs"
  hence defer_a:
    "\<exists>a. a \<in> defer m A p vs \<and> x = a"
    by simp
  then obtain x_inst :: 'a where
    inst_x: "x = x_inst \<and> x_inst \<in> defer m A p vs"
    by metis
  hence x_not_rej:
    "x \<notin> reject m A p vs"
    using disjoint_iff_not_equal f_prof inst_x module_m result_disj f_vec
    by (metis (no_types))
  have
    "\<forall>f A prof vs.
      (electoral_module f \<and> finite (A::'a set) \<and> profile A prof \<and> vector_pair A prof vs) \<longrightarrow>
        elect f A prof vs \<union> reject f A prof vs \<union> defer f A prof vs = A"
    using result_presv_alts
    by metis
  with x_in_defer
  have "x \<in> A"
    using f_prof module_m f_vec
    by blast
  with inst_x x_not_rej
  show "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p vs"
    using f_prof max_agg_eq_result
          max_agg_rej_iff_both_reject
          mod_contains_result_comm
          mod_contains_result_def
          module_m module_n rejected f_vec
    by metis
qed

lemma max_agg_rej2:
  assumes
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject n A p vs"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) m A p vs x"
  using mod_contains_result_comm max_agg_rej1
        module_m module_n f_prof rejected f_vec
  by metis

lemma max_agg_rej3:
  assumes
    f_prof:  "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p vs"
  shows
    "mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p vs x"
  unfolding mod_contains_result_def
proof (safe)
  show "electoral_module n"
    using module_n
    by simp
next
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using module_m module_n
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "finite A"
    using f_prof
    by simp
next
  show "profile A p"
    using f_prof
    by simp
next
  show "vector_pair A p vs"
    using f_vec
    by simp
next
  show "x \<in> A"
    using f_prof in_mono module_m reject_in_alts rejected f_vec
    by (metis (no_types))
next
  assume "x \<in> elect n A p vs"
  thus "x \<in> elect (m \<parallel>\<^sub>\<up> n) A p vs"
    using Un_iff combine_ele_rej_def fst_conv
          maximum_parallel_composition.simps
          max_aggregator.simps
          parallel_composition.simps
    by (metis (mono_tags, lifting))
next
  assume "x \<in> reject n A p vs"
  thus "x \<in> reject (m \<parallel>\<^sub>\<up> n) A p vs"
    using f_prof max_agg_rej_iff_both_reject module_m module_n rejected f_vec
    by metis
next
  assume x_in_def: "x \<in> defer n A p vs"
  have "x \<in> A"
    using f_prof max_agg_rej1 mod_contains_result_def module_m rejected f_vec
    by metis
  thus "x \<in> defer (m \<parallel>\<^sub>\<up> n) A p vs"
    using x_in_def disjoint_iff_not_equal f_prof
          max_agg_eq_result max_agg_rej_iff_both_reject
          mod_contains_result_comm mod_contains_result_def
          module_m module_n rejected result_disj f_vec
      by metis
qed

lemma max_agg_rej4:
  assumes
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    rejected: "x \<in> reject m A p vs"
  shows
    "mod_contains_result (m \<parallel>\<^sub>\<up> n) n A p vs x"
  using mod_contains_result_comm max_agg_rej3
        module_m module_n f_prof rejected f_vec
  by metis

lemma max_agg_rej_intersect:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "vector_pair A p vs"
  shows
    "reject (m \<parallel>\<^sub>\<up> n) A p vs =
      (reject m A p vs) \<inter> (reject n A p vs)"
proof -
  have
    "A = (elect m A p vs) \<union> (reject m A p vs) \<union> (defer m A p vs) \<and>
      A = (elect n A p vs) \<union> (reject n A p vs) \<union> (defer n A p vs)"
    by (simp add: module_m module_n f_prof result_presv_alts f_vec)
  hence
    "A - ((elect m A p vs) \<union> (defer m A p vs)) = (reject m A p vs) \<and>
      A - ((elect n A p vs) \<union> (defer n A p vs)) = (reject n A p vs)"
    using module_m module_n f_prof f_vec
    by (metis (no_types, lifting) double_diff elec_and_def_not_rej reject_in_alts subset_refl)
  hence
    "A - ((elect m A p vs) \<union> (elect n A p vs) \<union> (defer m A p vs) \<union> (defer n A p vs)) =
      (reject m A p vs) \<inter> (reject n A p vs)"
    by blast
  hence
    "let (e1, r1, d1) = m A p vs;
        (e2, r2, d2) = n A p vs in
      A - (e1 \<union> e2 \<union> d1 \<union> d2) = r1 \<inter> r2"
    by fastforce
  thus ?thesis
    by auto
qed

lemma dcompat_dec_by_one_mod:
  assumes
    compatible: "disjoint_compatibility m n" and
    in_A: "x \<in> A"
  shows
    "(\<forall>p vs. finite_profile A p \<and> finite_pair_vectors A p vs\<longrightarrow>
          mod_contains_result m (m \<parallel>\<^sub>\<up> n) A p vs x) \<or>
        (\<forall>p vs. finite_profile A p \<and> finite_pair_vectors A p vs\<longrightarrow>
          mod_contains_result n (m \<parallel>\<^sub>\<up> n) A p vs x)"
  using DiffI compatible disjoint_compatibility_def
        in_A max_agg_rej1 max_agg_rej3 sorry
  (*by metis*)

subsection \<open>Composition Rules\<close>

(*
   Using a conservative aggregator, the parallel composition
   preserves the property non-electing.
*)
theorem conserv_max_agg_presv_non_electing[simp]:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_n: "non_electing n"
  shows "non_electing (m \<parallel>\<^sub>\<up> n)"
  using non_electing_m non_electing_n
  by simp

(*
   Using the max aggregator, composing two compatible
   electoral modules in parallel preserves defer-lift-invariance.
*)
theorem par_comp_def_lift_inv[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<parallel>\<^sub>\<up> n)"
  unfolding defer_lift_invariance_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using monotone_m
    by (simp add: defer_lift_invariance_def)
  have electoral_mod_n: "electoral_module n"
    using monotone_n
    by (simp add: defer_lift_invariance_def)
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    S :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    x :: "'a"
  assume
    vec_S: "vector_pair S p vs" and
    defer_x: "x \<in> defer (m \<parallel>\<^sub>\<up> n) S p vs" and
    lifted_x: "Profile.lifted S p q x"
  hence f_profs: "finite_profile S p \<and> finite_profile S q"
    by (simp add: lifted_def)
  have f_vec:"finite_pair_vectors S p vs \<and> finite_pair_vectors S q vs" 
    using vec_S f_profs lifted_x lifted_finite_vectors by metis
  from compatible
  obtain A::"'a set" where A:
    "A \<subseteq> S \<and> (\<forall>x \<in> A. indep_of_alt m S vs x \<and>
      (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs\<longrightarrow> x \<in> reject m S p vs)) \<and>
        (\<forall>x \<in> S-A. indep_of_alt n S vs x \<and>
      (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs\<longrightarrow> x \<in> reject n S p vs))"
    using disjoint_compatibility_def f_profs sorry
    (*by (metis (no_types, lifting))*)
  have
    "\<forall>x \<in> S. prof_contains_result (m \<parallel>\<^sub>\<up> n) S vs p q x"
  proof cases
    assume a0: "x \<in> A"
    hence "x \<in> reject m S p vs"
      using A f_profs f_vec
      by blast
    with defer_x
    have defer_n: "x \<in> defer n S p vs"
      by (smt (verit, best) compatible disjoint_compatibility_def 
            f_profs f_vec max_agg_rej4 mod_contains_result_def) 
      (*using compatible disjoint_compatibility_def
            mod_contains_result_def f_profs max_agg_rej4
      by metis*)
    have
      "\<forall>x \<in> A. mod_contains_result (m \<parallel>\<^sub>\<up> n) n S p vs x"
      by (smt (verit, best) A defer_lift_invariance_def 
          f_profs f_vec max_agg_rej4 monotone_m monotone_n)
      (*using A compatible disjoint_compatibility_def
            max_agg_rej4 f_profs f_vec 
      by metis*)
    moreover have "\<forall>x \<in> S. prof_contains_result n S vs p q x"
      unfolding prof_contains_result_def
    proof (clarify)
      fix x :: "'a"
      assume
        x_in_S: "x \<in> S"
      show
        "electoral_module n \<and>
         finite_profile S p \<and>
         finite_profile S q \<and>
         x \<in> S \<and>
         finite_pair_vectors S p vs \<and>
         (x \<in> elect n S p vs \<longrightarrow> x \<in> elect n S q vs) \<and>
         (x \<in> reject n S p vs \<longrightarrow> x \<in> reject n S q vs) \<and>
         (x \<in> defer n S p vs \<longrightarrow> x \<in> defer n S q vs)"
      proof (safe)
        show "electoral_module n"
          using monotone_n defer_lift_invariance_def
          by metis
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S p"
          using f_profs
          by simp
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S q"
          using f_profs
          by simp
      next
        show "x \<in> S"
          using x_in_S
          by simp
      next
        assume "x \<in> elect n S p vs"
        thus "x \<in> elect n S q vs"
          using defer_n lifted_x monotone_n
                f_profs defer_lift_invariance_def f_vec
          by metis
      next
        assume "x \<in> reject n S p vs"
        thus "x \<in> reject n S q vs"
          using defer_n lifted_x monotone_n
                f_profs defer_lift_invariance_def f_vec
          by metis
      next
        assume "x \<in> defer n S p vs"
        thus "x \<in> defer n S q vs"
          using defer_n lifted_x monotone_n
                f_profs defer_lift_invariance_def f_vec
          by metis
      next
          show "vector_pair S p vs"
            using f_vec
          by simp 
      qed
    qed
    moreover have
      "\<forall>x \<in> A. mod_contains_result n (m \<parallel>\<^sub>\<up> n) S q vs x" 
      using A compatible disjoint_compatibility_def
            max_agg_rej3 f_profs f_vec
      by metis
    ultimately have 00:
      "\<forall>x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S vs p q  x"
      by (simp add: mod_contains_result_def prof_contains_result_def vec_S)
    have
      "\<forall>x \<in> S-A. mod_contains_result (m \<parallel>\<^sub>\<up> n) m S p vs x"
      using A max_agg_rej2 monotone_m monotone_n f_profs
            defer_lift_invariance_def f_vec
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result m S vs p q x"
      unfolding prof_contains_result_def
    proof (clarify)
      fix x :: "'a"
      assume
        x_in_S: "x \<in> S"
      show
        "electoral_module m \<and>
         finite_profile S p \<and>
         finite_profile S q \<and>
         x \<in> S \<and>
         finite_pair_vectors S p vs \<and>
         (x \<in> elect m S p vs \<longrightarrow> x \<in> elect m S q vs) \<and>
         (x \<in> reject m S p vs \<longrightarrow> x \<in> reject m S q vs) \<and>
         (x \<in> defer m S p vs \<longrightarrow> x \<in> defer m S q vs)"
      proof (safe)
        show "electoral_module m"
          using monotone_m defer_lift_invariance_def
          by metis
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S p"
          using f_profs
          by simp
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "profile S q"
          using f_profs
          by simp
      next
        show "x \<in> S"
          using x_in_S
          by simp
      next
        assume "x \<in> elect m S p vs"
        thus "x \<in> elect m S q vs"
          using A a0 indep_of_alt_def lifted_x
                lifted_imp_equiv_prof_except_a
          by metis
      next
        assume "x \<in> reject m S p vs"
        thus "x \<in> reject m S q vs"
          using A a0 indep_of_alt_def lifted_x
                lifted_imp_equiv_prof_except_a
          by metis
      next
        assume "x \<in> defer m S p vs"
        thus "x \<in> defer m S q vs"
          using A a0 indep_of_alt_def lifted_x
                lifted_imp_equiv_prof_except_a
          by metis
      next
        show "finite S"
          using f_profs
          by simp
      next
        show "vector_pair S p vs"
          using f_vec
          by simp
      qed
    qed
    moreover have
      "\<forall>x \<in> S-A. mod_contains_result m (m \<parallel>\<^sub>\<up> n) S q vs x"
      using A max_agg_rej1 monotone_m monotone_n f_profs
            defer_lift_invariance_def f_vec
      by metis
    ultimately have 01:
      "\<forall>x \<in> S-A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S vs p q x"
      by (simp add: mod_contains_result_def prof_contains_result_def)
    from 00 01
    show ?thesis
      by blast
  next
    assume "x \<notin> A"
    hence a1: "x \<in> S-A"
      using DiffI lifted_x compatible f_profs
            Profile.lifted_def
      by (metis (no_types, lifting))
    hence "x \<in> reject n S p vs"
      using A f_profs f_vec
      by blast
    with defer_x
    have defer_m: "x \<in> defer m S p vs"
      using DiffD1 DiffD2 compatible dcompat_dec_by_one_mod
            defer_not_elec_or_rej disjoint_compatibility_def
            not_rej_imp_elec_or_def mod_contains_result_def
            max_agg_sound par_comp_sound f_profs f_vec
            maximum_parallel_composition.simps
      by metis
    have
      "\<forall>x \<in> A. mod_contains_result (m \<parallel>\<^sub>\<up> n) n S p vs x"
      using A compatible disjoint_compatibility_def
            max_agg_rej4 f_profs f_vec
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result n S vs p q x"
      unfolding prof_contains_result_def f_vec
    proof (clarify)
      fix x :: "'a"
        assume
          x_in_S: "x \<in> S"
        show
          "electoral_module n \<and>
           finite_profile S p \<and>
           finite_profile S q \<and>
           x \<in> S \<and>
           finite_pair_vectors S p vs \<and>
           (x \<in> elect n S p vs \<longrightarrow> x \<in> elect n S q vs) \<and>
           (x \<in> reject n S p vs \<longrightarrow> x \<in> reject n S q vs) \<and>
           (x \<in> defer n S p vs \<longrightarrow> x \<in> defer n S q vs)"
        proof (safe)
          show "electoral_module n"
            using monotone_n defer_lift_invariance_def
            by metis
        next
          show "finite S"
            using f_profs
            by simp
        next
          show "finite S"
            using f_profs
            by simp
        next
          show "profile S p"
            using f_profs
            by simp
        next
          show "finite S"
            using f_profs
            by simp
        next
          show "profile S q"
            using f_profs
            by simp
        next
          show "x \<in> S"
            using x_in_S
            by simp
        next
          show "vector_pair S p vs"
            using f_vec
            by simp
        next
          assume "x \<in> elect n S p vs"
          thus "x \<in> elect n S q vs"
            using A a1 indep_of_alt_def lifted_x
                  lifted_imp_equiv_prof_except_a
            by metis
        next
          assume "x \<in> reject n S p vs"
          thus "x \<in> reject n S q vs"
            using A a1 indep_of_alt_def lifted_x
                  lifted_imp_equiv_prof_except_a
            by metis
        next
          assume "x \<in> defer n S p vs"
          thus "x \<in> defer n S q vs"
            using A a1 indep_of_alt_def lifted_x
                  lifted_imp_equiv_prof_except_a 
            by metis
        qed
    qed
    moreover have
      "\<forall>x \<in> A. mod_contains_result n (m \<parallel>\<^sub>\<up> n) S q vs x"
      using A compatible disjoint_compatibility_def
            max_agg_rej3 f_profs f_vec
      by metis
    ultimately have 10:
      "\<forall>x \<in> A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S vs p q x"
      by (simp add: mod_contains_result_def prof_contains_result_def vec_S)
    have
      "\<forall>x \<in> S-A. mod_contains_result (m \<parallel>\<^sub>\<up> n) m S p vs x"
      using A max_agg_rej2 monotone_m monotone_n
            f_profs defer_lift_invariance_def f_vec
      by metis
    moreover have "\<forall>x \<in> S. prof_contains_result m S vs p q x"
      unfolding prof_contains_result_def f_vec
    proof (clarify)
      fix x :: "'a"
        assume
          x_in_S: "x \<in> S"
        show
          "electoral_module m \<and>
           finite_profile S p \<and>
           finite_profile S q \<and>
           x \<in> S \<and>
           finite_pair_vectors S p vs \<and>
           (x \<in> elect m S p vs \<longrightarrow> x \<in> elect m S q vs) \<and>
           (x \<in> reject m S p vs \<longrightarrow> x \<in> reject m S q vs) \<and>
           (x \<in> defer m S p vs \<longrightarrow> x \<in> defer m S q vs)"
        proof (safe)
          show "electoral_module m"
            using monotone_m defer_lift_invariance_def
            by metis
        next
          show "finite S"
            using f_profs
            by simp
        next
          show "finite S"
            using f_profs
            by simp
        next
          show "profile S p"
            using f_profs
            by simp
        next
          show "finite S"
            using f_profs
            by simp
        next
          show "profile S q"
            using f_profs
            by simp
        next
          show "x \<in> S"
            using x_in_S
            by simp
        next
          show "vector_pair S p vs"
            using f_vec
            by simp
        next
          assume "x \<in> elect m S p vs"
          thus "x \<in> elect m S q vs"
            using defer_lift_invariance_def defer_m
                  lifted_x monotone_m f_vec
            by metis
        next
          assume "x \<in> reject m S p vs"
          thus "x \<in> reject m S q vs"
            using defer_lift_invariance_def defer_m
                  lifted_x monotone_m f_vec
            by metis
        next
          assume "x \<in> defer m S p vs"
          thus "x \<in> defer m S q vs"
            using defer_lift_invariance_def defer_m
                  lifted_x monotone_m f_vec
            by metis
        qed
    qed
    moreover have
      "\<forall>x \<in> S-A. mod_contains_result m (m \<parallel>\<^sub>\<up> n) S q vs x"
      using A max_agg_rej1 monotone_m monotone_n
            f_profs defer_lift_invariance_def f_vec
      by metis
    ultimately have 11:
      "\<forall>x \<in> S-A. prof_contains_result (m \<parallel>\<^sub>\<up> n) S vs p q x"
      using electoral_mod_defer_elem
      by (simp add: mod_contains_result_def prof_contains_result_def)
    from 10 11
    show ?thesis
      by blast
  qed
  thus "(m \<parallel>\<^sub>\<up> n) S p vs = (m \<parallel>\<^sub>\<up> n) S q vs"
    using compatible disjoint_compatibility_def f_profs f_vec
          eq_alts_in_profs_imp_eq_results max_par_comp_sound 
    by metis
qed

lemma par_comp_rej_card:
  assumes
    compatible: "disjoint_compatibility x y" and
    f_prof: "finite_profile S p" and
    f_vec: "finite_pair_vectors S p vs" and
    reject_sum: "card (reject x S p vs) + card (reject y S p vs) = card S + n"
  shows "card (reject (x \<parallel>\<^sub>\<up> y) S p vs) = n"
proof -
  from compatible obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall>a \<in> A. indep_of_alt x S vs a \<and>
          (\<forall>p vs. finite_profile S p \<and>  finite_pair_vectors S p vs \<longrightarrow> a \<in> reject x S p vs)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt y S vs a \<and>
          (\<forall>p vs. finite_profile S p \<and>  finite_pair_vectors S p vs \<longrightarrow> a \<in> reject y S p vs))"
    using disjoint_compatibility_def f_prof f_vec
    (*by (metis (no_types, lifting))*) sorry
  from f_prof compatible f_vec
  have reject_representation:
    "reject (x \<parallel>\<^sub>\<up> y) S p vs = (reject x S p vs) \<inter> (reject y S p vs)"
    using max_agg_rej_intersect disjoint_compatibility_def
    by blast
  have "electoral_module x \<and> electoral_module y"
    using compatible disjoint_compatibility_def
    by auto
  hence subsets: "(reject x S p vs) \<subseteq> S \<and> (reject y S p vs) \<subseteq> S"
    by (simp add: f_prof reject_in_alts f_vec)
  hence "finite (reject x S p vs) \<and> finite (reject y S p vs)"
    using rev_finite_subset f_prof reject_in_alts
    by auto
  hence 0:
    "card (reject (x \<parallel>\<^sub>\<up> y) S p vs) =
        card S + n -
          card ((reject x S p vs) \<union> (reject y S p vs))"
    using card_Un_Int reject_representation reject_sum
    by fastforce
  have
    "\<forall>a \<in> S. a \<in> (reject x S p vs) \<or> a \<in> (reject y S p vs)"
    using A f_prof f_vec
    by blast
  hence "S = reject x S p vs \<union> reject y S p vs"
    using subsets
    by force
  hence 1: "card ((reject x S p vs) \<union> (reject y S p vs)) = card S"
    by presburger
  from 0 1
  show "card (reject (x \<parallel>\<^sub>\<up> y) S p vs) = n"
    by simp
qed

(*
   Using the max-aggregator for composing two compatible modules in parallel,
   whereof the first one is non-electing and defers exactly one alternative,
   and the second one rejects exactly two alternatives, the composition
   results in an electoral module that eliminates exactly one alternative.
*)
theorem par_comp_elim_one[simp]:
  assumes
    defers_m_1: "defers 1 m" and
    non_elec_m: "non_electing m" and
    rejec_n_2: "rejects 2 n" and
    disj_comp: "disjoint_compatibility m n"
  shows "eliminates 1 (m \<parallel>\<^sub>\<up> n)"
  unfolding eliminates_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_elec_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using rejec_n_2
    by (simp add: rejects_def)
  show "electoral_module (m \<parallel>\<^sub>\<up> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  assume
    min_2_card: "1 < card A" and
    fin_A: "finite A" and
    prof_A: "profile A p" and
    vec_A: "vector_pair A p vs"
  have card_geq_1: "card A \<ge> 1"
    using min_2_card dual_order.strict_trans2 less_imp_le_nat
    by blast
  have module: "electoral_module m"
    using non_elec_m non_electing_def
    by auto
  have elec_card_0: "card (elect m A p vs) = 0"
    using fin_A prof_A non_elec_m card_eq_0_iff non_electing_def vec_A
    by metis
  moreover
  from card_geq_1 have def_card_1:
    "card (defer m A p vs) = 1"
    using defers_m_1 module fin_A prof_A vec_A
    by (simp add: defers_def)
  ultimately have card_reject_m:
    "card (reject m A p vs) = card A - 1"
  proof -
    have "finite A"
      by (simp add: fin_A)
    moreover have
      "well_formed A
        (elect m A p vs, reject m A p vs, defer m A p vs)"
      using fin_A prof_A electoral_module_def module vec_A
      by auto
    ultimately have
      "card A =
        card (elect m A p vs) + card (reject m A p vs) +
          card (defer m A p vs)"
      using result_count
      by blast
    thus ?thesis
      using def_card_1 elec_card_0
      by simp
  qed
  have case1: "card A \<ge> 2"
    using min_2_card
    by auto
  from case1 have card_reject_n:
    "card (reject n A p vs) = 2"
    using fin_A prof_A rejec_n_2 rejects_def vec_A
    by blast
  from card_reject_m card_reject_n
  have
    "card (reject m A p vs) + card (reject n A p vs) =
      card A + 1"
    using card_geq_1
    by linarith
  with disj_comp prof_A fin_A card_reject_m card_reject_n
  show
    "card (reject (m \<parallel>\<^sub>\<up> n) A p vs) = 1"
    using par_comp_rej_card vec_A
    by blast
qed

end
