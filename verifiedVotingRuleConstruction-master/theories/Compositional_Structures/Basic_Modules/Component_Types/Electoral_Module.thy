(*  File:       Electoral_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>

chapter \<open>Component Types\<close>

section \<open>Electoral Module\<close>

theory Electoral_Module
  imports "Social_Choice_Types/Preference_Relation"
          "Social_Choice_Types/Profile"
          "Social_Choice_Types/Result"
          "Social_Choice_Types/Vectors"

begin

text
\<open>Electoral modules are the principal component type of the composable modules
voting framework, as they are a generalization of voting rules in the sense of
social choice functions.
These are only the types used for electoral modules. Further restrictions are
encompassed by the electoral-module predicate.

An electoral module does not need to make final decisions for all alternatives,
but can instead defer the decision for some or all of them to other modules.
Hence, electoral modules partition the received (possibly empty) set of
alternatives into elected, rejected and deferred alternatives. In particular,
any of those sets, e.g., the set of winning (elected) alternatives, may also
be left empty, as long as they collectively still hold all the received
alternatives. Just like a voting rule, an electoral module also receives a
profile which holds the voters’ preferences, which, unlike a voting rule,
consider only the (sub-)set of alternatives that the module receives.\<close>

subsection \<open>Definition\<close>

(*An electoral module maps a set of alternatives and a profile to a result.*)
type_synonym 'a Electoral_Module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Result"
(*type_synonym 'a Electoral_Module = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Result"*)

subsection \<open>Auxiliary Definitions\<close>

(*
   Electoral modules partition a given set of alternatives A into a set of
   elected alternatives e, a set of rejected alternatives r, and a set of
   deferred alternatives d, using a profile.
   e, r, and d partition A.
   Electoral modules can be used as voting rules. They can also be composed
   in multiple structures to create more complex electoral modules.
*)
definition electoral_module :: " 'a Electoral_Module \<Rightarrow> bool" where
  "electoral_module m \<equiv> \<forall>A p vs. finite_profile A p \<and> finite_pair_vectors A vs
    \<longrightarrow> well_formed A (m A p vs)"

lemma electoral_modI:
  "((\<And>A p vs. \<lbrakk> finite_profile A p \<rbrakk> \<Longrightarrow> finite_pair_vectors A vs \<Longrightarrow> well_formed A (m A p vs))
     \<Longrightarrow> electoral_module m)"
  unfolding electoral_module_def
  by auto

(*
   The next three functions take an electoral module and turn it into a
   function only outputting the elect, reject, or defer set respectively.
*)
abbreviation elect ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a set" where
  "elect m A p vs \<equiv> elect_r (m A p vs)"

abbreviation reject ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a set" where
  "reject m A p vs \<equiv> reject_r (m A p vs)"

abbreviation "defer" ::
  "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a set" where
  "defer m A p vs \<equiv> defer_r (m A p vs)"

(*
   "defers n" is true for all electoral modules that defer exactly
   n alternatives, whenever there are n or more alternatives.
*)
definition defers :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "defers n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p vs. (card A \<ge> n \<and> finite_profile A p \<and> finite_pair_vectors A vs) \<longrightarrow>
          card (defer m A p vs) = n)"

(*
   "rejects n" is true for all electoral modules that reject exactly
   n alternatives, whenever there are n or more alternatives.
*)
definition rejects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "rejects n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p vs. (card A \<ge> n \<and> finite_profile A p \<and> finite_pair_vectors A vs) 
      \<longrightarrow> card (reject m A p vs) = n)"

(*
   As opposed to "rejects", "eliminates" allows to stop rejecting if no
   alternatives were to remain.
*)
definition eliminates :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "eliminates n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p vs. (card A > n \<and> finite_profile A p \<and> finite_pair_vectors A vs) 
      \<longrightarrow> card (reject m A p vs) = n)"

(*
   "elects n" is true for all electoral modules that
   elect exactly n alternatives, whenever there are n or more alternatives.
*)
definition elects :: "nat \<Rightarrow> 'a Electoral_Module \<Rightarrow> bool" where
  "elects n m \<equiv>
    electoral_module m \<and>
      (\<forall>A p vs. (card A \<ge> n \<and> finite_profile A p \<and> finite_pair_vectors A vs) 
      \<longrightarrow> card (elect m A p vs) = n)"

(*
(*
   An Electoral module m is rejecting iff at least one alternative gets
   rejected when possible
*)
definition rejecting :: "'a Electoral_Module \<Rightarrow> bool" where
  "
  "rejecting m \<equiv> \<forall>A . card A > 1 \<longrightarrow> (\<exists>n . (n > 0 \<and> rejects n m))"

(*WRONG definition, choose `n > card A` and already it is always true.*)
(*An electoral module m is eliminating iff the following holds*)
(*
   If there is at least one alternative that can be rejected,
   at least one alternative gets rejected.
*)
definition eliminating :: "'a Electoral_Module \<Rightarrow> bool" where
  "eliminating m \<equiv>  \<exists> n . (n > 0 \<and> eliminates n m)"
*)

(*
   An electoral module is independent of an alternative a iff
   a's ranking does not influence the outcome.
*)
definition indep_of_alt :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "indep_of_alt m A a \<equiv>
    electoral_module m \<and> (\<forall>p q vs. equiv_prof_except_a A p q a \<and> finite_pair_vectors A vs
      \<longrightarrow> m A p vs = m A q vs)"

subsection \<open>Equivalence Definitions\<close>

definition prof_contains_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow>
                                    'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_contains_result m A vs p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A \<and> 
    finite_pair_vectors A vs \<and>
    (a \<in> elect m A p vs \<longrightarrow> a \<in> elect m A q vs) \<and>
    (a \<in> reject m A p vs \<longrightarrow> a \<in> reject m A q vs) \<and>
    (a \<in> defer m A p vs \<longrightarrow> a \<in> defer m A q vs)"

definition prof_leq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_leq_result m A vs p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A 
    \<and> finite_pair_vectors A vs \<and>
    (a \<in> reject m A p vs \<longrightarrow> a \<in> reject m A q vs) \<and>
    (a \<in> defer m A p vs \<longrightarrow> a \<notin> elect m A q vs)"

definition prof_geq_result :: "'a Electoral_Module \<Rightarrow> 'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow>
                                  'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "prof_geq_result m A vs p q a \<equiv>
    electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and> a \<in> A 
    \<and> finite_pair_vectors A vs \<and>
    (a \<in> elect m A p vs \<longrightarrow> a \<in> elect m A q vs) \<and>
    (a \<in> defer m A p vs \<longrightarrow> a \<notin> reject m A q vs)"

definition mod_contains_result :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
                                      'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 
                                      'a \<Rightarrow> bool" where
  "mod_contains_result m n A p vs a \<equiv>
    electoral_module m \<and> electoral_module n \<and> finite_profile A p \<and> a \<in> A \<and> 
    finite_pair_vectors A vs \<and>
    (a \<in> elect m A p vs \<longrightarrow> a \<in> elect n A p vs) \<and>
    (a \<in> reject m A p vs \<longrightarrow> a \<in> reject n A p vs) \<and>
    (a \<in> defer m A p vs \<longrightarrow> a \<in> defer n A p vs)"

subsection \<open>Auxiliary Lemmata\<close>

lemma combine_ele_rej_def:
  assumes
    ele: "elect m A p vs = e" and
    rej: "reject m A p vs = r" and
    def: "defer m A p vs = d"
  shows "m A p vs = (e, r, d)"
  using def ele rej
  by auto

lemma par_comp_result_sound:
  assumes
    mod_m: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "well_formed A (m A p vs)"
  using electoral_module_def mod_m f_prof f_vec
  by auto

lemma result_presv_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "(elect m A p vs) \<union> (reject m A p vs) \<union> (defer m A p vs) = A"
proof (safe)
  fix
    x :: "'a"
  assume
    asm: "x \<in> elect m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof f_vec have set_partit:
    "set_equals_partition A (m A p vs)"
    using electoral_module_def
    by auto
  thus "x \<in> A"
    using UnI1 asm fstI set_partit partit
    by (metis (no_types))
next
  fix
    x :: "'a"
  assume
    asm: "x \<in> reject m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof f_vec have set_partit:
    "set_equals_partition A (m A p vs)"
    using electoral_module_def
    by auto
  thus "x \<in> A"
    using UnI1 asm fstI set_partit partit
          sndI subsetD sup_ge2
    by metis
next
  fix
    x :: "'a"
  assume
    asm: "x \<in> defer m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof f_vec have set_partit:
    "set_equals_partition A (m A p vs)"
    using electoral_module_def
    by auto
  thus "x \<in> A"
    using asm set_partit partit sndI subsetD sup_ge2
    by metis
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> A" and
    asm2: "x \<notin> defer m A p vs" and
    asm3: "x \<notin> reject m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from e_mod f_prof f_vec have set_partit:
    "set_equals_partition A (m A p vs)"
    using electoral_module_def
    by auto
  show "x \<in> elect m A p vs"
    using asm1 asm2 asm3 fst_conv partit
          set_partit snd_conv Un_iff
    by metis
qed

lemma result_disj:
  assumes
    module: "electoral_module m" and
    profile: "finite_profile A p" and
    vectors: "finite_pair_vectors A vs"
  shows
    "(elect m A p vs) \<inter> (reject m A p vs) = {} \<and>
        (elect m A p vs) \<inter> (defer m A p vs) = {} \<and>
        (reject m A p vs) \<inter> (defer m A p vs) = {}"
proof (safe, simp_all)
  fix
    x :: "'a"
  assume
    asm1: "x \<in> elect m A p vs" and
    asm2: "x \<in> reject m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from module profile vectors have set_partit:
    "set_equals_partition A (m A p vs)"
    using electoral_module_def
    by auto
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p vectors have wf_A_m:
    "well_formed A (m A p vs)"
    using electoral_module_def
    by metis
  show "False"
    using prod.exhaust_sel DiffE UnCI asm1 asm2
          module profile result_imp_rej wf_A_m
          prof_p set_partit partit
    by (metis (no_types))
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> elect m A p vs" and
    asm2: "x \<in> defer m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  have disj:
    "\<forall>p. \<not> disjoint3 p \<or>
      (\<exists>B C D. p = (B::'a set, C, D) \<and>
        B \<inter> C = {} \<and> B \<inter> D = {} \<and> C \<inter> D = {})"
    by simp
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p vectors have wf_A_m:
    "well_formed A (m A p vs)"
    using electoral_module_def
    by metis
  hence wf_A_m_0:
    "disjoint3 (m A p vs) \<and> set_equals_partition A (m A p vs)"
    by simp
  hence disj3:
    "disjoint3 (m A p vs)"
    by simp
  have set_partit:
    "set_equals_partition A (m A p vs)"
    using wf_A_m_0
    by simp
  from disj3 obtain
    AA :: "'a Result \<Rightarrow> 'a set" and
    AAa :: "'a Result \<Rightarrow> 'a set" and
    AAb :: "'a Result \<Rightarrow> 'a set"
    where
    "m A p vs =
      (AA (m A p vs), AAa (m A p vs), AAb (m A p vs)) \<and>
        AA (m A p vs) \<inter> AAa (m A p vs) = {} \<and>
        AA (m A p vs) \<inter> AAb (m A p vs) = {} \<and>
        AAa (m A p vs) \<inter> AAb (m A p vs) = {}"
    using asm1 asm2 disj
    by metis
  hence "((elect m A p vs) \<inter> (reject m A p vs) = {}) \<and>
          ((elect m A p vs) \<inter> (defer m A p vs) = {}) \<and>
          ((reject m A p vs) \<inter> (defer m A p vs) = {})"
    using disj3 eq_snd_iff fstI
    by metis
  thus "False"
    using asm1 asm2 module profile wf_A_m prof_p
          set_partit partit disjoint_iff_not_equal
    by (metis (no_types))
next
  fix
    x :: "'a"
  assume
    asm1: "x \<in> reject m A p vs" and
    asm2: "x \<in> defer m A p vs"
  have partit:
    "\<forall>A p.
      \<not> set_equals_partition (A::'a set) p \<or>
        (\<exists>B C D E. A = B \<and> p = (C, D, E) \<and> C \<union> D \<union> E = B)"
    by simp
  from module profile vectors have set_partit:
    "set_equals_partition A (m A p vs)"
    using electoral_module_def
    by auto
  from profile have prof_p:
    "finite A \<and> profile A p"
    by simp
  from module prof_p vectors have wf_A_m:
    "well_formed A (m A p vs)"
    using electoral_module_def
    by metis
  show "False"
    using prod.exhaust_sel DiffE UnCI asm1 asm2
          module profile result_imp_rej wf_A_m
          prof_p set_partit partit
    by (metis (no_types))
qed

lemma elect_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "elect m A p vs \<subseteq> A"
  using le_supI1 e_mod f_prof f_vec result_presv_alts sup_ge1
  by metis

lemma reject_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "reject m A p vs \<subseteq> A"
  using le_supI1 e_mod f_prof f_vec result_presv_alts sup_ge2
  by fastforce

lemma defer_in_alts:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "defer m A p vs \<subseteq> A"
  using e_mod f_prof f_vec result_presv_alts
  by blast

lemma def_presv_fin_prof:
  assumes module:  "electoral_module m" and
          f_prof: "finite_profile A p" and
          f_vec: "finite_pair_vectors A vs"
  shows
    "let new_A = defer m A p vs in
        finite_profile new_A (limit_profile new_A p)"
  using defer_in_alts infinite_super
        limit_profile_sound module f_prof f_vec
  by metis

lemma def_presv_fin_vector_pair:
  assumes module:  "electoral_module m" and
          f_prof: "finite_profile A p" and
          f_vec: "finite_pair_vectors A vs"
  shows
    "let new_A = defer m A p vs in
        finite_pair_vectors new_A (limit_pair_vectors new_A vs)"
proof-
  have 0:"let new_A = defer m A p vs in finite new_A"
    by (metis def_presv_fin_prof f_prof f_vec module) 
  have 1:"let new_A = defer m A p vs in vector_pair new_A (limit_pair_vectors new_A vs)"
    by (meson defer_in_alts f_prof f_vec limit_pair_vectors_sound module) 
  show "let new_A = defer m A p vs in
        finite_pair_vectors new_A (limit_pair_vectors new_A vs)" 
    using 0 1 by simp
qed

(*
   An electoral module can never reject, defer or elect more than
   |A| alternatives.
*)
lemma upper_card_bounds_for_result:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "vector_pair A vs"
  shows
    "card (elect m A p vs) \<le> card A \<and>
      card (reject m A p vs) \<le> card A \<and>
      card (defer m A p vs) \<le> card A "
  by (simp add: card_mono defer_in_alts elect_in_alts
                e_mod f_prof f_vec reject_in_alts)

lemma reject_not_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "reject m A p vs = A - (elect m A p vs) - (defer m A p vs)"
proof -
  from e_mod f_prof f_vec have 0: "well_formed A (m A p vs)"
    by (simp add: electoral_module_def)
  with e_mod f_prof f_vec
    have "(elect m A p vs) \<union> (reject m A p vs) \<union> (defer m A p vs) = A"
      using result_presv_alts 
      by blast
    moreover from 0 have
      "(elect m A p vs) \<inter> (reject m A p vs) = {} \<and>
          (reject m A p vs) \<inter> (defer m A p vs) = {}"
    using e_mod f_prof f_vec result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma elec_and_def_not_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "elect m A p vs \<union> defer m A p vs = A - (reject m A p vs)"
proof -
  from e_mod f_prof f_vec have 0: "well_formed A (m A p vs)"
    by (simp add: electoral_module_def)
  hence
    "disjoint3 (m A p vs) \<and> set_equals_partition A (m A p vs)"
    by simp
  with e_mod f_prof f_vec
  have "(elect m A p vs) \<union> (reject m A p vs) \<union> (defer m A p vs) = A"
    using e_mod f_prof result_presv_alts
    by blast
  moreover from 0 have
    "(elect m A p vs) \<inter> (reject m A p vs) = {} \<and>
        (reject m A p vs) \<inter> (defer m A p vs) = {}"
    using e_mod f_prof f_vec result_disj
    by blast
  ultimately show ?thesis
    by blast
qed

lemma defer_not_elec_or_rej:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "defer m A p vs = A - (elect m A p vs) - (reject m A p vs)"
proof -
  from e_mod f_prof f_vec have 0: "well_formed A (m A p vs)"
    by (simp add: electoral_module_def)
  hence "(elect m A p vs) \<union> (reject m A p vs) \<union> (defer m A p vs) = A"
    using e_mod f_prof f_vec result_presv_alts 
    by blast
  moreover from 0 have
    "(elect m A p vs) \<inter> (defer m A p vs) = {} \<and>
        (reject m A p vs) \<inter> (defer m A p vs) = {}"
      using e_mod f_prof f_vec result_disj
      by blast
  ultimately show ?thesis
    by blast
qed

lemma electoral_mod_defer_elem:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs" and
    alternative: "x \<in> A" and
    not_elected: "x \<notin> elect m A p vs" and
    not_rejected: "x \<notin> reject m A p vs"
  shows "x \<in> defer m A p vs"
  using DiffI e_mod f_prof f_vec alternative
        not_elected not_rejected
        reject_not_elec_or_def
  by metis

lemma mod_contains_result_comm:
  assumes "mod_contains_result m n A p vs a"
  shows "mod_contains_result n m A p vs a"
  unfolding mod_contains_result_def
proof (safe)
  show "electoral_module n"
    using assms mod_contains_result_def
    by metis
next
  show "electoral_module m"
    using assms mod_contains_result_def
    by metis
next
  show "finite A"
    using assms mod_contains_result_def
    by metis
next
  show "profile A p"
    using assms mod_contains_result_def
    by metis
next
  show "a \<in> A"
    using assms mod_contains_result_def
    by metis
next
  show "vector_pair A vs" 
    using assms mod_contains_result_def
    by metis
next
  show "finite A"
    using assms mod_contains_result_def
    by metis
next
  assume "a \<in> elect n A p vs"
  thus "a \<in> elect m A p vs"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
next
  assume "a \<in> reject n A p vs"
  thus "a \<in> reject m A p vs"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
next
  assume "a \<in> defer n A p vs"
  thus "a \<in> defer m A p vs"
    using IntI assms electoral_mod_defer_elem empty_iff
          mod_contains_result_def result_disj
    by (metis (mono_tags, lifting))
qed

lemma not_rej_imp_elec_or_def:
  assumes
    e_mod: "electoral_module m" and
    f_prof: "finite_profile A p" and
    alternative: "x \<in> A" and
    not_rejected: "x \<notin> reject m A p vs" and
    f_vec: "finite_pair_vectors A vs"
  shows "x \<in> elect m A p vs \<or> x \<in> defer m A p vs"
  using alternative electoral_mod_defer_elem
        e_mod not_rejected f_prof f_vec
  by metis

lemma single_elim_imp_red_def_set:
  assumes
    eliminating: "eliminates 1 m" and
    leftover_alternatives: "card A > 1" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "defer m A p vs \<subset> A"
  using Diff_eq_empty_iff Diff_subset card_eq_0_iff defer_in_alts
        eliminates_def eliminating eq_iff leftover_alternatives
        not_one_le_zero f_prof psubsetI reject_not_elec_or_def f_vec
  by metis

lemma eq_alts_in_profs_imp_eq_results:
  assumes
    eq: "\<forall>a \<in> A. prof_contains_result m A vs p q a" and
    (*for empty A*)
    input: "electoral_module m \<and> finite_profile A p \<and> finite_profile A q \<and>
    vector_pair A vs"
  shows "m A p vs = m A q vs"
proof -
  have "\<forall>a \<in> elect m A p vs. a \<in> elect m A q vs"
    using elect_in_alts eq prof_contains_result_def input in_mono
    by metis
  moreover have "\<forall>a \<in> elect m A q vs. a \<in> elect m A p vs"
    using contra_subsetD disjoint_iff_not_equal elect_in_alts
          electoral_mod_defer_elem eq prof_contains_result_def input
          result_disj
  proof -
    fix aa :: 'a
    have "\<forall> A Aa. (Aa::'a set) \<inter> A = {} \<or> Aa \<noteq> {}"
      by blast
    moreover have f1: "elect m A q vs - A = {}"
      using Diff_eq_empty_iff elect_in_alts input
      by metis
    moreover have f2: "defer m A q vs \<inter> elect m A q vs = {}"
      using disjoint_iff_not_equal input result_disj
      by (metis (no_types))
    moreover have f3: "reject m A q vs \<inter> elect m A q vs = {}"
      using disjoint_iff_not_equal input result_disj
      by (metis (no_types))
    ultimately have f4:
      "(\<exists> Aa. Aa \<inter> elect m A q vs = {} \<and> aa \<in> Aa) \<or>
          aa \<notin> elect m A q vs \<or> aa \<in> elect m A p vs"
      using DiffI electoral_mod_defer_elem eq prof_contains_result_def
      by (metis (no_types))
    hence f5:
      "aa \<notin> elect m A q vs \<or> aa \<in> elect m A p vs"
      using disjoint_iff_not_equal
      by metis
    from f1 f2 f3
    show ?thesis
      using Diff_iff Int_iff empty_iff eq not_rej_imp_elec_or_def
            prof_contains_result_def
      by metis
  qed
  moreover have
    "\<forall>a \<in> reject m A p vs. a \<in> reject m A q vs"
    using reject_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have
    "\<forall>a \<in> reject m A q vs. a \<in> reject m A p vs"
  proof -
    {
      fix aa :: 'a
      have ff1:
        "\<forall> f. reject f A q vs \<subseteq> A \<or> \<not> electoral_module f"
        using input reject_in_alts
        by metis
      have ff2:
        "\<forall> f. reject f A q vs \<inter> defer f A q vs = {} \<or> \<not> electoral_module f"
        using input result_disj
        by metis
      have "electoral_module m \<and> profile A p \<and> finite_profile A q"
        using input
        by blast
      hence ff3:
        "elect m A q vs \<inter> reject m A q vs = {} \<and> elect m A q vs \<inter> defer m A q vs = {} \<and>
          reject m A q vs \<inter> defer m A q vs = {}"
        using input
        by (simp add: result_disj)
      hence
        "aa \<in> elect m A q vs \<longrightarrow> aa \<notin> reject m A q vs \<or> aa \<in> reject m A p vs"
        using disjoint_iff_not_equal ff3
        by metis
      hence "aa \<notin> reject m A q vs \<or> aa \<in> reject m A p vs"
        using ff2 ff1 electoral_mod_defer_elem eq
              input prof_contains_result_def
        by fastforce
    }
    thus ?thesis
      by metis
  qed
  moreover have "\<forall>a \<in> defer m A p vs. a \<in> defer m A q vs"
    using defer_in_alts eq prof_contains_result_def input in_mono
    by fastforce
  moreover have "\<forall>a \<in> defer m A q vs. a \<in> defer m A p vs"
  proof (safe)
    fix a :: "'a"
    assume "a \<in> defer m A q vs"
    thus "a \<in> defer m A p vs"
      using calculation defer_not_elec_or_rej
            input subsetI subset_antisym
      by (metis)
  qed
  ultimately show ?thesis
    using prod.collapse subsetI subset_antisym 
    by (metis)
qed

lemma eq_def_and_elect_imp_eq:
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p" and
    "finite_profile A q" and
    "finite_pair_vectors A vs" and
    "elect m A p vs = elect n A q vs" and
    "defer m A p vs = defer n A q vs"
  shows "m A p vs = n A q vs"
proof -
  have disj_m:
    "disjoint3 (m A p vs)"
    using assms(1) assms(3) assms(5) electoral_module_def
    by auto
  have disj_n:
    "disjoint3 (n A q vs)"
    using assms(2) assms(4) assms(5) electoral_module_def
    by auto
  have set_partit_m:
    "set_equals_partition A ((elect m A p vs), (reject m A p vs), (defer m A p vs))"
    using assms(1) assms(3) assms(5) electoral_module_def
    by auto
  moreover have
    "disjoint3 ((elect m A p vs),(reject m A p vs),(defer m A p vs))"
    using disj_m prod.collapse
    by metis
  have set_partit_n:
    "set_equals_partition A ((elect n A q vs), (reject n A q vs), (defer n A q vs))"
    using assms(2) assms(4) assms(5) electoral_module_def
    by auto
  moreover have
    "disjoint3 ((elect n A q vs),(reject n A q vs),(defer n A q vs))"
    using disj_n prod.collapse
    by metis
  have reject_p:
    "reject m A p vs = A - ((elect m A p vs) \<union> (defer m A p vs))"
    using assms(1) assms(3) assms(5) combine_ele_rej_def
          electoral_module_def result_imp_rej
    by metis
  have reject_q:
    "reject n A q vs = A - ((elect n A q vs) \<union> (defer n A q vs))"
    using assms(2) assms(4) assms(5) combine_ele_rej_def
          electoral_module_def result_imp_rej
    by metis
  from reject_p reject_q
  show ?thesis
    by (simp add: assms(6) assms(7) prod_eqI)
qed

subsection \<open>Non-Blocking\<close>

(*
   An electoral module is non-blocking iff
   this module never rejects all alternatives.
*)
definition non_blocking :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_blocking m \<equiv>
    electoral_module m \<and>
      (\<forall>A p vs.
          ((A \<noteq> {} \<and> finite_profile A p \<and> finite_pair_vectors A vs) \<longrightarrow> reject m A p vs \<noteq> A))"

subsection \<open>Electing\<close>

(*
   An electoral module is electing iff
   it always elects at least one alternative.
*)
definition electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "electing m \<equiv>
    electoral_module m \<and>
      (\<forall>A p vs. (A \<noteq> {} \<and> finite_profile A p \<and> finite_pair_vectors A vs) \<longrightarrow> elect m A p vs \<noteq> {})"

lemma electing_for_only_alt:
  assumes
    one_alt: "card A = 1" and
    electing: "electing m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "elect m A p vs = A"
proof (safe)
  fix x :: "'a"
  assume
    electX: "x \<in> elect m A p vs"
  have
    "\<not> electoral_module m \<or> elect m A p vs \<subseteq> A"
    using elect_in_alts f_prof f_vec
    by (simp add: elect_in_alts)
  with electing have "elect m A p vs \<subseteq> A"
    unfolding electing_def
    by metis
  with electX show "x \<in> A"
    by auto
next
  fix x :: "'a"
  assume "x \<in> A"
  with electing f_prof f_vec one_alt
  show "x \<in> elect m A p vs"
    unfolding electing_def
    using One_nat_def Suc_leI card_seteq
          card_gt_0_iff elect_in_alts
          infinite_super
    by metis
qed

theorem electing_imp_non_blocking:
  assumes electing: "electing m"
  shows "non_blocking m"
  unfolding non_blocking_def
proof (safe)
  from electing
  show "electoral_module m"
    using electing_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    x :: "'a" 
  assume
    finA: "finite A" and
    profA: "profile A p" and
    vecA: "vector_pair A vs" and
    rejA: "reject m A p vs = A" and
    xInA: "x \<in> A"
  from electing have
    "electoral_module m \<and>
      (\<forall>A rs vs. A = {} \<or> infinite A \<or>
        \<not> profile A rs \<or> \<not> finite_pair_vectors A vs \<or> elect m A rs vs \<noteq> {})"
    unfolding electing_def
    by metis
  hence f1: "A = {}"
    using Diff_cancel Un_empty
          elec_and_def_not_rej
          finA profA rejA vecA
    by (metis (no_types))
  from  xInA
  have "x \<in> A"
    by metis
  with f1 show "x \<in> {}"
    by metis
qed

subsection \<open>Properties\<close>

(*
   An electoral module is non-electing iff
   it never elects an alternative.
*)
definition non_electing :: "'a Electoral_Module \<Rightarrow> bool" where
  "non_electing m \<equiv>
    electoral_module m \<and> 
    (\<forall>A p vs. finite_profile A p \<and> finite_pair_vectors A vs \<longrightarrow> elect m A p vs = {})"

lemma single_elim_decr_def_card:
  assumes
    rejecting: "rejects 1 m" and
    not_empty: "A \<noteq> {}" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "card (defer m A p vs) = card A - 1"
proof -
  have "rejects 1 m"
    using One_nat_def rejecting
    by metis
  moreover have
    "electoral_module m \<and>
      (\<forall> A rs vs. infinite A \<or> \<not> profile A rs \<or> 
      \<not> finite_pair_vectors A vs \<or> elect m A rs vs = {})"
    using non_electing
    unfolding non_electing_def
    by metis
  moreover from this have
    "reject m A p vs \<subseteq> A"
    using f_prof f_vec reject_in_alts
    by metis
  ultimately show ?thesis
    using f_prof f_vec not_empty
    by (simp add: Suc_leI card_Diff_subset card_gt_0_iff
                  defer_not_elec_or_rej finite_subset
                  rejects_def)
qed

lemma single_elim_decr_def_card2:
  assumes
    eliminating: "eliminates 1 m" and
    not_empty: "card A > 1" and
    non_electing: "non_electing m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "card (defer m A p vs) = card A - 1"
proof -
  have
    "\<forall>f. (non_electing f \<or>
            (\<exists>A rs vs. ({}::'a set) \<noteq> elect f A rs vs \<and> profile A rs \<and> vector_pair A vs \<and> finite A) \<or>
            \<not> electoral_module f) \<and>
          ((\<forall>A rs vs. {} = elect f A rs vs \<or> \<not> profile A rs \<or> \<not> vector_pair A vs \<or> infinite A) \<and>
            electoral_module f \<or> \<not> non_electing f)"
    using non_electing_def
    by metis
  moreover from this have
    "electoral_module m \<and>
      (\<forall>A rs vs. infinite A \<or> \<not> profile A rs \<or> \<not> vector_pair A vs \<or> elect m A rs vs = {})"
    using non_electing
    by (metis (no_types))
  moreover from this have
    "reject m A p vs \<subseteq> A"
    using f_prof f_vec reject_in_alts
    by metis
  moreover have "1 < card A"
    using not_empty
    by presburger
  moreover have "eliminates 1 m"
    using One_nat_def eliminating
    by presburger
  moreover have "eliminates 1 m"
    using eliminating
    by force
  ultimately show ?thesis
    using f_prof f_vec
    by (simp add: card_Diff_subset defer_not_elec_or_rej
                  eliminates_def finite_subset)
qed

(*
   An electoral module is defer-deciding iff
   this module chooses exactly 1 alternative to defer and
   rejects any other alternative.
   Note that `rejects n-1 m` can be omitted due to the
   well-formedness property.
*)
definition defer_deciding :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_deciding m \<equiv>
    electoral_module m \<and> non_electing m \<and> defers 1 m"

(*
   An electoral module decrements iff
   this module rejects at least one alternative whenever possible (|A|>1).
*)
definition decrementing :: "'a Electoral_Module \<Rightarrow> bool" where
  "decrementing m \<equiv>
    electoral_module m \<and> (
      \<forall> A p vs. finite_profile A p \<and> finite_pair_vectors A vs \<longrightarrow>
          (card A > 1 \<longrightarrow> card (reject m A p vs) \<ge> 1))"

definition defer_condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w vs. condorcet_winner A p w \<and> finite A \<and> vector_pair A vs \<longrightarrow>
      (m A p vs =
        ({},
        A - (defer m A p vs),
        {d \<in> A. condorcet_winner A p d})))"

definition condorcet_compatibility :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_compatibility m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w vs. condorcet_winner A p w \<and> finite A \<longrightarrow>
      (w \<notin> reject m A p vs \<and>
        (\<forall>l. \<not>condorcet_winner A p l \<longrightarrow> l \<notin> elect m A p vs) \<and>
          (w \<in> elect m A p vs \<longrightarrow>
            (\<forall>l. \<not>condorcet_winner A p l \<longrightarrow> l \<in> reject m A p vs))))"

(*
   An electoral module is defer-monotone iff,
   when a deferred alternative is lifted, this alternative remains deferred.
*)
definition defer_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q w vs.
          (finite A \<and> w \<in> defer m A p vs \<and> finite_pair_vectors A vs \<and> lifted A p q w) 
          \<longrightarrow> w \<in> defer m A q vs)"

(*
   An electoral module is defer-lift-invariant iff
   lifting a deferred alternative does not affect the outcome.
*)
definition defer_lift_invariance :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_lift_invariance m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q a vs.
          (a \<in> (defer m A p vs) \<and> finite_pair_vectors A vs \<and> lifted A p q a) 
              \<longrightarrow> m A p vs = m A q vs)"

(*
   Two electoral modules are disjoint-compatible if they only make decisions
   over disjoint sets of alternatives. Electoral modules reject alternatives
   for which they make no decision.
*)
definition disjoint_compatibility :: "'a Electoral_Module \<Rightarrow>
                                         'a Electoral_Module \<Rightarrow> bool" where
  "disjoint_compatibility m n \<equiv>
    electoral_module m \<and> electoral_module n \<and>
        (\<forall>S. finite S  \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> A. indep_of_alt m S a \<and>
              (\<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject m S p vs)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
              (\<forall>p vs. finite_profile S p  \<and> vector_pair S vs\<longrightarrow> a \<in> reject n S p vs))))"

(*
   Lifting an elected alternative a from an invariant-monotone
   electoral module either does not change the elect set, or
   makes a the only elected alternative.
*)
definition invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "invariant_monotonicity m \<equiv>
    electoral_module m \<and>
        (\<forall>A p q a vs. (a \<in> elect m A p vs \<and> lifted A p q a) \<longrightarrow>
          (elect m A q vs = elect m A p vs \<or> elect m A q vs = {a}))"

(*
   Lifting a deferred alternative a from a defer-invariant-monotone
   electoral module either does not change the defer set, or
   makes a the only deferred alternative.
*)
definition defer_invariant_monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "defer_invariant_monotonicity m \<equiv>
    electoral_module m \<and> non_electing m \<and>
        (\<forall>A p q a vs. (a \<in> defer m A p vs \<and> lifted A p q a) \<longrightarrow>
          (defer m A q vs = defer m A p vs \<or> defer m A q vs = {a}))"

subsection \<open>Inference Rules\<close>
(*
lemma ccomp_and_dd_imp_def_only_winner:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m" and
          winner: "condorcet_winner A p w" and
          f_vec: "finite_pair_vectors A p vs"
  shows "defer m A p vs = {w}"
proof (rule ccontr)
  assume not_w: "defer m A p vs \<noteq> {w}"
  from dd have def_1:
    "defers 1 m"
    using defer_deciding_def
    by metis
  hence c_win:
    "finite_profile A p \<and>  w \<in> A \<and> (\<forall>x \<in> A - {w} . wins w p x)"
    using winner
    by simp
  hence "card (defer m A p vs) = 1"
    using One_nat_def Suc_leI card_gt_0_iff
          def_1 defers_def equals0D
    by metis
  hence 0: "\<exists>x \<in> A . defer m A p vs = {x}"
    using card_1_singletonE dd defer_deciding_def
          defer_in_alts insert_subset c_win f_vec
    by metis
  with not_w have "\<exists>l \<in> A . l \<noteq> w \<and> defer m A p vs = {l}"
    by metis
  hence not_in_defer: "w \<notin> defer m A p vs"
    by auto
  have "non_electing m"
    using dd defer_deciding_def
    by metis
  hence not_in_elect: "w \<notin> elect m A p vs"
    using c_win equals0D non_electing_def f_vec
    by metis
  from not_in_defer not_in_elect f_vec have one_side:
    "w \<in> reject m A p vs"
    using ccomp condorcet_compatibility_def c_win
          electoral_mod_defer_elem
    by metis
  from ccomp f_vec have other_side: "w \<notin> reject m A p vs"
    using condorcet_compatibility_def c_win winner 
    by (metis (no_types, hide_lams))
  thus False
    by (simp add: one_side)
qed

theorem ccomp_and_dd_imp_dcc[simp]:
  assumes ccomp: "condorcet_compatibility m" and
          dd: "defer_deciding m"
  shows "defer_condorcet_consistency m"
proof (unfold defer_condorcet_consistency_def, auto)
  show "electoral_module m"
    using dd defer_deciding_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    w :: "'a"
  assume
    prof_A: "profile A p" and
    w_in_A: "w \<in> A" and
    finiteness: "finite A" and
    vec_A: "finite_pair_vectors A p vs" and
    assm: "\<forall>x\<in>A - {w}.
          card {i. i < length p \<and> (w, x) \<in> (p!i)} <
            card {i. i < length p \<and> (x, w) \<in> (p!i)}"
  have winner: "condorcet_winner A p w"
    using assm finiteness prof_A w_in_A
    by simp
  hence
    "m A p vs =
      ({},
        A - defer m A p vs,
        {d \<in> A. condorcet_winner A p d})"
  proof -
    (*Elect*)
    from dd have 0:
      "elect m A p vs = {}"
      using defer_deciding_def non_electing_def
            winner vec_A
      by fastforce
    (*Defers*)
    from dd ccomp have 1: "defer m A p vs = {w}"
      using ccomp_and_dd_imp_def_only_winner winner vec_A
      by metis    
    (*Reject*)
    from 0 1 have 2: "reject m A p vs = A - defer m A p vs"
      using Diff_empty dd defer_deciding_def
            reject_not_elec_or_def winner vec_A
      by fastforce
    from 0 1 2 have 3: "m A p vs = ({}, A - defer m A p vs, {w})"
      using combine_ele_rej_def
      by metis
    have "{w} = {d \<in> A. condorcet_winner A p d}"
      using cond_winner_unique3 winner
      by metis
    thus ?thesis
      using "3"
      by auto
  qed
  hence
    "m A p vs =
      ({},
        A - defer m A p vs,
        {d \<in> A. \<forall>x\<in>A - {d}. wins d p x})"
    using finiteness prof_A winner Collect_cong
    by auto
  hence
    "m A p vs =
        ({},
          A - defer m A p vs,
          {d \<in> A. \<forall>x\<in>A - {d}.
            prefer_count p x d < prefer_count p d x})"
    by simp
  hence
    "m A p vs =
        ({},
          A - defer m A p vs,
          {d \<in> A. \<forall>x\<in>A - {d}.
            card {i. i < length p \<and> (let r = (p!i) in (d \<preceq>\<^sub>r x))} <
                card {i. i < length p \<and> (let r = (p!i) in (x \<preceq>\<^sub>r d))}})"
    by simp
  thus
    "m A p vs =
        ({},
          A - defer m A p vs,
          {d \<in> A. \<forall>x\<in>A - {d}.
            card {i. i < length p \<and> (d, x) \<in> (p!i)} <
              card {i. i < length p \<and> (x, d) \<in> (p!i)}})"
    by simp
qed
*)
(*If m and n are disjoint compatible, so are n and m.*)
(*
theorem disj_compat_comm[simp]:
  assumes compatible: "disjoint_compatibility m n"
  shows "disjoint_compatibility n m"
proof -
  have
    "\<forall>S vs. finite S \<longrightarrow>
        (\<exists>A \<subseteq> S.
          (\<forall>a \<in> A. indep_of_alt n S vs a \<and>
            (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject n S p vs)) \<and>
          (\<forall>a \<in> S-A. indep_of_alt m S vs a \<and>
            (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject m S p vs)))"
  proof
    fix
      S :: "'a set" and
      vs :: "'a Pair_Vectors"
    obtain A where old_A:
      "finite S \<longrightarrow>
          (A \<subseteq> S \<and>
            (\<forall>a \<in> A. indep_of_alt m S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject m S p vs)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt n S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject n S p vs)))"
      using compatible disjoint_compatibility_def
      by fastforce
    hence
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> S-A. indep_of_alt n S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject n S p vs)) \<and>
            (\<forall>a \<in> A. indep_of_alt m S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject m S p vs)))"
      by auto
    hence
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> S-A. indep_of_alt n S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject n S p vs)) \<and>
            (\<forall>a \<in> S-(S-A). indep_of_alt m S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject m S p vs)))"
      using double_diff order_refl
      by metis
    thus
      "finite S \<longrightarrow>
          (\<exists>A \<subseteq> S.
            (\<forall>a \<in> A. indep_of_alt n S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject n S p vs)) \<and>
            (\<forall>a \<in> S-A. indep_of_alt m S vs a \<and>
              (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S p vs \<longrightarrow> a \<in> reject m S p vs)))"
      by fastforce
  qed
  moreover have "electoral_module m \<and> electoral_module n"
    using compatible disjoint_compatibility_def
    by auto
  ultimately show ?thesis
    by (simp add: disjoint_compatibility_def)
qed
*)
(*
   Every electoral module which is defer-lift-invariant is
   also defer-monotone.
*)
theorem dl_inv_imp_def_mono[simp]:
  assumes "defer_lift_invariance m"
  shows "defer_monotonicity m"
  using assms defer_monotonicity_def defer_lift_invariance_def
  by fastforce

subsection \<open>Social Choice Properties\<close>

subsubsection \<open>Condorcet Consistency\<close>

definition condorcet_consistency :: "'a Electoral_Module \<Rightarrow> bool" where
  "condorcet_consistency m \<equiv>
    electoral_module m \<and>
    (\<forall> A p w vs. condorcet_winner A p w \<and> vector_pair A vs \<longrightarrow>
      (m A p vs =
        ({e \<in> A. condorcet_winner A p e},
          A - (elect m A p vs),
          {})))"

lemma condorcet_consistency2:
  "condorcet_consistency m \<longleftrightarrow>
      electoral_module m \<and>
        (\<forall> A p w vs. condorcet_winner A p w \<and> vector_pair A vs \<longrightarrow>
            (m A p vs =
              ({w}, A - (elect m A p vs), {})))"
proof (safe)
  assume "condorcet_consistency m"
  thus "electoral_module m"
    using condorcet_consistency_def
    by metis
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    w :: "'a"
  assume
    cc: "condorcet_consistency m" and
    cwin: "condorcet_winner A p w" and
    vec_A: "vector_pair A vs"
  show
    "m A p vs = ({w}, A - elect m A p vs, {})"
    using cond_winner_unique3 condorcet_consistency_def cc cwin vec_A
    by (smt (verit)) 
next
  assume
    e_mod: "electoral_module m" and
    cwin:
    "\<forall>A p w vs. condorcet_winner A p w \<and> vector_pair A vs \<longrightarrow>
      m A p vs = ({w}, A - elect m A p vs, {})"
  have
    "\<forall>f. condorcet_consistency f =
      (electoral_module f \<and>
        (\<forall>A rs a vs. \<not> condorcet_winner A rs (a::'a) \<or> \<not> vector_pair A vs \<or>
          f A rs vs = ({a \<in> A. condorcet_winner A rs a},
                    A - elect f A rs vs, {})))"
    unfolding condorcet_consistency_def
    by blast
  moreover have
    "\<forall>A rs a. \<not> condorcet_winner A rs (a::'a) \<or>
        {a \<in> A. condorcet_winner A rs a} = {a}"
    using cond_winner_unique3
    by (metis (full_types))
  ultimately show
    "condorcet_consistency m"
    unfolding condorcet_consistency_def
    using e_mod cwin
    by (metis (no_types, lifting)) 
qed

subsubsection \<open>(Weak) Monotonicity\<close>

(*
   An electoral module is monotone iff
   when an elected alternative is lifted, this alternative remains elected.
*)
definition monotonicity :: "'a Electoral_Module \<Rightarrow> bool" where
  "monotonicity m \<equiv>
    electoral_module m \<and>
      (\<forall>A p q w vs.
          (finite A \<and> finite_pair_vectors A vs \<and> w \<in> elect m A p vs \<and> lifted A p q w) 
            \<longrightarrow> w \<in> elect m A q vs)"

subsubsection \<open>Homogeneity\<close>

fun times :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "times n l = concat (replicate n l)"

definition homogeneity :: "'a Electoral_Module \<Rightarrow> bool" where
"homogeneity m \<equiv>
  electoral_module m \<and>
    (\<forall> A p n vs.
      (finite_profile A p \<and> finite_pair_vectors A vs \<and> n > 0 \<longrightarrow>
          (m A p vs = m A (times n p) (times n vs))))"

subsubsection \<open>Reinforcement\<close>

definition reinforcement:: "'a Electoral_Module \<Rightarrow> bool" where
"reinforcement m \<equiv> electoral_module m \<and> 
(\<forall> A p1 p2 vs1 vs2. (finite_profile A p1 \<and> finite_pair_vectors A vs1 \<and> finite_profile A p2 
\<and> finite_pair_vectors A vs2 \<longrightarrow> 
(elect m A p1 vs1) \<inter> (elect m A p2 vs2) \<noteq> {} \<longrightarrow>
((elect m A p1 vs1) \<inter> (elect m A p2 vs2) = elect m A (p1 @ p2) (vs1@vs2))))"

definition reinforcement_defer:: "'a Electoral_Module \<Rightarrow> bool" where
"reinforcement_defer m \<equiv> electoral_module m \<and> 
(\<forall> A p1 p2 vs1 vs2. (finite_profile A p1 \<and> finite_pair_vectors A vs1 \<and> finite_profile A p2 
\<and> finite_pair_vectors A vs2 \<longrightarrow>
(defer m A p1 vs1) \<inter> (defer m A p2 vs2) \<noteq> {} \<longrightarrow>
((defer m A p1 vs1) \<inter> (defer m A p2 vs2) = defer m A (p1 @ p2) (vs1@vs2))))"

end
