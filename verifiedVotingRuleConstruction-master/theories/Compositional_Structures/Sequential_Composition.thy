(*  File:       Sequential_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Sequential Composition\<close>

theory Sequential_Composition
  imports "Basic_Modules/Component_Types/Electoral_Module"
begin

text
\<open>The sequential composition creates a new electoral module from
two electoral modules. In a sequential composition, the second
electoral module makes decisions over alternatives deferred by
the first electoral module.\<close>

subsection \<open>Definition\<close>

fun sequential_composition :: "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Electoral_Module" where
  "sequential_composition m n A p vs =
    (let new_A = defer m A p vs;
        new_p = limit_profile new_A p;
        new_vs =  limit_pair_vectors new_A vs in (
                  (elect m A p vs) \<union> (elect n new_A new_p new_vs),
                  (reject m A p vs) \<union> (reject n new_A new_p new_vs),
                  defer n new_A new_p new_vs))"

abbreviation sequence ::
  "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow> 'a Electoral_Module"
     (infix "\<triangleright>" 50) where
  "m \<triangleright> n == sequential_composition m n"

lemma seq_comp_presv_disj:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p" and
          f_vec: "finite_pair_vectors A vs"
  shows "disjoint3 ((m \<triangleright> n) A p vs)"
proof -
  let ?new_A = "defer m A p vs"
  let ?new_p = "limit_profile ?new_A p"
  let ?new_vs = "limit_pair_vectors ?new_A vs"
  have fin_def: "finite (defer m A p vs)"
    using def_presv_fin_prof f_prof module_m f_vec
    by metis
  have prof_def_lim:
    "profile (defer m A p vs) (limit_profile (defer m A p vs) p)"
    using def_presv_fin_prof f_prof module_m f_vec
    by metis
  have vec_def_lim:
    "vector_pair (defer m A p vs) (limit_pair_vectors (defer m A p vs) vs)"
    using f_prof module_m f_vec def_presv_fin_vector_pair
    by metis
  have defer_in_A:
    "\<forall>prof f a A vs.
      (profile A prof \<and> finite A \<and> vector_pair A vs \<and> electoral_module f \<and>
        (a::'a) \<in> defer f A prof vs) \<longrightarrow>
          a \<in> A"
    using UnCI result_presv_alts
    by (metis (mono_tags))
  from module_m f_prof f_vec
  have disjoint_m: "disjoint3 (m A p vs)"
    using electoral_module_def well_formed.simps
    by blast
  from module_m module_n def_presv_fin_prof f_prof
  have disjoint_n:
    "(disjoint3 (n ?new_A ?new_p ?new_vs))"
    using electoral_module_def well_formed.simps
    by (metis def_presv_fin_vector_pair f_vec)
  have disj_n:
    "elect m A p vs \<inter> reject m A p vs = {} \<and>
      elect m A p vs \<inter> defer m A p vs = {} \<and>
      reject m A p vs \<inter> defer m A p vs = {}"
    using f_prof module_m f_vec
    by (simp add: result_disj)
  from f_prof module_m module_n f_vec
  have rej_n_in_def_m:
    "reject n (defer m A p vs)
      (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs)  \<subseteq> defer m A p vs"
    using def_presv_fin_prof reject_in_alts  def_presv_fin_vector_pair
    by metis
  with disjoint_m module_m module_n f_prof f_vec
  have 0:
    "(elect m A p vs \<inter> reject n ?new_A ?new_p ?new_vs) = {}"
    using disj_n
    by (simp add: disjoint_iff_not_equal subset_eq)
  from f_prof module_m module_n f_vec
  have elec_n_in_def_m:
    "elect n (defer m A p vs)
      (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs) \<subseteq> defer m A p vs"
    using def_presv_fin_prof elect_in_alts def_presv_fin_vector_pair
    by metis
  from disjoint_m disjoint_n def_presv_fin_prof f_prof f_vec
       module_m module_n def_presv_fin_vector_pair
  have 1:
    "(elect m A p vs \<inter> defer n ?new_A ?new_p ?new_vs) = {}"
  proof -
    obtain sf :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>a b.
        (\<exists>c. c \<in> b \<and> (\<exists>d. d \<in> a \<and> c = d)) =
          (sf a b \<in> b \<and>
            (\<exists>e. e \<in> a \<and> sf a b = e))"
      by moura
    then obtain sf2 :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      "\<forall>A B.
        (A \<inter> B \<noteq> {} \<or> (\<forall>a. a \<notin> A \<or> (\<forall>b. b \<notin> B \<or> a \<noteq> b))) \<and>
          (A \<inter> B = {} \<or> sf B A \<in> A \<and> sf2 B A \<in> B \<and>
            sf B A = sf2 B A)"
      by auto
    thus ?thesis
      using defer_in_A disj_n fin_def module_n prof_def_lim vec_def_lim
      by (metis (no_types))
  qed
  from disjoint_m disjoint_n def_presv_fin_prof f_prof f_vec
       module_m module_n
  have 2:
    "(reject m A p vs \<inter> reject n ?new_A ?new_p ?new_vs) = {}"
    using disjoint_iff_not_equal reject_in_alts
          set_rev_mp result_disj Int_Un_distrib2
          Un_Diff_Int boolean_algebra_cancel.inf2
          inf.order_iff inf_sup_aci(1) subsetD
          rej_n_in_def_m disj_n
    by auto
  have "\<forall>A Aa. \<not> (A::'a set) \<subseteq> Aa \<or> A = A \<inter> Aa"
    by blast
  with disjoint_m disjoint_n def_presv_fin_prof f_prof
       module_m module_n elec_n_in_def_m
  have 3:
    "(reject m A p vs \<inter> elect n ?new_A ?new_p ?new_vs) = {}"
    using disj_n
    by blast
  have
    "(elect m A p vs \<union> elect n ?new_A ?new_p ?new_vs) \<inter>
          (reject m A p vs \<union> reject n ?new_A ?new_p ?new_vs) = {}"
  proof (safe)
    fix x :: "'a"
    assume
      elec_x: "x \<in> elect m A p vs" and
      rej_x: "x \<in> reject m A p vs"
    from elec_x rej_x
    have "x \<in> elect m A p vs \<inter> reject m A p vs"
      by simp
    thus "x \<in> {}"
      using disj_n
      by simp
  next
    fix x :: "'a"
    assume
      elec_x: "x \<in> elect m A p vs" and
      rej_lim_x:
      "x \<in> reject n (defer m A p vs)
        (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs)"
    from elec_x rej_lim_x
    show "x \<in> {}"
      using "0"
      by blast
  next
    fix x :: "'a"
    assume
      elec_lim_x:
      "x \<in> elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
          (limit_pair_vectors (defer m A p vs) vs)" and
      rej_x: "x \<in> reject m A p vs"
    from elec_lim_x rej_x
    show "x \<in> {}"
      using "3"
      by blast
  next
    fix x :: "'a"
    assume
      elec_lim_x:
      "x \<in> elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs)" and
      rej_lim_x:
      "x \<in> reject n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs)"
    from elec_lim_x rej_lim_x
    show "x \<in> {}"
      using disjoint_iff_not_equal elec_lim_x fin_def vec_def_lim
            module_n prof_def_lim rej_lim_x result_disj
      by metis
  qed
  moreover from 0 1 2 3 disjoint_n module_m module_n f_prof f_vec
  have
    "(elect m A p vs \<union> elect n ?new_A ?new_p ?new_vs) \<inter>
          (defer n ?new_A ?new_p ?new_vs) = {}"
    using Int_Un_distrib2 Un_empty def_presv_fin_prof result_disj vec_def_lim
    by metis
  moreover from 0 1 2 3 f_prof disjoint_m disjoint_n module_m module_n
  have
    "(reject m A p vs \<union> reject n ?new_A ?new_p ?new_vs) \<inter>
          (defer n ?new_A ?new_p ?new_vs) = {}"
(*    using Int_Un_distrib2 defer_in_alts distrib_imp2
          def_presv_fin_prof result_disj subset_Un_eq
          sup_inf_distrib1 *)
  proof (safe)
    fix x :: "'a"
    assume
      elec_rej_disj:
      "elect m A p vs \<inter>
        reject n (defer m A p vs) (limit_profile (defer m A p vs) p)
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      elec_def_disj:
      "elect m A p vs \<inter>
        defer n (defer m A p vs) (limit_profile (defer m A p vs) p)
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      rej_rej_disj:
      "reject m A p vs \<inter>
        reject n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      rej_elec_disj:
      "reject m A p vs \<inter>
        elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      disj_p: "disjoint3 (m A p vs)" and
      disj_limit:
      "disjoint3 (n (defer m A p vs) (limit_profile (defer m A p vs) p)
      (limit_pair_vectors (defer m A p vs) vs))" and
      mod_m: "electoral_module m" and
      mod_n: "electoral_module n" and
      fin_A: "finite A" and
      prof_A: "profile A p" and
      x_in_def:
      "x \<in> defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs)" and
      x_in_rej: "x \<in> reject m A p vs"
    from x_in_def
    have "x \<in> defer m A p vs"
      using defer_in_A fin_def module_n prof_def_lim vec_def_lim
      by blast
    with x_in_rej
    have "x \<in> reject m A p vs \<inter> defer m A p vs"
      by fastforce
    thus "x \<in> {}"
      using disj_n
      by blast
  next
    fix x :: "'a"
    assume
      elec_rej_disj:
      "elect m A p vs \<inter>
        reject n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      elec_def_disj:
      "elect m A p vs \<inter>
        defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      rej_rej_disj:
      "reject m A p vs \<inter>
        reject n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      rej_elec_disj:
      "reject m A p vs \<inter>
        elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}" and
      disj_p: "disjoint3 (m A p vs)" and
      disj_limit:
      "disjoint3 (n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs))" and
      mod_m: "electoral_module m" and
      mod_n: "electoral_module n" and
      fin_A: "finite A" and
      prof_A: "profile A p" and
      x_in_def:
      "x \<in> defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs)" and
      x_in_rej:
      "x \<in> reject n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs)"
    from x_in_def x_in_rej
    show "x \<in> {}"
      using fin_def module_n prof_def_lim reject_not_elec_or_def vec_def_lim 
       Diff_iff by fastforce
  qed
  ultimately have
    "disjoint3 (elect m A p vs \<union> elect n ?new_A ?new_p ?new_vs,
                reject m A p vs \<union> reject n ?new_A ?new_p ?new_vs,
                defer n ?new_A ?new_p ?new_vs)"
    by simp
  thus ?thesis
    using sequential_composition.simps
    by metis
qed

lemma seq_comp_presv_alts:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n" and
          f_prof:  "finite_profile A p" and
          f_vec: "finite_pair_vectors A vs"
  shows "set_equals_partition A ((m \<triangleright> n) A p vs)"
proof -
  let ?new_A = "defer m A p vs"
  let ?new_p = "limit_profile ?new_A p"
  let ?new_vs = "(limit_pair_vectors ?new_A vs)"
  from module_m f_prof f_vec have "set_equals_partition A (m A p vs)"
    by (simp add: electoral_module_def)
  with module_m f_prof f_vec have 0:
    "elect m A p vs \<union> reject m A p vs \<union> ?new_A = A"
    by (simp add: result_presv_alts)
  from module_n def_presv_fin_prof f_prof f_vec module_m have
    "set_equals_partition ?new_A (n ?new_A ?new_p ?new_vs)"
    using electoral_module_def well_formed.simps def_presv_fin_vector_pair    
    by metis
  with module_m module_n f_prof f_vec have 1:
    "elect n ?new_A ?new_p ?new_vs \<union>
        reject n ?new_A ?new_p ?new_vs \<union>
        defer n ?new_A ?new_p ?new_vs = ?new_A"
    using def_presv_fin_prof result_presv_alts def_presv_fin_vector_pair
    by metis
  from 0 1 have
    "(elect m A p vs \<union> elect n ?new_A ?new_p ?new_vs) \<union>
        (reject m A p vs \<union> reject n ?new_A ?new_p ?new_vs) \<union>
         defer n ?new_A ?new_p ?new_vs = A"
    by blast
  hence
    "set_equals_partition A
      (elect m A p vs \<union> elect n ?new_A ?new_p ?new_vs,
      reject m A p vs \<union> reject n ?new_A ?new_p ?new_vs,
      defer n ?new_A ?new_p ?new_vs)"
    by simp
  thus ?thesis
    using sequential_composition.simps
    by metis
qed

subsection \<open>Soundness\<close>

theorem seq_comp_sound[simp]:
  assumes module_m: "electoral_module m" and
          module_n: "electoral_module n"
        shows "electoral_module (m \<triangleright> n)"
  unfolding electoral_module_def
proof (safe)
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  assume
    fin_A: "finite A" and
    prof_A: "profile A p" and
    vec_A: "vector_pair A vs"
  have "\<forall>r. well_formed (A::'a set) r =
          (disjoint3 r \<and> set_equals_partition A r)"
    by simp
  thus "well_formed A ((m \<triangleright> n) A p vs)"
    using module_m module_n seq_comp_presv_disj
          seq_comp_presv_alts fin_A prof_A vec_A
    by metis
qed

subsection \<open>Lemmata\<close>

lemma seq_comp_dec_only_def:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs" and
    empty_defer: "defer m A p vs = {}"
  shows "(m \<triangleright> n) A p vs =  m A p vs"
proof
  have
    "\<forall>f A prof vs.
      (electoral_module f \<and> finite_profile A prof \<and> finite_pair_vectors A vs) \<longrightarrow>
        finite_pair_vectors (defer f A prof vs) (limit_pair_vectors (defer f A prof vs) vs)"
    using def_presv_fin_prof def_presv_fin_vector_pair
    by metis
  hence vec_no_alt: "vector_pair {} (limit_pair_vectors (defer m A p vs) vs)"
    using empty_defer f_prof f_vec module_m by fastforce 
  have
    "\<forall>f A prof vs.
      (electoral_module f \<and> finite_profile A prof \<and> finite_pair_vectors A vs) \<longrightarrow>
        finite_profile (defer f A prof vs)
          (limit_profile (defer f A prof vs) prof)"
    using def_presv_fin_prof 
    by metis
  hence prof_no_alt:
    "profile {} (limit_profile (defer m A p vs) p)"
    using empty_defer f_prof module_m f_vec
    by metis
  hence
    "(elect m A p vs) \<union>
      (elect n (defer m A p vs)
        (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs))
    = elect m A p vs"
    using elect_in_alts empty_defer module_n vec_no_alt
    by fastforce 
  thus "elect (m \<triangleright> n) A p vs = elect m A p vs"
    using fst_conv sequential_composition.simps
    by metis
next
  have rej_empty:
    "\<forall>f prof vs.
      (electoral_module f \<and> profile ({}::'a set) prof) \<and> vector_pair ({}::'a set) vs\<longrightarrow>
        reject f {} prof vs = {}"
    using bot.extremum_uniqueI infinite_imp_nonempty reject_in_alts
    by metis
  have prof_no_alt:
    "profile {} (limit_profile (defer m A p vs) p)"
    using empty_defer f_prof module_m limit_profile_sound
    by auto
  have vec_no_alt:
    "vector_pair {} (limit_pair_vectors (defer m A p vs) vs)" 
    using empty_defer f_prof f_vec module_m limit_profile_sound limit_pair_vectors_sound prof_no_alt
     by (simp add: vector_pair_def empty_defer)
  hence
    "(reject m A p vs, defer n {} (limit_profile {} p) (limit_pair_vectors {} vs)) =
        snd (m A p vs)"
    using bot.extremum_uniqueI defer_in_alts empty_defer
          infinite_imp_nonempty module_n prod.collapse vec_no_alt prof_no_alt
    by (metis (no_types))
  thus "snd ((m \<triangleright> n) A p vs) = snd (m A p vs)"
    using rej_empty empty_defer module_n prof_no_alt vec_no_alt
    by auto
qed

lemma seq_comp_def_then_elect:
  assumes
    n_electing_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "elect (m \<triangleright> n) A p vs = defer m A p vs"
proof cases
  assume "A = {}"
  with electing_n n_electing_m f_prof
  show ?thesis
    using bot.extremum_uniqueI defer_in_alts elect_in_alts
          electing_def non_electing_def seq_comp_sound f_vec
    by metis
next
  assume assm: "A \<noteq> {}"
  from n_electing_m f_prof f_vec
  have ele: "elect m A p vs = {}"
    using non_electing_def
    by blast
  from assm def_one_m f_prof finite f_vec
  have def_card:
    "card (defer m A p vs) = 1"
    by (simp add: Suc_leI card_gt_0_iff defers_def)
  with n_electing_m f_prof
  have def:
    "\<exists>a \<in> A. defer m A p vs = {a}"
    using card_1_singletonE defer_in_alts
          non_electing_def singletonI subsetCE f_vec 
    by metis
  from ele def n_electing_m
  have rej:
    "\<exists>a \<in> A. reject m A p vs = A-{a}"
    using Diff_empty def_one_m defers_def
          f_prof reject_not_elec_or_def f_vec
    by metis
  from ele rej def n_electing_m f_prof
  have res_m:
    "\<exists>a \<in> A. m A p vs = ({}, A-{a}, {a})"
    using Diff_empty combine_ele_rej_def non_electing_def
          reject_not_elec_or_def f_vec
    by metis
  hence
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p vs  =
        elect n {a} (limit_profile {a} p) (limit_pair_vectors (defer m A p vs) vs)"
    using prod.sel(1) prod.sel(2) sequential_composition.simps
          sup_bot.left_neutral
    by metis
  with def_card def electing_n n_electing_m f_prof
  have
    "\<exists>a \<in> A. elect (m \<triangleright> n) A p vs = {a}"
    using electing_for_only_alt non_electing_def prod.sel
          sequential_composition.simps def_presv_fin_prof
          sup_bot.left_neutral def_presv_fin_vector_pair f_vec
    by metis
  with def def_card electing_n n_electing_m f_prof res_m f_vec
  show ?thesis
    using def_presv_fin_prof electing_for_only_alt fst_conv
          non_electing_def sequential_composition.simps
          sup_bot.left_neutral def_presv_fin_vector_pair
    by metis
qed

lemma seq_comp_def_card_bounded:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "card (defer (m \<triangleright> n) A p vs) \<le> card (defer m A p vs)"
  using card_mono defer_in_alts module_m module_n f_prof f_vec
        sequential_composition.simps def_presv_fin_prof snd_conv
        def_presv_fin_vector_pair
  by metis

lemma seq_comp_def_set_bounded:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows "defer (m \<triangleright> n) A p vs \<subseteq> defer m A p vs"
  using defer_in_alts module_m module_n prod.sel(2) f_prof def_presv_fin_vector_pair
        sequential_composition.simps def_presv_fin_prof f_vec
  by metis

lemma seq_comp_defers_def_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows
    "defer (m \<triangleright> n) A p vs =
      defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
    (limit_pair_vectors (defer m A p vs) vs)"
  using sequential_composition.simps snd_conv
  by metis

lemma seq_comp_def_then_elect_elec_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "electoral_module n" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A vs"
  shows
    "elect (m \<triangleright> n) A p vs =
      elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs) \<union> (elect m A p vs)"
  using Un_commute fst_conv sequential_composition.simps
  by metis

lemma seq_comp_elim_one_red_def_set:
  assumes
    module_m: "electoral_module m" and
    module_n: "eliminates 1 n" and
    f_prof: "finite_profile A p" and
    enough_leftover: "card (defer m A p vs) > 1" and
    f_vec: "finite_pair_vectors A vs"
  shows "defer (m \<triangleright> n) A p vs \<subset> defer m A p vs"
  using enough_leftover module_m module_n f_prof
        sequential_composition.simps def_presv_fin_prof
        single_elim_imp_red_def_set snd_conv f_vec def_presv_fin_vector_pair
  by metis

lemma seq_comp_def_set_sound:
  assumes
    "electoral_module m" and
    "electoral_module n" and
    "finite_profile A p" and
    "finite_pair_vectors A vs"
  shows "defer (m \<triangleright> n) A p vs \<subseteq> defer m A p vs"
proof -
  have "\<forall>A p vs. finite_profile A p \<and> finite_pair_vectors A vs
        \<longrightarrow> well_formed A (n A p vs)"
    using assms(2) electoral_module_def
    by auto
  hence
    "finite_profile (defer m A p vs) (limit_profile (defer m A p vs) p) \<and>
     finite_pair_vectors (defer m A p vs) (limit_pair_vectors (defer m A p vs) vs) \<longrightarrow>
        well_formed (defer m A p vs)
          (n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs))"
    by simp
  hence
    "well_formed (defer m A p vs) (n (defer m A p vs)
      (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs))"
    using assms(1) assms(3) assms(4) def_presv_fin_prof def_presv_fin_vector_pair
    by metis
  thus ?thesis
    using assms seq_comp_def_set_bounded
    by blast
qed

lemma seq_comp_def_set_trans:
  assumes
    "a \<in> (defer (m \<triangleright> n) A p vs)" and
    "electoral_module m \<and> electoral_module n" and
    "finite_profile A p" and 
    "finite_pair_vectors A vs"
  shows
    "a \<in> defer n (defer m A p vs)
      (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs) \<and>
      a \<in> defer m A p vs"
  using seq_comp_def_set_bounded assms(1) assms(2)
        assms(3) assms(4) in_mono seq_comp_defers_def_set
  by (smt (verit, ccfv_threshold))

subsection \<open>Composition Rules\<close>

(*The sequential composition preserves the non-blocking property.*)
theorem seq_comp_presv_non_blocking[simp]:
  assumes
    non_blocking_m: "non_blocking m" and
    non_blocking_n: "non_blocking n"
  shows "non_blocking (m \<triangleright> n)"
proof -
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  let ?input_sound = "((A::'a set) \<noteq> {} \<and> finite_profile A p \<and> 
      finite_pair_vectors A vs)"
  from non_blocking_m have
    "?input_sound \<longrightarrow> reject m A p vs \<noteq> A"
    by (simp add: non_blocking_def)
  with non_blocking_m have 0:
    "?input_sound \<longrightarrow> A - reject m A p vs \<noteq> {}"
    using Diff_eq_empty_iff non_blocking_def
          reject_in_alts subset_antisym
    by metis
  from non_blocking_m have
    "?input_sound \<longrightarrow> well_formed A (m A p vs)"
    by (simp add: electoral_module_def non_blocking_def)
  hence
    "?input_sound \<longrightarrow>
        elect m A p vs \<union> defer m A p vs = A - reject m A p vs"
    using non_blocking_def non_blocking_m elec_and_def_not_rej
    by metis
  with 0 have
    "?input_sound \<longrightarrow> elect m A p vs \<union> defer m A p vs \<noteq> {}"
    by auto
  hence "?input_sound \<longrightarrow> (elect m A p vs \<noteq> {} \<or> defer m A p vs \<noteq> {})"
    by simp
  with non_blocking_m non_blocking_n
  show ?thesis
  proof (unfold non_blocking_def)
    assume
      emod_reject_m:
      "electoral_module m \<and>
        (\<forall>A p vs. A \<noteq> {} \<and> finite_profile A p \<and> finite_pair_vectors A vs \<longrightarrow>
          reject m A p vs \<noteq> A)" and
      emod_reject_n:
      "electoral_module n \<and>
        (\<forall>A p vs. A \<noteq> {} \<and> finite_profile A p \<and> finite_pair_vectors A vs \<longrightarrow>
          reject n A p vs \<noteq> A)"
    show
      "electoral_module (m \<triangleright> n) \<and>
        (\<forall>A p vs.
          A \<noteq> {} \<and> finite_profile A p \<and> finite_pair_vectors A vs \<longrightarrow>
            reject (m \<triangleright> n) A p vs \<noteq> A)"
    proof (safe)
      show "electoral_module (m \<triangleright> n)"
        using emod_reject_m emod_reject_n
        by simp
    next
      fix
        A :: "'a set" and
        p :: "'a Profile" and
        vs :: "'a Pair_Vectors" and
        x :: "'a"
      assume
        fin_A: "finite A" and
        prof_A: "profile A p" and
        vec_A: "vector_pair A vs" and
        rej_mn: "reject (m \<triangleright> n) A p vs = A" and
        x_in_A: "x \<in> A"
      from emod_reject_m fin_A prof_A vec_A
      have fin_defer:
        "finite_profile (defer m A p vs) (limit_profile (defer m A p vs) p)"
        using def_presv_fin_prof
        by (metis (no_types))
      from emod_reject_m fin_A prof_A vec_A
      have fin_defer2:
        "finite_pair_vectors (defer m A p vs) (limit_pair_vectors (defer m A p vs) vs)"
        using def_presv_fin_prof def_presv_fin_vector_pair
        by (metis (no_types))
      from emod_reject_m emod_reject_n fin_A prof_A vec_A
      have seq_elect:
        "elect (m \<triangleright> n) A p vs =
          elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
          (limit_pair_vectors (defer m A p vs) vs) \<union>
            elect m A p vs"
        using seq_comp_def_then_elect_elec_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A vec_A
      have def_limit:
        "defer (m \<triangleright> n) A p vs =
          defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
          (limit_pair_vectors (defer m A p vs) vs)"
        using seq_comp_defers_def_set
        by metis
      from emod_reject_n emod_reject_m fin_A prof_A vec_A
      have
        "elect (m \<triangleright> n) A p vs \<union> defer (m \<triangleright> n) A p vs = A - reject (m \<triangleright> n) A p vs"
        using elec_and_def_not_rej seq_comp_sound
        by metis
      hence elect_def_disj:
        "elect n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) \<union>
        elect m A p vs \<union>
        defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {}"
        using def_limit seq_elect Diff_cancel rej_mn
        by auto
      have rej_def_eq_set:
        "defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) -
        defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {} \<longrightarrow>
        reject n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) =
              defer m A p vs"
        using elect_def_disj emod_reject_n fin_defer fin_defer2
        by (simp add: reject_not_elec_or_def)
      have
        "defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) -
          defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
        (limit_pair_vectors (defer m A p vs) vs) = {} \<longrightarrow>
            elect m A p vs = elect m A p vs \<inter> defer m A p vs"
        using elect_def_disj
        by blast
      thus "x \<in> {}"
        using rej_def_eq_set result_disj fin_defer
        using Diff_cancel Diff_empty emod_reject_m emod_reject_n
              fin_A prof_A vec_A reject_not_elec_or_def x_in_A fin_defer2
        by metis
    qed
  qed
qed

(*Sequential composition preserves the non-electing property.*)
theorem seq_comp_presv_non_electing[simp]:
  assumes
    m_elect: "non_electing m" and
    n_elect: "non_electing n"
  shows "non_electing (m \<triangleright> n)"
  unfolding non_electing_def
proof (safe)
  from m_elect n_elect
  have "electoral_module m \<and> electoral_module n"
    unfolding non_electing_def
    by blast
  thus "electoral_module (m \<triangleright> n)"
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    x :: "'a" and
    vs :: "'a Pair_Vectors"
  assume
    "finite A" and
    "profile A p" and
    "vector_pair A vs" and
    "x \<in> elect (m \<triangleright> n) A p vs"
  with m_elect n_elect
  show "x \<in> {}"
    unfolding non_electing_def
    using seq_comp_def_then_elect_elec_set def_presv_fin_prof
          Diff_empty Diff_partition empty_subsetI def_presv_fin_vector_pair
    by metis
qed

(*
   Composing an electoral module that defers exactly 1 alternative
   in sequence after an electoral module that is electing
   results (still) in an electing electoral module.
*)
theorem seq_comp_electing[simp]:
  assumes def_one_m1:  "defers 1 m1" and
          electing_m2: "electing m2"
  shows "electing (m1 \<triangleright> m2)"
proof -
  have
    "\<forall>A p vs. (card A \<ge> 1 \<and> finite_profile A p \<and> finite_pair_vectors A vs) \<longrightarrow>
        card (defer m1 A p vs) = 1"
    using def_one_m1 defers_def
    by blast
  hence def_m1_not_empty:
    "\<forall>A p vs. (A \<noteq> {} \<and> finite_profile A p \<and> finite_pair_vectors A vs) \<longrightarrow>
        defer m1 A p vs \<noteq> {}"
    using One_nat_def Suc_leI card_eq_0_iff
          card_gt_0_iff zero_neq_one
    by metis
  thus ?thesis
    using Un_empty def_one_m1 defers_def electing_def
          electing_m2 seq_comp_def_then_elect_elec_set
          seq_comp_sound def_presv_fin_prof 
  proof -
    have def_card_one:
      "electoral_module m1 \<and>
        (\<forall>A prof vs.
          (1 \<le> card A \<and> finite A \<and> profile A prof \<and> vector_pair A vs) \<longrightarrow>
            card (defer m1 A prof vs) = 1)"
      using def_one_m1 defers_def
      by blast
   (* hence "electoral_module (m1 \<triangleright> m2)"
      using  seq_comp_sound
      by metis*)
    with  def_card_one
    show ?thesis
      using seq_comp_def_then_elect_elec_set def_presv_fin_prof
            def_m1_not_empty bot_eq_sup_iff def_presv_fin_vector_pair
      by (smt (z3) electing_def electing_m2 seq_comp_sound)
  qed
qed

lemma def_lift_inv_seq_comp_help:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n" and
    f_vec: "finite_pair_vectors A vs" and
    def_and_lifted: "a \<in> (defer (m \<triangleright> n) A p vs) \<and> lifted A p q a"
  shows "(m \<triangleright> n) A p vs = (m \<triangleright> n) A q vs"
proof -
  let ?new_Ap = "defer m A p vs"
  let ?new_Aq = "defer m A q vs"
  let ?new_p = "limit_profile ?new_Ap p"
  let ?new_q = "limit_profile ?new_Aq q"
  let ?new_vsp = "limit_pair_vectors ?new_Ap vs"
  let ?new_vsq = "limit_pair_vectors ?new_Aq vs"
  from monotone_m monotone_n have modules:
    "electoral_module m \<and> electoral_module n"
    unfolding defer_lift_invariance_def
    by simp
  hence "finite_profile A p \<and> finite_pair_vectors A vs 
    \<longrightarrow> defer (m \<triangleright> n) A p vs \<subseteq> defer m A p vs"
    using seq_comp_def_set_bounded
    by metis
  moreover have profile_p: "lifted A p q a \<longrightarrow> finite_profile A p"
    unfolding lifted_def
    by simp
 ultimately have defer_subset: "defer (m \<triangleright> n) A p vs \<subseteq> defer m A p vs"
    using def_and_lifted f_vec
    by blast
  hence mono_m: "m A p vs = m A q vs"
    using monotone_m defer_lift_invariance_def def_and_lifted
          modules profile_p seq_comp_def_set_trans f_vec
    by metis
  hence new_A_eq: "?new_Ap = ?new_Aq"
    by presburger
  have defer_eq:
    "defer (m \<triangleright> n) A p vs = defer n ?new_Ap ?new_p ?new_vsp"
    using sequential_composition.simps snd_conv
    by metis
  hence mono_n:
    "n ?new_Ap ?new_p ?new_vsp = n ?new_Aq ?new_q ?new_vsq"
  proof cases
    have m0: "finite (defer m A p vs)"
      by (metis def_and_lifted defer_in_alts f_vec modules profile_p rev_finite_subset)
    have m1: "vector_pair ?new_Ap ?new_vsp" 
      using f_vec vector_pair_def profile_p def_and_lifted defer_in_alts
      by (smt (verit, ccfv_SIG) limit_pair_vectors_sound modules)
      
    have m2: "finite_pair_vectors ?new_Ap ?new_vsp" using m0 m1 by simp

    assume "lifted ?new_Ap ?new_p ?new_q a"  
    thus ?thesis
      using defer_eq mono_m monotone_n
            defer_lift_invariance_def def_and_lifted m2 (*f_vec lifted_finite_vectors*)
      by (metis (no_types, lifting))
  next
    assume a2: "\<not>lifted ?new_Ap ?new_p ?new_q a"
    from def_and_lifted
    have "finite_profile A q"
      by (simp add: lifted_def)
    with modules new_A_eq
    have 1:
      "finite_profile ?new_Ap ?new_q"
      using def_presv_fin_prof f_vec
      by (metis)
    moreover from modules profile_p def_and_lifted
    have 0:
      "finite_profile ?new_Ap ?new_p"
      using def_presv_fin_prof
      by (metis def_and_lifted f_vec profile_p)
    moreover from defer_subset def_and_lifted
    have 2: "a \<in> ?new_Ap"
      by blast
    moreover from def_and_lifted
    have eql_lengths:
      "length ?new_p = length ?new_q"
      by (simp add: lifted_def)
    ultimately have 0:
      "(\<forall>i::nat. i < length ?new_p \<longrightarrow>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a) \<or>
       (\<exists>i::nat. i < length ?new_p \<and>
          \<not>Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<and>
              (?new_p!i) \<noteq> (?new_q!i))"
      using a2 lifted_def
      by (metis (no_types, lifting))
    from def_and_lifted modules have
      "\<forall>i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
          (Preference_Relation.lifted A (p!i) (q!i) a \<or> (p!i) = (q!i))"
      using defer_in_alts Profile.lifted_def limit_prof_presv_size f_vec
      by metis
    with def_and_lifted modules mono_m have
      "\<forall>i. (0 \<le> i \<and> i < length ?new_p) \<longrightarrow>
          (Preference_Relation.lifted ?new_Ap (?new_p!i) (?new_q!i) a \<or>
           (?new_p!i) = (?new_q!i))"
      using limit_lifted_imp_eq_or_lifted defer_in_alts
            Profile.lifted_def limit_prof_presv_size
            limit_profile.simps nth_map f_vec
      by (metis (no_types, lifting))
    with 0 eql_lengths mono_m
    show ?thesis
      using leI not_less_zero nth_equalityI
      by metis
  qed
  from mono_m mono_n
  show ?thesis
    using sequential_composition.simps
    by (metis (full_types))
qed

(*Sequential composition preserves the property defer-lift-invariance.*)
theorem seq_comp_presv_def_lift_inv[simp]:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_n: "defer_lift_invariance n"
  shows "defer_lift_invariance (m \<triangleright> n)"
  using monotone_m monotone_n def_lift_inv_seq_comp_help
        seq_comp_sound defer_lift_invariance_def
  by (smt (z3)) 
 
(*
   Composing a non-blocking, non-electing electoral module
   in sequence with an electoral module that defers exactly
   one alternative results in an electoral module that defers
   exactly one alternative.
*)
theorem seq_comp_def_one[simp]:
  assumes
    non_blocking_m: "non_blocking m" and
    non_electing_m: "non_electing m" and
    def_1_n: "defers 1 n"
  shows "defers 1 (m \<triangleright> n)"
  unfolding defers_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_electing_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using def_1_n
    by (simp add: defers_def)
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    vs :: "'a Pair_Vectors"
  assume
    pos_card: "1 \<le> card A" and
    fin_A: "finite A" and
    prof_A: "profile A p" and
    vec_A: "vector_pair A vs"
  from pos_card have
    "A \<noteq> {}"
    by auto
  with fin_A prof_A vec_A have m_non_blocking:
    "reject m A p vs \<noteq> A"
    using non_blocking_m non_blocking_def
    by metis
  hence
    "\<exists>a. a \<in> A \<and> a \<notin> reject m A p vs"
    using pos_card non_electing_def non_electing_m
          reject_in_alts subset_antisym subset_iff
          fin_A prof_A vec_A subsetI
    by metis
  hence "defer m A p vs \<noteq> {}"
    using electoral_mod_defer_elem empty_iff pos_card
          non_electing_def non_electing_m fin_A prof_A vec_A
    by (metis (no_types))
  hence defer_non_empty:
    "card (defer m A p vs) \<ge> 1"
    using One_nat_def Suc_leI card_gt_0_iff pos_card fin_A prof_A vec_A
          non_blocking_def non_blocking_m def_presv_fin_prof 
    by metis
  have defer_fun:
    "defer (m \<triangleright> n) A p vs =
      defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs)"
    using def_1_n defers_def fin_A non_blocking_def non_blocking_m
          prof_A vec_A seq_comp_defers_def_set
    by (metis (no_types, hide_lams))
  have
    "\<forall>n f. defers n f =
      (electoral_module f \<and>
        (\<forall>A prof vs.
          (\<not> n \<le> card (A::'a set) \<or> infinite A \<or>
            \<not> profile A prof \<or> \<not> vector_pair A vs) \<or>
          card (defer f A prof vs) = n))"
    using defers_def 
    by blast
  hence
    "card (defer n (defer m A p vs)
      (limit_profile (defer m A p vs) p) 
      (limit_pair_vectors (defer m A p vs) vs)) = 1"
    using defer_non_empty def_1_n
          fin_A prof_A vec_A non_blocking_def
          non_blocking_m def_presv_fin_prof def_presv_fin_vector_pair
    by metis
  thus "card (defer (m \<triangleright> n) A p vs) = 1"
    using defer_fun
    by auto
qed

(*
   Sequentially composing electoral modules after compatible
   electoral modules does not break their compatibility.
*)
theorem disj_compat_seq[simp]:
  assumes
    compatible: "disjoint_compatibility m n" and
    module_m2: "electoral_module m2"
  shows "disjoint_compatibility (m \<triangleright> m2) n"
  unfolding disjoint_compatibility_def 
proof (safe)
  show "electoral_module (m \<triangleright> m2)"
    using compatible disjoint_compatibility_def
          module_m2 seq_comp_sound
  proof -
    have "electoral_module m"
      using compatible disjoint_compatibility_def by blast
    then show ?thesis
      by (meson module_m2 seq_comp_sound)
  qed
next
  show "electoral_module n"
    using compatible disjoint_compatibility_def by blast
next
  fix
    S :: "'a set" (*and
    vs :: "'a Pair_Vectors"*)
  assume
    fin_S: "finite S" (*and
    vec_A: "vector_pair S vs"*)
  have modules:
    "electoral_module (m \<triangleright> m2) \<and> electoral_module n"
    using compatible disjoint_compatibility_def
          module_m2 seq_comp_sound
    by auto

 obtain A where A:
    "A \<subseteq> S \<and>
      (\<forall>a \<in> A. indep_of_alt m S a \<and>
        (\<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject m S p vs)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
        (\<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject n S p vs))"
    using compatible disjoint_compatibility_def fin_S (*vec_A*)
    by (metis (no_types, lifting))
  show "\<exists>A\<subseteq>S. 
          (\<forall>a\<in>A. indep_of_alt (m \<triangleright> m2) S a \<and> 
            (\<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p vs)) \<and>
              (\<forall>a\<in>S - A. indep_of_alt n S a \<and> (\<forall>p vs. finite_profile S p \<and> vector_pair S vs
                \<longrightarrow> a \<in> reject n S p vs)) "
    (*"\<exists>A \<subseteq> S.
      (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
        (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S vs 
        \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p vs)) \<and>
      (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
        (\<forall>p vs. finite_profile S p \<and> finite_pair_vectors S vs
        \<longrightarrow> a \<in> reject n S p vs))"*)
  proof
    (*have
      "\<forall>a p q.
        a \<in> A \<and> equiv_prof_except_a S p q a \<and> 
      finite_pair_vectors S p vs \<and> finite_pair_vectors S q vs \<longrightarrow>
          (m \<triangleright> m2) S p vs = (m \<triangleright> m2) S q vs"*)
     have t0:
      "\<forall>a \<in> A. \<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p vs"
      using A UnI1 prod.sel sequential_composition.simps 
      by metis
    have 
      "\<forall>a p q vs.
        a \<in> A \<and> equiv_prof_except_a S p q a \<and> finite_pair_vectors S vs\<longrightarrow>
          (m \<triangleright> m2) S p vs = (m \<triangleright> m2) S q vs"
    proof (safe)
      fix
        a :: "'a" and
        p :: "'a Profile" and
        q :: "'a Profile" and
        vs :: "'a Pair_Vectors"
      assume
        a: "a \<in> A" and
        b: "equiv_prof_except_a S p q a" and
        c1: "finite S" and
        c2: "vector_pair S vs"
      have c: "finite_pair_vectors S vs" using c1 c2 by simp 
      have eq_def:
        "defer m S p vs = defer m S q vs"
        using A a b c indep_of_alt_def
        by metis
      from a b have profiles:
        "finite_profile S p \<and> finite_profile S q"
        using equiv_prof_except_a_def
        by fastforce
      hence "(defer m S p vs) \<subseteq> S"
        using compatible defer_in_alts disjoint_compatibility_def c by blast
      hence
        "limit_profile (defer m S p vs) p =
          limit_profile (defer m S q vs) q"
        using A DiffD2 a b compatible defer_not_elec_or_rej
              disjoint_compatibility_def eq_def profiles
              negl_diff_imp_eq_limit_prof c 
        by (metis (no_types, lifting))
      with eq_def have 0:
        "m2 (defer m S p vs) (limit_profile (defer m S p vs) p) 
          (limit_pair_vectors (defer m S p vs) vs) =
          m2 (defer m S q vs) (limit_profile (defer m S q vs) q) 
      (limit_pair_vectors (defer m S q vs) vs)"
        by simp
      moreover have "m S p vs = m S q vs"
        using A a b indep_of_alt_def c
        by metis
      ultimately have "(m \<triangleright> m2) S p vs = (m \<triangleright> m2) S q vs"
        using sequential_composition.simps c 
        by (metis (full_types))
      then show
        "(m \<triangleright> m2) S p vs = (m \<triangleright> m2) S q vs"
        using c
        by (metis (full_types))
    qed
    then have "(\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a)" 
      using modules indep_of_alt_def unfolding indep_of_alt_def
      by blast 
     (*have "A \<subseteq> S \<and> (\<forall>a \<in> A. electoral_module (m \<triangleright> m2) \<and> (\<forall>p q vs. equiv_prof_except_a A p q a 
      \<longrightarrow> (m \<triangleright> m2) A p vs = (m \<triangleright> m2) A q vs))" sorry*)
    then show
      "A \<subseteq> S \<and>
        (\<forall>a \<in> A. indep_of_alt (m \<triangleright> m2) S a \<and>
          (\<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject (m \<triangleright> m2) S p vs)) \<and>
        (\<forall>a \<in> S-A. indep_of_alt n S a \<and>
          (\<forall>p vs. finite_profile S p \<and> vector_pair S vs \<longrightarrow> a \<in> reject n S p vs))"
      using A indep_of_alt_def modules compatible fin_S  disjoint_compatibility_def t0 by auto 
      (*by (metis (mono_tags, lifting))*)
  qed
qed

(*
   Composing a defer-lift invariant and a non-electing
   electoral module that defers exactly one alternative
   in sequence with an electing electoral module
   results in a monotone electoral module.
*)
theorem seq_comp_mono[simp]:
  assumes
    def_monotone_m: "defer_lift_invariance m" and
    non_ele_m: "non_electing m" and
    def_one_m: "defers 1 m" and
    electing_n: "electing n"
  shows "monotonicity (m \<triangleright> n)"
  unfolding monotonicity_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using non_ele_m
    by (simp add: non_electing_def)
  have electoral_mod_n: "electoral_module n"
    using electing_n
    by (simp add: electing_def)
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    w :: "'a"
  assume
    fin_A: "finite A" and
    elect_w_in_p: "w \<in> elect (m \<triangleright> n) A p vs" and
    lifted_w: "Profile.lifted A p q w" and
    vec_f: "vector_pair A vs"

  have
    "finite_profile A p \<and> finite_profile A q"
    using lifted_w lifted_def
    by metis
  thus "w \<in> elect (m \<triangleright> n) A q vs"
    using seq_comp_def_then_elect defer_lift_invariance_def
          elect_w_in_p lifted_w def_monotone_m non_ele_m
          def_one_m electing_n vec_f
    by (smt (verit, del_insts))
    (*by metis *)
qed

(*
   Composing a defer-invariant-monotone electoral module in sequence before
   a non-electing, defer-monotone electoral module that defers exactly
   1 alternative results in a defer-lift-invariant electoral module.
*)
theorem def_inv_mono_imp_def_lift_inv[simp]:
  assumes
    strong_def_mon_m: "defer_invariant_monotonicity m" and
    non_electing_n: "non_electing n" and
    defers_1: "defers 1 n" and
    defer_monotone_n: "defer_monotonicity n"
  shows "defer_lift_invariance (m \<triangleright> n)"
  unfolding defer_lift_invariance_def
proof (safe)
  have electoral_mod_m: "electoral_module m"
    using defer_invariant_monotonicity_def
          strong_def_mon_m
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  show "electoral_module (m \<triangleright> n)"
    using electoral_mod_m electoral_mod_n
    by simp
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    a :: "'a"
  assume
  defer_a_p: "a \<in> defer (m \<triangleright> n) A p vs" and
  lifted_a: "Profile.lifted A p q a" and
  vec_A: "vector_pair A vs"
  from strong_def_mon_m
  have non_electing_m: "non_electing m"
    by (simp add: defer_invariant_monotonicity_def)
  have electoral_mod_m: "electoral_module m"
    using strong_def_mon_m defer_invariant_monotonicity_def
    by auto
  have electoral_mod_n: "electoral_module n"
    using defers_1 defers_def
    by auto
  have finite_profile_q: "finite_profile A q"
    using lifted_a
    by (simp add: Profile.lifted_def)
  have finite_profile_p: "profile A p"
    using lifted_a
    by (simp add: Profile.lifted_def)
  show "(m \<triangleright> n) A p vs = (m \<triangleright> n) A q vs"
  proof cases
    assume not_unchanged: "defer m A q vs \<noteq> defer m A p vs"
    from not_unchanged
    have a_single_defer: "{a} = defer m A q vs"
      using strong_def_mon_m electoral_mod_n defer_a_p
            defer_invariant_monotonicity_def lifted_a
            seq_comp_def_set_trans finite_profile_p
            finite_profile_q vec_A
      by metis
    moreover have
      "{a} = defer m A q vs \<longrightarrow> defer (m \<triangleright> n) A q vs \<subseteq> {a}"
      using finite_profile_q electoral_mod_m electoral_mod_n
            seq_comp_def_set_sound vec_A
      by (metis) 
    ultimately have
      "(a \<in> defer m A p vs) \<longrightarrow> defer (m \<triangleright> n) A q vs \<subseteq> {a}"
      by blast (* lifted defer-subset of a *)
    moreover have def_card_one:
      "(a \<in> defer m A p vs) \<longrightarrow> card (defer (m \<triangleright> n) A q vs) = 1"
      using One_nat_def a_single_defer card_eq_0_iff
            card_insert_disjoint defers_1 defers_def
            electoral_mod_m empty_iff finite.emptyI
            seq_comp_defers_def_set order_refl
            def_presv_fin_prof finite_profile_q vec_A
            def_presv_fin_vector_pair 
      by (smt (verit))
    moreover have defer_a_in_m_p:
      "a \<in> defer m A p vs"
      using electoral_mod_m electoral_mod_n defer_a_p
            seq_comp_def_set_bounded finite_profile_p
            finite_profile_q
      by (metis (no_types, lifting) insert_Diff insert_subset vec_A)
    ultimately have
      "defer (m \<triangleright> n) A q vs = {a}" (* lifted defer set = a *)
      using Collect_mem_eq card_1_singletonE empty_Collect_eq
            insertCI subset_singletonD
      by metis
    moreover have
      "defer (m \<triangleright> n) A p vs = {a}" (* regular defer set = a *)
    proof (safe)
      fix x :: "'a"
      assume
      defer_x: "x \<in> defer (m \<triangleright> n) A p vs" and
      x_exists: "x \<notin> {}"
      show "x = a"
      proof - 
        have fin_defer:
          "\<forall>f (A::'a set) prof vs.
            (electoral_module f \<and> finite A \<and> profile A prof \<and> vector_pair A vs) \<longrightarrow>
              finite_profile (defer f A prof vs)
                (limit_profile (defer f A prof vs) prof)"
          using def_presv_fin_prof 
          by (metis (no_types))
        have "finite_profile (defer m A p vs) (limit_profile (defer m A p vs) p)"
          using electoral_mod_m finite_profile_p finite_profile_q fin_defer vec_A
          by blast
        hence "Suc (card (defer m A p vs - {a})) = card (defer m A p vs)"
          using card_Suc_Diff1 defer_a_in_m_p
          by metis
        hence min_card:
          "Suc 0 \<le> card (defer m A p vs)"
          by linarith
        have emod_n_then_mn:
          "electoral_module n \<longrightarrow> electoral_module (m \<triangleright> n)"
          using electoral_mod_m
          by simp
        have "defers (Suc 0) n"
          using defers_1
          by auto
        hence defer_card_one:
          "electoral_module n \<and>
            (\<forall>A prof vs.
              (Suc 0 \<le> card A \<and> finite A \<and> profile A prof \<and> finite_pair_vectors A vs) \<longrightarrow>
                card (defer n A prof vs) = Suc 0)"
          by (simp add: defers_def)
        hence emod_mn: "electoral_module (m \<triangleright> n)"
          using emod_n_then_mn
          by blast
        have nat_diff:
          "\<forall> (i::nat) j. i \<le> j \<longrightarrow> i - j = 0"
          by auto
        have nat_comp:
          "\<forall> (i::nat) j k.
            i \<le> j \<and> j \<le> k \<or>
              j \<le> i \<and> i \<le> k \<or>
              i \<le> k \<and> k \<le> j \<or>
              k \<le> j \<and> j \<le> i \<or>
              j \<le> k \<and> k \<le> i \<or>
              k \<le> i \<and> i \<le> j"
          using le_cases3
          by linarith
        have fin_diff_card:
          "\<forall>A a.
            (finite A \<and> (a::'a) \<in> A) \<longrightarrow>
              card (A - {a}) = card A - 1"
          using card_Diff_singleton
          by metis
        have m1:"vector_pair A vs \<Longrightarrow> Profile.lifted A p q a \<Longrightarrow> finite_pair_vectors A vs"
          by (simp add: finite_profile_q) 
        have fin_vec_defer:
          "\<forall>f (A::'a set) prof vs.
            (electoral_module f \<and> finite A \<and> profile A prof \<and> vector_pair A vs) \<longrightarrow>
              finite_pair_vectors (defer f A prof vs) (limit_pair_vectors (defer f A prof vs) vs)"
          using def_presv_fin_vector_pair
          by (metis (no_types))
        with fin_defer defer_card_one min_card
         have "card (defer (m \<triangleright> n) A p vs) = Suc 0"
          using electoral_mod_m seq_comp_defers_def_set electoral_mod_n
                finite_profile_p finite_profile_q m1 fin_vec_defer vec_A
          by metis
        with fin_diff_card nat_comp nat_diff emod_mn fin_defer
        have "{a} = {x}"
          using One_nat_def card_1_singletonE singletonD
                defer_a_p defer_x
          by metis
        thus ?thesis
          by force
      qed
    next
      show "a \<in> defer (m \<triangleright> n) A p vs"
        using defer_a_p
        by linarith
    qed
    ultimately have (* defer sets equal *)
      mm3: "defer (m \<triangleright> n) A p vs = defer (m \<triangleright> n) A q vs"
      by blast 
    moreover have (* elect sets sets equal *)
      "elect (m \<triangleright> n) A p vs = elect (m \<triangleright> n) A q vs"
      using finite_profile_p finite_profile_q
            non_electing_m non_electing_n
            seq_comp_presv_non_electing
            non_electing_def vec_A lifted_a 
            finite_profile_q 
      by metis (* elect sets equal *)
    thus ?thesis (*(m \<triangleright> n) A p vs = (m \<triangleright> n) A q vs*)
        proof -
      have f1: "electoral_module (m \<triangleright> n)"
        by (meson electoral_mod_m electoral_mod_n seq_comp_sound)
      have "vector_pair A vs"
        by (meson finite_profile_q lifted_a vec_A)
      then show ?thesis
        using f1 \<open>elect (m \<triangleright> n) A p vs = elect (m \<triangleright> n) A q vs\<close> 
          eq_def_and_elect_imp_eq finite_profile_p finite_profile_q mm3 vec_A by blast
    qed
  next
    assume not_different_alternatives:
      "\<not>(defer m A q vs \<noteq> defer m A p vs)"
    have "elect m A p vs = {}"
      using non_electing_m finite_profile_p finite_profile_q vec_A
      by (simp add: non_electing_def)
    moreover have "elect m A q vs = {}"
      using non_electing_m finite_profile_q finite_profile_p lifted_a vec_A non_electing_def
       finite_profile_q by metis
    ultimately have elect_m_equal:
      "elect m A p vs = elect m A q vs"
      by simp (* m elects the same stuff *)
    from not_different_alternatives
    have same_alternatives: "defer m A q vs = defer m A p vs"
      by simp
    hence
      "(limit_profile (defer m A p vs) p) =
        (limit_profile (defer m A p vs) q) \<or>
          lifted (defer m A q vs)
            (limit_profile (defer m A p vs) p)
              (limit_profile (defer m A p vs) q) a"
      using defer_in_alts electoral_mod_m
            lifted_a finite_profile_q
            limit_prof_eq_or_lifted vec_A
      by metis
    thus ?thesis
    proof
      assume
        "limit_profile (defer m A p vs) p =
          limit_profile (defer m A p vs) q"
      hence same_profile:
        "limit_profile (defer m A p vs) p =
          limit_profile (defer m A q vs) q"
        using same_alternatives
        by simp
      hence results_equal_n:
        "n (defer m A q vs) (limit_profile (defer m A q vs) q) =
          n (defer m A p vs) (limit_profile (defer m A p vs) p)"
        by (simp add: same_alternatives)
      moreover have results_equal_m: "m A p vs = m A q vs"
        using elect_m_equal same_alternatives
              finite_profile_p finite_profile_q vec_A lifted_a
        by (simp add: electoral_mod_m eq_def_and_elect_imp_eq)
      hence "(m \<triangleright> n) A p vs = (m \<triangleright> n) A q vs"
        using same_profile
        by auto
      thus ?thesis
        by blast
    next
      assume still_lifted:
        "lifted (defer m A q vs) (limit_profile (defer m A p vs) p)
          (limit_profile (defer m A p vs) q) a"
      hence a_in_def_p:
        "a \<in> defer n (defer m A p vs)
          (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs)"
        using electoral_mod_m electoral_mod_n
              finite_profile_p defer_a_p
              seq_comp_def_set_trans
              finite_profile_q vec_A  
        by metis
      hence a_still_deferred_p:
        "{a} \<subseteq> defer n (defer m A p vs)
          (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs)"
        by simp
      have card_le_1_p: "card (defer m A p vs) \<ge> 1"
        using One_nat_def Suc_leI card_gt_0_iff
              electoral_mod_m electoral_mod_n
              equals0D finite_profile_p defer_a_p
              seq_comp_def_set_trans def_presv_fin_prof
              finite_profile_q vec_A
        by metis
      hence
        "card (defer n (defer m A p vs)
          (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs)) = 1"
        using defers_1 defers_def electoral_mod_m
              finite_profile_p def_presv_fin_prof
              finite_profile_q vec_A lifted_a def_presv_fin_vector_pair 
        by metis
      hence def_set_is_a_p:
        "{a} = defer n (defer m A p vs) (limit_profile (defer m A p vs) p) 
          (limit_pair_vectors (defer m A p vs) vs)"
        using a_still_deferred_p card_1_singletonE
              insert_subset singletonD
        by metis
      have a_still_deferred_q:
        "a \<in> defer n (defer m A q vs)
          (limit_profile (defer m A p vs) q) (limit_pair_vectors (defer m A p vs) vs)"
        using still_lifted a_in_def_p
              defer_monotonicity_def
              defer_monotone_n electoral_mod_m
              same_alternatives
              def_presv_fin_prof finite_profile_q finite_profile_p
              def_presv_fin_vector_pair vec_A
        by metis
      have "card (defer m A q vs) \<ge> 1"
        using card_le_1_p same_alternatives
        by auto
      hence
        "card (defer n (defer m A q vs)
          (limit_profile (defer m A q vs) q) (limit_pair_vectors (defer m A q vs) vs)) = 1"
        using defers_1 defers_def electoral_mod_m
              finite_profile_q def_presv_fin_prof vec_A lifted_a def_presv_fin_vector_pair 
        by metis
      hence def_set_is_a_q:
        "{a} =
          defer n (defer m A q vs)
            (limit_profile (defer m A q vs) q) (limit_pair_vectors (defer m A q vs) vs)"
        using a_still_deferred_q card_1_singletonE
              same_alternatives singletonD
        by metis
      have
        "defer n (defer m A p vs)
          (limit_profile (defer m A p vs) p) (limit_pair_vectors (defer m A p vs) vs)=
            defer n (defer m A q vs)
              (limit_profile (defer m A q vs) q) (limit_pair_vectors (defer m A q vs) vs)"
        using def_set_is_a_q def_set_is_a_p
        by auto
      thus ?thesis
        using seq_comp_presv_non_electing
              eq_def_and_elect_imp_eq non_electing_def
              finite_profile_p finite_profile_q
              non_electing_m non_electing_n
              seq_comp_defers_def_set vec_A lifted_a
        by metis
    qed
  qed
qed

end
