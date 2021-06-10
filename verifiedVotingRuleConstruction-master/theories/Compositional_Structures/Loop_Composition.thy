(*  File:       Loop_Composition.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Loop Composition\<close>

theory Loop_Composition
  imports "Basic_Modules/Component_Types/Termination_Condition"
          "Basic_Modules/Defer_Module"
          Sequential_Composition
begin

text
\<open>The loop composition uses the same module in sequence,
combined with a termination condition, until either
  (1) the termination condition is met or
  (2) no new decisions are made (i.e., a fixed point is reached).\<close>

subsection \<open>Definition\<close>

lemma loop_termination_helper:
  assumes             
    not_term: "\<not>t (acc A p vs)" and
    subset: "defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs" and
    not_inf: "\<not>infinite (defer acc A p vs)"
  shows
    "((acc \<triangleright> m, m, t, A, p), (acc, m, t, A, p)) \<in>
        measure (\<lambda>(acc, m, t, A, p). card (defer acc A p vs))"
  using assms psubset_card_mono
  by auto

(*
   This function handles the accumulator for the following loop composition
   function.
*)
function loop_comp_helper ::
    "'a Electoral_Module \<Rightarrow> 'a Electoral_Module \<Rightarrow>
        'a Termination_Condition \<Rightarrow> 'a Electoral_Module" where
  "t (acc A p vs) \<or> \<not>((defer (acc \<triangleright> m) A p vs) \<subset> (defer acc A p vs)) \<or>
    infinite (defer acc A p vs) \<Longrightarrow>
      loop_comp_helper acc m t A p vs = acc A p vs" |
  "\<not>(t (acc A p vs) \<or> \<not>((defer (acc \<triangleright> m) A p vs) \<subset> (defer acc A p vs)) \<or>
    infinite (defer acc A p vs)) \<Longrightarrow>
      loop_comp_helper acc m t A p vs = loop_comp_helper (acc \<triangleright> m) m t A p vs"
proof -
  fix
    P :: bool and
    x :: "('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
          ('a Termination_Condition) \<times> 'a set \<times> 'a Profile \<times> 'a Pair_Vectors"
  assume
    a1: "\<And>t acc A p vs m.
          \<lbrakk>t (acc A p vs) \<or> \<not> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<or>
              infinite (defer acc A p vs);
            x = (acc, m, t, A, p, vs)\<rbrakk> \<Longrightarrow> P" and
    a2: "\<And>t acc A p vs m.
          \<lbrakk>\<not> (t (acc A p vs) \<or> \<not> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<or>
              infinite (defer acc A p vs));
            x = (acc, m, t, A, p, vs)\<rbrakk> \<Longrightarrow> P"
  have "\<exists>f A p p2 g vs. (g, f, p, A, p2, vs) = x"
    using prod_cases5
    by metis
  then show P
    using a2 a1
    by (metis (no_types))
next
  show
    "\<And>t acc A p vs m ta acca Aa pa vsa ma.
       t (acc A p vs) \<or> \<not> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<or>
        infinite (defer acc A p vs) \<Longrightarrow>
          ta (acca Aa pa vsa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa vsa \<subset> defer acca Aa pa vsa \<or>
          infinite (defer acca Aa pa vsa) \<Longrightarrow>
           (acc, m, t, A, p, vs) = (acca, ma, ta, Aa, pa, vsa) \<Longrightarrow>
              acc A p vs= acca Aa pa vsa"
    by fastforce
next
  show
    "\<And>t acc A p vs m ta acca Aa pa vsa ma.
       t (acc A p vs) \<or> \<not> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<or>
        infinite (defer acc A p vs) \<Longrightarrow>
          \<not> (ta (acca Aa pa vsa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa vsa \<subset> defer acca Aa pa vsa \<or>
          infinite (defer acca Aa pa vsa)) \<Longrightarrow>
           (acc, m, t, A, p, vs) = (acca, ma, ta, Aa, pa, vsa) \<Longrightarrow>
              acc A p vs = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa, vsa)"
  proof -
    fix
      t :: "'a Termination_Condition" and
      acc :: "'a Electoral_Module" and
      A :: "'a set" and
      p :: "'a Profile" and
      vs :: "'a Pair_Vectors" and
      m :: "'a Electoral_Module" and
      ta :: "'a Termination_Condition" and
      acca :: "'a Electoral_Module" and
      Aa :: "'a set" and
      pa :: "'a Profile" and
      vsa :: "'a Pair_Vectors" and
      ma :: "'a Electoral_Module"
    assume
      a1: "t (acc A p vs) \<or> \<not> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<or>
            infinite (defer acc A p vs)" and
      a2: "\<not> (ta (acca Aa pa vsa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa vsa \<subset> defer acca Aa pa vsa \<or>
            infinite (defer acca Aa pa vsa))" and
      "(acc, m, t, A, p, vs) = (acca, ma, ta, Aa, pa, vsa)"
    hence False
      using a2 a1
      by force
  thus "acc A p vs = loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa, vsa)"
    by auto
qed
next
  show
    "\<And>t acc A p vs m ta acca Aa pa vsa ma.
       \<not> (t (acc A p vs) \<or> \<not> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<or>
          infinite (defer acc A p vs)) \<Longrightarrow>
           \<not> (ta (acca Aa pa vsa) \<or> \<not> defer (acca \<triangleright> ma) Aa pa vsa \<subset> defer acca Aa pa vsa \<or>
            infinite (defer acca Aa pa vsa)) \<Longrightarrow>
             (acc, m, t, A, p, vs) = (acca, ma, ta, Aa, pa, vsa) \<Longrightarrow>
                loop_comp_helper_sumC (acc \<triangleright> m, m, t, A, p, vs) =
                  loop_comp_helper_sumC (acca \<triangleright> ma, ma, ta, Aa, pa, vsa)"
    by force
qed
termination
proof -
  have f0:
    "\<exists>r. wf r \<and>
        (\<forall>p f (A::'a set) prof g vs.
          p (f A prof) \<or>
          \<not> defer (f \<triangleright> g) A prof vs \<subset> defer f A prof vs \<or>
          infinite (defer f A prof vs) \<or>
          ((f \<triangleright> g, g, p, A, prof, vs), (f, g, p, A, prof, vs)) \<in> r)"
    using loop_termination_helper wf_measure "termination"
    (*by (metis (no_types))*) sorry
  hence
    "\<forall>r p.
      Ex ((\<lambda>ra. \<forall>f (A::'a set) prof pa g vs.
            \<exists>prof2 pb p_rel pc pd h (B::'a set) prof3 i pe vs1.
        \<not> wf r \<or>
          loop_comp_helper_dom
            (p::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
              (_ Termination_Condition) \<times> _ set \<times> _ Profile \<times> _ Pair_Vectors) \<or>
          infinite (defer f A prof vs) \<or>
          pa (f A prof) \<and>
            wf
              (prof2::((
                ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
                ('a Termination_Condition) \<times> 'a set \<times> 'a Profile \<times> 'a Pair_Vectors) \<times> _) set) \<and>
            \<not> loop_comp_helper_dom (pb::
                ('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                (_ Termination_Condition) \<times> _ set \<times> _ Profile \<times> _ Pair_Vectors) \<or>
          wf p_rel \<and> \<not> defer (f \<triangleright> g) A prof vs \<subset> defer f A prof vs \<and>
            \<not> loop_comp_helper_dom
                (pc::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile \<times> _ Pair_Vectors) \<or>
            ((f \<triangleright> g, g, pa, A, prof, vs), f, g, pa, A, prof, vs) \<in> p_rel \<and> wf p_rel \<and>
            \<not> loop_comp_helper_dom
                (pd::('a Electoral_Module) \<times> (_ Electoral_Module) \<times>
                  (_ Termination_Condition) \<times> _ set \<times> _ Profile \<times> _ Pair_Vectors) \<or>
            finite (defer h B prof3 vs1) \<and>
            defer (h \<triangleright> i) B prof3 vs1 \<subset> defer h B prof3 vs1\<and>
            \<not> pe (h B prof3) \<and>
            ((h \<triangleright> i, i, pe, B, prof3, vs1), h, i, pe, B, prof3, vs1) \<notin> r)::
          ((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile \<times> 'a Pair_Vectors) \<times>
            ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
            ('a Termination_Condition) \<times> 'a set \<times> 'a Profile \<times> 'a Pair_Vectors) set \<Rightarrow> bool)"
    (*by metis*) sorry
  obtain
    p_rel ::  "((('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
               ('a Termination_Condition) \<times> 'a set \<times> 'a Profile \<times> 'a Pair_Vectors) \<times>
               ('a Electoral_Module) \<times> ('a Electoral_Module) \<times>
               ('a Termination_Condition) \<times> 'a set \<times> 'a Profile \<times> 'a Pair_Vectors) set" where
      "wf p_rel \<and>
        (\<forall>p f A prof g vs. p (f A prof vs) \<or>
          \<not> defer (f \<triangleright> g) A prof vs \<subset> defer f A prof vs \<or>
          infinite (defer f A prof vs) \<or>
          ((f \<triangleright> g, g, p, A, prof, vs), f, g, p, A, prof, vs) \<in> p_rel)"
    using f0
    (*by presburger*) sorry
  thus ?thesis
    using "termination"
    by metis
qed

lemma loop_comp_code_helper[code]:
  "loop_comp_helper acc m t A p vs =
    (if (t (acc A p vs) \<or> \<not>((defer (acc \<triangleright> m) A p vs) \<subset> (defer acc A p vs)) \<or>
      infinite (defer acc A p vs))
    then (acc A p vs) else (loop_comp_helper (acc \<triangleright> m) m t A p vs))" 
  by simp 
  

function loop_composition ::
    "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow>
        'a Electoral_Module" where
  "t ({}, {}, A) \<Longrightarrow>
    loop_composition m t A p vs = defer_module A p vs" |
  "\<not>(t ({}, {}, A)) \<Longrightarrow>
    loop_composition m t A p vs = (loop_comp_helper m m t) A p vs"
  by (fastforce, simp_all)
termination
  using  "termination" wf_empty
  by blast

abbreviation loop ::
  "'a Electoral_Module \<Rightarrow> 'a Termination_Condition \<Rightarrow> 'a Electoral_Module"
    ("_ \<circlearrowleft>\<^sub>_" 50) where
  "m \<circlearrowleft>\<^sub>t \<equiv> loop_composition m t"

lemma loop_comp_code[code]:
  "loop_composition m t A p vs =
    (if (t ({},{},A))
    then (defer_module A p vs) else (loop_comp_helper m m t) A p vs)"
  by simp

lemma loop_comp_helper_imp_partit:
  assumes
    module_m: "electoral_module m" and
    profile: "finite_profile A p" and
    vectors: "finite_pair_vectors A p vs"
  shows
    "electoral_module acc \<and> (n = card (defer acc A p vs)) \<Longrightarrow>
        well_formed A (loop_comp_helper acc m t A p vs)"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have
    "\<forall>(f::'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Result) g.
      (electoral_module f \<and> electoral_module g) \<longrightarrow>
        electoral_module (f \<triangleright> g)"
    by auto
  hence "electoral_module (acc \<triangleright> m)"
    using less.prems module_m
    by metis
  hence wf_acc:
    "\<not> t (acc A p vs) \<and> \<not> t (acc A p vs) \<and>
      defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<and>
      finite (defer acc A p vs) \<longrightarrow>
        well_formed A (loop_comp_helper acc m t A p vs)"
    using less.hyps less.prems loop_comp_helper.simps(2)
          psubset_card_mono
  by metis
  have "well_formed A (acc A p vs)"
    using electoral_module_def less.prems profile vectors
    by blast
  thus ?case
    using wf_acc loop_comp_helper.simps(1)
    by (metis (no_types))
qed

subsection \<open>Soundness\<close>

theorem loop_comp_sound:
  assumes m_module: "electoral_module m"
  shows "electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound electoral_module_def loop_composition.simps(1)
        loop_composition.simps(2) loop_comp_helper_imp_partit m_module
  by metis

lemma loop_comp_helper_imp_no_def_incr:
  assumes
    module_m: "electoral_module m"
  shows
    "(electoral_module acc \<and> n = card (defer acc A p vs)) \<Longrightarrow>
        defer (loop_comp_helper acc m t) A p vs \<subseteq> defer acc A p vs"
proof (induct arbitrary: acc rule: less_induct)
  case (less)
  have emod_acc_m: "electoral_module (acc \<triangleright> m)"
    using less.prems module_m
    by simp
  have "\<forall>A Aa. infinite (A::'a set) \<or> \<not> Aa \<subset> A \<or> card Aa < card A"
    using psubset_card_mono
    by metis
  hence
    "\<not> t (acc A p vs) \<and> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<and>
      finite (defer acc A p vs) \<longrightarrow>
        defer (loop_comp_helper (acc \<triangleright> m) m t) A p vs \<subseteq> defer acc A p vs"
    using emod_acc_m less.hyps less.prems
    by blast
  hence
    "\<not> t (acc A p vs) \<and> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<and>
        finite (defer acc A p vs) \<longrightarrow>
          defer (loop_comp_helper acc m t) A p vs \<subseteq> defer acc A p vs"
    using loop_comp_helper.simps(2)
    by (metis (no_types))
  thus ?case
    using eq_iff loop_comp_helper.simps(1)
    by (metis (no_types))
qed

subsection \<open>Lemmata\<close>

lemma loop_comp_helper_def_lift_inv_helper:
  assumes
    monotone_m: "defer_lift_invariance m" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs"
  shows
    "(defer_lift_invariance acc \<and> n = card (defer acc A p vs)) \<longrightarrow>
        (\<forall>q a.
          (a \<in> (defer (loop_comp_helper acc m t) A p vs) \<and>
            lifted A p q a) \<longrightarrow>
                (loop_comp_helper acc m t) A p vs =
                  (loop_comp_helper acc m t) A q vs)"
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have defer_card_comp:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc \<triangleright> m) A p vs) = card (defer (acc \<triangleright> m) A q vs))"
    using monotone_m def_lift_inv_seq_comp_help f_vec
    by metis
  have defer_card_acc:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc) A p vs) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p vs) = card (defer (acc) A q vs))"
    by (smt (verit, del_insts) defer_lift_invariance_def f_vec)
  hence defer_card_acc_2:
    "defer_lift_invariance acc \<longrightarrow>
        (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> lifted A p q a) \<longrightarrow>
            card (defer (acc) A p vs) = card (defer (acc) A q vs))"
    using monotone_m f_prof defer_lift_invariance_def seq_comp_def_set_trans f_vec
    by metis
  thus ?case
  proof cases
    assume card_unchanged: "card (defer (acc \<triangleright> m) A p vs) = card (defer acc A p vs)"
    with defer_card_comp defer_card_acc monotone_m
    have
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (acc) A p vs) \<and> lifted A p q a) \<longrightarrow>
              (loop_comp_helper acc m t) A q vs= acc A q vs)"
    proof (safe)
      fix
        q :: "'a Profile" and
        a :: "'a"
      assume
        def_card_eq:
        "card (defer (acc \<triangleright> m) A p vs) = card (defer acc A p vs)" and
        dli_acc: "defer_lift_invariance acc" and
        def_seq_lift_card:
        "\<forall>q a. a \<in> defer (acc \<triangleright> m) A p vs \<and> Profile.lifted A p q a \<longrightarrow>
          card (defer (acc \<triangleright> m) A p vs) = card (defer (acc \<triangleright> m) A q vs)" and
        a_in_def_acc: "a \<in> defer acc A p vs" and
        lifted_A: "Profile.lifted A p q a"
      have emod_m: "electoral_module m"
        using defer_lift_invariance_def monotone_m
        by auto
      have emod_acc: "electoral_module acc"
        using defer_lift_invariance_def dli_acc
        by blast
      have acc_eq_pq: "acc A q vs = acc A p vs"
        using a_in_def_acc defer_lift_invariance_def dli_acc lifted_A f_vec
        by (metis (full_types))
      with emod_acc emod_m
      have
        "finite (defer acc A p vs) \<longrightarrow>
          loop_comp_helper acc m t A q vs = acc A q vs"
        using a_in_def_acc def_card_eq def_seq_lift_card
              dual_order.strict_iff_order f_prof lifted_A
              loop_comp_code_helper psubset_card_mono
              seq_comp_def_set_bounded f_vec
        by (metis (no_types))
      thus "loop_comp_helper acc m t A q vs = acc A q vs"
        using acc_eq_pq loop_comp_code_helper
        by (metis (full_types))
    qed
    moreover from card_unchanged have
      "(loop_comp_helper acc m t) A p vs = acc A p vs"
      using loop_comp_helper.simps(1) order.strict_iff_order
            psubset_card_mono
      by metis
    ultimately have
      "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (loop_comp_helper acc m t) A p vs) \<and>
              lifted A p q a) \<longrightarrow>
                  (loop_comp_helper acc m t) A p vs =
                    (loop_comp_helper acc m t) A q vs)"
      using defer_lift_invariance_def f_vec
      by metis
    thus ?thesis
      using monotone_m seq_comp_presv_def_lift_inv f_vec 
      (*by blast*) sorry
  next
    assume card_changed:
      "\<not> (card (defer (acc \<triangleright> m) A p vs) = card (defer acc A p vs))"
    with f_prof seq_comp_def_card_bounded have card_smaller_for_p:
      "electoral_module (acc) \<longrightarrow>
          (card (defer (acc \<triangleright> m) A p vs) < card (defer acc A p vs))"
      using monotone_m order.not_eq_order_implies_strict
            defer_lift_invariance_def f_vec
      by (metis (full_types))
    with defer_card_acc_2 defer_card_comp
    have card_changed_for_q:
      "defer_lift_invariance (acc) \<longrightarrow>
          (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> lifted A p q a) \<longrightarrow>
              (card (defer (acc \<triangleright> m) A q vs) < card (defer acc A q vs)))"
      using defer_lift_invariance_def
      by (metis (no_types, lifting))
    thus ?thesis
    proof cases
      assume t_not_satisfied_for_p: "\<not> t (acc A p vs)"
      hence t_not_satisfied_for_q:
        "defer_lift_invariance (acc) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> lifted A p q a) \<longrightarrow>
                \<not> t (acc A q vs))"
        using monotone_m f_prof defer_lift_invariance_def seq_comp_def_set_trans f_vec
        by metis
      from card_changed defer_card_comp defer_card_acc
      have dli_card_def:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> Profile.lifted A p q a) \<longrightarrow>
                card (defer (acc \<triangleright> m) A q vs) \<noteq> (card (defer acc A q vs)))"
      proof -
        have
          "\<forall>f.
            (defer_lift_invariance f \<or>
              (\<exists>A prof prof2 (a::'a) vs.
                f A prof vs \<noteq> f A prof2 vs \<and>
                  Profile.lifted A prof prof2 a \<and>
                  a \<in> defer f A prof vs) \<or> \<not> electoral_module f) \<and>
                  ((\<forall>A p1 p2 b vs. f A p1 vs = f A p2 vs \<or> \<not> Profile.lifted A p1 p2 b \<or>
                    b \<notin> defer f A p1 vs) \<and>
                  electoral_module f \<or> \<not> defer_lift_invariance f)"
          using defer_lift_invariance_def f_vec
          (*by blast*) sorry
        thus ?thesis
          using card_changed monotone_m f_prof seq_comp_def_set_trans f_vec
          by (metis (no_types, hide_lams))
      qed
      hence dli_def_subset:
        "defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> lifted A p q a) \<longrightarrow>
                defer (acc \<triangleright> m) A q vs \<subset> defer acc A q vs)"
      proof -
        {
          fix
            alt :: 'a and
            prof :: "'a Profile"
          have
            "(\<not> defer_lift_invariance (acc \<triangleright> m) \<or> \<not> defer_lift_invariance acc) \<or>
              (alt \<notin> defer (acc \<triangleright> m) A p vs \<or> \<not> lifted A p prof alt) \<or>
              defer (acc \<triangleright> m) A prof vs \<subset> defer acc A prof vs"
            using Profile.lifted_def dli_card_def defer_lift_invariance_def
                  monotone_m psubsetI seq_comp_def_set_bounded f_vec lifted_finite_vectors
            by (metis (no_types))
        }
        thus ?thesis
          by metis
      qed
      with t_not_satisfied_for_p
      have rec_step_q:
        "(defer_lift_invariance (acc \<triangleright> m) \<and> defer_lift_invariance (acc)) \<longrightarrow>
            (\<forall>q a. (a \<in> (defer (acc \<triangleright> m) A p vs) \<and> lifted A p q a) \<longrightarrow>
                loop_comp_helper acc m t A q vs=
                  loop_comp_helper (acc \<triangleright> m) m t A q vs)"
      proof (safe)
        fix
          q :: "'a Profile" and
          a :: "'a"
        assume
          a_in_def_impl_def_subset:
          "\<forall>q a. a \<in> defer (acc \<triangleright> m) A p vs \<and> lifted A p q a \<longrightarrow>
            defer (acc \<triangleright> m) A q vs \<subset> defer acc A q vs" and
          dli_acc: "defer_lift_invariance acc" and
          a_in_def_seq_acc_m: "a \<in> defer (acc \<triangleright> m) A p vs" and
          lifted_pq_a: "lifted A p q a"
        have defer_subset_acc:
          "defer (acc \<triangleright> m) A q vs \<subset> defer acc A q vs"
          using a_in_def_impl_def_subset lifted_pq_a
                a_in_def_seq_acc_m
          by metis
        have "electoral_module acc"
          using dli_acc defer_lift_invariance_def
          by auto
        hence "finite (defer acc A q vs) \<and> \<not> t (acc A q vs)"
          using lifted_def dli_acc a_in_def_seq_acc_m
                lifted_pq_a def_presv_fin_prof
                t_not_satisfied_for_q f_vec lifted_finite_vectors
          by metis
        with defer_subset_acc
        show
          "loop_comp_helper acc m t A q vs=
            loop_comp_helper (acc \<triangleright> m) m t A q vs"
          using loop_comp_code_helper 
          by metis
      qed
      have rec_step_p:
        "electoral_module acc \<longrightarrow>
            loop_comp_helper acc m t A p vs = loop_comp_helper (acc \<triangleright> m) m t A p vs"
      proof (safe)
        assume emod_acc: "electoral_module acc"
        have emod_implies_defer_subset:
          "electoral_module m \<longrightarrow> defer (acc \<triangleright> m) A p vs \<subseteq> defer acc A p vs"
          using emod_acc f_prof seq_comp_def_set_bounded f_vec
          by blast
        have card_ineq: "card (defer (acc \<triangleright> m) A p vs) < card (defer acc A p vs)"
          using card_smaller_for_p emod_acc
          by force
        have fin_def_limited_acc:
          "finite_profile (defer acc A p vs) (limit_profile (defer acc A p vs) p)"
          using def_presv_fin_prof emod_acc f_prof f_vec
          by metis
        have "defer (acc \<triangleright> m) A p vs \<subseteq> defer acc A p vs"
          using emod_implies_defer_subset defer_lift_invariance_def monotone_m
          by blast
        hence "defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs"
          using fin_def_limited_acc card_ineq card_psubset
          by metis
        with fin_def_limited_acc
        show "loop_comp_helper acc m t A p vs = loop_comp_helper (acc \<triangleright> m) m t A p vs"
          using loop_comp_code_helper t_not_satisfied_for_p
          by (metis (no_types))
      qed
      show ?thesis
      proof (safe)
        fix
          q :: "'a Profile" and
          a :: "'a"
        assume
          dli_acc: "defer_lift_invariance acc" and
          n_card_acc: "n = card (defer acc A p vs)" and
          a_in_defer_lch: "a \<in> defer (loop_comp_helper acc m t) A p vs" and
          a_lifted: "Profile.lifted A p q a"
        hence emod_acc: "electoral_module acc"
          using defer_lift_invariance_def
          by metis
        have "defer_lift_invariance (acc \<triangleright> m) \<and> a \<in> defer (acc \<triangleright> m) A p vs"
          using a_in_defer_lch defer_lift_invariance_def dli_acc
                f_prof loop_comp_helper_imp_no_def_incr monotone_m
                rec_step_p seq_comp_presv_def_lift_inv subsetD f_vec
          by (metis (no_types))
        with emod_acc
        show "loop_comp_helper acc m t A p vs = loop_comp_helper acc m t A q vs"
          using a_in_defer_lch a_lifted card_smaller_for_p dli_acc
                less.hyps n_card_acc rec_step_p rec_step_q
          by (metis (full_types))
      qed
    next
      assume "\<not> \<not>t (acc A p vs)"
      with defer_lift_invariance_def
      show ?thesis
        using loop_comp_helper.simps(1) f_vec
        by metis
    qed
  qed
qed

lemma loop_comp_helper_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    profile: "finite_profile A p" and
    vector: "finite_pair_vectors A p vs"
    
  shows
    "\<forall>q a. (lifted A p q a \<and> a \<in> (defer (loop_comp_helper acc m t) A p vs)) \<longrightarrow>
        (loop_comp_helper acc m t) A p vs= (loop_comp_helper acc m t) A q vs"
  using loop_comp_helper_def_lift_inv_helper
        monotone_m monotone_acc profile vector 
  by blast

lemma loop_comp_helper_def_lift_inv2:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    finite_A_p: "finite_profile A p" and
    lifted_A_pq: "lifted A p q a" and
    finite_vec: "finite_pair_vectors A p vs" and
    a_in_defer_acc: "a \<in> defer (loop_comp_helper acc m t) A p vs"
  shows
    "(loop_comp_helper acc m t) A p vs = (loop_comp_helper acc m t) A q vs"
  using finite_A_p lifted_A_pq a_in_defer_acc
        loop_comp_helper_def_lift_inv
        monotone_acc monotone_m finite_vec
  by blast

lemma lifted_imp_fin_prof:
  assumes "lifted A p q a"
  shows "finite_profile A p"
  using assms Profile.lifted_def
  by fastforce

lemma loop_comp_helper_presv_def_lift_inv:
  assumes
    monotone_m: "defer_lift_invariance m" and
    monotone_acc: "defer_lift_invariance acc" and
    f_vec: "finite_pair_vectors A p vs"
  shows "defer_lift_invariance (loop_comp_helper acc m t)"
proof -
  have
    "\<forall>f. (defer_lift_invariance f \<or>
         (\<exists>A prof prof2 (a::'a) vs.
            f A prof vs \<noteq> f A prof2 vs \<and>
              Profile.lifted A prof prof2 a \<and>
              finite_pair_vectors A prof vs \<and>
              a \<in> defer f A prof vs) \<or>
         \<not> electoral_module f) \<and>
      ((\<forall>A prof prof2 a vs. f A prof vs = f A prof2 vs \<or>
          \<not> Profile.lifted A prof prof2 a \<or>
          \<not> finite_pair_vectors A prof vs \<or>
          a \<notin> defer f A prof vs) \<and>
      electoral_module f \<or> \<not> defer_lift_invariance f)"
    using defer_lift_invariance_def f_vec lifted_finite_vectors
    (*by blast*) sorry
  thus ?thesis
    using electoral_module_def lifted_imp_fin_prof
          loop_comp_helper_def_lift_inv loop_comp_helper_imp_partit
          monotone_acc monotone_m f_vec defer_lift_invariance_def
    by (metis (full_types))
qed

lemma loop_comp_presv_non_electing_helper:
  assumes
    non_electing_m: "non_electing m" and
    non_electing_acc: "non_electing acc" and
    f_prof: "finite_profile A p" and
    f_vec: "finite_pair_vectors A p vs" and
    acc_defer_card: "n = card (defer acc A p vs)"
  shows "elect (loop_comp_helper acc m t) A p vs = {}"
  using acc_defer_card non_electing_acc
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  thus ?case
  proof (safe)
    fix x :: "'a"
    assume
      y_acc_no_elect:
      "(\<And>y acc'. y < card (defer acc A p vs) \<Longrightarrow>
        y = card (defer acc' A p vs) \<Longrightarrow> non_electing acc' \<Longrightarrow>
          elect (loop_comp_helper acc' m t) A p vs = {})" and
      acc_non_elect:
      "non_electing acc" and
      x_in_acc_elect:
      "x \<in> elect (loop_comp_helper acc m t) A p vs"
    have
      "\<forall>(f::'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Result) g.
        (non_electing f \<and> non_electing g) \<longrightarrow>
          non_electing (f \<triangleright> g)"
      by simp
    hence seq_acc_m_non_elect: "non_electing (acc \<triangleright> m)"
      using acc_non_elect non_electing_m
      by blast
    have "\<forall>A B. (finite (A::'a set) \<and> B \<subset> A) \<longrightarrow> card B < card A"
      using psubset_card_mono
      by metis
    hence card_ineq:
      "\<forall>A B. (finite (A::'a set) \<and> B \<subset> A) \<longrightarrow> card B < card A"
      by presburger
    have no_elect_acc: "elect acc A p vs = {}"
      using acc_non_elect f_prof non_electing_def f_vec
      by blast
    have card_n_no_elect:
      "\<forall>n f.
        (n < card (defer acc A p vs) \<and> n = card (defer f A p vs) \<and> non_electing f) \<longrightarrow>
          elect (loop_comp_helper f m t) A p vs = {}"
      using y_acc_no_elect
      by blast
    have
      "\<And>f.
        (finite (defer acc A p vs) \<and> defer f A p vs \<subset> defer acc A p vs \<and> non_electing f) \<longrightarrow>
          elect (loop_comp_helper f m t) A p vs = {}"
      using card_n_no_elect psubset_card_mono
      by metis
    hence f0:
      "(\<not> t (acc A p vs) \<and> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs \<and>
            finite (defer acc A p vs)) \<and>
          \<not> t (acc A p vs) \<longrightarrow>
        elect (loop_comp_helper acc m t) A p vs = {}"
      using loop_comp_code_helper seq_acc_m_non_elect
      by (metis (no_types))
    obtain set_func :: "'a set \<Rightarrow> 'a" where
      "\<forall>A. (A = {} \<longrightarrow> (\<forall>a. a \<notin> A)) \<and> (A \<noteq> {} \<longrightarrow> set_func A \<in> A)"
      using all_not_in_conv
      by (metis (no_types))
    thus "x \<in> {}"
      using loop_comp_code_helper no_elect_acc x_in_acc_elect f0
      by (metis (no_types))
  qed
qed

lemma loop_comp_helper_iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    f_vec: "vector_pair A p vs" and
    n_acc_defer_card: "n = card (defer acc A p vs)" and
    n_ge_x: "n \<ge> x" and
    def_card_gt_one: "card (defer acc A p vs) > 1" and
    acc_nonelect: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) A p vs) = x"
  using n_ge_x def_card_gt_one acc_nonelect n_acc_defer_card
proof (induct n arbitrary: acc rule: less_induct)
  case (less n)
  have subset:
    "(card (defer acc A p vs) > 1 \<and> finite_profile A p \<and> finite_pair_vectors A p vs 
        \<and> electoral_module acc) \<longrightarrow> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs"
    using seq_comp_elim_one_red_def_set single_elimination
    by blast
  hence step_reduces_defer_set:
    "(card (defer acc A p vs) > 1 \<and> finite_profile A p \<and> finite_pair_vectors A p vs 
        \<and> non_electing acc) \<longrightarrow> defer (acc \<triangleright> m) A p vs \<subset> defer acc A p vs"
    using non_electing_def
    by auto
  thus ?case
  proof cases
    assume term_satisfied: "t (acc A p vs)"
    have "card (defer_r (loop_comp_helper acc m t A p vs)) = x"
      using loop_comp_helper.simps(1) term_satisfied terminate_if_n_left
      by metis
    thus ?case
      by blast
  next
    assume term_not_satisfied: "\<not>(t (acc A p vs))"
    hence card_not_eq_x: "card (defer acc A p vs) \<noteq> x"
      by (simp add: terminate_if_n_left)
    have rec_step:
      "(card (defer acc A p vs) > 1 \<and> finite_profile A p \<and> finite_pair_vectors A p vs 
          \<and> non_electing acc) \<longrightarrow> loop_comp_helper acc m t A p vs =
              loop_comp_helper (acc \<triangleright> m) m t A p vs" (*needed for step*)
      using loop_comp_helper.simps(2) non_electing_def def_presv_fin_prof
            step_reduces_defer_set term_not_satisfied
      by metis
    thus ?case
    proof cases
      assume card_too_small:
        "card (defer acc A p vs) < x"
      thus ?thesis
        using not_le card_too_small less.prems(1) less.prems(4) not_le
        by (metis (no_types))
    next
      assume old_card_at_least_x: "\<not>(card (defer acc A p vs) < x)"
      obtain i where i_is_new_card: "i = card (defer (acc \<triangleright> m) A p vs)"
        by blast
      with card_not_eq_x
      have card_too_big:
        "card (defer acc A p vs) > x"
        using nat_neq_iff old_card_at_least_x
        by blast
      hence enough_leftover:
        "card (defer acc A p vs) > 1"
        using x_greater_zero
        by auto
      have "electoral_module acc \<longrightarrow> (defer acc A p vs) \<subseteq> A"
        by (simp add: defer_in_alts f_prof f_vec)
      hence step_profile:
        "electoral_module acc \<longrightarrow>
            finite_profile (defer acc A p vs)
              (limit_profile (defer acc A p vs) p)"
        using f_prof limit_profile_sound
        by auto
      hence
        "electoral_module acc \<longrightarrow>
            card (defer m (defer acc A p vs)
              (limit_profile (defer acc A p vs) p) 
              (limit_pair_vectors (defer acc A p vs) vs)) =
                card (defer acc A p vs) - 1"
        using non_electing_m single_elimination
              single_elim_decr_def_card2 enough_leftover
        by (metis def_presv_fin_vector_pair f_prof f_vec)
      hence "electoral_module acc \<longrightarrow> i = card (defer acc A p vs) - 1"
        using sequential_composition.simps snd_conv i_is_new_card
        by metis
      hence "electoral_module acc \<longrightarrow> i \<ge> x"
        using card_too_big
        by linarith
      hence new_card_still_big_enough: "electoral_module acc \<longrightarrow> x \<le> i"
        by blast
      have
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            defer (acc \<triangleright> m) A p vs \<subseteq> defer acc A p vs"
        using enough_leftover f_prof subset f_vec
        by blast
      hence
        "electoral_module acc \<and> electoral_module m \<longrightarrow>
            i \<le> card (defer acc A p vs)"
        using card_mono i_is_new_card step_profile
        by blast
      hence i_geq_x:
        "electoral_module acc \<and> electoral_module m \<longrightarrow> (i = x \<or> i > x)"
        using nat_less_le new_card_still_big_enough
        by blast
      thus ?thesis
      proof cases
        assume new_card_greater_x: "electoral_module acc \<longrightarrow> i > x"
        hence "electoral_module acc \<longrightarrow> 1 < card (defer (acc \<triangleright> m) A p vs)"
          using x_greater_zero i_is_new_card
          by linarith
        moreover have new_card_still_big_enough2:
          "electoral_module acc \<longrightarrow> x \<le> i" (* Needed for step *)
          using i_is_new_card new_card_still_big_enough
          by blast
        moreover have
          "n = card (defer acc A p vs) \<longrightarrow>
              (electoral_module acc \<longrightarrow> i < n)" (* Needed for step *)
          using subset step_profile enough_leftover f_prof psubset_card_mono
                i_is_new_card f_vec
          by blast
        moreover have
          "electoral_module acc \<longrightarrow>
              electoral_module (acc \<triangleright> m)" (* Needed for step *)
          using non_electing_def non_electing_m seq_comp_sound
          by blast
        moreover have non_electing_new:
          "non_electing acc \<longrightarrow> non_electing (acc \<triangleright> m)"
          by (simp add: non_electing_m)
        ultimately have card_x:
          "(n = card (defer acc A p vs) \<and> non_electing acc \<and>
              electoral_module acc) \<longrightarrow>
                  card (defer (loop_comp_helper (acc \<triangleright> m) m t) A p vs) = x"
          using less.hyps i_is_new_card new_card_greater_x
          by blast
        have f1: "loop_comp_helper acc m t A p vs = loop_comp_helper (acc \<triangleright> m) m t A p vs"
          using enough_leftover f_prof less.prems(3) rec_step f_vec
          by blast
        have "electoral_module acc"
          using less.prems(3) non_electing_def
          by blast
        thus ?thesis
          using f1 card_x less.prems(3) less.prems(4)
          by presburger
      next
        assume i_not_gt_x: "\<not>(electoral_module acc \<longrightarrow> i > x)"
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> i = x"
          using i_geq_x
          by blast
        hence "electoral_module acc \<and> electoral_module m \<longrightarrow> t ((acc \<triangleright> m) A p vs)"
          using i_is_new_card terminate_if_n_left
          by blast
        hence
          "electoral_module acc \<and> electoral_module m \<longrightarrow>
              card (defer_r (loop_comp_helper (acc \<triangleright> m) m t A p vs)) = x"
          using loop_comp_helper.simps(1) terminate_if_n_left
          by metis
        thus ?thesis
          using i_not_gt_x dual_order.strict_iff_order i_is_new_card
                loop_comp_helper.simps(1) new_card_still_big_enough
                f_prof rec_step terminate_if_n_left
                enough_leftover less.prems(3) f_vec
          by metis
      qed
    qed
  qed
qed

lemma loop_comp_helper_iter_elim_def_n:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    f_vec: "vector_pair A p vs" and
    acc_defers_enough: "card (defer acc A p vs) \<ge> x" and
    non_electing_acc: "non_electing acc"
  shows "card (defer (loop_comp_helper acc m t) A p vs) = x"
  using acc_defers_enough gr_implies_not0 le_neq_implies_less
        less_one linorder_neqE_nat loop_comp_helper.simps(1)
        loop_comp_helper_iter_elim_def_n_helper non_electing_acc
        non_electing_m f_prof single_elimination nat_neq_iff
        terminate_if_n_left x_greater_zero less_le f_vec
  by (metis (no_types, lifting))

lemma iter_elim_def_n_helper:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = x))" and
    x_greater_zero: "x > 0" and
    f_prof: "finite_profile A p" and
    f_vec: "vector_pair A p vs" and
    enough_alternatives: "card A \<ge> x"
  shows "card (defer (m \<circlearrowleft>\<^sub>t) A p vs) = x"
proof cases
  assume "card A = x"
  thus ?thesis
    by (simp add: terminate_if_n_left)
next
  assume card_not_x: "\<not> card A = x"
  thus ?thesis
  proof cases
    assume "card A < x"
    thus ?thesis
      using enough_alternatives not_le
      by blast
  next
    assume "\<not>card A < x"
    hence card_big_enough_A: "card A > x"
      using card_not_x
      by linarith
    hence card_m: "card (defer m A p vs) = card A - 1"
      using non_electing_m f_prof single_elimination
            single_elim_decr_def_card2 x_greater_zero f_vec
      by fastforce
    hence card_big_enough_m: "card (defer m A p vs) \<ge> x"
      using card_big_enough_A
      by linarith
    hence "(m \<circlearrowleft>\<^sub>t) A p vs = (loop_comp_helper m m t) A p vs"
      by (simp add: card_not_x terminate_if_n_left)
    thus ?thesis
      using card_big_enough_m non_electing_m f_prof single_elimination
            terminate_if_n_left x_greater_zero f_vec
            loop_comp_helper_iter_elim_def_n
      by metis
  qed
qed

subsection \<open>Composition Rules\<close>

(*The loop composition preserves defer-lift-invariance.*)
theorem loop_comp_presv_def_lift_inv[simp]:
  assumes monotone_m: "defer_lift_invariance m" and
          f_vec: "vector_pair A p vs"
  shows "defer_lift_invariance (m \<circlearrowleft>\<^sub>t)"
  unfolding defer_lift_invariance_def
proof (safe)
  from monotone_m
  have "electoral_module m"
    unfolding defer_lift_invariance_def
    by simp
  thus "electoral_module (m \<circlearrowleft>\<^sub>t)"
    by (simp add: loop_comp_sound)
next
  fix
    A :: "'a set" and
    p :: "'a Profile" and
    q :: "'a Profile" and
    vs :: "'a Pair_Vectors" and
    a :: "'a"
  assume
    a_in_loop_defer: "a \<in> defer (m \<circlearrowleft>\<^sub>t) A p vs" and
    lifted_a: "Profile.lifted A p q a" and
    fin_vec: "vector_pair A p vs"
  have defer_lift_loop:
    "\<forall> p q a vs. (a \<in> (defer (m \<circlearrowleft>\<^sub>t) A p vs)\<and> vector_pair A p vs \<and> lifted A p q a) \<longrightarrow>
        (m \<circlearrowleft>\<^sub>t) A p vs = (m \<circlearrowleft>\<^sub>t) A q vs"
    using monotone_m lifted_imp_fin_prof loop_comp_helper_def_lift_inv2
          loop_composition.simps defer_module.simps
    by (metis (full_types))
  show "(m \<circlearrowleft>\<^sub>t) A p vs = (m \<circlearrowleft>\<^sub>t) A q vs"
    using a_in_loop_defer lifted_a defer_lift_loop fin_vec
    by metis
qed

(*The loop composition preserves the property non-electing.*)
theorem loop_comp_presv_non_electing[simp]:
  assumes non_electing_m: "non_electing m"
  shows "non_electing (m \<circlearrowleft>\<^sub>t)"
  unfolding non_electing_def
proof (safe, simp_all)
  show "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound non_electing_def non_electing_m
    by metis
next
    fix
      A :: "'a set" and
      p :: "'a Profile" and
      vs :: "'a Pair_Vectors" and
      x :: "'a"
    assume
      fin_A: "finite A" and
      prof_A: "profile A p" and
      vec_A: "vector_pair A p vs" and
      x_elect: "x \<in> elect (m \<circlearrowleft>\<^sub>t) A p vs"
    show "False"
  using def_mod_non_electing loop_comp_presv_non_electing_helper
        non_electing_m empty_iff fin_A loop_comp_code
        non_electing_def prof_A x_elect vec_A
  by metis
qed

theorem iter_elim_def_n[simp]:
  assumes
    non_electing_m: "non_electing m" and
    single_elimination: "eliminates 1 m" and
    terminate_if_n_left: "\<forall> r. ((t r) \<longleftrightarrow> (card (defer_r r) = n))" and
    x_greater_zero: "n > 0"
  shows "defers n (m \<circlearrowleft>\<^sub>t)"
proof -
  have
    "\<forall> A p vs. finite_profile A p \<and> vector_pair A p vs \<and> card A \<ge> n \<longrightarrow>
        card (defer (m \<circlearrowleft>\<^sub>t) A p vs) = n"
    using iter_elim_def_n_helper non_electing_m single_elimination
          terminate_if_n_left x_greater_zero
    by blast
  moreover have "electoral_module (m \<circlearrowleft>\<^sub>t)"
    using loop_comp_sound eliminates_def single_elimination
    by blast
  thus ?thesis
    by (simp add: calculation defers_def)
qed

end
