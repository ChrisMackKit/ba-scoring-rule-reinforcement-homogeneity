theory Homogeneity
imports   "Compositional_Structures/Basic_Modules/Scoring_Module"
          "Compositional_Structures/Elect_Composition"
          "Compositional_Structures/Basic_Modules/Condorcet_Module"
begin
(***Homogeneity***)

lemma homogeneity_elim:
  assumes "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow>
      elimination_module e t r A p = elimination_module e t r A (times n p)"
shows "homogeneity (elimination_module e t r)" using homogeneity_def assms 
proof-
  have "electoral_module (elimination_module e t r)" by simp 
  then show ?thesis using assms
    using homogeneity_def by blast 
qed

lemma homogeneity_elim_set:
  assumes "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow>
      elimination_set e t r A p = elimination_set e t r A (times n p)"
shows "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow>
      elimination_module e t r A p = elimination_module e t r A (times n p)" 
  using assms by fastforce


(*In the eval_func_homogeneity lemma we needed the condition from this lemma, but
Isabelle did not accept it through an assumed statement directly in the lemma*)



lemma times_eval:
  shows "((e::'a Evaluation_Function) x A (times n p)) = e x A  p * n"
  sorry

(*Proof that a natural number k can be pulled out of the Max condition*)
lemma pull_numb_out_of_max:
  fixes k::nat and e::"'a Evaluation_Function"
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {e x A p * k |x. x\<in>A} = Max {e x A p|x. x\<in>A} * k" 
proof-
  have m: "\<And>x y. max x y * k = max (x*k) (y*k)"
    by(simp add: max_def antisym add_right_mono)
  have "{e x A p * k|x. x\<in>A} = (\<lambda>y. y * k) ` {e x A p|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {e x A p|x. x\<in>A} * k"
    using assms hom_Max_commute [of "\<lambda>y. y*k" "{e x A p|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed

(*If the elim_set is equal than is also max_elim equal*)
lemma max_value_same:
  assumes "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
       elimination_set eval_func (Max {eval_func x A p |x. x \<in> A}) (<) A p = 
       elimination_set eval_func (Max {eval_func x A (Electoral_Module.times n p) |x. x \<in> A}) 
       (<) A (Electoral_Module.times n p)"
  shows"(\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p = max_eliminator eval_func A (Electoral_Module.times n p))"
  unfolding max_eliminator.simps less_eliminator.simps elimination_module.simps using assms
  by fastforce 


(*if max value is bigger for p than also for n*p *)
lemma from_eval_follows_eval_n:
  fixes e::"'a Evaluation_Function"
  assumes "x \<in> A" and "xb \<in> A" and "finite A" and "profile A p" and "0 < n" and 
    "e xb A p < Max {e x A p |x. x \<in> A}"
  shows "e xb A (times n p) < Max {e x A (times n p) |x. x \<in> A}" 
proof-
  have 0 :"Max {e x A (times n p) |x. x \<in> A} = 
        Max {e x A p * n |x. x \<in> A}" 
      using times_eval by metis
  then have 1:  "Max {e x A (times n p) |x. x \<in> A} = 
      n* Max {e x A p |x. x \<in> A}" 
  proof -
     have "\<And>A rs n. infinite A \<or> A = Collect bot \<or> 
        Max {e (a::'a) A rs |a. a \<in> A} * n = Max {e a A rs * n |a. a \<in> A}" 
      using pull_numb_out_of_max bot_set_def assms by fastforce
    then have f5: "\<And>rs n. Max {e a A rs |a. a \<in> A} * n = 
              Max {e a A rs * n |a. a \<in> A}"
      using assms(1) assms(3) by blast
    have 
      "Max {e a A (times n p) |a. a \<in> A} = Max {e a A p * n |a. a \<in> A}"
      using assms 0 by clarify
    then show "Max {e a A (times n p) |a. a \<in> A} = 
          n * Max {e a A p |a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:"e xb A p < Max {e x A p |x. x \<in> A} \<Longrightarrow> 
            n* e xb A p < n* Max {e x A p |x. x \<in> A}"
    using assms(5) mult_less_mono2 by blast
  then have 3: "n* e xb A p < n* Max {e x A p |x. x \<in> A} \<Longrightarrow> 
    e xb A (times n p) < 
    Max {e x A (times n p) |x. x \<in> A}"
    by (metis (mono_tags, lifting) "1" mult.commute times_eval)
  then show "e xb A (times n p) < 
    Max {e x A (times n p) |x. x \<in> A}"
    using 2 assms by auto
qed



(*if max value is bigger for n*p than also for p *)
lemma from_eval_n_follows_eval:
  fixes e::"'a Evaluation_Function"
  assumes "x \<in> A" and "finite A" and "profile A p" and "0 < n" and "xa \<in> A" and "xb \<in> A" and
  "e xb A (times n p) < Max {e x A (times n p) |x. x \<in> A}"
shows "e xb A p < Max {e x A p |x. x \<in> A}" 
proof-
    have 0 :"Max {e x A (times n p) |x. x \<in> A} = 
        Max {e x A p * n |x. x \<in> A}" 
      using times_eval by metis 
  then have 1: "Max {e x A (times n p) |x. x \<in> A} = 
      n* Max {e x A p |x. x \<in> A}" 
  proof -
    have "\<And>A rs n. infinite A \<or> A = Collect bot \<or> 
        Max {e (a::'a) A rs |a. a \<in> A} * n = Max {e a A rs * n |a. a \<in> A}" 
      using pull_numb_out_of_max bot_set_def by fastforce 
    then have f5: "\<And>rs n. Max {e a A rs |a. a \<in> A} * n = 
              Max {e a A rs * n |a. a \<in> A}"
      using assms(1) assms(2) by blast
    have 
      "Max {e a A (times n p) |a. a \<in> A} = Max {e a A p * n |a. a \<in> A}"
      using assms 0 by clarify
    then show "Max {e a A (times n p) |a. a \<in> A} = 
          n * Max {e a A p |a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:"e xb A p < Max {e x A p |x. x \<in> A} \<Longrightarrow> 
            n* e xb A p < n* Max {e x A p |x. x \<in> A}"
    using assms(4) mult_less_mono2 by blast
  then have 3: "n* e xb A p < n* Max {e x A p |x. x \<in> A} \<Longrightarrow> 
    e xb A (times n p) < Max {e x A (times n p) |x. x \<in> A}"
    using assms(7) by auto 
  then show "e xb A p < Max {e x A p |x. x \<in> A}"
     using 1 2 assms(7) times_eval
     by (metis (no_types, lifting) mult.commute mult_less_cancel2) 
qed


lemma eval_func_homogeneity:
  assumes "\<forall>x. eval_func x A (times n p) = eval_func x A p * n"
  shows "homogeneity (max_eliminator eval_func)" 
  unfolding homogeneity_def 
proof-
  show "electoral_module (max_eliminator eval_func) \<and>
    (\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> max_eliminator eval_func A p = 
    max_eliminator eval_func A (Electoral_Module.times n p))"
  proof-
    have elim_set_same:
          "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
          elimination_set eval_func (Max {eval_func x A p |x. x \<in> A}) (<) A p = 
          elimination_set eval_func (Max {eval_func x A (Electoral_Module.times n p) |x. x \<in> A}) (<) A 
          (Electoral_Module.times n p)" 
      using from_eval_n_follows_eval from_eval_follows_eval_n
      by (smt (z3) Collect_cong elimination_set.simps)
    have elect_mod:"electoral_module (max_eliminator eval_func)" by auto
    have "(\<forall>A p n.
        finite_profile A p \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p =
        max_eliminator eval_func A (Electoral_Module.times n p))" 
      using  max_value_same elim_set_same by fastforce 
    then show ?thesis
      using elect_mod by blast 
  qed
qed

(*If two modules are homogenious, that the sequantial module is homogenious*)
lemma seq_hom:
  shows "homogeneity m \<Longrightarrow> homogeneity n \<Longrightarrow> homogeneity (m \<triangleright> n)"
  unfolding homogeneity_def
proof(auto)
  show "\<And>A p na.
       electoral_module m \<Longrightarrow>
       \<forall>A p n. finite A \<and> profile A p \<and> 0 < n \<longrightarrow> m A p = m A (concat (replicate n p)) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p na. finite A \<and> profile A p \<and> 0 < na \<longrightarrow> n A p = n A (concat (replicate na p)) \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p \<Longrightarrow>
       0 < na \<Longrightarrow>
       (let new_A = defer m A (concat (replicate na p)); new_p = map (limit new_A) p
        in (elect m A (concat (replicate na p)) \<union> elect n new_A new_p,
            reject m A (concat (replicate na p)) \<union> reject n new_A new_p, defer n new_A new_p)) =
       (let new_A = defer m A (concat (replicate na p)); new_p = 
          map (limit new_A) (concat (replicate na p))
        in (elect m A (concat (replicate na p)) \<union> elect n new_A new_p,
            reject m A (concat (replicate na p)) \<union> reject n new_A new_p, defer n new_A new_p))"
    by (smt (z3) def_presv_fin_prof limit_profile.simps map_concat map_replicate)
qed


(*elector module satisfies homogeneity*)
lemma elector_homogeneity:
  shows "homogeneity m \<Longrightarrow> homogeneity (elector m)"
proof(simp)
  have "homogeneity elect_module"
    by (simp add: homogeneity_def) 
  then show "homogeneity m \<Longrightarrow> homogeneity (m \<triangleright> elect_module)" using seq_hom by auto
qed
