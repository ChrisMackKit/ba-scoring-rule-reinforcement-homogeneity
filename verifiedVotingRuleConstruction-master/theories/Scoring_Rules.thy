theory Scoring_Rules
  imports 
          "Compositional_Structures/Basic_Modules/Scoring_Module"
          "Compositional_Structures/Elect_Composition"
          "Compositional_Structures/Basic_Modules/Condorcet_Module"

(*Electoral_Module Evaluation_Function Elect_Module Elimination_Module Condorcet_Rule*)
begin


(*******Lemmas*******)

lemma scoring_mod_A[simp]:
  shows "electoral_module (elector(max_eliminator 
        ((scoring (v:: 'a Vector_A))::'a Evaluation_Function)))"
  by auto

lemma scoring4_mod_A[simp]:
  shows "electoral_module (elector(max_eliminator 
      ((scoring4 (v:: 'a Vector_A))::'a Evaluation_Function)))"
  by auto

(****************Homogeneity ****************)

(*Addieren von Profilen für scoring*)
lemma add_scoring_profiles:
  shows "(scoring v x A (b@p) (vs1@vs2) = (scoring v x A b vs1) + (scoring v x A p vs2))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed

lemma times_profile:
  shows "times (Suc(n)) p = p @ (times n p)" by auto

lemma scoring_move_out:
  shows "scoring v x A (p @ (times n p)) (vs @ (times n vs)) 
  = scoring v x A p vs + scoring v x A (times n p) (times n vs)"
  by (metis add_scoring_profiles) 

lemma times_scoring:
  shows "(scoring v x A (times n p) (times n vs)) = scoring v x A  p vs * n"
proof(induct n)
case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis mult_Suc_right scoring_move_out times_profile) 
qed

lemma max_split_scoring:
  shows 
    "Max {scoring v x A (b@p) (vs1@vs2) |x. x \<in> A} = Max {(scoring v x A b vs1) + (scoring v x A p vs2) |x. x \<in> A}"
  by (metis add_scoring_profiles)

lemma Max_homo_add:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {scoring v x A p vs + k |x. x\<in>A} = Max {scoring v x A p vs|x. x\<in>A} + k"
proof -
  have m: "\<And>x y. max x y + k = max (x+k) (y+k)"
    by(simp add: max_def antisym add_right_mono)
  have "{scoring v x A p vs + k|x. x\<in>A} = (\<lambda>y. y + k) ` {scoring v x A p vs|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {scoring v x A p vs|x. x\<in>A} + k"
    using assms hom_Max_commute [of "\<lambda>y. y+k" "{scoring v x A p vs|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed


lemma Max_homo_mult_eval:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {eval_func x A p vs * k |x. x\<in>A} = Max {eval_func x A p vs|x. x\<in>A} * k"
proof -
  have m: "\<And>x y. max x y * k = max (x*k) (y*k)"
    by(simp add: max_def antisym add_right_mono)
  have "{eval_func x A p vs * k|x. x\<in>A} = (\<lambda>y. y * k) ` {eval_func x A p vs|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {eval_func x A p vs|x. x\<in>A} * k"
    using assms hom_Max_commute [of "\<lambda>y. y*k" "{eval_func x A p vs|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed

lemma Max_homo_mult:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {scoring v x A p vs * k |x. x\<in>A} = Max {scoring v x A p vs|x. x\<in>A} * k" using Max_homo_mult_eval 
proof-
  have m: "\<And>x y. max x y * k = max (x*k) (y*k)"
    by(simp add: max_def antisym add_right_mono)
  have "{scoring v x A p vs * k|x. x\<in>A} = (\<lambda>y. y * k) ` {scoring v x A p vs|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {scoring v x A p vs|x. x\<in>A} * k"
    using assms hom_Max_commute [of "\<lambda>y. y*k" "{scoring v x A p vs|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed


(** Homogeneity Beweis**)
(*scoring*)
lemma for_goal1:
  shows "\<And>A p n x xb. x \<in> A \<Longrightarrow>finite A \<Longrightarrow>profile A p \<Longrightarrow> 0 < n \<Longrightarrow> xb \<in> A \<Longrightarrow>
scoring v xb A p vs < Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
scoring v xb A (concat (replicate n p)) vs < Max {scoring v x A (concat (replicate n p)) vs|x. x \<in> A}"
proof-
  fix A :: "'a set" and p :: "('a \<times> 'a) set list" and 
    n :: "nat" and x :: "'a" and xb :: "'a" and vs :: "'a Pair_Vectors"
    assume a1: "finite A"
    assume a2: "profile A p"
    assume a3: "0 < n"
    assume a4: "x \<in> A"
    have 0 :"Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
        Max {scoring v x A p vs * n |x. x \<in> A}" 
      using times_scoring by (metis times.simps) 
  then have 1:  "Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
      n* Max {scoring v x A p vs|x. x \<in> A}" 
  proof -
    have "\<And>A f rs n vs. infinite A \<or> A = Collect bot \<or> 
        Max {scoring f (a::'a) A rs vs|a. a \<in> A} * n = Max {scoring f a A rs vs * n |a. a \<in> A}"
      using Max_homo_mult by fastforce
    then have f5: "\<And>f rs n vs. Max {scoring f a A rs vs|a. a \<in> A} * n = 
              Max {scoring f a A rs vs * n |a. a \<in> A}"
      using a4 a1 by blast
    have 
      "Max {scoring v a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} 
      = Max {scoring v a A p vs * n |a. a \<in> A}"
      using "0" by blast
    then show "Max {scoring v a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
          n * Max {scoring v a A p vs|a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:"scoring v xb A p vs < Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
            n* scoring v xb A p vs < n* Max {scoring v x A p vs|x. x \<in> A}"
    using a3 mult_less_mono2 by blast
  then have 3: "n* scoring v xb A p vs < n* Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
    scoring v xb A (concat (replicate n p)) (concat (replicate n vs)) < 
    Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A}"
    by (metis (no_types, lifting) "1" mult.commute times.simps times_scoring)
  then show "scoring v xb A p vs < Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
    scoring v xb A (concat (replicate n p)) vs < 
    Max {scoring v x A (concat (replicate n p)) vs|x. x \<in> A}"
    using 2 3 by auto
qed


lemma for_goal2:
  shows "\<And>A p n x xa xb vs. x \<in> A \<Longrightarrow> finite A \<Longrightarrow> profile A p \<Longrightarrow> vector_pair A p vs 
      \<Longrightarrow> 0 < n \<Longrightarrow> xa \<in> A \<Longrightarrow> xb \<in> A \<Longrightarrow> 
       scoring v xb A (concat (replicate n p)) (concat (replicate n vs)) < 
       Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} 
        \<Longrightarrow> scoring v xb A p vs< Max {scoring v x A p vs|x. x \<in> A}"
proof-
  fix A :: "'a set" and p :: "('a \<times> 'a) set list" 
      and n :: nat and x :: 'a and xb :: 'a and vs :: "'a Pair_Vectors"
    assume a1: "finite A"
    assume a2: "profile A p"
    assume a3: "0 < n"
    assume a4: "x \<in> A"
  have 0 :"
   Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
    Max {scoring v x A p vs * n |x. x \<in> A}" 
      using times_scoring by (metis times.simps) 
    then have 1:  "Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
          n* Max {scoring v x A p vs|x. x \<in> A}" 
proof -
  have "\<And>A f rs n vs. infinite A \<or> A = Collect bot \<or> Max {scoring f (a::'a) A rs vs|a. a \<in> A} * n = 
          Max {scoring f a A rs vs * n |a. a \<in> A}" 
    using Max_homo_mult by fastforce
    then have f5: 
      "\<And>f rs n. Max {scoring f a A rs vs|a. a \<in> A} * n = Max {scoring f a A rs vs * n |a. a \<in> A}"
      using a4 a1 by blast
    have 
      "Max {scoring v a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
      Max {scoring v a A p vs * n |a. a \<in> A}"
      using "0" by blast
    then show "Max {scoring v a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
            n * Max {scoring v a A p vs|a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:" n* scoring v xb A p vs < n* Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
            scoring v xb A p vs < Max {scoring v x A p vs|x. x \<in> A}"
    by simp
  then have 3: "n* scoring v xb A p vs < n* Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
     scoring v xb A (concat (replicate n p)) (concat (replicate n vs)) < 
     Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A}"
    by (metis (no_types, lifting) "1" mult.commute times.simps times_scoring)
  then show "scoring v xb A (concat (replicate n p)) (concat (replicate n vs)) <  
        Max {scoring v x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} \<Longrightarrow> 
        scoring v xb A p vs < Max {scoring v x A p vs|x. x \<in> A}"
    using 2 3 by (metis (no_types, lifting) "1" mult.commute times.simps times_scoring) 
qed


(***** Für Black's Rule bzw Condorcet *****)

(*
primrec replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
replicate_0: "replicate 0 x = []" |
replicate_Suc: "replicate (Suc n) x = x # replicate n x"
*)

(*IMMER RELEVANT; DASS N > 0 IST*)


lemma value_same_for_mult_profile:
  assumes "finite A" and  "profile A p" and "0 < n" and "x \<in> A"
  shows "condorcet_score xb A p vs = condorcet_score xb A (concat (replicate n p)) (concat (replicate n vs))" 
    unfolding condorcet_score.simps condorcet_winner.simps
  proof-
    have 000:" (\<forall>x \<in> A - {xb} . wins xb p x) =
     (\<forall>x \<in> A - {xb} . wins xb (concat (replicate n p)) x)" sorry

    have "finite_profile A p = finite_profile A (concat (replicate n p))" 
    proof(auto) 
      show "finite A \<Longrightarrow> profile A p \<Longrightarrow> profile A (concat (replicate n p))"  
      proof-
(*Linearität von n*p beweisen*)
        have"finite A \<Longrightarrow> \<forall>i<length p. linear_order_on A (p ! i) \<Longrightarrow> 
        \<forall>i<length (concat (replicate n p)). linear_order_on A (concat (replicate n p) ! i)" sorry
        then show "finite A \<Longrightarrow> profile A p \<Longrightarrow> profile A (concat (replicate n p))"
          by (simp add: profile_def) 
      qed
      show "finite A \<Longrightarrow> profile A (concat (replicate n p)) \<Longrightarrow> profile A p" 
      proof-
        have"finite A \<Longrightarrow> 
        \<forall>i<length (concat (replicate n p)). linear_order_on A (concat (replicate n p) ! i)
        \<Longrightarrow> \<forall>i<length p. linear_order_on A (p ! i)" sorry
        then show "finite A \<Longrightarrow> profile A (concat (replicate n p)) \<Longrightarrow> profile A p"
          by (simp add: profile_def) 
      qed
    qed
    then show "(if finite_profile A p \<and> xb \<in> A \<and> (\<forall>x \<in> A - {xb} . wins xb p x) then 1 else 0) =
    (if finite_profile A (concat (replicate n p)) \<and> xb \<in> A \<and> 
    (\<forall>x \<in> A - {xb} . wins xb (concat (replicate n p)) x) then 1 else 0)" using 000 by simp
  qed

lemma max_same_for_mult_profile:
  assumes "finite A" and  "profile A p" and "vector_pair A p vs" and "0 < n" and "x \<in> A" 
  shows "Max {condorcet_score x A p vs|x. x \<in> A} = Max {condorcet_score x A (concat (replicate n p)) 
          (concat (replicate n vs))|x. x \<in> A}" 
by (metis (no_types, lifting) assms(1) assms(2) assms(4) value_same_for_mult_profile)


lemma for_goal1_condorcet:
  shows "\<And>A p n x xb vs. x \<in> A \<Longrightarrow>finite A \<Longrightarrow>profile A p \<Longrightarrow> 
        vector_pair  A p vs \<Longrightarrow> 0 < n \<Longrightarrow> xb \<in> A \<Longrightarrow>
    condorcet_score xb A p vs < Max {condorcet_score x A p vs|x. x \<in> A} \<Longrightarrow> 
    condorcet_score xb A (concat (replicate n p)) (concat (replicate n vs)) < 
    Max {condorcet_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A}"
  by (metis (mono_tags, lifting) max_same_for_mult_profile value_same_for_mult_profile) 




lemma for_goal2_condorcet:
  shows "\<And>A p n x xa xb vs. x \<in> A \<Longrightarrow> finite A \<Longrightarrow>profile A p \<Longrightarrow> 
      vector_pair A p vs \<Longrightarrow>0 < n \<Longrightarrow>xa \<in> A \<Longrightarrow> xb \<in> A \<Longrightarrow>
    condorcet_score xb A (concat (replicate n p)) (concat (replicate n vs)) < 
    Max {condorcet_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} \<Longrightarrow> 
    condorcet_score xb A p vs < Max {condorcet_score x A p vs|x. x \<in> A}"
  by (metis (mono_tags, lifting) max_same_for_mult_profile value_same_for_mult_profile)


(*******************************************)

lemma seq_hom:
  shows "homogeneity_range m \<Longrightarrow> homogeneity_range n \<Longrightarrow> homogeneity_range (m \<triangleright> n)"
  unfolding homogeneity_range_def
proof(auto)
  show "\<And>A p na vs.
       electoral_module m \<Longrightarrow>
       \<forall>A p n vs. finite A \<and> profile A p \<and> finite A \<and> vector_pair A p vs \<and> 0 < n 
        \<longrightarrow> m A p vs = m A (concat (replicate n p)) (concat (replicate n vs)) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p na vs. finite A \<and> profile A p \<and> finite A \<and> vector_pair A p vs \<and> 0 < na 
        \<longrightarrow> n A p vs = n A (concat (replicate na p)) (concat (replicate na vs)) \<Longrightarrow>
       profile A p \<Longrightarrow>
       finite A \<Longrightarrow>
       vector_pair A p vs \<Longrightarrow>
       0 < na \<Longrightarrow>
       (let new_A = defer m A (concat (replicate na p)) (concat (replicate na vs)); 
        new_p = map (limit new_A) p; new_vs = map (limit_pairs new_A) vs
        in (elect m A (concat (replicate na p)) (concat (replicate na vs)) \<union> elect n new_A new_p new_vs,
            reject m A (concat (replicate na p)) (concat (replicate na vs)) \<union> reject n new_A new_p new_vs, 
          defer n new_A new_p new_vs)) =
       (let new_A = defer m A (concat (replicate na p)) (concat (replicate na vs)); 
        new_p = map (limit new_A) (concat (replicate na p));
            new_vs = map (limit_pairs new_A) (concat (replicate na vs))
        in (elect m A (concat (replicate na p)) (concat (replicate na vs)) \<union> elect n new_A new_p new_vs,
            reject m A (concat (replicate na p)) (concat (replicate na vs)) \<union> reject n new_A new_p new_vs, 
          defer n new_A new_p new_vs))" sorry
    (*by (smt (z3) def_presv_fin_prof def_presv_fin_vector_pair limit_pair_vectors.simps 
          limit_profile.elims map_concat map_replicate) *) 
qed

lemma elector_homogeneity:
  shows "homogeneity_range m \<Longrightarrow> homogeneity_range (elector m)"
proof(simp)
  have "homogeneity_range elect_module"
    by (simp add: homogeneity_range_def) 
  then show "homogeneity_range m \<Longrightarrow> homogeneity_range (m \<triangleright> elect_module)" using seq_hom by auto
qed

(**Eval_Func Beweis: Evaluation_Function ***)

lemma max_value_same:
  assumes"\<forall>A p n vs. finite_profile A p \<and> vector_pair A p vs \<and> 0 < n \<longrightarrow> 
       elimination_set eval_func (Max {eval_func x A p vs|x. x \<in> A}) (<) A p vs = 
       elimination_set eval_func (Max {eval_func x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)|x. x \<in> A}) (<) A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)"
  shows"(\<forall>A p n vs. finite_profile A p \<and> vector_pair A p vs \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p vs =
        max_eliminator eval_func A (Electoral_Module.times n p) (Electoral_Module.times n vs))"
  unfolding max_eliminator.simps less_eliminator.simps elimination_module.simps using assms
  by fastforce 

lemma eval_func_homogeneity:
  assumes "\<forall>A p n vs. finite_profile A p \<and> vector_pair A p vs \<and> 0 < n \<longrightarrow> 
       elimination_set eval_func (Max {eval_func x A p vs|x. x \<in> A}) (<) A p vs = 
       elimination_set eval_func (Max {eval_func x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)|x. x \<in> A}) 
        (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)"
  shows "homogeneity_range (max_eliminator eval_func)" 
  unfolding homogeneity_range_def using assms
proof-
  show "\<forall>A p n vs.
       finite_profile A p \<and> vector_pair A p vs \<and> 0 < n \<longrightarrow>
       elimination_set eval_func (Max {eval_func x A p vs |x. x \<in> A}) (<) A p vs =
       elimination_set eval_func
        (Max {eval_func x A (Electoral_Module.times n p) (
        Electoral_Module.times n vs) |x. x \<in> A}) (<)
        A (Electoral_Module.times n p) (Electoral_Module.times n vs) \<Longrightarrow>
    electoral_module (max_eliminator eval_func) \<and>
    (\<forall>A p n vs. finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p vs =
        max_eliminator eval_func A (Electoral_Module.times n p) (Electoral_Module.times n vs)) "
    proof-
    have 0:"electoral_module (max_eliminator eval_func)" by auto
    have "(\<forall>A p n vs.
        finite_profile A p \<and> vector_pair A p vs \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p vs=
        max_eliminator eval_func A (Electoral_Module.times n p) (Electoral_Module.times n vs))" 
        using assms max_value_same
      by fastforce 
    then show ?thesis
      using 0 by blast 
  qed
qed
 
  

lemma scoring_homogeneity:
  shows "homogeneity_range (max_eliminator (scoring v))"
proof-
  have "\<forall>A p n vs. finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow> 
  elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs = 
       elimination_set (scoring v) (Max {(scoring v) x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)|x. x \<in> A}) 
      (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)"
    using for_goal1 for_goal2 by auto
   then show "homogeneity_range (max_eliminator (scoring v))"
     by (simp add: eval_func_homogeneity) 
 qed

lemma scoring_rules_homogeneity:
  shows "homogeneity_range (elector (max_eliminator (scoring vec_A_borda)))" 
  using scoring_homogeneity elector_homogeneity by auto

lemma condorcet_homogeneity:
  shows "homogeneity (max_eliminator condorcet_score)" 
  unfolding homogeneity_def
proof-
  have 0: "\<forall>A p vs. max_eliminator condorcet_score A p vs
        = elimination_module condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A}) (<) A p vs"
    by force
  have 1:"\<forall>A p vs. elimination_module condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A}) (<) A p vs =
  (if (elimination_set condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A})  (<) A p vs) \<noteq> A
        then ({}, (elimination_set condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A})  (<) A p vs), A 
        - (elimination_set condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A}) (<) A p vs))
        else ({},{},A))"
    using elimination_module.simps by blast
   have 2:"\<forall>A p n vs. finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow> 
    (if (elimination_set condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A})  (<) A p vs) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A})  (<) A p vs), 
    A - (elimination_set condorcet_score (Max {condorcet_score x A p vs| x. x \<in> A}) (<) A p vs))
    else ({},{},A)) = 
    (if (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p ) (Electoral_Module.times n vs)), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A}) 
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)))
    else ({},{},A))" 
     using 1 for_goal1_condorcet for_goal2_condorcet 
     by (smt (z3) Collect_cong elimination_set.simps times.simps)
  then have 3:"\<forall>A p n vs.  finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow> 
    max_eliminator condorcet_score A p vs = 
        (if (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A}) 
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)))
    else ({},{},A))" using 0 1 by (smt (z3))
  then have "\<forall>A p n vs.  finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow> 
    max_eliminator condorcet_score A  (Electoral_Module.times n p) (Electoral_Module.times n vs) = 
        (if (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A}) 
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)))
    else ({},{},A))"
    by (smt (z3) "0" "1" Collect_cong)
  then have "\<forall>A p n vs.  finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow> 
    max_eliminator condorcet_score A (Electoral_Module.times n p) (Electoral_Module.times n vs) = 
    max_eliminator condorcet_score A p vs"
    by (smt (z3) "3")

   then show "electoral_module (max_eliminator condorcet_score) \<and>
        (\<forall>A p n vs. finite_profile A p \<and> finite_pair_vectors A p vs \<and> 0 < n \<longrightarrow> max_eliminator condorcet_score A p vs= 
        max_eliminator condorcet_score A (Electoral_Module.times n p) (Electoral_Module.times n vs))"
     by (smt (z3) max_elim_sound) 
     
 qed


(*****)

(********************reinforcement proof**********************************)



lemma combined_eqless_single:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A p1 vs1" and "vector_pair A p2 vs2"
  shows "scoring v x A p1 vs1 + scoring v x A p2 vs2 \<le> Max {scoring v x A p1 vs1|x. x \<in> A} + 
          Max {scoring v x A p2 vs2|x. x \<in> A}"
proof-
  have "scoring v x A p1 vs1\<in> {scoring v x A p1 vs1|x. x \<in> A}" using assms(3) by blast
  then have 0:"scoring v x A p1 vs1 \<le> Max {scoring v x A p1 vs1|x. x \<in> A}" by (simp add: assms(1))
  have "scoring v x A p2 vs2\<in> {scoring v x A p2 vs2|x. x \<in> A}" using assms(3) by blast
  then have 1:"scoring v x A p2 vs2\<le> Max {scoring v x A p2 vs2|x. x \<in> A}" by (simp add: assms(1))
  then show ?thesis using "0" "1" add_mono by blast
qed



lemma combined_max_eqless_single_all:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A p1 vs1" and "vector_pair A p2 vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A} \<le> 
    Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2|x. x \<in> A}"
proof-
  have fin: "finite {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A} 
        \<in> {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast 
  have eqToMax:"\<exists>x \<in> A. scoring v x A p1 vs1 + scoring v x A p2 vs2 = 
        Max {scoring v x A p1 vs1 + scoring v x A p2 vs2 |x. x \<in> A}" using "maxInSet" by auto
  have allSmaller:"\<forall>x\<in> A. scoring v x A p1 vs1 + scoring v x A p2 vs2 \<le>
        Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2 |x. x \<in> A}"
    using combined_eqless_single all_not_in_conv assms(1) assms(3) assms(4) assms(5)
  proof -
  { fix aa :: 'a
    have "\<And>A a rs rsa Ps Psa f. infinite A \<or> (a::'a) \<notin> A \<or> \<not> profile A rs \<or> \<not> profile A rsa 
  \<or> \<not> vector_pair A rs Ps \<or> \<not> vector_pair A rsa Psa \<or> scoring f a A rsa Psa + scoring f a A rs Ps 
  \<le> Max {scoring f a A rsa Psa |a. a \<in> A} + Max {scoring f a A rs Ps |a. a \<in> A}"
      by (smt (z3) all_not_in_conv combined_eqless_single)
    then have "aa \<notin> A \<or> scoring v aa A p1 vs1 + scoring v aa A p2 vs2 
  \<le> Max {scoring v a A p1 vs1 |a. a \<in> A} + Max {scoring v a A p2 vs2 |a. a \<in> A}"
      using assms(1) assms(4) assms(5) assms(6) assms(7) by blast }
  then show ?thesis
    by meson
  have following:"\<exists>x \<in> A. scoring v x A p1 vs1 + scoring v x A p2 vs2 = 
        Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A} 
  \<Longrightarrow> \<forall>x\<in> A. scoring v x A p1 vs1 + scoring v x A p2 vs2\<le> 
        Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2|x. x \<in> A} 
  \<Longrightarrow> Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A} \<le> 
        Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2|x. x \<in> A}"
    by fastforce 
  qed
  then show ?thesis
    using eqToMax by fastforce
qed





lemma add_scoring_profiles_all:
  shows "\<forall>x \<in> (defer (max_eliminator (scoring v)) A p1 vs1
      \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
        (scoring v x A (b@p) (vs1@vs2) = 
(scoring v x A b vs1) + (scoring v x A p vs2))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed

lemma add_scoring_profiles_all2:
  shows "\<forall>x. (scoring v x A (b@p) (vs1@vs2)= 
(scoring v x A b vs1) + (scoring v x A p vs2))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed



lemma max_is_defer_combined_than_in_both_all:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A p1 vs1" and "vector_pair A p2 vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
          scoring v a A p1 vs1 + scoring v a A p2 vs2 \<ge> Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} \<Longrightarrow>
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    a \<in> defer (max_eliminator (scoring v)) A (p1@p2) (vs1@vs2)"
proof -
  assume "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
      scoring v a A p1 vs1 + scoring v a A p2 vs2 \<ge> Max {scoring v x A (p1 @ p2) (vs1@vs2)|x. x \<in> A}"
  then have 
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v a A (p1 @ p2) (vs1@vs2)"
    using assms by (metis (no_types, lifting) add_scoring_profiles_all)
  have 
    "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
      Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v a A (p1 @ p2) (vs1@vs2) \<Longrightarrow> 
     \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
    a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)"
    (*by (smt (z3) Collect_cong add_scoring_profiles_all max_is_defer_combined)*)
proof -
  assume a1: "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
      Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v a A (p1 @ p2) (vs1@vs2)"
  { fix aa :: 'a
    { assume "Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v aa A (p1 @ p2) (vs1@vs2)"
      moreover
      { assume "aa \<notin> A"
        then have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)\<or> 
      aa \<notin> defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2"
          by simp }
      ultimately have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)\<or> 
      aa \<notin> defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2"
        by simp }
    then have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2) \<or> 
      aa \<notin> defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2"
      using a1 by meson }
  then show ?thesis
    by metis
qed
  then show ?thesis
    using \<open>\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
      Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v a A (p1 @ p2) (vs1@vs2)\<close> 
    by linarith 
qed



lemma max_in_both__than_in_combined_defer_all:
  assumes "finite_profile A p1" and "finite_profile A p2" and "a \<in> A" "finite A" and "A \<noteq> {}" and 
    "vector_pair A p1 vs1" and "vector_pair A p2 vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
        scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A} \<and> 
        scoring v a A p2 vs2 =  Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow>
        \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
          a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)"
proof-
  have 00:
  "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2|x. x \<in> A} \<ge> 
      Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}" 
    using assms combined_max_eqless_single_all
    by (metis (mono_tags, lifting) )
  have 11: 
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      scoring v a A p2 vs2 =  Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2|x. x \<in> A} = scoring v a A p1 vs1 + 
          scoring v a A p2 vs2"
    by (metis (no_types, lifting)) 
  have 0:
  "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    scoring v a A p2 vs2 =  Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
    scoring v a A p1 vs1 + scoring v a A p2 vs2 \<ge> Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}" 
      using "00" "11" by (metis (no_types, lifting)) 
  have 1 :"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
    Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A} = Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A}"
    using max_split_scoring sorry (*by metis*)
  have 2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
    scoring v a A p1 vs1=  Max {scoring v x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
        scoring v a A p2 vs2 =  Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
        scoring v a A p1 vs1 + scoring v a A p2 vs2\<ge> Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
    using assms "1" "0" by (smt (z3))
  have 3:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2).
      scoring v a A p1 vs1 + scoring v a A p2 vs2\<ge> Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} \<Longrightarrow>
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)" 
    using assms max_is_defer_combined_than_in_both_all by (metis (mono_tags, lifting)) 
  show "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
       scoring v a A p1 vs1 = Max {scoring v x A p1 vs1 |x. x \<in> A} \<and>
       scoring v a A p2 vs2 = Max {scoring v x A p2 vs2 |x. x \<in> A} \<Longrightarrow>
    \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
       a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1 @ vs2) " 
    using assms "2" "3" by blast 
qed


lemma max_alway_exists0:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<exists>a \<in> A. scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}"
proof-
  have fin: "finite {scoring v x A p vs|x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{scoring v x A p vs|x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {scoring v x A p vs|x. x \<in> A} \<in> {scoring v x A p vs|x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast
  have "Max {scoring v x A p vs|x. x \<in> A} \<in> {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
        \<exists>a \<in> A. scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}" by auto
  then show ?thesis using maxInSet by simp
qed

lemma max_alway_exists:
  assumes "finite A" and "A \<noteq> {}"
  shows "{a \<in> A. scoring v a A p vs < Max {scoring v x A p vs|x. x \<in> A}} = A \<Longrightarrow> False"
proof-
  have "\<exists>a \<in> A. scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}" using assms max_alway_exists0 
        by simp
  then show "{a \<in> A. scoring v a A p vs < Max {scoring v x A p vs|x. x \<in> A}} = A \<Longrightarrow> False"
    using nat_neq_iff by auto 
qed

lemma max_alway_exists2:
  assumes "finite A" and "A \<noteq> {}" and "finite_profile A p"
  shows "(elimination_set (scoring v) (Max {(scoring v) x A p vs | x. x \<in> A}) (<) A p vs \<noteq> A) = True"
  using assms max_alway_exists by auto


lemma not_less_is_max:
  assumes "finite A"
  shows "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      scoring v a A p vs =  Max {scoring v x A p vs|x. x \<in> A}"
proof-
  have "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      a \<in> A" by clarify
  then have "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      scoring v a A p vs \<in> {scoring v x A p vs|x. x \<in> A}" 
    by blast
      (*sc a p nicht größer als Max*)
  then have 0:"a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs |x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      scoring v a A p vs \<le>  Max{scoring v x A p vs|x. x \<in> A}"  
    using assms (1) by auto
      (*sc a p nicht kleiner als Max*)
  have 1:"a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      scoring v a A p vs \<ge>  Max{scoring v x A p vs|x. x \<in> A}"
    by auto
  have "a \<in> A \<Longrightarrow>\<not> scoring v a A p vs < Max {scoring v x A p vs|x. x \<in> A} \<Longrightarrow> 
      scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}" using "0" "1" by simp
  then show "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      scoring v a A p vs =  Max {scoring v x A p vs|x. x \<in> A}"
    by simp
qed



(** from defer follows Max value **)

lemma from_defer_follows_max:
  assumes "finite A" and "A \<noteq> {}"
  shows "a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> 
            scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}"
proof-
  have "({a \<in> A. scoring v a A p vs < Max {(scoring v) x A p vs|x. x \<in> A}} \<noteq> A) = True" 
          using assms max_alway_exists by auto
        then have 0: "a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> 
      a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs)"
    by simp
  have "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      scoring v a A p vs =  Max {scoring v x A p vs|x. x \<in> A}" 
    using assms(1) not_less_is_max by simp
  then have 1:"a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> scoring v a A p vs = 
      Max {scoring v x A p vs|x. x \<in> A}" using "0" by simp
  then show "a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> 
      scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}"
     by simp
 qed


lemma from_defer_follows_max_all:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
      a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> 
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}"
proof-

  have 0:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
        ({a \<in> A. scoring v a A p vs < Max {(scoring v) x A p vs|x. x \<in> A}} \<noteq> A) = True" 
          using assms max_alway_exists by auto

        have "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      scoring v a A p vs =  Max {scoring v x A p vs|x. x \<in> A}" 
    using assms(1) not_less_is_max by simp
  then have 1:
        "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
                a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> 
                \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> 
                defer (max_eliminator (scoring v)) A p2 vs2). 
                scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}" using "0"
    by (metis (mono_tags, lifting) assms(1) assms(2) from_defer_follows_max)
  then show 
      "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      a \<in> defer (max_eliminator (scoring v)) A p vs \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      scoring v a A p vs = Max {scoring v x A p vs|x. x \<in> A}"
    by simp
qed


lemma from_defer_follows_max2_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
  a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2) 
  \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      (scoring v a A p1 vs1 = Max {scoring v x A p1 vs1|x. x \<in> A})" 
  by (metis (mono_tags, lifting) IntD1 assms from_defer_follows_max_all)


lemma from_defer_follows_max3_for_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
   a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2) \<Longrightarrow> 
   \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
      (scoring v a A p1 vs1 = Max {scoring v x A p1 vs1|x. x \<in> A}) \<and> 
      (scoring v a A p2 vs2 = Max {scoring v x A p2 vs2|x. x \<in> A})" 
  using assms from_defer_follows_max2_all
  by blast 


(*** ---------- ***)



lemma reinforcement_defer_scoring_helper:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A p1 vs1" and "vector_pair A p2 vs2"
  shows "defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 \<noteq> {} \<Longrightarrow>
  defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)"
proof-

  have all:
      "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)" 
    by (meson from_defer_follows_max3_for_all max_in_both__than_in_combined_defer_all assms)

  then have d1:"(defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2)
      \<subseteq> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)"
    using assms by blast 
(***********)
  have 00:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2).
  a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2) \<Longrightarrow> 
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2). 
   (scoring v a A p1 vs1= Max {scoring v x A p1 vs1|x. x \<in> A}) \<and> 
      (scoring v a A p2 vs2= Max {scoring v x A p2 vs2|x. x \<in> A})" 
    by (metis (mono_tags, lifting) assms(1) assms(2) from_defer_follows_max3_for_all) 

  have 11:"scoring v a A p1 vs1=  Max {scoring v x A p1 vs1|x. x \<in> A} \<and> 
      scoring v a A p2 vs2= Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow>
   \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2).
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)" 
    using assms max_in_both__than_in_combined_defer_all all by blast 
  have all:
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2).
    a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)" using assms "00" "11"
    using all by blast (*by simp*)
  then have d1:"(defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2)
      \<subseteq> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)"
    using assms by blast 


  have "defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2\<noteq> {} \<Longrightarrow>
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)).
    a \<in> (defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2)"
proof-
(*1)*)
(*relevant für "comb_is_eq"*)
  have a_is_max_p1_p2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)).
          scoring v a A (p1@p2) (vs1@vs2) = Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
    using assms by (smt (z3) Collect_cong from_defer_follows_max)

  have same_as_add:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
      (scoring v a A (p1@p2) (vs1@vs2) = (scoring v a A p1 vs1) + (scoring v a A p2 vs2))" 
      using add_scoring_profiles by fastforce


    have elem_A2:
        "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2. a\<in>A"
      using assms(1) assms(4) defer_in_alts max_elim_sound
      using Int_iff assms(6) in_mono by auto
    have elem_A:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). a \<in> A" by simp

(*relevant für "1"*)
    then have "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). scoring v a A p1 vs1\<in> 
      {scoring v x A p1 vs1|x. x \<in> A}" 
      using assms(3) by blast
    then have smaller_max:
          "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). scoring v a A p1 vs1 \<le> 
      Max {scoring v x A p1 vs1|x. x \<in> A}" 
      using assms(1) by simp
    then have "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). scoring v a A p2 vs2 \<in> 
      {scoring v x A p2 vs2|x. x \<in> A}" 
      using assms(3) "elem_A" by blast
    then have smaller_max2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
      scoring v a A p2 vs2 \<le>  Max {scoring v x A p2 vs2|x. x \<in> A}" 
      using assms(1) by simp
(*relevant für "from_single_follows_combined"*)
    have 11:"defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 \<noteq> {}
      \<Longrightarrow> \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
          (scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A}) \<and> (scoring v a A p2 vs2 = 
      Max {scoring v x A p2 vs2|x. x \<in> A})"
      using "00" by blast

        have elem_of:
          "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2.
                        scoring v a A p1 vs1 + scoring v a A p2 vs2\<in> {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
      using same_as_add
      by (metis (mono_tags, lifting) all elem_A2 mem_Collect_eq) 

    have 001:"\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
        Max {scoring v x A p1 vs1|x. x \<in> A} + Max {scoring v x A p2 vs2|x. x \<in> A} \<ge> 
        Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}" 
      using assms combined_max_eqless_single_all by (metis (mono_tags, lifting) ) 


    then have 000:
        "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
         scoring v a A p1 vs1 + scoring v a A p2 vs2\<ge> Max {scoring v x A p1 vs1 + scoring v x A p2 vs2|x. x \<in> A}" 
      using assms by (metis (no_types, lifting) "11" equals0D)  

    then  have 
        "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
                  Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} \<le> scoring v a A p1 vs1 + scoring v a A p2 vs2"
      by (metis (no_types, lifting) a_is_max_p1_p2 all dual_order.eq_iff same_as_add) 

    then have comb_is_eq:
          "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
          Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} = scoring v a A p1 vs1 + scoring v a A p2 vs2" 
      using elem_of
          proof -
            { fix aa :: 'a
              have "\<And>a. a \<notin> defer (max_eliminator (scoring v)) A p1 vs1 \<inter> 
                  defer (max_eliminator (scoring v)) A p2 vs2\<or> 
                  Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v a A (p1 @ p2) (vs1@vs2)"
                using a_is_max_p1_p2 all dual_order.order_iff_strict by blast
              moreover
              {assume "aa \<in> A \<and> Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> scoring v aa A (p1 @ p2) (vs1@vs2)"
                then have m1:"aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)"
                  by simp
            then have "Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} = scoring v aa A (p1 @ p2) (vs1@vs2)"
              by (smt (z3) a_is_max_p1_p2)
            then have 
              "scoring v aa A p1 vs1 + scoring v aa A p2 vs2= Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} 
        \<or> aa \<notin> defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2"
              using m1 same_as_add by fastforce}

          ultimately have "scoring v aa A p1 vs1 + scoring v aa A p2 vs2 = 
              Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<or> 
             aa \<notin> defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2"
            using \<open>\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> 
                  defer (max_eliminator (scoring v)) A p2 vs2. a \<in> A\<close> by blast }
        then have "\<forall>a. scoring v a A p1 vs1 + scoring v a A p2 vs2= 
                    Max {scoring v a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<or> 
              a \<notin> defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2"
              by satx
            then show ?thesis
              by (smt (z3))
                 qed

    have eq:"\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
            Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} = scoring v a A p1 vs1+ scoring v a A p2 vs2 \<Longrightarrow> 
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
            scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A} \<and> scoring v a A p2 vs2 = 
                  Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow>
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2. 
            Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} = Max {scoring v x A p1 vs1|x. x \<in> A} + 
            Max {scoring v x A p2 vs2|x. x \<in> A}"
      by (metis (no_types, lifting)) 

    then have "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
          (scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A}) \<and> 
          (scoring v a A p2 vs2 =  Max {scoring v x A p2 vs2|x. x \<in> A}) \<Longrightarrow>
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2.
            Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} = scoring v a A p1 vs1 + scoring v a A p2 vs2" 
              using assms comb_is_eq
      by linarith 

    then have from_single_follows_combined:
        "defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 \<noteq> {} \<Longrightarrow>
        Max {scoring v x A (p1@p2) (vs1@vs2)|x. x \<in> A} = Max {scoring v x A p1 vs1|x. x \<in> A} + 
        Max {scoring v x A p2 vs2|x. x \<in> A}"
    using assms "11" "eq" by blast


  have 00:"defer (max_eliminator (scoring v)) A p1 vs1\<inter> defer (max_eliminator (scoring v)) A p2 vs2\<noteq> {} 
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
        scoring v a A p1 vs1 + scoring v a A p2 vs2 = Max {scoring v x A p1 vs1|x. x \<in> A} + 
        Max {scoring v x A p2 vs2|x. x \<in> A}"
    using a_is_max_p1_p2 from_single_follows_combined same_as_add by fastforce
        

  have 1:"defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2\<noteq> {} 
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
        (scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A}) \<and> 
      (scoring v a A p2 vs2 =  Max {scoring v x A p2 vs2|x. x \<in> A})"
    using assms "a_is_max_p1_p2" "from_single_follows_combined" "same_as_add" 
          "smaller_max" "smaller_max2" "00"
    by (smt (z3) add_le_cancel_right le_antisym nat_add_left_cancel_le)
    

    have 3:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
          scoring v a A p1 vs1 =  Max {scoring v x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
          \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
          scoring v a A p2 vs2=  Max {scoring v x A p2 vs2|x. x \<in> A} \<Longrightarrow>
          \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)). 
          a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> 
          defer (max_eliminator (scoring v)) A p2 vs2)" 
      using assms sorry

          then show 
            "defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2\<noteq> {}
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)).
      a \<in> (defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2)" 
            using assms "1" "3" by blast
  qed
  

  then show "defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 \<noteq> {}
      \<Longrightarrow> defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2)" 
    using assms "d1" by blast
qed



lemma reinforcement_defer_scoring:
  shows "reinforcement_defer (max_eliminator (scoring v))"
  unfolding reinforcement_defer_def 
proof-
  have 0:"electoral_module (max_eliminator (scoring v))" by simp
  have 1:"(\<forall>A p1 p2 vs1 vs2.
        finite_profile A p1 \<and> finite_profile A p2 \<and> finite_pair_vectors A p1 vs1 
        \<and> finite_pair_vectors A p2 vs2 \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2\<noteq> {} \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1@vs2))" 
    using  "0" Int_emptyI defer_in_alts equals0D in_mono reinforcement_defer_scoring_helper
    by (smt (z3)) 
  then show "electoral_module (max_eliminator (scoring v)) \<and>
    (\<forall>A p1 p2 vs1 vs2.
        finite_profile A p1 \<and> finite_pair_vectors A p1 vs1 \<and> finite_profile A p2 
        \<and> finite_pair_vectors A p2 vs2 \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 \<noteq> {} \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 vs1 \<inter> defer (max_eliminator (scoring v)) A p2 vs2 =
        defer (max_eliminator (scoring v)) A (p1 @ p2) (vs1 @ vs2))" 
    using "0"
    by presburger 
qed

(*klar, weil es keinen Gewinner gibt. Umschreiben mit defer?*)
lemma reinforcement_scoring:
  shows "reinforcement (max_eliminator (scoring v))"
  unfolding reinforcement_def by simp

lemma elector_reinforcement:
  shows "reinforcement (elector(max_eliminator (scoring v)))"
proof(simp)
  have def: "reinforcement_defer (max_eliminator (scoring v))"
    by (simp add: reinforcement_defer_scoring) 
  have "reinforcement elect_module" 
    by (simp add: reinforcement_def) 
  have emp: "\<forall>A p vs. elect (max_eliminator (scoring v)) A p vs = {}" using max_elim_non_electing by simp
  have "\<forall>A p vs. elect (max_eliminator (scoring v)) A p vs = {} \<Longrightarrow> 
        \<forall>A p vs. defer (max_eliminator (scoring v)) A p vs = elect (elector(max_eliminator (scoring v))) A p vs" 
      by (simp add: reinforcement_def)
    then show "reinforcement (max_eliminator (scoring v) \<triangleright> elect_module)" 
      using emp def elect_mod_sound elector.elims reinforcement_def reinforcement_defer_def seq_comp_sound
      sorry (*by (smt (z3))*) 
qed


lemma scoring_module_rein:
  shows "reinforcement (elector(max_eliminator (scoring v)))" 
proof-
  have 0:"\<forall>A p vs. elect (max_eliminator (scoring v)) A p vs = {}" by simp
  have "\<forall>A p vs. well_formed A ((max_eliminator (scoring v)) A p vs)" by auto
  then show ?thesis using elector_reinforcement reinforcement_defer_scoring 0 by blast
qed