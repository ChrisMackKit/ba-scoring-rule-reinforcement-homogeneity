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
  shows "(scoring v x A (b@p) = (scoring v x A b) + (scoring v x A p))" 
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
  shows "scoring v x A (p @ (times n p)) = scoring v x A p + scoring v x A (times n p)"
  by (metis add_scoring_profiles) 

lemma times_scoring:
  shows "(scoring v x A (times n p)) = scoring v x A  p * n"
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
    "Max {scoring v x A (b@p) |x. x \<in> A} = Max {(scoring v x A b) + (scoring v x A p) |x. x \<in> A}"
  by (metis add_scoring_profiles)

lemma Max_homo_add:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {scoring v x A p + k |x. x\<in>A} = Max {scoring v x A p|x. x\<in>A} + k"
proof -
  have m: "\<And>x y. max x y + k = max (x+k) (y+k)"
    by(simp add: max_def antisym add_right_mono)
  have "{scoring v x A p + k|x. x\<in>A} = (\<lambda>y. y + k) ` {scoring v x A p|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {scoring v x A p|x. x\<in>A} + k"
    using assms hom_Max_commute [of "\<lambda>y. y+k" "{scoring v x A p|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed


lemma Max_homo_mult_eval:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {eval_func x A p * k |x. x\<in>A} = Max {eval_func x A p|x. x\<in>A} * k"
proof -
  have m: "\<And>x y. max x y * k = max (x*k) (y*k)"
    by(simp add: max_def antisym add_right_mono)
  have "{eval_func x A p * k|x. x\<in>A} = (\<lambda>y. y * k) ` {eval_func x A p|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {eval_func x A p|x. x\<in>A} * k"
    using assms hom_Max_commute [of "\<lambda>y. y*k" "{eval_func x A p|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed

lemma Max_homo_mult:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {scoring v x A p * k |x. x\<in>A} = Max {scoring v x A p|x. x\<in>A} * k" 
  using Max_homo_mult_eval 
proof-
  have m: "\<And>x y. max x y * k = max (x*k) (y*k)"
    by(simp add: max_def antisym add_right_mono)
  have "{scoring v x A p * k|x. x\<in>A} = (\<lambda>y. y * k) ` {scoring v x A p|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {scoring v x A p|x. x\<in>A} * k"
    using assms hom_Max_commute [of "\<lambda>y. y*k" "{scoring v x A p|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed


(** Homogeneity Beweis**)
(*scoring*)
lemma for_goal1:
  assumes "x \<in> A" and "xb \<in> A" and "finite A" and "profile A p" and "0 < n" and 
    "scoring v xb A p < Max {scoring v x A p |x. x \<in> A}"
  shows "scoring v xb A (times n p) < 
        Max {scoring v x A (times n p) |x. x \<in> A}"
proof-
    have 0 :"Max {scoring v x A (times n p) |x. x \<in> A} = 
        Max {scoring v x A p * n |x. x \<in> A}" 
      using times_scoring by metis 
  then have 1:  "Max {scoring v x A (times n p) |x. x \<in> A} = 
      n* Max {scoring v x A p |x. x \<in> A}" 
  proof -
    have "\<And>A f rs n. infinite A \<or> A = Collect bot \<or> 
        Max {scoring f (a::'a) A rs |a. a \<in> A} * n = Max {scoring f a A rs * n |a. a \<in> A}" 
      using Max_homo_mult bot_set_def by fastforce 
    then have f5: "\<And>f rs n. Max {scoring f a A rs |a. a \<in> A} * n = 
              Max {scoring f a A rs * n |a. a \<in> A}"
      using assms(1) assms(3) by blast
    have 
      "Max {scoring v a A (times n p) |a. a \<in> A} = Max {scoring v a A p * n |a. a \<in> A}"
      using assms 0 by clarify
    then show "Max {scoring v a A (times n p) |a. a \<in> A} = 
          n * Max {scoring v a A p |a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:"scoring v xb A p < Max {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
            n* scoring v xb A p < n* Max {scoring v x A p |x. x \<in> A}"
    using assms(5) mult_less_mono2 by blast
  then have 3: "n* scoring v xb A p < n* Max {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
    scoring v xb A (times n p) < 
    Max {scoring v x A (times n p) |x. x \<in> A}"
    by (metis (no_types, lifting) "1" mult.commute times_scoring)
  then show "scoring v xb A (times n p) < 
    Max {scoring v x A (times n p) |x. x \<in> A}"
    using 2 assms by auto
qed


lemma for_goal2:
  assumes "x \<in> A" and "finite A" and "profile A p" and "0 < n" and "xa \<in> A" and "xb \<in> A" and
  "scoring v xb A (times n p) < Max {scoring v x A (times n p) |x. x \<in> A}"
  shows " scoring v xb A p < Max {scoring v x A p |x. x \<in> A}"
proof-
  have 0 :"
   Max {scoring v x A (times n p) |x. x \<in> A} = Max {scoring v x A p * n |x. x \<in> A}" 
      using times_scoring by metis 
    then have 1:  "Max {scoring v x A (times n p) |x. x \<in> A} = 
          n* Max {scoring v x A p |x. x \<in> A}" 
proof -
  have "\<And>A f rs n. infinite A \<or> A = Collect bot \<or> Max {scoring f (a::'a) A rs |a. a \<in> A} * n = 
          Max {scoring f a A rs * n |a. a \<in> A}"
      by (smt (z3) Max_homo_mult bot_set_def)
    then have f5: 
      "\<And>f rs n. Max {scoring f a A rs |a. a \<in> A} * n = Max {scoring f a A rs * n |a. a \<in> A}"
      using assms(1) assms(2) by blast
    have 
      "Max {scoring v a A (times n p) |a. a \<in> A} = Max {scoring v a A p * n |a. a \<in> A}"
      using assms 0 by clarify
    then show "Max {scoring v a A (times n p) |a. a \<in> A} = 
            n * Max {scoring v a A p |a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:" n* scoring v xb A p < n* Max {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
            scoring v xb A p < Max {scoring v x A p |x. x \<in> A}"
    by simp
  then have 3: "n* scoring v xb A p < n* Max {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
     scoring v xb A (times n p) < 
     Max {scoring v x A (times n p) |x. x \<in> A}"
    by (metis (no_types, lifting) "1" mult.commute times_scoring)
  then show "scoring v xb A p < Max {scoring v x A p |x. x \<in> A}"
    using 1 2 3 assms(7) by (metis (no_types, lifting) mult.commute times_scoring) 
qed

(***** Für Black's Rule bzw Condorcet *****)


lemma add_prefer_profiles:
  shows "(prefer_count (b@p) x y = (prefer_count b x y) + (prefer_count p x y))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case sorry
qed


lemma prefer_move_out:
  shows "prefer_count (p @ (times n p)) x y = prefer_count p x y + prefer_count (times n p) x y" 
  by (metis add_prefer_profiles)

lemma times_prefer:
  shows "(prefer_count p x y) * n = prefer_count (times n p) x y"
proof(induct n)
case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case                 
    by (metis mult_Suc_right prefer_move_out times_profile) 
qed
             

lemma lin_n_follows:
  assumes "finite A" and "(\<forall>i<length p. linear_order_on A (p ! i) \<Longrightarrow> 
      \<forall>n \<ge> 0. \<forall>i<length (times (n+1) p). linear_order_on A ((times (n+1) p) ! i))"
  shows "(\<forall>i<length p. linear_order_on A (p ! i) \<Longrightarrow> 
        \<forall>n > 0. \<forall>i<length (times n p). linear_order_on A ((times n p) ! i))" 
proof- 
  have "\<forall>n \<ge> 0. \<forall>i<length (times (Suc n) p). linear_order_on A ((times (Suc n) p) ! i) \<Longrightarrow> 
        \<forall>n > 0. \<forall>i<length (times n p). linear_order_on A ((times n p) ! i)"
    by (metis gr0_implies_Suc less_Suc_eq_le) 
  then have "\<forall>n \<ge> 0. \<forall>i<length (times (n + 1) p). linear_order_on A ((times (n + 1) p) ! i) \<Longrightarrow> 
        \<forall>n > 0. \<forall>i<length (times n p). linear_order_on A ((times n p) ! i) " by auto
  then show "(\<forall>i<length p. linear_order_on A (p ! i) \<Longrightarrow> 
        \<forall>n > 0. \<forall>i<length (times n p). linear_order_on A ((times n p) ! i))" using assms
    by blast 
qed

lemma lin_induct:
  assumes "finite A" and "n \<ge> 0" and "\<forall>i<length p. linear_order_on A (p ! i)"
  shows "\<forall>i<length (times (n+1) p). linear_order_on A ((times (n+1) p) ! i)" 
        proof(induct n)
          case 0
          then show ?case using assms(3) by simp
        next
          case (Suc n)
          then show ?case proof-
            have f0:"(\<forall>i<length (Electoral_Module.times ((Suc n)+1) p). 
            linear_order_on A (Electoral_Module.times ((Suc n)+1) p ! i)) = 
            (\<forall>i<length (p@(Electoral_Module.times (n+1) p)). 
            linear_order_on A ((p@(Electoral_Module.times (n+1) p)) ! i))"
              by simp
            have "\<forall>i<length p. linear_order_on A (p ! i) \<Longrightarrow> 
            (\<forall>i<length (p@(Electoral_Module.times (n+1) p)). 
            linear_order_on A ((p@(Electoral_Module.times (n+1) p)) ! i)) = 
            ((\<forall>i<length (Electoral_Module.times (n+1) p). 
            linear_order_on A (Electoral_Module.times (n+1) p ! i)))"
              by (metis Suc.hyps add_diff_inverse_nat  length_append 
                   nat_add_left_cancel_less nth_append) 
            then show ?thesis using f0 Suc.hyps assms(1) assms(3) by blast  
          qed
        qed

lemma n_times_lin:
  assumes "n > 0" and "finite A" and "\<forall>i<length p. linear_order_on A (p ! i)"
  shows "\<forall>i<length (times n p). linear_order_on A ((times n p) ! i)" 
  using lin_n_follows lin_induct assms(1) assms(2) assms(3)
  by metis


lemma value_same_for_mult_profile:
  assumes "finite A" and  "profile A p" and "0 < n" and "x \<in> A"
  shows "condorcet_score xb A p  = condorcet_score xb A (times n p)" 
    unfolding condorcet_score.simps condorcet_winner.simps
  proof-
    have 0: "\<forall>x y. (prefer_count p x y) * n = prefer_count (times n p) x y"
      by (metis times_prefer)
    have 1:"\<forall>x\<in>A - {xb}. (prefer_count p x xb < prefer_count p xb x) = 
    (prefer_count (times n p) x xb < prefer_count (times n p) xb x)"
      by (metis assms(3) 0 mult_less_cancel2)
    have "finite_profile A p = finite_profile A (times n p)" 
    proof(auto) 
      show " profile A (concat (replicate n p))" using assms
      proof-
(*Linearität von n*p beweisen*)
(*induct bei 1 starten anstatt 0*)

        have "\<forall>i<length p. linear_order_on A (p ! i) \<Longrightarrow> 
        \<forall>i<length (times n p). linear_order_on A ((times n p) ! i)" 
          by (metis n_times_lin assms(1) assms(3))

        then show "profile A (concat (replicate n p))" using assms
          by (simp add: profile_def) 
      qed
      show "profile A (concat (replicate n p)) \<Longrightarrow> profile A p" using assms(1)
      proof-
        have"\<forall>i<length (concat (replicate n p)). linear_order_on A ((times n p) ! i)
        \<Longrightarrow> \<forall>i<length p. linear_order_on A (p ! i)"
          using assms(2) profile_def by blast
        then show "profile A (concat (replicate n p)) \<Longrightarrow> profile A p" 
          unfolding profile_def by simp
      qed
    qed
    then show "(if finite_profile A p \<and> xb \<in> A \<and> (\<forall>x \<in> A - {xb} . wins xb p x) then 1 else 0) =
    (if finite_profile A (times n p) \<and> xb \<in> A \<and> 
    (\<forall>x \<in> A - {xb} . wins xb (times n p) x) then 1 else 0)" using 1 by simp
  qed

(*  "condorcet_score x A p =
    (if (condorcet_winner A p x) then 1 else 0)"
*)
lemma max_same_for_mult_profile:
  assumes "finite A" and  "profile A p" and "0 < n" and "x \<in> A"
  shows "Max {condorcet_score x A p |x. x \<in> A} = Max {condorcet_score x A (times n p) |x. x \<in> A}" 
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) value_same_for_mult_profile) 


lemma for_goal1_condorcet:
  assumes "x \<in> A" and "finite A" and "profile A p" and "0 < n" and
  "condorcet_score xb A p < Max {condorcet_score x A p |x. x \<in> A}"
  shows "condorcet_score xb A (times n p) < 
    Max {condorcet_score x A (times n p) |x. x \<in> A}" 
  by (metis (mono_tags, lifting) max_same_for_mult_profile value_same_for_mult_profile assms) 


lemma for_goal2_condorcet:
  assumes "x \<in> A" and "finite A" and "profile A p" and "0 < n" and 
      "condorcet_score xb A (times n p) < Max {condorcet_score x A (times n p) |x. x \<in> A}"
  shows "condorcet_score xb A p < Max {condorcet_score x A p |x. x \<in> A}"
  by (metis (mono_tags, lifting) max_same_for_mult_profile value_same_for_mult_profile assms)

(*******************************************)

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

lemma elector_homogeneity:
  shows "homogeneity m \<Longrightarrow> homogeneity (elector m)"
proof(simp)
  have "homogeneity elect_module"
    by (simp add: homogeneity_def) 
  then show "homogeneity m \<Longrightarrow> homogeneity (m \<triangleright> elect_module)" using seq_hom by auto
qed

(**Eval_Func Beweis: Evaluation_Function ***)

lemma max_value_same:
  assumes "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
       elimination_set eval_func (Max {eval_func x A p |x. x \<in> A}) (<) A p = 
       elimination_set eval_func (Max {eval_func x A (Electoral_Module.times n p) |x. x \<in> A}) 
       (<) A (Electoral_Module.times n p)"
  shows"(\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p = max_eliminator eval_func A (Electoral_Module.times n p))"
  unfolding max_eliminator.simps less_eliminator.simps elimination_module.simps using assms
  by fastforce 

lemma eval_func_homogeneity:
  assumes "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
       elimination_set eval_func (Max {eval_func x A p |x. x \<in> A}) (<) A p = 
       elimination_set eval_func (Max {eval_func x A (Electoral_Module.times n p) |x. x \<in> A}) (<) A 
      (Electoral_Module.times n p)"
  shows "homogeneity (max_eliminator eval_func)" 
  unfolding homogeneity_def using assms
proof-
  show "electoral_module (max_eliminator eval_func) \<and>
    (\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> max_eliminator eval_func A p = 
    max_eliminator eval_func A (Electoral_Module.times n p))"
    proof-
    have 0:"electoral_module (max_eliminator eval_func)" by auto
    have "(\<forall>A p n.
        finite_profile A p \<and> 0 < n \<longrightarrow>
        max_eliminator eval_func A p =
        max_eliminator eval_func A (Electoral_Module.times n p))" using assms max_value_same
      by fastforce 
    then show ?thesis
      using 0 by blast 
  qed
qed
 
  

lemma scoring_homogeneity:
  shows "homogeneity (max_eliminator (scoring v))"
proof-
  have "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
      elimination_set (scoring v) (Max {(scoring v) x A p |x. x \<in> A}) (<) A p = 
       elimination_set (scoring v) (Max {(scoring v) x A (Electoral_Module.times n p) |x. x \<in> A}) 
      (<) A (Electoral_Module.times n p)"
    using for_goal1 for_goal2 by auto
   then show "homogeneity (max_eliminator (scoring v))"
     by (simp add: eval_func_homogeneity) 
 qed

lemma scoring_rules_homogeneity:
  shows "homogeneity (elector (max_eliminator (scoring vec_A_borda)))" 
  using scoring_homogeneity elector_homogeneity by auto


lemma condorcet_homogeneity:
  shows "homogeneity (max_eliminator condorcet_score)" 
  using elimination_module.simps elimination_set.simps
proof-
  have "\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
      elimination_set condorcet_score (Max {condorcet_score x A p |x. x \<in> A}) (<) A p = 
       elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) |x. x \<in> A}) 
      (<) A (Electoral_Module.times n p)"
    using for_goal1_condorcet for_goal2_condorcet
    by (smt (verit, best) Collect_cong elimination_set.simps) 
  then show ?thesis using eval_func_homogeneity by blast
 qed
(*
lemma condorcet_homogeneity2:
  shows "homogeneity (max_eliminator condorcet_score)" 
  unfolding homogeneity_def
proof-
  have 0: "\<forall>A p. max_eliminator condorcet_score A p
        = elimination_module condorcet_score (Max {condorcet_score x A p | x. x \<in> A}) (<) A p"
    by force
  have 1:"\<forall>A p. elimination_module condorcet_score (Max {condorcet_score x A p | x. x \<in> A}) (<) A p =
  (if (elimination_set condorcet_score (Max {condorcet_score x A p | x. x \<in> A})  (<) A p) \<noteq> A
        then ({}, (elimination_set condorcet_score (Max {condorcet_score x A p | x. x \<in> A})  (<) A p), A 
        - (elimination_set condorcet_score (Max {condorcet_score x A p | x. x \<in> A}) (<) A p))
        else ({},{},A))"
    using elimination_module.simps by blast
   have 2:"\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> 
    (if (elimination_set condorcet_score (Max {condorcet_score x A p | x. x \<in> A})  (<) A p) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A p | x. x \<in> A})  (<) A p), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A p | x. x \<in> A}) (<) A p))
    else ({},{},A)) = 
    (if (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A})  
    (<) A (Electoral_Module.times n p)) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A})  
    (<) A (Electoral_Module.times n p)), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A}) 
    (<) A (Electoral_Module.times n p)))
    else ({},{},A))" 
     using 1 for_goal1_condorcet for_goal2_condorcet by (smt (z3) Collect_cong elimination_set.simps times.simps)
  then have 3:"\<forall>A p n.  finite_profile A p \<and> 0 < n \<longrightarrow> 
    max_eliminator condorcet_score A p = 
        (if (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A})  
    (<) A (Electoral_Module.times n p)) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A})  
    (<) A (Electoral_Module.times n p)), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A}) 
    (<) A (Electoral_Module.times n p)))
    else ({},{},A))" using 0 1 by (smt (z3))
  then have "\<forall>A p n.  finite_profile A p \<and> 0 < n \<longrightarrow> 
    max_eliminator condorcet_score A  (Electoral_Module.times n p) = 
        (if (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A})  
    (<) A (Electoral_Module.times n p)) \<noteq> A
    then ({}, (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A})  
    (<) A (Electoral_Module.times n p)), A 
    - (elimination_set condorcet_score (Max {condorcet_score x A (Electoral_Module.times n p) | x. x \<in> A}) 
    (<) A (Electoral_Module.times n p)))
    else ({},{},A))"
    by (smt (z3) "0" "1" Collect_cong)
  then have "\<forall>A p n.  finite_profile A p \<and> 0 < n \<longrightarrow> 
    max_eliminator condorcet_score A  (Electoral_Module.times n p) = max_eliminator condorcet_score A p"
    by (smt (z3) "3")

   then show "electoral_module (max_eliminator condorcet_score) \<and>
        (\<forall>A p n. finite_profile A p \<and> 0 < n \<longrightarrow> max_eliminator condorcet_score A p = 
        max_eliminator condorcet_score A (Electoral_Module.times n p))"
     by (smt (z3) max_elim_sound) 
     
 qed
*)

(*****)

(********************reinforcement proof**********************************)



lemma combined_eqless_single:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2"
  shows "scoring v x A p1 + scoring v x A p2 \<le> Max {scoring v x A p1 |x. x \<in> A} + 
          Max {scoring v x A p2 |x. x \<in> A}"
proof-
  have "scoring v x A p1 \<in> {scoring v x A p1 |x. x \<in> A}" using assms(3) by blast
  then have 0:"scoring v x A p1 \<le> Max {scoring v x A p1 |x. x \<in> A}" by (simp add: assms(1))
  have "scoring v x A p2 \<in> {scoring v x A p2 |x. x \<in> A}" using assms(3) by blast
  then have 1:"scoring v x A p2 \<le> Max {scoring v x A p2 |x. x \<in> A}" by (simp add: assms(1))
  then show ?thesis using "0" "1" add_mono by blast
qed



lemma combined_max_eqless_single_all:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A} \<le> 
    Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A}"
proof-
  have fin: "finite {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{scoring v x A p1 + scoring v x A p2 |x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A} 
        \<in> {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast 
  have eqToMax:"\<exists>x \<in> A. scoring v x A p1 + scoring v x A p2 = 
        Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" using "maxInSet" by auto
  have allSmaller:"\<forall>x\<in> A. scoring v x A p1 + scoring v x A p2 \<le>
        Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A}"
    using combined_eqless_single all_not_in_conv assms(1) assms(3) assms(4) assms(5) by fastforce  
  have following:"\<exists>x \<in> A. scoring v x A p1 + scoring v x A p2 = 
        Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A} 
  \<Longrightarrow> \<forall>x\<in> A. scoring v x A p1 + scoring v x A p2 \<le> 
        Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A} 
  \<Longrightarrow> Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A} \<le> 
        Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A}"
    by fastforce 
  then show ?thesis using following allSmaller eqToMax by simp
qed





lemma add_scoring_profiles_all:
  shows "\<forall>x \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
        (scoring v x A (b@p) = 
(scoring v x A b) + (scoring v x A p))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed

lemma add_scoring_profiles_all2:
  shows "\<forall>x. (scoring v x A (b@p) = 
(scoring v x A b) + (scoring v x A p))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed



lemma max_is_defer_combined_than_in_both_all:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2" and
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
          scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A (p1@p2) |x. x \<in> A}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    a \<in> defer (max_eliminator (scoring v)) A (p1@p2)"
proof -
   have 0:
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<le> scoring v a A (p1 @ p2)"
    using assms by (metis (no_types, lifting) add_scoring_profiles_all)
  have 
    "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
      Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<le> scoring v a A (p1 @ p2) \<Longrightarrow> 
     \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
    a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"
    (*by (smt (z3) Collect_cong add_scoring_profiles_all max_is_defer_combined)*) 
proof -
  assume a1: "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
      Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<le> scoring v a A (p1 @ p2)"
  { fix aa :: 'a
    { assume "Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<le> scoring v aa A (p1 @ p2)"
      moreover
      { assume "aa \<notin> A"
        then have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) \<or> 
      aa \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2"
          by simp }
      ultimately have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) \<or> 
      aa \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2"
        by simp }
    then have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2) \<or> 
      aa \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2"
      using a1 by meson }
  then show ?thesis
    by metis
qed
  then show "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
       a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"
    using 0 assms
    by linarith 
qed



lemma max_in_both__than_in_combined_defer_all:
  assumes "finite_profile A p1" and "finite_profile A p2" and "a \<in> A" and "finite A" and "A \<noteq> {}" and 
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
        scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A} \<and> 
        scoring v a A p2 =  Max {scoring v x A p2 |x. x \<in> A}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
          a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"
proof-
  have 00:
  "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A} \<ge> 
      Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" 
    using assms combined_max_eqless_single_all
    by (metis (mono_tags, lifting) )
  have 11: 
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A} = scoring v a A p1 + 
          scoring v a A p2" using assms(6)
    by (metis (no_types, lifting)) 
  have 0:
  "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" 
      using "00" "11" assms(6) by (metis (no_types, lifting)) 
  have 1 :"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
    Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A} = Max {scoring v x A (p1@p2) |x. x \<in> A}"
    using max_split_scoring by metis
  have 2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
        scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A (p1@p2) |x. x \<in> A}" 
    using assms 1 0 by (smt (z3))
  moreover have 3:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
      scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A (p1@p2)|x. x \<in> A} \<Longrightarrow>
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms max_is_defer_combined_than_in_both_all by (metis (mono_tags, lifting)) 
  ultimately show "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
          a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms "2" "3" by blast 
qed


lemma max_alway_exists0:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<exists>a \<in> A. scoring v a A p = Max {scoring v x A p |x. x \<in> A}"
proof-
  have fin: "finite {scoring v x A p |x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{scoring v x A p |x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {scoring v x A p |x. x \<in> A} \<in> {scoring v x A p |x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast
  have "Max {scoring v x A p |x. x \<in> A} \<in> {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
        \<exists>a \<in> A. scoring v a A p = Max {scoring v x A p |x. x \<in> A}" by auto
  then show ?thesis using maxInSet by simp
qed

lemma max_alway_exists:
  assumes "finite A" and "A \<noteq> {}"
  shows "{a \<in> A. scoring v a A p < Max {scoring v x A p |x. x \<in> A}} = A \<Longrightarrow> False"
proof-
  have "\<exists>a \<in> A. scoring v a A p = Max {scoring v x A p |x. x \<in> A}" using assms max_alway_exists0 
        by simp
  then show "{a \<in> A. scoring v a A p < Max {scoring v x A p |x. x \<in> A}} = A \<Longrightarrow> False"
    using nat_neq_iff by auto 
qed

lemma max_alway_exists2:
  assumes "finite A" and "A \<noteq> {}" and "finite_profile A p"
  shows "(elimination_set (scoring v) (Max {(scoring v) x A p | x. x \<in> A}) (<) A p \<noteq> A) = True"
  using assms max_alway_exists by auto


lemma not_less_is_max:
  assumes "finite A" and 
    "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p |x. x \<in> A}) (<) A p)"
  shows "scoring v a A p =  Max {scoring v x A p |x. x \<in> A}"
proof-
  have "a \<in> A" using assms(2) by clarify
  then have "scoring v a A p \<in> {scoring v x A p |x. x \<in> A}" 
    using assms(2) by blast
      (*sc a p nicht größer als Max*)
  then have 0:"scoring v a A p \<le>  Max{scoring v x A p |x. x \<in> A}"  
    using assms by auto
      (*sc a p nicht kleiner als Max*)
  have 1:"scoring v a A p \<ge>  Max{scoring v x A p |x. x \<in> A}" 
    using assms(2) by auto
  have "a \<in> A \<Longrightarrow>\<not> scoring v a A p < Max {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
      scoring v a A p = Max {scoring v x A p |x. x \<in> A}" using "0" "1" by simp
  then show "scoring v a A p =  Max {scoring v x A p |x. x \<in> A}" using assms(2)
    by simp
qed



(** from defer follows Max value **)

lemma from_defer_follows_max:
  assumes "finite A" and "A \<noteq> {}"
  shows "a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> 
            scoring v a A p = Max {scoring v x A p |x. x \<in> A}"
proof-
  have "({a \<in> A. scoring v a A p < Max {(scoring v) x A p |x. x \<in> A}} \<noteq> A) = True" 
          using assms max_alway_exists by auto
        then have 0: "a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> 
      a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p |x. x \<in> A}) (<) A p)"
    by simp
  have "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p |x. x \<in> A}) (<) A p) \<Longrightarrow> 
      scoring v a A p =  Max {scoring v x A p |x. x \<in> A}" 
    using assms(1) not_less_is_max by simp
  then have 1:"a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> scoring v a A p = 
      Max {scoring v x A p |x. x \<in> A}" using "0" by simp
  then show "a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> 
      scoring v a A p = Max {scoring v x A p |x. x \<in> A}"
     by simp
 qed


lemma from_defer_follows_max_all:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
      a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> 
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      scoring v a A p = Max {scoring v x A p |x. x \<in> A}"
proof-

  have 0:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
        ({a \<in> A. scoring v a A p < Max {(scoring v) x A p |x. x \<in> A}} \<noteq> A) = True" 
          using assms max_alway_exists by auto

        have "a \<in> (A - elimination_set (scoring v) (Max {(scoring v) x A p |x. x \<in> A}) (<) A p) \<Longrightarrow>
      scoring v a A p =  Max {scoring v x A p |x. x \<in> A}" 
    using assms(1) not_less_is_max by simp
  then have 1:
        "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
                a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> 
                \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> 
                defer (max_eliminator (scoring v)) A p2). 
                scoring v a A p = Max {scoring v x A p |x. x \<in> A}" using "0"
    by (metis (mono_tags, lifting) assms(1) assms(2) from_defer_follows_max)
  then show 
      "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      a \<in> defer (max_eliminator (scoring v)) A p \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      scoring v a A p = Max {scoring v x A p |x. x \<in> A}"
    by simp
qed


lemma from_defer_follows_max2_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
  a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2) 
  \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      (scoring v a A p1 = Max {scoring v x A p1 |x. x \<in> A})" 
  by (metis (mono_tags, lifting) IntD1 assms from_defer_follows_max_all)


lemma from_defer_follows_max3_for_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
   a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2) \<Longrightarrow> 
   \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      (scoring v a A p1 = Max {scoring v x A p1 |x. x \<in> A}) \<and> 
      (scoring v a A p2 = Max {scoring v x A p2 |x. x \<in> A})" 
  using assms from_defer_follows_max2_all
  by blast 


(*** ---------- ***)



lemma reinforcement_defer_scoring_helper:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2"
  shows "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} \<Longrightarrow>
  defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2)"
proof-

  have all:
      "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"
    by (meson from_defer_follows_max3_for_all max_in_both__than_in_combined_defer_all assms) 

  then have d1:"(defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)
      \<subseteq> defer (max_eliminator (scoring v)) A (p1 @ p2)"
    using assms by blast 
(***********)
  have 00:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
  a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2) \<Longrightarrow> 
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
   (scoring v a A p1 = Max {scoring v x A p1 |x. x \<in> A}) \<and> 
      (scoring v a A p2 = Max {scoring v x A p2 |x. x \<in> A})" 
    by (metis (mono_tags, lifting) assms(1) assms(2) from_defer_follows_max3_for_all) 

  have 11:"scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A} \<and> 
      scoring v a A p2 = Max {scoring v x A p2 |x. x \<in> A} \<Longrightarrow>
   \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms max_in_both__than_in_combined_defer_all all by blast 
  have all:
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
    a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)" using assms "00" "11"
    using all by blast (*by simp*)
  then have d1:"(defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)
      \<subseteq> defer (max_eliminator (scoring v)) A (p1 @ p2)"
    using assms by blast 


  have "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} \<Longrightarrow>
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ).
    a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)"
proof-
(*1)*)
(*relevant für "comb_is_eq"*)
  have a_is_max_p1_p2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ).
          scoring v a A (p1@p2) = Max {scoring v x A (p1@p2) |x. x \<in> A}" 
    using assms by (smt (z3) Collect_cong from_defer_follows_max)

  have same_as_add:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
      (scoring v a A (p1@p2) = (scoring v a A p1) + (scoring v a A p2))" 
      using add_scoring_profiles by fastforce


    have elem_A2:
        "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. a\<in>A"
      using assms(1) assms(4) defer_in_alts max_elim_sound by blast
    have elem_A:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). a \<in> A" by simp

(*relevant für "1"*)
    then have "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). scoring v a A p1 \<in> 
      {scoring v x A p1 |x. x \<in> A}" 
      using assms(3) by blast
    then have smaller_max:
          "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). scoring v a A p1 \<le> 
      Max {scoring v x A p1 |x. x \<in> A}" 
      using assms(1) by simp
    then have "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). scoring v a A p2 \<in> 
      {scoring v x A p2 |x. x \<in> A}" 
      using assms(3) "elem_A" by blast
    then have smaller_max2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
      scoring v a A p2 \<le>  Max {scoring v x A p2 |x. x \<in> A}" 
      using assms(1) by simp
(*relevant für "from_single_follows_combined"*)
    have 11:"defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {}
      \<Longrightarrow> \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
          (scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A}) \<and> (scoring v a A p2 = 
      Max {scoring v x A p2 |x. x \<in> A})"
      using "00" by blast

        have elem_of:
          "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
                        scoring v a A p1 + scoring v a A p2 \<in> {scoring v x A (p1@p2) |x. x \<in> A}" 
      using same_as_add by (metis (mono_tags, lifting) elem_A2 add_scoring_profiles mem_Collect_eq) 


    have 001:"\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
        Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A} \<ge> 
        Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" 
      using assms combined_max_eqless_single_all by (metis (mono_tags, lifting) ) 


    then have 000:
        "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
         scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" 
      using assms by (metis (no_types, lifting) "11" equals0D)  

    then  have 
        "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
                  Max {scoring v x A (p1@p2) |x. x \<in> A} \<le> scoring v a A p1 + scoring v a A p2" 
      by (smt (verit, del_insts) Collect_cong add_scoring_profiles_all2 assms elem_of) 

    then have comb_is_eq:
          "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
          Max {scoring v x A (p1@p2) |x. x \<in> A} = scoring v a A p1 + scoring v a A p2" using elem_of
          proof -
            { fix aa :: 'a
              have "\<And>a. a \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> 
                  defer (max_eliminator (scoring v)) A p2 \<or> 
                  Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<le> scoring v a A (p1 @ p2)"
                by (smt (z3) \<open>\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> 
                defer (max_eliminator (scoring v)) A p2. 
                Max {scoring v x A (p1 @ p2) |x. x \<in> A} \<le> 
                scoring v a A p1 + scoring v a A p2\<close> add_scoring_profiles)
              moreover
              {assume "aa \<in> A \<and> Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<le> scoring v aa A (p1 @ p2)"
                then have "aa \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"
                  by simp
            then have "Max {scoring v a A (p1 @ p2) |a. a \<in> A} = scoring v aa A (p1 @ p2)"
              by (smt (z3) a_is_max_p1_p2)
            then have 
              "scoring v aa A p1 + scoring v aa A p2 = Max {scoring v a A (p1 @ p2) |a. a \<in> A} 
        \<or> aa \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2"
              by (smt (z3) add_scoring_profiles) }
          ultimately have "scoring v aa A p1 + scoring v aa A p2 = 
              Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<or> 
             aa \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2"
            using \<open>\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> 
                  defer (max_eliminator (scoring v)) A p2. a \<in> A\<close> by blast }
        then have "\<forall>a. scoring v a A p1 + scoring v a A p2 = 
                    Max {scoring v a A (p1 @ p2) |a. a \<in> A} \<or> 
              a \<notin> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2"
              by satx
            then show ?thesis
              by (smt (z3))
                 qed

    have eq:"\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
            Max {scoring v x A (p1@p2) |x. x \<in> A} = scoring v a A p1 + scoring v a A p2 \<Longrightarrow> 
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
            scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A} \<and> scoring v a A p2 = 
                  Max {scoring v x A p2 |x. x \<in> A} \<Longrightarrow>
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
            Max {scoring v x A (p1@p2) |x. x \<in> A} = Max {scoring v x A p1 |x. x \<in> A} + 
            Max {scoring v x A p2 |x. x \<in> A}"
      by (metis (no_types, lifting)) 

    then have "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
          (scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A}) \<and> 
          (scoring v a A p2 =  Max {scoring v x A p2 |x. x \<in> A}) \<Longrightarrow>
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
            Max {scoring v x A (p1@p2) |x. x \<in> A} = scoring v a A p1 + scoring v a A p2" 
              using assms comb_is_eq
      by linarith 

    then have from_single_follows_combined:
        "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} \<Longrightarrow>
        Max {scoring v x A (p1@p2) |x. x \<in> A} = Max {scoring v x A p1 |x. x \<in> A} + 
        Max {scoring v x A p2 |x. x \<in> A}"
    using assms "11" "eq" by blast


  have 00:"defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} 
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
        scoring v a A p1 + scoring v a A p2 = Max {scoring v x A p1 |x. x \<in> A} + 
        Max {scoring v x A p2 |x. x \<in> A}"
    using a_is_max_p1_p2 from_single_follows_combined same_as_add by fastforce
        

  have 1:"defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} 
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
        (scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A}) \<and> 
      (scoring v a A p2 =  Max {scoring v x A p2 |x. x \<in> A})"
    using assms "a_is_max_p1_p2" "from_single_follows_combined" "same_as_add" 
          "smaller_max" "smaller_max2" "00"
    by (smt (z3) add_le_cancel_right le_antisym nat_add_left_cancel_le)
    

    have 3:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
          scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A} \<Longrightarrow> 
          \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
          scoring v a A p2 =  Max {scoring v x A p2 |x. x \<in> A} \<Longrightarrow>
          \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
          a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> 
          defer (max_eliminator (scoring v)) A p2)" 
            using assms by simp

          then show 
            "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {}
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ).
      a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)" 
            using assms "1" "3" by blast
  qed
  

  then show "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {}
      \<Longrightarrow> defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms "d1" by blast
qed

(*
lemma reinforcement_defer_scoring_different_A_helper:
  assumes "finite A1" and "finite A1" and "A1 \<noteq> {}" and "A2 \<noteq> {}" and "a \<in> A1" and "a \<in> A2" 
    and "profile A1 p1" and "profile A2 p2"
  shows "defer (max_eliminator (scoring v)) A1 p1 \<inter> defer (max_eliminator (scoring v)) A2 p2 \<noteq> {} \<Longrightarrow>
  defer (max_eliminator (scoring v)) A1 p1 \<inter> defer (max_eliminator (scoring v)) A2 p2 = 
      defer (max_eliminator (scoring v)) (A1\<union>A2) (p1 @ p2)" sorry
*)

lemma reinforcement_defer_scoring:
  shows "reinforcement_defer (max_eliminator (scoring v))"
  unfolding reinforcement_defer_def 
proof-
  have 0:"electoral_module (max_eliminator (scoring v))" by simp
  have 1:"(\<forall>A p1 p2.
        finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2))" 
    by (smt (verit, best) "0" Int_emptyI defer_in_alts equals0D in_mono reinforcement_defer_scoring_helper) 
  then show "electoral_module (max_eliminator (scoring v)) \<and>
    (\<forall>A p1 p2. finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} \<longrightarrow>
        defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2))" 
    using "0" by clarify
qed

(*
lemma reinforcement_defer_different_A_scoring:
  shows "reinforcement_defer_different_A (max_eliminator (scoring v))"
  unfolding reinforcement_defer_different_A_def 
proof-
  have 0:"electoral_module (max_eliminator (scoring v))" by simp
  have 1:"(\<forall>A1 A2 p1 p2.
        finite_profile A1 p1 \<and> finite_profile A2 p2 \<longrightarrow>
        defer (max_eliminator (scoring v)) A1 p1 \<inter> defer (max_eliminator (scoring v)) A2 p2 \<noteq> {} \<longrightarrow>
        defer (max_eliminator (scoring v)) A1 p1 \<inter> defer (max_eliminator (scoring v)) A2 p2 = 
      defer (max_eliminator (scoring v)) (A1\<union>A2) (p1 @ p2))" 
    by (smt (verit, best) "0" Int_emptyI defer_in_alts equals0D in_mono reinforcement_defer_scoring_different_A_helper) 
  then show "electoral_module (max_eliminator (scoring v)) \<and>
    (\<forall>A1 A2 p1 p2. finite_profile A1 p1 \<and> finite_profile A2 p2 \<longrightarrow>
        defer (max_eliminator (scoring v)) A1 p1 \<inter> defer (max_eliminator (scoring v)) A2 p2 \<noteq> {} \<longrightarrow>
        defer (max_eliminator (scoring v)) A1 p1 \<inter> defer (max_eliminator (scoring v)) A2 p2 = 
      defer (max_eliminator (scoring v)) (A1\<union>A2) (p1 @ p2))" 
    using "0" by clarify
qed
*)

(*klar, weil es keinen Gewinner gibt. Umschreiben mit defer?*)
lemma reinforcement_scoring:
  shows "reinforcement (max_eliminator (scoring v))"
  unfolding reinforcement_def by simp

(*
lemma reinforcement_different_A_scoring:
  shows "reinforcement_different_A (max_eliminator (scoring v))"
  unfolding reinforcement_different_A_def by simp
*)


(*********************************)
(*
lemma seq_rein:
  shows "reinforcement_defer m \<Longrightarrow> \<forall>A p. well_formed A (m A p) \<Longrightarrow> \<forall>A p. elect m A p = {} \<Longrightarrow> reinforcement n \<Longrightarrow> reinforcement (m \<triangleright> n)"
proof-


  have 0:"\<forall>A p. elect m A p = {} \<Longrightarrow> 
  \<forall>A p. elect (m \<triangleright> n) A p = elect n (defer m A p) (limit_profile (defer m A p) p)"
  proof(simp)
    show "\<forall>A p. elect m A p = {} \<Longrightarrow>
    \<forall>A p. elect_r (let new_A = defer m A p; new_p = map (limit new_A) p
    in (elect n new_A new_p, reject m A p \<union> reject n new_A new_p, defer n new_A new_p)) =
    elect n (defer m A p) (map (limit (defer m A p)) p)"
      by (metis fst_conv) 
  qed 



  have "electoral_module m \<and>
    (\<forall>A p1 p2.
        finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2)) \<Longrightarrow>

    \<forall>A p. elect m A p = {} \<Longrightarrow>
    \<forall>A p. well_formed A (m A p) \<Longrightarrow>
    electoral_module n \<and>
    (\<forall>A p1 p2.
        finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2)) \<Longrightarrow>

    (\<forall>A p1 p2. finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow> 
    elect n (defer m A p1) (limit_profile (defer m A p1) p1) 
    \<inter> elect n (defer m A p2) (limit_profile (defer m A p2) p2) \<noteq> {} \<longrightarrow>

    elect n (defer m A p1) (limit_profile (defer m A p1) p1) 
    \<inter> elect n (defer m A p2) (limit_profile (defer m A p2) p2) = 
    elect n (defer m A (p1 @ p2)) (limit_profile (defer m A (p1 @ p2)) (p1 @ p2)))"
  proof(auto)
(*******)
    show "\<And>A p1 p2 x xa.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>
       x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
       x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
       xa \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1 @ map (limit (defer m A (p1 @ p2))) p2)
" 
     proof-





(****)


      have f1:"\<And>A p1 p2 x. \<forall>p. elect m A p = {} \<Longrightarrow> 
            \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
            electoral_module m \<Longrightarrow>
            finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
           defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
    
           electoral_module n \<Longrightarrow>
            finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
           elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
           profile A p1 \<Longrightarrow>
           finite A \<Longrightarrow>
           profile A p2 \<Longrightarrow>
           finite_profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1) \<and> 
           finite_profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2)" 
      proof-
(**)
       
        have ff1:"\<And>A p1 p2. finite A \<and> profile A p1 \<and> profile A p2 \<Longrightarrow>
                  profile A (p1@p2)" by (simp add: nth_append profile_def) 


        have "\<And>A p. finite A \<and> finite_profile A p \<Longrightarrow> 
        disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
        finite (defer m A p)"
          by (metis defer_subset rev_finite_subset well_formed.elims(3))

        then have xx0:"\<And>A p1 p2. finite A \<and> profile A (p1@p2) \<and> finite_profile A (p1@p2) \<Longrightarrow> 
          \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
          finite (defer m A (p1 @ p2))" 
          using ff1 by simp


        have yy1: "\<And>A p1 p2.  \<And>A p1 p2. finite (defer m A (p1 @ p2)) \<Longrightarrow> 
                  \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
                  \<forall>i::nat. i < length (map (limit (defer m A (p1 @ p2))) p1) 
        \<longrightarrow> linear_order_on (defer m A (p1 @ p2)) ((map (limit (defer m A (p1 @ p2))) p1)!i)" sorry
        have yy2: "\<And>A p1 p2. finite (defer m A (p1 @ p2)) \<Longrightarrow> 
                  \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
                  \<forall>i::nat. i < length (map (limit (defer m A (p1 @ p2))) p2) 
        \<longrightarrow> linear_order_on (defer m A (p1 @ p2)) ((map (limit (defer m A (p1 @ p2))) p2)!i)" sorry

        have xx1:"\<And>A p1 p2. finite (defer m A (p1 @ p2)) \<Longrightarrow> 
                  \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
                profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1)" 
          using yy1 profile_def by blast 
        have xx2:"\<And>A p1 p2 x. finite (defer m A (p1 @ p2)) \<Longrightarrow> 
                \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> 
                profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2)"  
          using yy2 profile_def by blast


         have x1:"\<And>A p1 p2. \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
            finite A \<and> profile A (p1@p2) \<and> finite_profile A (p1@p2) \<Longrightarrow>
            finite_profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1)" 
           using xx0 xx1 by simp


         have x2:"\<And>A p1 p2. \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
            finite A \<and> profile A (p1@p2) \<Longrightarrow>
            finite_profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2)" 
           using xx0 xx2 by simp

(* Hier fehlen noch die Vorraussetzungen von x1 und x2. Kann man aus ff1 evtl ziehn *)
        have "\<And>A p p1 p2. profile A p1 \<Longrightarrow> finite A \<Longrightarrow> profile A p2 \<Longrightarrow> profile A (p1@p2)"
          by (simp add: ff1) 
        then show "\<And>A p1 p2 x.  \<forall>p. elect m A p = {} \<Longrightarrow> 
            \<forall>p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
            electoral_module m \<Longrightarrow>
            finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
           defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
    
           electoral_module n \<Longrightarrow>
            finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
           elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
           profile A p1 \<Longrightarrow>
           finite A \<Longrightarrow>
           profile A p2 \<Longrightarrow>
           finite_profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1) \<and> 
           finite_profile (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2)"
         by (simp add: ff1 x1 x2) 
        qed
(**)


(******************)
        have "\<And>A1 A2 A3 p1 p2 x. electoral_module n \<Longrightarrow> finite A1 \<Longrightarrow>finite A2 \<Longrightarrow> A3 = (A1 \<inter> A2) \<Longrightarrow>
              profile A1 p1 \<Longrightarrow>profile A2 p2 \<Longrightarrow> 
          \<forall>A1 A2 A3 p1 p2. finite A1 \<and> profile A1 p1 \<and> finite_profile A2 p2 \<longrightarrow>
          elect n A1 p1 \<inter> elect n A2 p2 \<noteq> {} \<longrightarrow> elect n A1 p1 \<inter> elect n A2 p2 = elect n (A1 \<union> A2) (p1 @ p2) \<Longrightarrow>
              x \<in> elect n A1 (map (limit A1) p1) \<Longrightarrow>
              x \<in> elect n A2 (map (limit A2) p2) \<Longrightarrow>
              x \<in> elect n A3  (map (limit A3) p1)" sorry

      then have f2:"\<And>A p1 p2 x.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>

            x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
            x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
            x \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1)" using f1 sorry

      have f3:"\<And>A p1 p2 x.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>

            x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
            x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
            x \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2)" sorry

      have f4:"\<And>A p1 p2 x.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>

            x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
            x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>

            x \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1) \<Longrightarrow>
            x \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2) \<Longrightarrow>
           elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1) \<inter> 
           elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p2) \<noteq> {}"
        by blast 

(*show1*)
       show "\<And>A p1 p2 x xa.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>
       x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
       x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
       xa \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1 @ map (limit (defer m A (p1 @ p2))) p2)"
         using f1 f2 f3 f4 by simp 
    qed

(*show2*)
    show"\<And>A p1 p2 x xa.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>
       x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
       x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1 @ map (limit (defer m A (p1 @ p2))) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1)" sorry
(*show3*)
    show"\<And>A p1 p2 x xa.
       \<forall>A p. elect m A p = {} \<Longrightarrow>
       \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow>
       electoral_module m \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2) \<Longrightarrow>
       electoral_module n \<Longrightarrow>
       \<forall>A p1 p2.
          finite A \<and> profile A p1 \<and> finite_profile A p2 \<longrightarrow>
          elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2) \<Longrightarrow>
       profile A p1 \<Longrightarrow>
       finite A \<Longrightarrow>
       profile A p2 \<Longrightarrow>
       x \<in> elect n (defer m A p1) (map (limit (defer m A p1)) p1) \<Longrightarrow>
       x \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A (p1 @ p2)) (map (limit (defer m A (p1 @ p2))) p1 @ map (limit (defer m A (p1 @ p2))) p2) \<Longrightarrow>
       xa \<in> elect n (defer m A p2) (map (limit (defer m A p2)) p2)" sorry
  qed

  then have 1:"electoral_module m \<and>
        (\<forall>A p1 p2.
        finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        defer m A p1 \<inter> defer m A p2 \<noteq> {} \<longrightarrow> defer m A p1 \<inter> defer m A p2 = defer m A (p1 @ p2)) \<Longrightarrow>

    \<forall>A p. well_formed A (m A p) \<Longrightarrow>
    \<forall>A p. elect m A p = {} \<Longrightarrow>

    electoral_module n \<and>
    (\<forall>A p1 p2.
        finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2)) \<Longrightarrow>

    (\<forall>A p1 p2. finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
        elect n A p1 \<inter> elect n A p2 \<noteq> {} \<longrightarrow> elect n A p1 \<inter> elect n A p2 = elect n A (p1 @ p2)) \<Longrightarrow>

    (\<forall>A p1 p2. finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow> 
      elect n (defer m A p1) (limit_profile (defer m A p1) p1) 
    \<inter> elect n (defer m A p2) (limit_profile (defer m A p2) p2) \<noteq> {} \<longrightarrow>
      elect n (defer m A p1) (limit_profile (defer m A p1) p1) 
    \<inter> elect n (defer m A p2) (limit_profile (defer m A p2) p2) =
    elect n (defer m A (p1 @ p2)) (limit_profile (defer m A (p1 @ p2)) (p1 @ p2)))" by simp

  have 2:"electoral_module m \<Longrightarrow> electoral_module n \<Longrightarrow> electoral_module (m \<triangleright> n)" by simp

  show "reinforcement_defer m \<Longrightarrow> \<forall>A p. well_formed A (m A p) \<Longrightarrow> \<forall>A p. elect m A p = {} \<Longrightarrow> reinforcement n \<Longrightarrow> reinforcement (m \<triangleright> n)" 
    unfolding reinforcement_defer_def reinforcement_def using 0 1 2 by presburger
qed



(*******************************************)
lemma elector_reinforcement:
  shows "reinforcement_defer m \<Longrightarrow>\<forall>A p. well_formed A (m A p) \<Longrightarrow> \<forall>A p. elect m A p = {} \<Longrightarrow> reinforcement (elector m)"
proof(simp)
  have "reinforcement elect_module"
    by (simp add: reinforcement_def) 
  then show "reinforcement_defer m \<Longrightarrow>
    \<forall>A p. disjoint3 (m A p) \<and> set_equals_partition A (m A p) \<Longrightarrow> \<forall>A p. elect m A p = {} \<Longrightarrow> reinforcement (m \<triangleright> elect_module)"
    by (simp add: \<open>reinforcement elect_module\<close> seq_rein)
qed
*)
(*fun elect_module :: "'a Electoral_Module" where
  "elect_module A p = (A, {}, {})"*)
lemma elector_reinforcement2:
  shows "reinforcement (elector(max_eliminator (scoring v)))"
proof(simp)
  have def: "reinforcement_defer (max_eliminator (scoring v))"
    by (simp add: reinforcement_defer_scoring) 
  have "reinforcement elect_module" 
    by (simp add: reinforcement_def) 
  have emp: "\<forall>A p. elect (max_eliminator (scoring v)) A p = {}" using max_elim_non_electing by simp
  have "\<forall>A p. elect (max_eliminator (scoring v)) A p = {} \<Longrightarrow> 
        \<forall>A p. defer (max_eliminator (scoring v)) A p = elect (elector(max_eliminator (scoring v))) A p" 
      by (simp add: reinforcement_def)
  then show "reinforcement (max_eliminator (scoring v) \<triangleright> elect_module)"
    by (smt (z3) emp
         def elect_mod_sound elector.elims reinforcement_def reinforcement_defer_def seq_comp_sound)
qed


lemma scoring_module_rein:
  shows "reinforcement (elector(max_eliminator (scoring v)))" 
proof-
  have 0:"\<forall>A p. elect (max_eliminator (scoring v)) A p = {}" by simp
  have "\<forall>A p. well_formed A ((max_eliminator (scoring v)) A p)" by auto
  then show ?thesis using elector_reinforcement2 reinforcement_defer_scoring 0 by blast
qed







(*Addieren von Profilen für scoring4*)
lemma add_scoring_same_profiles:
  shows "scoring v x A (p @ p) = scoring v x A p + scoring v x A p"
  by (metis add_scoring_profiles)

lemma add_scoring4_profiles:
  shows "(scoring4 v x A (b@p) = (scoring4 v x A b) + (scoring4 v x A p))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed
(*
lemma add_scoring4_same_profiles:
  shows "scoring4 v x A (p @ p) = scoring4 v x A p + scoring4 v x A p"
  by (metis add_scoring4_profiles)
*)
end
