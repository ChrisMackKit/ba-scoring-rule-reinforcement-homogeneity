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




lemma Max_homo_mult:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {scoring v x A p * k |x. x\<in>A} = Max {scoring v x A p|x. x\<in>A} * k" 
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
    by (metis (no_types, lifting) 1 mult.commute times_scoring)
  then show "scoring v xb A (times n p) < 
    Max {scoring v x A (times n p) |x. x \<in> A}"
    using 2 assms by auto
qed


lemma for_goal2:
  assumes "x \<in> A" and "finite A" and "profile A p" and "0 < n" and "xa \<in> A" and "xb \<in> A" and
  "scoring v xb A (times n p) < Max {scoring v x A (times n p) |x. x \<in> A}"
  shows " scoring v xb A p < Max {scoring v x A p |x. x \<in> A}"
proof-
  have 0 :"Max {scoring v x A (times n p) |x. x \<in> A} = Max {scoring v x A p * n |x. x \<in> A}" 
      using times_scoring by metis 
    then have 1:  "Max {scoring v x A (times n p) |x. x \<in> A} = 
          n* Max {scoring v x A p |x. x \<in> A}" 
proof -
  have "\<And>A f rs n. infinite A \<or> A = Collect bot \<or> Max {scoring f (a::'a) A rs |a. a \<in> A} * n = 
          Max {scoring f a A rs * n |a. a \<in> A}" 
    using Max_homo_mult bot_set_def by fastforce
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
     Max {scoring v x A (times n p) |x. x \<in> A}" using assms(7) by auto 
  then show "scoring v xb A p < Max {scoring v x A p |x. x \<in> A}"
    using 1 2 assms(7) times_scoring by (metis (no_types, lifting) mult.commute times_scoring) 
qed

(***** Für Black's Rule bzw Condorcet *****)

lemma add_prefer_profiles_code:
  shows "(prefer_count_code (b@p) x y = (prefer_count_code b x y) + (prefer_count_code p x y))" 
proof(induct b)
  case Nil
  then show ?case by auto
next
  case (Cons a b)
  then show ?case by auto
qed

lemma pref_count_test_code:
"(prefer_count_code p x y) * n = prefer_count_code (times n p) x y"
  proof(induct n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case using times_profile mult_Suc_right add_prefer_profiles_code
      by metis
  qed

lemma times_prefer:
  shows "(prefer_count p x y) * n = prefer_count (times n p) x y"
    using pref_count_test_code pref_count_equiv by metis 
             


(*********)

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


lemma max_same_for_mult_profile:
  assumes "finite A" and  "profile A p" and "0 < n" and "x \<in> A"
  shows "Max {condorcet_score x A p |x. x \<in> A} = Max {condorcet_score x A (times n p) |x. x \<in> A}" 
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) value_same_for_mult_profile) 


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
    using max_same_for_mult_profile value_same_for_mult_profile
    by (smt (z3) Collect_cong elimination_set.simps) 
  then show ?thesis using eval_func_homogeneity by blast
 qed


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
        (scoring v x A (b@p) = (scoring v x A b) + (scoring v x A p))" 
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



lemma max_alway_exists:
  assumes "finite A" and "A \<noteq> {}"
  shows "{a \<in> A. scoring v a A p < Max {scoring v x A p |x. x \<in> A}} = A \<Longrightarrow> False"
proof-
  have "\<exists>a \<in> A. scoring v a A p = Max {scoring v x A p |x. x \<in> A}" using assms  
        proof-
          have fin: "finite {scoring v x A p |x. x \<in> A}" using assms(1) by simp
          have nonEmpty: "{scoring v x A p |x. x \<in> A}  \<noteq> {}" using assms(2) by simp
          then have maxInSet:"Max {scoring v x A p |x. x \<in> A} \<in> {scoring v x A p |x. x \<in> A}"
            using "fin" "nonEmpty" eq_Max_iff by blast
          have "Max {scoring v x A p |x. x \<in> A} \<in> {scoring v x A p |x. x \<in> A} \<Longrightarrow> 
                \<exists>a \<in> A. scoring v a A p = Max {scoring v x A p |x. x \<in> A}" by auto
          then show ?thesis using maxInSet by simp
        qed
  then show "{a \<in> A. scoring v a A p < Max {scoring v x A p |x. x \<in> A}} = A \<Longrightarrow> False"
    using nat_neq_iff by auto 
qed



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
    by linarith 
    (*by simp*)
qed


lemma from_defer_follows_max2_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
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

lemma max_in_both__than_in_combined_defer_all_test:
  assumes "finite_profile A p1" and "finite_profile A p2" and "a \<in> A" and "finite A" and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
          a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"
proof-
  have 00:
  "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A} \<ge> 
      Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" 
    using assms combined_max_eqless_single_all
    by (metis (mono_tags, lifting) )

  have p1: "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A}" 
    using assms from_defer_follows_max2_all by blast
  have p2: "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      scoring v a A p2 =  Max {scoring v x A p2 |x. x \<in> A}" 
    using assms from_defer_follows_max2_all by blast

  have 11: 
    "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      Max {scoring v x A p1 |x. x \<in> A} + Max {scoring v x A p2 |x. x \<in> A} = scoring v a A p1 + 
          scoring v a A p2" using assms p1 p2
    by (metis (no_types, lifting)) 
  have 0:
  "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
    scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A}" 
      using "00" "11" by (metis (no_types, lifting)) 
  have 1 :"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
    Max {scoring v x A p1 + scoring v x A p2 |x. x \<in> A} = Max {scoring v x A (p1@p2) |x. x \<in> A}"
    using max_split_scoring by metis
  have 2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
        scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A (p1@p2) |x. x \<in> A}" 
    using assms 1 0  by (metis (no_types, lifting))
  moreover have 3:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
      scoring v a A p1 + scoring v a A p2 \<ge> Max {scoring v x A (p1@p2)|x. x \<in> A} \<Longrightarrow>
      \<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2). 
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms max_is_defer_combined_than_in_both_all by (metis (mono_tags, lifting)) 
  ultimately show "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
          a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms "2" "3" by blast 
qed
(*** ---------- ***)



lemma reinforcement_defer_scoring_helper:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2" and 
    "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {}"
  shows "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2)"
proof-

  have all:
      "\<forall>a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2).
      a \<in> defer (max_eliminator (scoring v)) A (p1 @ p2)"  
    using  max_in_both__than_in_combined_defer_all_test 
      assms(1) assms(2) assms(3) assms(4) assms(5) assms(6)
    by metis 

  then have d1:"(defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)
      \<subseteq> defer (max_eliminator (scoring v)) A (p1 @ p2)"
    using assms by blast 
(***********)


  have "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 \<noteq> {} \<Longrightarrow>
    \<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ).
    a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)"
proof-

  have a_is_max_p1_p2:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ).
          scoring v a A (p1@p2) = Max {scoring v x A (p1@p2) |x. x \<in> A}" 
    using assms 
    by (smt (z3) Collect_cong from_defer_follows_max)

  have same_as_add:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
      (scoring v a A (p1@p2) = (scoring v a A p1) + (scoring v a A p2))" 
      using add_scoring_profiles by fastforce



    have elem_A:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). a \<in> A" by simp


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



     have comb_is_eq:
          "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2.
          Max {scoring v x A (p1@p2) |x. x \<in> A} = scoring v a A p1 + scoring v a A p2" 
            using a_is_max_p1_p2 add_scoring_profiles all
      by (metis (no_types, lifting)) 
      
    have "\<forall>a\<in>defer (max_eliminator (scoring v)) A p1  \<inter> defer (max_eliminator (scoring v)) A p2 . 
          (scoring v a A p1  =  Max {scoring v x A p1 |x. x \<in> A}) \<and> (scoring v a A p2  = 
      Max {scoring v x A p2 |x. x \<in> A})"
      using from_defer_follows_max2_all assms by blast

    then have eq:"
            \<forall>a\<in>defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2. 
            Max {scoring v x A (p1@p2) |x. x \<in> A} = Max {scoring v x A p1 |x. x \<in> A} + 
            Max {scoring v x A p2 |x. x \<in> A}"  using comb_is_eq
      by (metis (no_types, lifting)) 

     have from_single_follows_combined:
        "Max {scoring v x A (p1@p2) |x. x \<in> A} = Max {scoring v x A p1 |x. x \<in> A} + 
        Max {scoring v x A p2 |x. x \<in> A}"
    using assms eq by blast

        

  have 1:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
        (scoring v a A p1 =  Max {scoring v x A p1 |x. x \<in> A}) \<and> 
      (scoring v a A p2 =  Max {scoring v x A p2 |x. x \<in> A})"
    using assms "a_is_max_p1_p2" "from_single_follows_combined" "same_as_add" 
          "smaller_max" "smaller_max2" by fastforce
    

    then have 3:"\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ). 
          a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> 
          defer (max_eliminator (scoring v)) A p2)" 
            using assms by simp

           show 
            "\<forall>a \<in> (defer (max_eliminator (scoring v)) A (p1 @ p2) ).
          a \<in> (defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2)" 
            using assms "3" by blast
  qed
  

  then show "defer (max_eliminator (scoring v)) A p1 \<inter> defer (max_eliminator (scoring v)) A p2 = 
      defer (max_eliminator (scoring v)) A (p1 @ p2)" 
    using assms "d1" by blast
qed


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



lemma reinforcement_scoring:
  shows "reinforcement_elect (max_eliminator (scoring v))"
  unfolding reinforcement_elect_def by simp

lemma complete_reinforcement_scoring:
  shows "reinforcement_complete (max_eliminator (scoring v))"    
  by (simp add: from_elect_and_defer_follows_reinforcement 
reinforcement_defer_scoring reinforcement_scoring) 

(*********************************)

lemma elect_complete_reinforcement:
  shows "reinforcement_complete elect_module"
  by (simp add: reinforcement_defer_def reinforcement_elect_def 
from_elect_and_defer_follows_reinforcement)  

lemma module_with_elect_reinforcement_complete:
  shows "reinforcement (elector(max_eliminator (scoring v)))" 
proof(simp)
  have def: "reinforcement_defer (max_eliminator (scoring v))"
    by (simp add: reinforcement_defer_scoring)
  then have 1:"electoral_module (max_eliminator (scoring v)) \<and> 
    (\<forall> A p1 p2 vs1 vs2. (finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
    (defer (max_eliminator (scoring v)) A p1) \<inter> (defer (max_eliminator (scoring v)) A p2) \<noteq> {} \<longrightarrow>
    ((defer (max_eliminator (scoring v)) A p1) \<inter> (defer (max_eliminator (scoring v)) A p2) = 
    defer (max_eliminator (scoring v)) A (p1 @ p2))))" 
    using reinforcement_defer_def by blast
  have emp: "\<forall>A p. elect (max_eliminator (scoring v)) A p = {}" 
    using max_elim_non_electing by simp
   show "reinforcement ((max_eliminator (scoring v)) \<triangleright> elect_module)" 
    unfolding reinforcement_elect_def reinforcement_def 
    using 1 emp
    by  (simp add: reinforcement_def) 
qed




lemma elector_reinforcement:
  shows "reinforcement_complete (elector(max_eliminator (scoring v)))" 
proof(simp)
  have "\<forall> A p. defer (elector(max_eliminator (scoring v))) A p = {}" 
    unfolding elector.simps by simp
  then have elect_defer:"reinforcement_defer (elector(max_eliminator (scoring v)))" 
    by (simp add: reinforcement_defer_def) 
  have def: "reinforcement_defer (max_eliminator (scoring v))"
    by (simp add: reinforcement_defer_scoring)
  then have 1:"electoral_module (max_eliminator (scoring v)) \<and> 
    (\<forall> A p1 p2 vs1 vs2. (finite_profile A p1 \<and> finite_profile A p2 \<longrightarrow>
    (defer (max_eliminator (scoring v)) A p1) \<inter> (defer (max_eliminator (scoring v)) A p2) \<noteq> {} \<longrightarrow>
    ((defer (max_eliminator (scoring v)) A p1) \<inter> (defer (max_eliminator (scoring v)) A p2) = 
    defer (max_eliminator (scoring v)) A (p1 @ p2))))" 
    using reinforcement_defer_def by blast
  have emp: "\<forall>A p. elect (max_eliminator (scoring v)) A p = {}" 
    using max_elim_non_electing by simp
  have "defer (max_eliminator (scoring v)) A p = 
      elect (elector((max_eliminator (scoring v)))) A p" 
    by (simp add: reinforcement_elect_def)
  then show "reinforcement_complete ((max_eliminator (scoring v)) \<triangleright> elect_module)" 
    unfolding reinforcement_elect_def 
    using elect_defer 1 emp 
    by (simp add: reinforcement_complete_def) 
  qed


lemma scoring_module_rein:
  shows "reinforcement_complete (elector(max_eliminator (scoring v)))" 
proof-
  have 0:"\<forall>A p. elect (max_eliminator (scoring v)) A p = {}" by simp
  have "\<forall>A p. well_formed A ((max_eliminator (scoring v)) A p)" by auto
  then show ?thesis using elector_reinforcement 0 by blast
qed


end
