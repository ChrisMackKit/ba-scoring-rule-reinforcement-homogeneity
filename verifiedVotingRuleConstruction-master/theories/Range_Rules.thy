theory Range_Rules
  imports Scoring_Rules
          "Compositional_Structures/Basic_Modules/Range_Module"
          "Compositional_Structures/Elect_Composition"
          "Compositional_Structures/Basic_Modules/Condorcet_Module"

(*Electoral_Module Evaluation_Function Elect_Module Elimination_Module Condorcet_Rule*)
begin


(*******Lemmas*******)

lemma range_mod_A[simp]:
  shows "electoral_module (elector(max_eliminator 
        (range_score::'a Evaluation_Function)))"
  by auto

(****************Homogeneity ****************)

(*Addieren von Profilen für scoring*)
lemma testing:
  shows "range_score x A (b @ p) vz = range_score x A p vz"
proof(induct vz)
  case Nil
  then show ?case by simp
next
  case (Cons a b)
  then show ?case by simp
qed

lemma add_range_vectors:
  shows "(range_score x A (b@p) (vs@vz) = (range_score x A b vs) + (range_score x A p vz))" 
proof(induct vs)
case Nil
  then show ?case proof-
    have "range_score x A b [] = 0" by simp
    have "range_score x A (b @ p) ([] @ vz) = range_score x A (b @ p) (vz)" by simp
    have "range_score x A (b @ p) vz = range_score x A p vz" using testing by fastforce
    then show ?thesis by simp
  qed
next
case (Cons a vz)
  then show ?case by auto
qed

lemma times_range_vector:
  shows "times (Suc(n)) vs = vs @ (times n vs)" by auto

lemma range_move_out:
  shows "range_score x A (p @ (times n p)) (vs @ (times n vs)) = 
        (range_score x A p vs) + (range_score x A (times n p) (times n vs))"
  by (metis add_range_vectors) 

lemma times_scoring:
  shows "(range_score x A (times n p) (times n vs)) = range_score x A  p vs * n"
proof(induct n)
case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (metis mult_Suc_right range_move_out times_profile) 
qed

lemma max_split_range:
  shows 
    "Max {range_score x A (b@p) (vs@vz) |x. x \<in> A} = 
      Max {(range_score x A b vs) + (range_score x A p vz) |x. x \<in> A}"
  by (metis add_range_vectors)

lemma Max_homo_add_range:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {range_score x A p vs + k |x. x\<in>A} = Max {range_score x A p vs|x. x\<in>A} + k"
proof -
  have m: "\<And>x y. max x y + k = max (x+k) (y+k)"
    by(simp add: max_def antisym add_right_mono)
  have "{range_score x A p vs + k|x. x\<in>A} = (\<lambda>y. y + k) ` {range_score x A p vs|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {range_score x A p vs|x. x\<in>A} + k"
    using assms hom_Max_commute [of "\<lambda>y. y+k" "{range_score x A p vs|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed


lemma Max_homo_mult_eval_range:
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

lemma Max_homo_mult_range:
  fixes k::nat
  assumes "finite A" and "A \<noteq> {}"
  shows "Max {range_score x A p vs * k |x. x\<in>A} = Max {range_score x A p vs|x. x\<in>A} * k" 
    using Max_homo_mult_eval_range 
proof-
  have m: "\<And>x y. max x y * k = max (x*k) (y*k)"
    by(simp add: max_def antisym add_right_mono)
  have "{range_score x A p vs * k|x. x\<in>A} = (\<lambda>y. y * k) ` {range_score x A p vs|x. x\<in>A}" by auto
  also have "Max \<dots> = Max {range_score x A p vs|x. x\<in>A} * k"
    using assms hom_Max_commute [of "\<lambda>y. y*k" "{range_score x A p vs|x. x\<in>A}", OF m, symmetric] by simp
  finally show ?thesis by simp
qed


(** Homogeneity Beweis**)
(*scoring*)
lemma for_range_goal1:
  shows "\<And>A p n x xb vs. x \<in> A \<Longrightarrow>finite A \<Longrightarrow>profile A p \<Longrightarrow> 0 < n \<Longrightarrow> xb \<in> A \<Longrightarrow>
range_score xb A p vs < Max {range_score x A p vs|x. x \<in> A} \<Longrightarrow> 
range_score xb A (concat (replicate n p)) (concat (replicate n vs)) < 
Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A}"
proof-
  fix A :: "'a set" and p :: "('a \<times> 'a) set list" and 
    n :: "nat" and x :: "'a" and xb :: "'a" and vs :: "'a Pair_Vectors"
    assume a1: "finite A"
    assume a2: "profile A p"
    assume a3: "0 < n"
    assume a4: "x \<in> A"
    have 0 :"Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
        Max {range_score x A p vs * n |x. x \<in> A}" 
      using times_scoring by (metis times.simps) 
  then have 1:  "Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
      n* Max {range_score x A p vs|x. x \<in> A}" 
  proof -
    have "\<And>A f rs n vs. infinite A \<or> A = Collect bot \<or> 
        Max {range_score (a::'a) A rs vs|a. a \<in> A} * n = Max {range_score a A rs vs * n |a. a \<in> A}"
      using Max_homo_mult_range by fastforce 
    then have f5: "\<And>f rs n vs. Max {range_score a A rs vs|a. a \<in> A} * n = 
              Max {range_score a A rs vs * n |a. a \<in> A}"
      using a4 a1 by blast
    have 
      "Max {range_score a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
      Max {range_score a A p vs * n |a. a \<in> A}"
      using "0" by blast
    then show "Max {range_score a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
          n * Max {range_score a A p vs|a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:"range_score xb A p vs < Max {range_score x A p vs|x. x \<in> A} \<Longrightarrow> 
            n* range_score xb A p vs < n* Max {range_score x A p vs|x. x \<in> A}"
    using a3 mult_less_mono2 by blast
  then have 3: "n* range_score xb A p vs < n* Max {range_score x A p vs|x. x \<in> A} \<Longrightarrow> 
    range_score xb A (concat (replicate n p)) (concat (replicate n vs))  < 
    Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A}"
    by (metis (no_types, lifting) "1" mult.commute times.simps times_scoring)
  then show "range_score xb A p vs < Max {range_score x A p vs|x. x \<in> A} \<Longrightarrow> 
    range_score xb A (concat (replicate n p)) (concat (replicate n vs))  < 
    Max {range_score x A (concat (replicate n p)) (concat (replicate n vs)) |x. x \<in> A}"
    using 2 3 by auto
qed


lemma for_range_goal2:
  shows "\<And>A p n x xa xb vs. x \<in> A \<Longrightarrow> finite A \<Longrightarrow> profile A p \<Longrightarrow> vector_pair A vs 
      \<Longrightarrow> 0 < n \<Longrightarrow> xa \<in> A \<Longrightarrow> xb \<in> A \<Longrightarrow>
       range_score xb A (concat (replicate n p)) (concat (replicate n vs)) < 
       Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} 
        \<Longrightarrow> range_score xb A p vs< Max {range_score x A p vs|x. x \<in> A}"
proof-
  fix A :: "'a set" and p :: "('a \<times> 'a) set list" 
      and n :: nat and x :: 'a and xb :: 'a and vs :: "'a Pair_Vectors"
    assume a1: "finite A"
    assume a2: "profile A p"
    assume a3: "0 < n"
    assume a4: "x \<in> A"
  have 0 :"
   Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
   Max {range_score x A p vs * n |x. x \<in> A}" 
      using times_scoring by (metis times.simps) 
  then have 1:  "Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} = 
          n* Max {range_score x A p vs|x. x \<in> A}" 
proof -
  have "\<And>A rs n vs. infinite A \<or> A = Collect bot \<or> Max {range_score (a::'a) A rs vs|a. a \<in> A} * n = 
          Max {range_score a A rs vs * n |a. a \<in> A}" 
    using Max_homo_mult_range by fastforce
    then have f5: 
      "\<And>rs n. Max {range_score a A rs vs|a. a \<in> A} * n = Max {range_score a A rs vs * n |a. a \<in> A}"
      using a4 a1 by blast
    have 
      "Max {range_score a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
      Max {range_score a A p vs * n |a. a \<in> A}"
      using "0" by blast
    then show "Max {range_score a A (concat (replicate n p)) (concat (replicate n vs))|a. a \<in> A} = 
            n * Max {range_score a A p vs|a. a \<in> A}"
      using f5 by (simp add: mult.commute)
  qed
  have 2:" n* range_score xb A p vs < n* Max {range_score x A p vs|x. x \<in> A} \<Longrightarrow> 
            range_score xb A p vs< Max {range_score x A p vs|x. x \<in> A}"
    by simp
  then have 3: "n* range_score xb A p vs < n* Max {range_score x A p vs|x. x \<in> A} \<Longrightarrow> 
     range_score xb A (concat (replicate n p)) (concat (replicate n vs)) < 
     Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A}" 
    by (metis (no_types, lifting) "1" mult.commute times.simps times_scoring)
  then show "range_score xb A (concat (replicate n p)) (concat (replicate n vs)) <  
        Max {range_score x A (concat (replicate n p)) (concat (replicate n vs))|x. x \<in> A} \<Longrightarrow> 
        range_score xb A p vs < Max {range_score x A p vs|x. x \<in> A}"
    using 2 3 by (metis (no_types, lifting) "1" mult.commute times.simps times_scoring) 
qed




 lemma range_homogeneity:
  shows "homogeneity (max_eliminator range_score)" 
  unfolding homogeneity_def
proof-
  have 0: "\<forall>A p vs. max_eliminator range_score A p vs
        = elimination_module range_score (Max {range_score x A p vs| x. x \<in> A}) (<) A p vs"
    by force
  have 1:"\<forall>A p vs. elimination_module range_score (Max {range_score x A p vs| x. x \<in> A}) (<) A p vs =
  (if (elimination_set range_score (Max {range_score x A p vs| x. x \<in> A})  (<) A p vs) \<noteq> A
        then ({}, (elimination_set range_score (Max {range_score x A p vs| x. x \<in> A})  (<) A p vs), A 
        - (elimination_set range_score (Max {range_score x A p vs| x. x \<in> A}) (<) A p vs))
        else ({},{},A))"
    using elimination_module.simps by blast
   have 2:"\<forall>A p n vs. finite_profile A p \<and> finite_pair_vectors A vs \<and> 0 < n \<longrightarrow> 
    (if (elimination_set range_score (Max {range_score x A p vs| x. x \<in> A})  (<) A p vs) \<noteq> A
    then ({}, (elimination_set range_score (Max {range_score x A p vs| x. x \<in> A})  (<) A p vs), 
    A - (elimination_set range_score (Max {range_score x A p vs| x. x \<in> A}) (<) A p vs))
    else ({},{},A)) = 
    (if (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)) \<noteq> A
    then ({}, (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p ) (Electoral_Module.times n vs)), A 
    - (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A}) 
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)))
    else ({},{},A))" 
     using 1 for_range_goal1 for_range_goal2
     by (smt (z3) Collect_cong elimination_set.simps times.simps)
  then have 3:"\<forall>A p n vs.  finite_profile A p \<and> finite_pair_vectors A vs \<and> 0 < n \<longrightarrow> 
    max_eliminator range_score A p vs = 
        (if (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)) \<noteq> A
    then ({}, (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)), A 
    - (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A}) 
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)))
    else ({},{},A))" using 0 1 by (smt (z3))
  then have "\<forall>A p n vs.  finite_profile A p \<and> finite_pair_vectors A vs \<and> 0 < n \<longrightarrow> 
    max_eliminator range_score A  (Electoral_Module.times n p) (Electoral_Module.times n vs) = 
        (if (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
      (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)) \<noteq> A
    then ({}, (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A})  
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)), A 
    - (elimination_set range_score (Max {range_score x A (Electoral_Module.times n p) 
    (Electoral_Module.times n vs)| x. x \<in> A}) 
    (<) A (Electoral_Module.times n p) (Electoral_Module.times n vs)))
    else ({},{},A))"
    by (smt (z3) "0" "1" Collect_cong)
  then have "\<forall>A p n vs.  finite_profile A p \<and> finite_pair_vectors A vs \<and> 0 < n \<longrightarrow> 
    max_eliminator range_score A (Electoral_Module.times n p) (Electoral_Module.times n vs) = 
    max_eliminator range_score A p vs"
    by (smt (z3) "3")

   then show "electoral_module (max_eliminator range_score) \<and>
        (\<forall>A p n vs. finite_profile A p \<and> finite_pair_vectors A vs \<and> 0 < n \<longrightarrow> 
        max_eliminator range_score A p vs= 
        max_eliminator range_score A (Electoral_Module.times n p) (Electoral_Module.times n vs))"
     by (smt (z3) max_elim_sound) 
     
 qed


lemma range_rules_homogeneity:
  shows "homogeneity (elector (max_eliminator range_score))" 
  using range_homogeneity elector_homogeneity by simp


(*****)

(********************reinforcement proof**********************************)

(*lemma combined_eqless_single:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A p1 vs1" and "vector_pair A p2 vs2"
  shows "eval_func x A p1 vs1 + eval_func x A p2 vs2 \<le> Max {eval_func x A p1 vs1|x. x \<in> A} + 
          Max {eval_func x A p2 vs2|x. x \<in> A}"
proof-
  have "eval_func x A p1 vs1\<in> {eval_func x A p1 vs1|x. x \<in> A}" using assms(3) by blast
  then have 0:"eval_func x A p1 vs1 \<le> Max {eval_func x A p1 vs1|x. x \<in> A}" by (simp add: assms(1))
  have "eval_func x A p2 vs2\<in> {eval_func x A p2 vs2|x. x \<in> A}" using assms(3) by blast
  then have 1:"eval_func x A p2 vs2 \<le> Max {eval_func x A p2 vs2|x. x \<in> A}" by (simp add: assms(1))
  then show ?thesis using "0" "1" add_mono sorry
qed*)

lemma combined_eqless_single_range:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "range_score x A p1 vs1 + range_score x A p2 vs2 \<le> Max {range_score x A p1 vs1|x. x \<in> A} + 
          Max {range_score x A p2 vs2|x. x \<in> A}"
proof-
  have "range_score x A p1 vs1\<in> {range_score x A p1 vs1|x. x \<in> A}" using assms(3) by blast
  then have 0:"range_score x A p1 vs1 \<le> Max {range_score x A p1 vs1|x. x \<in> A}" by (simp add: assms(1))
  have "range_score x A p2 vs2\<in> {range_score x A p2 vs2|x. x \<in> A}" using assms(3) by blast
  then have 1:"range_score x A p2 vs2\<le> Max {range_score x A p2 vs2|x. x \<in> A}" by (simp add: assms(1))
  then show ?thesis using "0" "1" add_mono by auto
qed




lemma combined_max_eqless_single_all:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2). 
    Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A} \<le> 
    Max {range_score x A p1 vs1|x. x \<in> A} + Max {range_score x A p2 vs2|x. x \<in> A}"
proof-
  have fin: "finite {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A} 
        \<in> {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast 
  have eqToMax:"\<exists>x \<in> A. range_score x A p1 vs1 + range_score x A p2 vs2 = 
        Max {range_score x A p1 vs1 + range_score x A p2 vs2 |x. x \<in> A}" using "maxInSet" by auto
  have allSmaller:"\<forall>x\<in> A. range_score x A p1 vs1 + range_score x A p2 vs2 \<le>
        Max {range_score x A p1 vs1|x. x \<in> A} + Max {range_score x A p2 vs2 |x. x \<in> A}"
    using combined_eqless_single_range
 all_not_in_conv assms(1) assms(3) assms(4) assms(5)
  proof -
  { fix aa :: 'a
    have "\<And>A a rs rsa Ps Psa. infinite A \<or> (a::'a) \<notin> A \<or> \<not> profile A rs \<or> \<not> profile A rsa 
  \<or> \<not> vector_pair A Ps \<or> \<not> vector_pair A Psa \<or> range_score a A rsa Psa + range_score a A rs Ps 
  \<le> Max {range_score a A rsa Psa |a. a \<in> A} + Max {range_score a A rs Ps |a. a \<in> A}"
      by (smt (z3) all_not_in_conv combined_eqless_single_range)
    then have "aa \<notin> A \<or> range_score aa A p1 vs1 + range_score aa A p2 vs2 
  \<le> Max {range_score a A p1 vs1 |a. a \<in> A} + Max {range_score a A p2 vs2 |a. a \<in> A}"
      using assms(1) assms(4) assms(5) assms(6) assms(7) by blast }
  then show ?thesis
    by meson
  have following:"\<exists>x \<in> A. range_score x A p1 vs1 + range_score x A p2 vs2 = 
        Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A} 
  \<Longrightarrow> \<forall>x\<in> A. range_score x A p1 vs1 + range_score x A p2 vs2\<le> 
        Max {range_score x A p1 vs1|x. x \<in> A} + Max {range_score x A p2 vs2|x. x \<in> A} 
  \<Longrightarrow> Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A} \<le> 
        Max {range_score x A p1 vs1|x. x \<in> A} + Max {range_score x A p2 vs2|x. x \<in> A}"
    by fastforce 
  qed
  then show ?thesis
    using eqToMax by fastforce
qed






lemma add_range_profiles_all:
  shows "\<forall>x \<in> (defer (max_eliminator (range_score)) A p1 vs1
      \<inter> defer (max_eliminator (range_score)) A p2 vs2).
        (range_score x A (b@p) (vs@vz) = (range_score x A b vs) + (range_score x A p vz))" 
proof(induct vs)
case Nil
then show ?case
  by (metis add_range_vectors) 
next
case (Cons a b)
  then show ?case by auto
qed



lemma combined_eqless_single_eval:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "eval x A p1 vs1 + eval x A p2 vs2 \<le> Max {eval x A p1 vs1|x. x \<in> A} + 
          Max {eval x A p2 vs2|x. x \<in> A}"
proof-
  have "eval x A p1 vs1 \<in> {eval x A p1 vs1|x. x \<in> A}" using assms(3) by blast
  then have 0:"eval x A p1 vs1 \<le> Max {eval x A p1 vs1|x. x \<in> A}" by (simp add: assms(1))
  have "eval x A p2 vs2 \<in> {eval x A p2 vs2|x. x \<in> A}" using assms(3) by blast
  then have 1:"eval x A p2 vs2 \<le> Max {eval x A p2 vs2|x. x \<in> A}" by (simp add: assms(1))
  then show ?thesis using "0" "1" add_mono assms sorry
qed

lemma combined_max_eqless_single_all_eval:
  assumes "finite A" and "A \<noteq> {}" and "x \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (eval_func)) A p1 vs1 \<inter> defer (max_eliminator (eval_func)) A p2 vs2). 
    Max {eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A} \<le> 
    Max {eval_func x A p1 vs1|x. x \<in> A} + Max {eval_func x A p2 vs2|x. x \<in> A}"
proof-
  have fin: "finite {eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A} 
        \<in> {eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast 
  have eqToMax:"\<exists>x \<in> A. eval_func x A p1 vs1 + eval_func x A p2 vs2 = 
        Max {eval_func x A p1 vs1 + eval_func x A p2 vs2 |x. x \<in> A}" using "maxInSet" by auto
  have allSmaller:"\<forall>x\<in> A. eval_func x A p1 vs1 + eval_func x A p2 vs2 \<le>
        Max {eval_func x A p1 vs1|x. x \<in> A} + Max {eval_func x A p2 vs2 |x. x \<in> A}"
    using combined_eqless_single_range
 all_not_in_conv assms(1) assms(3) assms(4) assms(5)
  proof -
    { fix aa :: 'a
    have "\<And>A a rs rsa Ps Psa. infinite A \<or> (a::'a) \<notin> A \<or> \<not> profile A rs \<or> \<not> profile A rsa 
  \<or> \<not> vector_pair A Ps \<or> \<not> vector_pair A Psa \<or> eval_func a A rsa Psa + eval_func a A rs Ps 
  \<le> Max {eval_func a A rsa Psa |a. a \<in> A} + Max {eval_func a A rs Ps |a. a \<in> A}" 
      using combined_eqless_single_eval all_not_in_conv by fastforce
      (*by (smt (z3) all_not_in_conv combined_eqless_single_range)*)
    then have "aa \<notin> A \<or> eval_func aa A p1 vs1 + eval_func aa A p2 vs2 
  \<le> Max {eval_func a A p1 vs1 |a. a \<in> A} + Max {eval_func a A p2 vs2 |a. a \<in> A}"
      using assms(1) assms(4) assms(5) assms(6) assms(7) by blast }
  then show ?thesis
    by meson
  have following:"\<exists>x \<in> A. eval_func x A p1 vs1 + eval_func x A p2 vs2 = 
        Max {eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A} 
  \<Longrightarrow> \<forall>x\<in> A. eval_func x A p1 vs1 + eval_func x A p2 vs2\<le> 
        Max {eval_func x A p1 vs1|x. x \<in> A} + Max {eval_func x A p2 vs2|x. x \<in> A} 
  \<Longrightarrow> Max {eval_func x A p1 vs1 + eval_func x A p2 vs2|x. x \<in> A} \<le> 
        Max {eval_func x A p1 vs1|x. x \<in> A} + Max {eval_func x A p2 vs2|x. x \<in> A}"
    by fastforce 
  qed
  then show ?thesis
    using eqToMax by fastforce
qed

(*lemma add_eval_profiles_all:
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
qed*)

(*
lemma add_scoring_profiles_all2:
  shows "\<forall>x. (Evaluation_Function x A (b@p) vs= 
(Evaluation_Function x A b vs) + (Evaluation_Function x A p vs))" 
proof(induct b)
case Nil
then show ?case by auto
next
case (Cons a b)
  then show ?case by auto
qed
*)




lemma max_is_defer_combined_than_in_both_all:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
          Evaluation_Function a A p1 vs1 + Evaluation_Function a A p2 vs2 \<ge> Max {Evaluation_Function x A (p1@p2) (vs1@vs2)|x. x \<in> A} \<Longrightarrow>
    \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
    a \<in> defer (max_eliminator (Evaluation_Function)) A (p1@p2) (vs1@vs2)"
proof -
  assume "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
      Evaluation_Function a A p1 vs1 + Evaluation_Function a A p2 vs2 \<ge> Max {Evaluation_Function x A (p1 @ p2) (vs1@vs2)|x. x \<in> A}"
  then have 
    "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
    Max {Evaluation_Function a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> Evaluation_Function a A (p1 @ p2) (vs1@vs2)"
    using assms (*by (metis (no_types, lifting) add_scoring_profiles_all)*) sorry (*weil add_scoring.. nicht für eval*)
  have 
    "\<forall>a\<in>defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2. 
      Max {Evaluation_Function a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> Evaluation_Function a A (p1 @ p2) (vs1@vs2) \<Longrightarrow> 
     \<forall>a\<in>defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2. 
    a \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1@vs2)"
    (*by (smt (z3) Collect_cong add_scoring_profiles_all max_is_defer_combined)*) 
proof -
  assume a1: "\<forall>a\<in>defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2. 
      Max {Evaluation_Function a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> Evaluation_Function a A (p1 @ p2) (vs1@vs2)"
  { fix aa :: 'a
    { assume "Max {Evaluation_Function a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> Evaluation_Function aa A (p1 @ p2) (vs1@vs2)"
      moreover
      { assume "aa \<notin> A"
        then have "aa \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1@vs2)\<or> 
      aa \<notin> defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2"
          by simp }
      ultimately have "aa \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1@vs2)\<or> 
      aa \<notin> defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2"
        by simp }
    then have "aa \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1@vs2) \<or> 
      aa \<notin> defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2"
      using a1 by meson }
  then show ?thesis
    by metis
qed
  then show ?thesis
    using \<open>\<forall>a\<in>defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2. 
      Max {Evaluation_Function a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> Evaluation_Function a A (p1 @ p2) (vs1@vs2)\<close> 
    by linarith 
qed


lemma max_in_both__than_in_combined_defer_all:
  assumes "finite_profile A p1" and "finite_profile A p2" and "a \<in> A" "finite A" and "A \<noteq> {}" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
        Evaluation_Function a A p1 vs1 =  Max {Evaluation_Function x A p1 vs1|x. x \<in> A} \<and> 
        Evaluation_Function a A p2 vs2 =  Max {Evaluation_Function x A p2 vs2|x. x \<in> A} \<Longrightarrow>
        \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
          a \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1@vs2)"
proof-
  have 00:
  "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
    Max {Evaluation_Function x A p1 vs1|x. x \<in> A} + Max {Evaluation_Function x A p2 vs2|x. x \<in> A} \<ge> 
      Max {Evaluation_Function x A p1 vs1 + Evaluation_Function x A p2 vs2|x. x \<in> A}" 
    using assms combined_max_eqless_single_all sorry (*weil combined.. noch für range .. gehts für eval? by fastforce*)
  have 11: 
    "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      Evaluation_Function a A p1 vs1 =  Max {Evaluation_Function x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      Evaluation_Function a A p2 vs2 =  Max {Evaluation_Function x A p2 vs2|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      Max {Evaluation_Function x A p1 vs1|x. x \<in> A} + Max {Evaluation_Function x A p2 vs2|x. x \<in> A} = Evaluation_Function a A p1 vs1 + 
          Evaluation_Function a A p2 vs2"
    by (metis (no_types, lifting)) 
  have 0:
  "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
    Evaluation_Function a A p1 vs1 =  Max {Evaluation_Function x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
    Evaluation_Function a A p2 vs2 =  Max {Evaluation_Function x A p2 vs2|x. x \<in> A} \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
    Evaluation_Function a A p1 vs1 + Evaluation_Function a A p2 vs2 \<ge> Max {Evaluation_Function x A p1 vs1 + Evaluation_Function x A p2 vs2|x. x \<in> A}" 
    using "00" "11" by (metis (no_types, lifting)) 
(*  have 1 :"\<forall>a \<in> (defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2).
    Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A} = Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
    by (smt (z3) Collect_cong add_range_vectors) *)
  have 1 :"\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
    Max {Evaluation_Function x A p1 vs1 + Evaluation_Function x A p2 vs2|x. x \<in> A} = Max {Evaluation_Function x A (p1@p2) (vs1@vs2)|x. x \<in> A}"
    using max_split_scoring sorry (*weil max_slit mit scoring nicht eval ist*)
  have 2:"\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
    Evaluation_Function a A p1 vs1=  Max {Evaluation_Function x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
        Evaluation_Function a A p2 vs2 =  Max {Evaluation_Function x A p2 vs2|x. x \<in> A} \<Longrightarrow> 
    \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
        Evaluation_Function a A p1 vs1 + Evaluation_Function a A p2 vs2\<ge> Max {Evaluation_Function x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
    using assms "1" "0" by (smt (z3))
  have 3:"\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
      Evaluation_Function a A p1 vs1 + Evaluation_Function a A p2 vs2\<ge> Max {Evaluation_Function x A (p1@p2) (vs1@vs2)|x. x \<in> A} \<Longrightarrow>
      \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1\<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      a \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1@vs2)" 
    using assms max_is_defer_combined_than_in_both_all by (metis (mono_tags, lifting)) 
  show "\<forall>a\<in>defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2.
       Evaluation_Function a A p1 vs1 = Max {Evaluation_Function x A p1 vs1 |x. x \<in> A} \<and>
       Evaluation_Function a A p2 vs2 = Max {Evaluation_Function x A p2 vs2 |x. x \<in> A} \<Longrightarrow>
    \<forall>a\<in>defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2.
       a \<in> defer (max_eliminator (Evaluation_Function)) A (p1 @ p2) (vs1 @ vs2) " 
    using assms "2" "3" by blast 
qed


lemma max_always_exists0:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<exists>a \<in> A. Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}"
proof-
  have fin: "finite {Evaluation_Function x A p vs|x. x \<in> A}" using assms(1) by simp
  have nonEmpty: "{Evaluation_Function x A p vs|x. x \<in> A}  \<noteq> {}" using assms(2) by simp
  then have maxInSet:"Max {Evaluation_Function x A p vs|x. x \<in> A} \<in> {Evaluation_Function x A p vs|x. x \<in> A}"
    using "fin" "nonEmpty" eq_Max_iff by blast
  have "Max {Evaluation_Function x A p vs|x. x \<in> A} \<in> {Evaluation_Function x A p vs|x. x \<in> A} \<Longrightarrow> 
        \<exists>a \<in> A. Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}" by auto
  then show ?thesis using maxInSet by simp
qed


lemma max_always_exists:
  assumes "finite A" and "A \<noteq> {}"
  shows "{a \<in> A. Evaluation_Function a A p vs < 
    Max {Evaluation_Function x A p vs|x. x \<in> A}} = A \<Longrightarrow> False"
proof-
    have "\<exists>a \<in> A. Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}" 
      using assms by (simp add: Range_Rules.max_always_exists0) 
    then show "{a \<in> A. Evaluation_Function a A p vs < 
    Max {Evaluation_Function x A p vs|x. x \<in> A}} = A \<Longrightarrow> False"
    using neq_iff by fastforce 
qed


lemma not_less_is_max:
  assumes "finite A"
  shows "a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      Evaluation_Function a A p vs =  Max {Evaluation_Function x A p vs|x. x \<in> A}"
proof-
  have "a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      a \<in> A" by clarify
  then have "a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      Evaluation_Function a A p vs \<in> {Evaluation_Function x A p vs|x. x \<in> A}" 
    by blast
      (*sc a p nicht größer als Max*)
  then have 0:"a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs |x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      Evaluation_Function a A p vs \<le>  Max{Evaluation_Function x A p vs|x. x \<in> A}"  
    using assms (1) by auto
      (*sc a p nicht kleiner als Max*)
  have 1:"a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      Evaluation_Function a A p vs \<ge>  Max{Evaluation_Function x A p vs|x. x \<in> A}"
    by auto
  have "a \<in> A \<Longrightarrow>\<not> Evaluation_Function a A p vs < Max {Evaluation_Function x A p vs|x. x \<in> A} \<Longrightarrow> 
      Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}" using "0" "1" by simp
  then show "a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      Evaluation_Function a A p vs =  Max {Evaluation_Function x A p vs|x. x \<in> A}"
    by simp
qed



(** from defer follows Max value **)


lemma from_defer_follows_max:
  assumes "finite A" and "A \<noteq> {}"
  shows "a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> 
            Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}"
proof-
  have "({a \<in> A. Evaluation_Function a A p vs < Max {(Evaluation_Function) x A p vs|x. x \<in> A}} \<noteq> A) = True" 
          using assms Range_Rules.max_always_exists by fastforce
        then have 0: "a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> 
      a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs)"
    by simp
  have "a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow> 
      Evaluation_Function a A p vs =  Max {Evaluation_Function x A p vs|x. x \<in> A}" 
    using assms(1) not_less_is_max by simp
  then have 1:"a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> Evaluation_Function a A p vs = 
      Max {Evaluation_Function x A p vs|x. x \<in> A}" using "0" by simp
  then show "a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> 
      Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}"
     by simp
 qed


lemma from_defer_follows_max_all:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
      a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> 
      \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}"
proof-

  have 0:"\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
        ({a \<in> A. Evaluation_Function a A p vs < Max {(Evaluation_Function) x A p vs|x. x \<in> A}} \<noteq> A) = True" 
          using assms max_always_exists by fastforce

        have "a \<in> (A - elimination_set (Evaluation_Function) (Max {(Evaluation_Function) x A p vs|x. x \<in> A}) (<) A p vs) \<Longrightarrow>
      Evaluation_Function a A p vs =  Max {Evaluation_Function x A p vs|x. x \<in> A}" 
    using assms(1) not_less_is_max by simp
  then have 1:
        "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
                a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> 
                \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> 
                defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
                Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}" using "0"
    by (metis (mono_tags, lifting) assms(1) assms(2) from_defer_follows_max)
  then show 
      "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      a \<in> defer (max_eliminator (Evaluation_Function)) A p vs \<Longrightarrow> 
  \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      Evaluation_Function a A p vs = Max {Evaluation_Function x A p vs|x. x \<in> A}" by fastforce
qed


lemma from_defer_follows_max2_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
  a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2) 
  \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      (Evaluation_Function a A p1 vs1 = Max {Evaluation_Function x A p1 vs1|x. x \<in> A})" 
  by (metis (mono_tags, lifting) IntD1 assms from_defer_follows_max_all)


lemma from_defer_follows_max3_for_all:
  assumes "finite A"  and "A \<noteq> {}"
  shows "\<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2).
   a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2) \<Longrightarrow> 
   \<forall>a \<in> (defer (max_eliminator (Evaluation_Function)) A p1 vs1 \<inter> defer (max_eliminator (Evaluation_Function)) A p2 vs2). 
      (Evaluation_Function a A p1 vs1 = Max {Evaluation_Function x A p1 vs1|x. x \<in> A}) \<and> 
      (Evaluation_Function a A p2 vs2 = Max {Evaluation_Function x A p2 vs2|x. x \<in> A})" 
  using assms from_defer_follows_max2_all
  by blast 


lemma reinforcement_defer_range_helper:
  assumes "finite A" and "A \<noteq> {}" and "a \<in> A" and "profile A p1" and "profile A p2" and 
    "vector_pair A vs1" and "vector_pair A vs2"
  shows "defer (max_eliminator range_score) A p1 vs1 \<inter> 
  defer (max_eliminator range_score) A p2 vs2 \<noteq> {} \<Longrightarrow>
  defer (max_eliminator range_score) A p1 vs1 \<inter> 
  defer (max_eliminator range_score) A p2 vs2 = 
  defer (max_eliminator range_score) A (p1 @ p2) (vs1@vs2)"
proof-

  have all:
      "\<forall>a \<in> (defer (max_eliminator range_score) A p1 vs1 \<inter> 
      defer (max_eliminator range_score) A p2 vs2).
      a \<in> defer (max_eliminator range_score) A (p1 @ p2) (vs1@vs2)"
    by (meson from_defer_follows_max3_for_all max_in_both__than_in_combined_defer_all assms)

  then have d1:"(defer (max_eliminator range_score) A p1 vs1 \<inter> 
      defer (max_eliminator range_score) A p2 vs2)
      \<subseteq> defer (max_eliminator range_score) A (p1 @ p2) (vs1@vs2)"
    using assms by blast
(***********)
  have 00:"\<forall>a \<in> (defer (max_eliminator range_score) A p1 vs1 \<inter> defer (max_eliminator range_score) A p2 vs2).
  a \<in> (defer (max_eliminator range_score) A p1 vs1\<inter> defer (max_eliminator range_score) A p2 vs2) \<Longrightarrow> 
      \<forall>a \<in> (defer (max_eliminator range_score) A p1 vs1 \<inter> defer (max_eliminator range_score) A p2 vs2). 
   (range_score a A p1 vs1= Max {range_score x A p1 vs1|x. x \<in> A}) \<and> 
      (range_score a A p2 vs2= Max {range_score x A p2 vs2|x. x \<in> A})" 
    using from_defer_follows_max3_for_all assms(1) assms(2)
    by blast 

   have 11:"range_score a A p1 vs1=  Max {range_score x A p1 vs1|x. x \<in> A} \<and> 
      range_score a A p2 vs2= Max {range_score x A p2 vs2|x. x \<in> A} \<Longrightarrow>
   \<forall>a \<in> (defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2).
      a \<in> defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)" 
    using assms max_in_both__than_in_combined_defer_all all by blast 
  have all:
    "\<forall>a \<in> (defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2).
    a \<in> defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)" using assms "00" "11"
    using all by blast (*by simp*)
  then have d1:"(defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2)
      \<subseteq> defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)"
    using assms by blast 


  have "defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2\<noteq> {} \<Longrightarrow>
    \<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)).
    a \<in> (defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2)"
proof-
(*1)*)
(*relevant für "comb_is_eq"*)
  have a_is_max_p1_p2:"\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)).
          range_score a A (p1@p2) (vs1@vs2) = Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
    using assms by (smt (z3) Collect_cong from_defer_follows_max)

  have same_as_add:"\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
      (range_score a A (p1@p2) (vs1@vs2) = (range_score a A p1 vs1) + (range_score a A p2 vs2))" 
      using add_range_vectors by fastforce


    have elem_A2:
        "\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2. a\<in>A"
      using assms(1) assms(4) defer_in_alts max_elim_sound
      using Int_iff assms(6) in_mono by auto
    have elem_A:"\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). a \<in> A" by simp

(*relevant für "1"*)
    then have "\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). range_score a A p1 vs1\<in> 
      {range_score x A p1 vs1|x. x \<in> A}" 
      using assms(3) by blast
    then have smaller_max:
          "\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). range_score a A p1 vs1 \<le> 
      Max {range_score x A p1 vs1|x. x \<in> A}" 
      using assms(1) by simp
    then have "\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). range_score a A p2 vs2 \<in> 
      {range_score x A p2 vs2|x. x \<in> A}" 
      using assms(3) "elem_A" by blast
    then have smaller_max2:"\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
      range_score a A p2 vs2 \<le>  Max {range_score x A p2 vs2|x. x \<in> A}" 
      using assms(1) by simp
(*relevant für "from_single_follows_combined"*)
    have 11:"defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2 \<noteq> {}
      \<Longrightarrow> \<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2. 
          (range_score a A p1 vs1 =  Max {range_score x A p1 vs1|x. x \<in> A}) \<and> (range_score a A p2 vs2 = 
      Max {range_score x A p2 vs2|x. x \<in> A})"
      using "00" by blast

        have elem_of:
          "\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2.
                        range_score a A p1 vs1 + range_score a A p2 vs2\<in> {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A}" 
      using same_as_add
      by (metis (mono_tags, lifting) all elem_A2 mem_Collect_eq) 

    have 001:"\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2.
        Max {range_score x A p1 vs1|x. x \<in> A} + Max {range_score x A p2 vs2|x. x \<in> A} \<ge> 
        Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A}" 
      using assms combined_max_eqless_single_all by (metis (mono_tags, lifting) )


    then have 000:
        "\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2.
         range_score a A p1 vs1 + range_score a A p2 vs2\<ge> Max {range_score x A p1 vs1 + range_score x A p2 vs2|x. x \<in> A}" 
      using assms by (metis (no_types, lifting) "11" equals0D) 

    then  have 
        "\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2. 
                  Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A} \<le> range_score a A p1 vs1 + range_score a A p2 vs2"
      by (metis (no_types, lifting) a_is_max_p1_p2 all dual_order.eq_iff same_as_add) 

    then have comb_is_eq:
          "\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2.
          Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A} = range_score a A p1 vs1 + range_score a A p2 vs2" 
      using elem_of
          proof -
            { fix aa :: 'a
              have "\<And>a. a \<notin> defer (max_eliminator (range_score)) A p1 vs1 \<inter> 
                  defer (max_eliminator (range_score)) A p2 vs2\<or> 
                  Max {range_score a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> range_score a A (p1 @ p2) (vs1@vs2)"
                using a_is_max_p1_p2 all dual_order.order_iff_strict by blast
              moreover
              {assume "aa \<in> A \<and> Max {range_score a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<le> range_score aa A (p1 @ p2) (vs1@vs2)"
                then have m1:"aa \<in> defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)"
                  by simp
            then have "Max {range_score a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} = range_score aa A (p1 @ p2) (vs1@vs2)"
              by (smt (z3) a_is_max_p1_p2)
            then have 
              "range_score aa A p1 vs1 + range_score aa A p2 vs2= Max {range_score a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} 
        \<or> aa \<notin> defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2"
              using m1 same_as_add by fastforce}

          ultimately have "range_score aa A p1 vs1 + range_score aa A p2 vs2 = 
              Max {range_score a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<or> 
             aa \<notin> defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2"
            using \<open>\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> 
                  defer (max_eliminator (range_score)) A p2 vs2. a \<in> A\<close> by blast }
        then have "\<forall>a. range_score a A p1 vs1 + range_score a A p2 vs2= 
                    Max {range_score a A (p1 @ p2) (vs1@vs2)|a. a \<in> A} \<or> 
              a \<notin> defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2"
              by satx
            then show ?thesis
              by (smt (z3))
                 qed

    have eq:"\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2.
            Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A} = range_score a A p1 vs1+ range_score a A p2 vs2 \<Longrightarrow> 
            \<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2. 
            range_score a A p1 vs1 =  Max {range_score x A p1 vs1|x. x \<in> A} \<and> range_score a A p2 vs2 = 
                  Max {range_score x A p2 vs2|x. x \<in> A} \<Longrightarrow>
            \<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2. 
            Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A} = Max {range_score x A p1 vs1|x. x \<in> A} + 
            Max {range_score x A p2 vs2|x. x \<in> A}"
      by (metis (no_types, lifting)) 

    then have "\<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2.
          (range_score a A p1 vs1 =  Max {range_score x A p1 vs1|x. x \<in> A}) \<and> 
          (range_score a A p2 vs2 =  Max {range_score x A p2 vs2|x. x \<in> A}) \<Longrightarrow>
            \<forall>a\<in>defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2.
            Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A} = range_score a A p1 vs1 + range_score a A p2 vs2" 
              using assms comb_is_eq
      by linarith 

    then have from_single_follows_combined:
        "defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2 \<noteq> {} \<Longrightarrow>
        Max {range_score x A (p1@p2) (vs1@vs2)|x. x \<in> A} = Max {range_score x A p1 vs1|x. x \<in> A} + 
        Max {range_score x A p2 vs2|x. x \<in> A}"
    using assms "11" "eq" by blast


  have 00:"defer (max_eliminator (range_score)) A p1 vs1\<inter> defer (max_eliminator (range_score)) A p2 vs2\<noteq> {} 
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
        range_score a A p1 vs1 + range_score a A p2 vs2 = Max {range_score x A p1 vs1|x. x \<in> A} + 
        Max {range_score x A p2 vs2|x. x \<in> A}"
    using a_is_max_p1_p2 from_single_follows_combined same_as_add by fastforce
        

  have 1:"defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2\<noteq> {} 
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
        (range_score a A p1 vs1 =  Max {range_score x A p1 vs1|x. x \<in> A}) \<and> 
      (range_score a A p2 vs2 =  Max {range_score x A p2 vs2|x. x \<in> A})"
    using assms "a_is_max_p1_p2" "from_single_follows_combined" "same_as_add" 
          "smaller_max" "smaller_max2" "00"
    using add.commute add_le_cancel_right le_antisym by fastforce
    

    have 3:"\<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
          range_score a A p1 vs1 =  Max {range_score x A p1 vs1|x. x \<in> A} \<Longrightarrow> 
          \<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
          range_score a A p2 vs2=  Max {range_score x A p2 vs2|x. x \<in> A} \<Longrightarrow>
          \<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)). 
          a \<in> (defer (max_eliminator (range_score)) A p1 vs1 \<inter> 
          defer (max_eliminator (range_score)) A p2 vs2)" 
      using assms sorry

          then show 
            "defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2\<noteq> {}
      \<Longrightarrow> \<forall>a \<in> (defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)).
      a \<in> (defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2)" 
            using assms "1" "3" by blast
  qed
  

  then show "defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2 \<noteq> {}
      \<Longrightarrow> defer (max_eliminator (range_score)) A p1 vs1 \<inter> defer (max_eliminator (range_score)) A p2 vs2 = 
      defer (max_eliminator (range_score)) A (p1 @ p2) (vs1@vs2)" 
    using assms "d1" by blast
qed
  

lemma reinforcement_defer_range:
  shows "reinforcement_defer (max_eliminator range_score)"
  unfolding reinforcement_defer_def 
proof-
  have 0:"electoral_module (max_eliminator range_score)" by simp
  have 1:"(\<forall>A p1 p2 vs1 vs2.
        finite_profile A p1 \<and> finite_profile A p2 \<and> finite_pair_vectors A vs1 
        \<and> finite_pair_vectors A vs2 \<longrightarrow>
        defer (max_eliminator range_score) A p1 vs1 \<inter> 
        defer (max_eliminator range_score) A p2 vs2\<noteq> {} \<longrightarrow>
        defer (max_eliminator range_score) A p1 vs1 \<inter> 
        defer (max_eliminator range_score) A p2 vs2 = 
      defer (max_eliminator range_score) A (p1 @ p2) (vs1@vs2))" 
    using  "0" Int_emptyI defer_in_alts equals0D in_mono reinforcement_defer_range_helper
    by (smt (z3))
  then show "electoral_module (max_eliminator range_score) \<and>
    (\<forall>A p1 p2 vs1 vs2.
        finite_profile A p1 \<and> finite_pair_vectors A vs1 \<and> finite_profile A p2 
        \<and> finite_pair_vectors A vs2 \<longrightarrow>
        defer (max_eliminator range_score) A p1 vs1 \<inter> 
        defer (max_eliminator range_score) A p2 vs2 \<noteq> {} \<longrightarrow>
        defer (max_eliminator range_score) A p1 vs1 \<inter> 
        defer (max_eliminator range_score) A p2 vs2 =
        defer (max_eliminator range_score) A (p1 @ p2) (vs1 @ vs2))" 
    using "0"
    by blast
qed

lemma reinforcement_range:
  shows "reinforcement (max_eliminator (range_score))"
  unfolding reinforcement_def by simp

lemma elector_reinforcement:
  shows "reinforcement (elector(max_eliminator range_score))"
proof(simp)
  have def: "reinforcement_defer (max_eliminator range_score)"
    by (simp add: reinforcement_defer_range) 
  have "reinforcement elect_module" 
    by (simp add: reinforcement_def) 
  have emp: "\<forall>A p vs. elect (max_eliminator range_score) A p vs = {}" 
    using max_elim_non_electing by simp
  have "\<forall>A p vs. elect (max_eliminator range_score) A p vs = {} \<Longrightarrow> 
        \<forall>A p vs. defer (max_eliminator range_score) A p vs = 
    elect (elector(max_eliminator range_score)) A p vs" 
      by (simp add: reinforcement_def)
    then show "reinforcement (max_eliminator range_score \<triangleright> elect_module)" 
      using emp def elect_mod_sound elector.elims reinforcement_def reinforcement_defer_def seq_comp_sound
      by (smt (z3)) 
qed



lemma range_module_rein:
  shows "reinforcement (elector(max_eliminator range_score))" 
proof-
  have 0:"\<forall>A p vs. elect (max_eliminator range_score) A p vs = {}" by simp
  have "\<forall>A p vs. well_formed A ((max_eliminator range_score) A p vs)" by auto
  then show ?thesis using elector_reinforcement reinforcement_defer_range 0 by blast
qed

end