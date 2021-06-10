section \<open>Preference Vectors\<close>

theory Vectors
  imports Preference_Relation Profile
begin


subsection \<open>Definition\<close>


type_synonym 'a pair_candid_points = "'a * nat"
type_synonym 'a Pair_Vector = "('a pair_candid_points) set"
type_synonym 'a Pair_Vectors = "('a Pair_Vector) list"


(*Jeder Kandidat kommt genau einmal vor*)
fun in_vector :: "'a Pair_Vector \<Rightarrow> 'a \<Rightarrow> bool" where
"in_vector v x = (\<exists>(a, b) \<in> v. x = a)"

definition vector_pair :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> bool" where
  "vector_pair A p vs \<equiv> 
(\<forall>i::nat. i < length vs \<longrightarrow> (card (vs!i) = card A) \<and> (\<forall>x\<in>A. in_vector (vs!i) x))"

abbreviation finite_pair_vectors :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> bool" where
  "finite_pair_vectors A p vs \<equiv> finite A \<and> vector_pair A p vs"

fun limit_pairs :: "'a set \<Rightarrow> 'a Pair_Vector \<Rightarrow> 'a Pair_Vector" where
  "limit_pairs A v = {(a, b) \<in> v. a \<in> A}"
(*
definition lifted :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "lifted A p q a \<equiv>
    finite_profile A p \<and> finite_profile A q \<and>
      a \<in> A \<and> length p = length q \<and>
      (\<forall>i::nat.
        (i < length p \<and> \<not>Preference_Relation.lifted A (p!i) (q!i) a) \<longrightarrow>
          (p!i) = (q!i)) \<and>
      (\<exists>i::nat. i < length p \<and> Preference_Relation.lifted A (p!i) (q!i) a)"*)

lemma lifted_finite_vectors:
  shows "finite_pair_vectors A p vs \<Longrightarrow> lifted A p q a \<Longrightarrow> finite_pair_vectors A q vs" 
    unfolding vector_pair_def 
    by (metis Profile.lifted_def)

fun limit_pair_vectors :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Pair_Vectors" where
"limit_pair_vectors A vs =  map (limit_pairs A) vs"

lemma limit_pair_vectors_trans:
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "finite_pair_vectors A p vs"
  shows "limit_pair_vectors C vs = limit_pair_vectors C (limit_pair_vectors B vs)" 
  using assms by auto

lemma limit_pair_vectors_trans_test_list:
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "finite_pair_vectors2 A p vs"
  shows "limit_pair_vectors2 C vs = limit_pair_vectors2 C (limit_pair_vectors2 B vs)" 
  using assms sorry



lemma limit_pair_vectors_sound:
  assumes
    profile: "finite_profile S p" and
    subset: "A \<subseteq> S" and
    vectors: "finite_pair_vectors S p vs"
  shows "finite_pair_vectors A p (limit_pair_vectors A vs)"
proof(auto)
  show "finite A" using profile subset finite_subset by blast 
(*(length vs = length p) \<and> 
(\<forall>i::nat. i < length vs \<longrightarrow> (card (vs!i) = card A) \<and> (\<forall>x\<in>A. in_vector (vs!i) x))*)
  show "vector_pair A p (map (limit_pairs A) vs)" 
  proof-
    (*have 0:"length (map (limit_pairs A) vs) = length p"     
     by (metis vectors length_map vector_pair_def) *)

    have 1:"(\<forall>i::nat. i < length (map (limit_pairs A) vs) \<longrightarrow> 
    (card ((map (limit_pairs A) vs)!i) = card A) \<and> 
    (\<forall>x\<in>A. in_vector ((map (limit_pairs A) vs)!i) x))" 
      proof-
        have 00:"(\<forall>i::nat. i < length (map (limit_pairs A) vs) \<longrightarrow> 
              card ((map (limit_pairs A) vs)!i) = card A)" 

    using length_map  nth_map vectors vector_pair_def 
           vector_pair_def subset infinite_super sorry

        have 11:"(\<forall>i::nat. i < length (map (limit_pairs A) vs) \<longrightarrow> 
              (\<forall>x\<in>A. in_vector ((map (limit_pairs A) vs)!i) x))" sorry
        show ?thesis using 00 11 by simp
      qed
    show ?thesis
      using 1 (*0*) vector_pair_def by blast
  qed
qed


lemma limit_pair_vectors_presv_size:
  assumes f_prof: "finite_profile S p" and
          subset:  "A \<subseteq> S" and
          f_vec: "finite_pair_vectors A p vs"
  shows "length vs = length (map (limit_pairs A) vs)"
  by simp

end