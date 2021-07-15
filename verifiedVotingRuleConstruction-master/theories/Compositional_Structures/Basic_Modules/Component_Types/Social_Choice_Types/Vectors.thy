section \<open>Preference Vectors\<close>

theory Vectors
  imports Preference_Relation Profile
begin


subsection \<open>Definition\<close>


type_synonym 'a pair_candid_points = "'a \<times> nat"
type_synonym 'a Pair_Vector = "('a pair_candid_points) set"
type_synonym 'a Pair_Vectors = "('a Pair_Vector) list"

type_synonym  Range_vector = "nat list"
type_synonym  Range_vector_list = "( Range_vector) list"

(*Jeder Kandidat kommt genau einmal vor*)
fun in_vector :: "'a Pair_Vector \<Rightarrow> 'a \<Rightarrow> bool" where
"in_vector v x = (\<exists>(a, _) \<in> v. x = a)"

(*
lemma testing_vector:
  assumes "finite v"
  shows " (a, b) \<in> v \<Longrightarrow> card v > 0" using assms card_0_eq by auto  

fun in_vector2 :: "'a Pair_Vector \<Rightarrow> 'a \<Rightarrow> bool" where
"in_vector2 v x = (card{\<forall>(a, b) \<in> v. x = a} = 1)"

lemma testing_vec:
  assumes "finite A" and "finite v"
  shows "\<forall>x\<in>A. x \<in> v \<Longrightarrow> card A \<le> card v" using assms
  by (meson card_mono subsetI)  


lemma testing_vec2:
  assumes "finite A" and "finite v"
  shows "\<forall>x\<in>A. (x, y) \<in> v \<Longrightarrow> card A \<le> card v" using assms
  by (metis (no_types, hide_lams) imageI old.prod.exhaust prod.inject subset_iff surj_card_le) 
*)


definition vector_pair :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> bool" where
  "vector_pair A vs \<equiv> 
(\<forall>i::nat. i < length vs \<longrightarrow> (card (vs!i) = card A) \<and> (\<forall>x\<in>A. in_vector (vs!i) x))"

(*definition total_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool"
  where "total_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r)"*)
definition range_vector :: "'a set \<Rightarrow> 'a Profile \<Rightarrow>  Range_vector_list \<Rightarrow> bool" where
"range_vector A p rv \<equiv> length rv = length p \<and> (\<forall>i::nat. i < length rv \<longrightarrow> (length(rv!i) = card A))"

abbreviation finite_range_vector :: "'a set  \<Rightarrow> 'a Profile \<Rightarrow>  Range_vector_list \<Rightarrow> bool" where
"finite_range_vector A p rv \<equiv> finite A \<and> range_vector A p rv"

fun limit_kick :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set" where
  "limit_kick A r = {a. \<not>a \<in> A \<and> (a, a) \<in> r}"

fun rank_kicked_set :: "'a set \<Rightarrow> 'a Preference_Relation \<Rightarrow> nat set" where
"rank_kicked_set A r = {rank r x | x. x \<in> (limit_kick A r) }"

fun kicked_set_to_list :: "nat set \<Rightarrow> nat \<Rightarrow> nat list" where
"kicked_set_to_list s 0 = []" |
"kicked_set_to_list s n = (Max s) # (if ((card s) = 0) then [] else kicked_set_to_list (s - {Max s}) (n-1))"

fun remove_from_range :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"remove_from_range rv 0 = tl rv" |
"remove_from_range rv n = (hd rv) # (remove_from_range (tl rv) (n-1))"

fun limit_range_vector :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"limit_range_vector [] rv = rv" |
"limit_range_vector ranks rv = limit_range_vector (tl ranks) (remove_from_range rv ((hd ranks)-1))"


fun limit_range_vectors :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> Range_vector_list \<Rightarrow> Range_vector_list" where
"limit_range_vectors A p [] = []" |
"limit_range_vectors A p rs = (limit_range_vector (kicked_set_to_list (rank_kicked_set A (hd p)) 
(card (rank_kicked_set A (hd p)))) 
(hd rs)) # limit_range_vectors A (tl p) (tl rs)"

lemma length_limit_range: "length (limit_range_vectors A p rs) = length rs" 
proof(induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  then show ?case proof-
    have 0:"length (a # rs) = length rs +1" by simp
    have "length (limit_range_vectors A p (a # rs)) = length (limit_range_vectors A p rs) + 1" sorry
    then show ?thesis
      using 0 Cons.hyps by linarith 
  qed
qed

lemma limit_range_vectors_sound:
  assumes
    profile: "finite_profile S p" and
    subset: "A \<subseteq> S" and
    vectors: "finite_range_vector S p rv"
  shows "finite_range_vector A (limit_profile A p) (limit_range_vectors A p rv)" 
proof(auto)
  show "finite A" using finite_subset subset vectors by auto  
  show "range_vector A (map (limit A) p) (limit_range_vectors A p rv)"
    unfolding range_vector_def
  proof-
    have a:"length rv = length p" using vectors range_vector_def by auto
    have b:"length (map (limit A) p) = length p" by simp
    have 0:"length (limit_range_vectors A p rv) = length (map (limit A) p)" 
      by (simp add: b a length_limit_range) 

    have 1: "(\<forall>i<length (limit_range_vectors A p rv). 
        length (limit_range_vectors A p rv ! i) = card A)" sorry
    show "length (limit_range_vectors A p rv) = length (map (limit A) p) \<and>
      (\<forall>i<length (limit_range_vectors A p rv). 
      length (limit_range_vectors A p rv ! i) = card A)"
      using 0 1 by simp
qed
qed
(**)

abbreviation finite_pair_vectors :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> bool" where
  "finite_pair_vectors A vs \<equiv> finite A \<and> vector_pair A vs"


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


fun limit_pair_vectors :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Pair_Vectors" where
"limit_pair_vectors A vs =  map (limit_pairs A) vs"

lemma limit_pair_vectors_trans:
  assumes
    "B \<subseteq> A" and
    "C \<subseteq> B" and
    "finite_pair_vectors A vs"
  shows "limit_pair_vectors C vs = limit_pair_vectors C (limit_pair_vectors B vs)" 
  using assms by auto

lemma limit_presv_card1:
  assumes
    assm1: "(\<forall>x\<in>S. in_vector v x)" and
    assm2:  "A \<subseteq> S"
    shows "(\<forall>x\<in>A. in_vector (limit_pairs A v) x)"
proof-
  have "(\<forall>x\<in>A. in_vector v x)"
    using assm1 assm2
    by blast
  hence "\<forall>x\<in>A. in_vector (limit_pairs A v) x"
    by auto
  thus "\<forall>x\<in>A. in_vector (limit_pairs A v) x"
    by simp
qed

lemma limit_presv_card2:
  assumes
    assm0: "(card v = card S)" and
    assm1: "(\<forall>x\<in>S. in_vector v x)" and
    assm2:  "A \<subseteq> S"
    shows "(card (limit_pairs A v) = card A)"
proof -
  fix x :: "'a"
  have x_in_A: "\<exists> m::nat. (x,m) \<in> (limit_pairs A v) \<Longrightarrow> x \<in> A"
    using limit_presv_card1
    by simp
  have "x \<in> A \<Longrightarrow> \<exists> m::nat. (x,m) \<in> v"
    using assm1 assm2
    by fastforce
  hence x_in_limit_pairs: "x \<in> A \<Longrightarrow> \<exists> m::nat. (x,m) \<in> (limit_pairs A v)"
    by simp
  have "{y \<in> A. \<exists> m::nat. (y,m) \<in> (limit_pairs A v)} = A"
    using x_in_A x_in_limit_pairs
    sorry
  hence "card {y \<in> A. \<exists> m::nat. (y,m) \<in> (limit_pairs A v)} = card A"
    by presburger
  thus "card (limit_pairs A v) = card A"
    sorry
qed

lemma limit_presv_card:
  assumes
    assm0: "(card v = card S)" and
    assm1: "(\<forall>x\<in>S. in_vector v x)" and
    assm2:  "A \<subseteq> S"
  shows "(\<forall>x\<in>A. in_vector (limit_pairs A v) x) \<and>
         (card (limit_pairs A v) = card A)"
  using limit_presv_card1 limit_presv_card2
        assm0 assm1 assm2
  by metis


(*hier evtl. Beweis nötig, dass card(vs!i) = A*)
lemma limit_pair_vectors_sound:
  assumes
    profile: "finite_profile S p" and
    subset: "A \<subseteq> S" and
    vectors: "finite_pair_vectors S vs"
  shows "finite_pair_vectors A (limit_pair_vectors A vs)"
proof(auto)
  show "finite A" using profile subset finite_subset by blast 
  show "vector_pair A (map (limit_pairs A) vs)" 
    using length_map nth_map limit_presv_card vector_pair_def subset profile vectors
    by (smt (verit, del_insts)) 
qed


lemma limit_pair_vectors_presv_size:
  assumes f_prof: "finite_profile S p" and
          subset:  "A \<subseteq> S" and
          f_vec: "finite_pair_vectors A vs"
  shows "length vs = length (map (limit_pairs A) vs)"
  by simp


(*************)

fun all_alternatives_in_A :: "'a set \<Rightarrow> 'a Pair_Vector \<Rightarrow> bool" where
"all_alternatives_in_A A v = (\<forall>(a, _) \<in> v. a \<in> A)"

fun every_alt_just_once :: "'a Pair_Vector \<Rightarrow> bool" where
"every_alt_just_once v = (\<forall>(a, n) \<in> v. \<forall>(b, m) \<in> (v - {(a, n)}). a \<noteq> b)"

definition vector_pair_test :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> bool" where
  "vector_pair_test A vs \<equiv> 
(\<forall>i::nat. i < length vs \<longrightarrow> all_alternatives_in_A A (vs!i) \<and> every_alt_just_once (vs!i))"

abbreviation finite_pair_vectors_test :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> bool" where
  "finite_pair_vectors_test A vs \<equiv> finite A \<and> vector_pair_test A vs"


fun limit_pairs_test :: "'a set \<Rightarrow> 'a Pair_Vector \<Rightarrow> 'a Pair_Vector" where
  "limit_pairs_test A v = {(a, b) \<in> v. a \<in> A}"

fun limit_pair_vectors_test :: "'a set \<Rightarrow> 'a Pair_Vectors \<Rightarrow> 'a Pair_Vectors" where
"limit_pair_vectors_test A vs =  map (limit_pairs A) vs"

lemma limit_presv_range_vec:
  assumes
    assm0: "all_alternatives_in_A S v" and
    assm1: "every_alt_just_once v" and
    assm2:  "A \<subseteq> S"
  shows "all_alternatives_in_A A (limit_pairs A v) \<and>
         every_alt_just_once (limit_pairs A v)"
proof-
  have " (\<forall>(a, n) \<in> v. \<forall>(b, m) \<in> (v - {(a, n)}). a \<noteq> b) \<Longrightarrow> 
 (\<forall>(a, n) \<in> (limit_pairs A v). \<forall>(b, m) \<in> ((limit_pairs A v) - {(a, n)}). a \<noteq> b)"
    by fastforce 
  then have 0:"every_alt_just_once (limit_pairs A v)" using assms by simp
  have "(\<forall>(a, _) \<in> v. a \<in> S) \<Longrightarrow>  (\<forall>(a, _) \<in> (limit_pairs A v). a \<in> A)"
    by auto 
  then have 1:"all_alternatives_in_A A (limit_pairs A v)" using assms by simp
  show ?thesis using 0 1 by simp
qed

lemma limit_pair_vectors_test_sound:
  assumes
    profile: "finite_profile S p" and
    subset: "A \<subseteq> S" and
    vectors: "finite_pair_vectors_test S vs"
  shows "finite_pair_vectors_test A (limit_pair_vectors A vs)" 
proof(auto)
  show "finite A"  using profile subset finite_subset by blast 
  show "vector_pair_test A (map (limit_pairs A) vs)"
using length_map nth_map limit_presv_range_vec
           subset vector_pair_test_def
  by (metis (mono_tags, lifting) vectors) 
        
qed
end