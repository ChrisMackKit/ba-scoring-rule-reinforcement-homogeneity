section \<open>Preference Vectors\<close>

theory Vectors
  imports Preference_Relation Profile
begin


subsection \<open>Definition\<close>


type_synonym 'a pair_candid_points = "'a * nat"
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

lemma length_limit_range: "length (limit_range_vectors A p rs) = length rs" sorry 

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

lemma limit_presv_card:
  assumes
    "(card v = card S) \<and> (\<forall>x\<in>S. in_vector v x)" and
      "A \<subseteq> S"
    shows "(card (limit_pairs A v) = card A) \<and> (\<forall>x\<in>A. in_vector (limit_pairs A v) x)" 
proof-
  have 01:"(\<forall>x\<in>A. in_vector v x)" using assms
    by blast 
  have 02:"\<forall>x\<in>A. in_vector v x \<Longrightarrow> \<forall>x\<in>A. in_vector (limit_pairs A v) x" by auto
  have 0:"\<forall>x\<in>A. in_vector (limit_pairs A v) x" using assms 01 02 by simp

(*Da alle x aus A in limit v sind, ist limit v min. so groß wie A
"limit_pairs A v = {(a, b) \<in> v. a \<in> A}"

"in_vector2 v x = (card{(a, b) \<in> v. x = a} = 1)""
*)

  have "in_vector v x \<Longrightarrow> v \<noteq> {}" using in_vector.simps by auto
  have "card ({1, 2, 3}::nat set) > 2" using card_def by simp

   have 111: "\<forall>x\<in>A. in_vector (limit_pairs A v) x \<Longrightarrow> card (limit_pairs A v) \<ge> card A"  
    sorry 
  have 11: "card (limit_pairs A v) \<ge> card A" using assms 0 111 sorry (*by simp*)
(*da jedes Element nur ein mal in v ist (card s = card v und alle x aus S in v)
ist auch nur jedes Element 1 mal in limit v*)
  have 12: "card (limit_pairs A v) \<le> card A" using assms sorry
  have 1:"(card (limit_pairs A v) = card A)" using assms 11 12 by simp
  show ?thesis using 0 1 by simp
qed

value "card ({(a::'a), (b::'a)}::'a set) > 0"

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
  (*proof-
    have "vector_pair S vs" using vectors by simp 
    then have 1:"(\<forall>i::nat. i < length (map (limit_pairs A) vs) \<longrightarrow> 
        card ((map (limit_pairs A) vs)!i) = card A)" using length_map nth_map limit_presv_card
      by (metis subset vector_pair_def) 

(*fun limit_pairs :: "'a set \<Rightarrow> 'a Pair_Vector \<Rightarrow> 'a Pair_Vector" where
  "limit_pairs A v = {(a, b) \<in> v. a \<in> A}"*)
(* length (map (limit_pairs A) vs) = length vs ? *)
    have length:"length (map (limit_pairs A) vs) = length vs"
      using length_map by blast 
    have 0: "(\<forall>i::nat. i < length vs \<longrightarrow>  
    (\<forall>x\<in>A. in_vector (vs!i) x))" using assms
      by (meson subsetD vector_pair_def) 
    have "\<forall>x\<in>A. in_vector v x \<Longrightarrow> \<forall>x\<in>A. in_vector (limit_pairs A v) x" sorry
    then have 2: "(\<forall>i::nat. i < length (map (limit_pairs A) vs) \<longrightarrow>  
    (\<forall>x\<in>A. in_vector ((map (limit_pairs A) vs)!i) x))" using 0 length sorry
    then show ?thesis          
      using 1 vector_pair_def by blast
  qed*)
qed


lemma limit_pair_vectors_presv_size:
  assumes f_prof: "finite_profile S p" and
          subset:  "A \<subseteq> S" and
          f_vec: "finite_pair_vectors A vs"
  shows "length vs = length (map (limit_pairs A) vs)"
  by simp

end