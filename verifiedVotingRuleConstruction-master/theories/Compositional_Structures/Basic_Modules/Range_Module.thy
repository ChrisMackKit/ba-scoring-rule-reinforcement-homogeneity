theory Range_Module
  imports "Component_Types/Electoral_Module" 
          "Component_Types/Evaluation_Function"
          "Component_Types/Elimination_Module"

begin

fun score :: "'a \<Rightarrow> 'a Pair_Vector \<Rightarrow> nat" where
"score x v = \<Sum>(snd`{(a,b)\<in>v. a = x})"


fun range_score :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> nat" where
"range_score x A p [] = 0" |
"range_score x A p vs =  score x (hd vs) + range_score x A p (tl vs)"

definition range_scoring :: "'a Electoral_Module" where
  "range_scoring A p vs = max_eliminator range_score A p vs"



(*Checks if all points are in range*)
fun cap_max ::"'a pair_candid_points \<Rightarrow> nat \<Rightarrow> 'a pair_candid_points" where
"cap_max s n = (if (snd s > n) then ((fst s),n) else s)"

fun cap_min ::"'a pair_candid_points \<Rightarrow> nat \<Rightarrow> 'a pair_candid_points" where
"cap_min s n = (if (snd s < n) then ((fst s),n) else s)"

fun cap_max_set :: "'a Pair_Vector \<Rightarrow> nat \<Rightarrow> 'a Pair_Vector" where
"cap_max_set vs n = (\<lambda>x. cap_max x n)` vs"

fun cap_min_set :: "'a Pair_Vector \<Rightarrow> nat \<Rightarrow> 'a Pair_Vector" where
"cap_min_set vs n = (\<lambda>x. cap_min x n)` vs"

fun range_change_max :: "'a Pair_Vectors \<Rightarrow> nat \<Rightarrow> 'a Pair_Vectors" where
"range_change_max [] n = []" |
"range_change_max vs n =  cap_max_set (hd vs) n # range_change_max (tl vs) n"

fun range_change_min :: "'a Pair_Vectors \<Rightarrow> nat \<Rightarrow> 'a Pair_Vectors" where
"range_change_min [] n = []" |
"range_change_min vs n =  cap_min_set (hd vs) n # range_change_min (tl vs) n"

fun approval_check :: "'a Pair_Vectors \<Rightarrow> 'a Pair_Vectors" where
"approval_check vs = range_change_max vs 1"


end                         