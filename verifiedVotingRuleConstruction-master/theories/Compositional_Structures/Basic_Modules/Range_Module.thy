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

fun range_scoring :: "'a Electoral_Module" where
  "range_scoring A p vs = max_eliminator range_score A p vs"



(*Checks if all points are in range*)
fun range_check_set :: "'a Pair_Vector \<Rightarrow> nat \<Rightarrow> 'a Pair_Vector" where
"range_check_set vs n = {(a,b)\<in>vs. 0 \<le> b \<and> b \<le> n}"

fun range_check :: "'a Pair_Vectors \<Rightarrow> nat \<Rightarrow> 'a Pair_Vectors" where
"range_check [] n = []" |
"range_check vs n =  range_check_set (hd vs) n # range_check (tl vs) n"

fun approval_check :: "'a Pair_Vectors \<Rightarrow> 'a Pair_Vectors" where
"approval_check [] = []" |
"approval_check vs =  range_check_set (hd vs) 1 # approval_check (tl vs)"

end                         