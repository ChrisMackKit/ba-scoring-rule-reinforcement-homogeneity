theory Scoring_Module
  imports "Component_Types/Electoral_Module" 
          "Component_Types/Evaluation_Function"
          "Component_Types/Elimination_Module"
(* Condorcet_Rule*)
begin

type_synonym Vector = "(nat) list"
type_synonym 'a Vector_A = "'a set \<Rightarrow> (nat) list"

(*Punkte abhängig von Rang geben. Beim Aufruf wird card{}-1 genommen, da above r x = {x} für Rang 1*)
primrec scoring_points :: "nat \<Rightarrow> Vector \<Rightarrow> nat" where
scoring_points_0: "scoring_points 0 v = hd v" |
scoring_points_Suc: "scoring_points (Suc n) v  = scoring_points n (tl v)"

fun scoring4:: "'a Vector_A \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> nat" where
"scoring4 v x A [] vs = 0" | 
"scoring4 v x A p vs = (scoring4 v x A (tl p) vs) + (scoring_points ((rank (hd p) x)-1) (v A))"


(*klarer*)
fun scoring:: "'a Vector_A \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> nat" where
"scoring v x A p vs = sum_list (map (\<lambda>s. (scoring_points ((rank s x) -1) (v A))) p)"

end
