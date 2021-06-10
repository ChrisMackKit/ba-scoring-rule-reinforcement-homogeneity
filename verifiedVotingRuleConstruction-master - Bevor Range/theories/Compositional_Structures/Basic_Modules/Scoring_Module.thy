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

fun scoring4:: "'a Vector_A \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> nat" where
"scoring4 v x A [] = 0" | 
"scoring4 v x A p = (scoring4 v x A (tl p)) + (scoring_points (card(above (hd p) x)-1) (v A))"

primrec sum1 :: "nat list => nat" where
"sum1 [] = 0"
| "sum1 (x#xs) = x + sum1 xs"

fun scoring:: "'a Vector_A \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> nat" where
"scoring v x A p = sum1 (map (\<lambda>s. (scoring_points (card(above s x)-1) (v A))) p)"

end
