theory Scoring_Module
  imports "Component_Types/Electoral_Module" 
          "Component_Types/Evaluation_Function"
          "Component_Types/Elimination_Module"
(* Condorcet_Rule*)
begin

type_synonym Vector = "(nat) list"
type_synonym 'a Vector_A = "'a set \<Rightarrow> (nat) list"


primrec scoring_points :: "nat \<Rightarrow> Vector \<Rightarrow> nat" where
scoring_points_0: "scoring_points 0 v = hd v" |
scoring_points_Suc: "scoring_points (Suc n) v  = scoring_points n (tl v)"

fun scoring:: "'a Vector_A \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> nat" where
"scoring v x A [] = 0" | 
"scoring v x A p = (scoring v x A (tl p)) + (scoring_points ((rank (hd p) x)-1) (v A))"

end
