theory Approval_Module
imports Range_Module

begin


fun approval_score:: "'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Pair_Vectors \<Rightarrow> nat" where
"approval_score x A p vs = range_score x A p vs"

definition approval :: "'a Electoral_Module" where
  "approval A p vs = max_eliminator approval_score A p vs"
  
end
