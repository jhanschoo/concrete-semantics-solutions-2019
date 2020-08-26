theory Induction_Demo_My
  imports Main
begin

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"

(* arbitrary ys tells us to have ys arbitrary in the IH and inductive conclusion *)
lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply auto
  done
