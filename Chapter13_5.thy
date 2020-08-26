theory Chapter13_5
imports Main "HOL-Library.Lattice_Syntax"
begin

text \<open>
0:
  A1: None
  A2: None
  A3: None
  A4: None
  A5: None

1:
  A1: Odd

2:
  A2: Odd

3:
  A3: Odd

4:
  A4: Even

5:
  A2: Either

6:
  A3: Either
  A5: Either

7:
  A4: Either

8:
  No change
\<close>

text\<open>
\setcounter{exercise}{10}

\begin{exercise}
Take the Isabelle theories that define commands, big-step semantics,
annotated commands and the collecting semantics and extend them with a
nondeterministic choice construct. Start with Exercise~\ref{exe:IMP:OR}
and extend type @{text com}, then extend type @{text acom} with a
corresponding construct:
\begin{alltt}
  Or "'a acom" "'a acom" 'a     ("_ OR// _//{_}"  [60, 61, 0] 60)
\end{alltt}
Finally extend function @{text Step}. Update proofs as well.
Hint: think of @{text OR} as a nondeterministic conditional without a test.
\end{exercise}

\exercise
Prove the following lemmas in a detailed and readable style:
\<close>

lemma fixes x0 :: "'a :: order"
assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"  and  "f q \<le> q"  and  "x0 \<le> q"
shows "(f ^^ i) x0 \<le> q"
proof (induction i)
  case 0
  then show ?case by (auto simp add: assms(3))
next
  case (Suc i)
  have "(f ^^ Suc i) x0 = f ((f ^^ i) x0)" by auto
  also have "\<dots> \<le> f q" by (auto intro!: assms(1) simp add: Suc)
  also from assms(2) have "\<dots> \<le> q" .
  finally show ?case .
qed


lemma fixes x0 :: "'a :: order"
assumes "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y" and "x0 \<le> f x0"
shows "(f ^^ i) x0 \<le> (f ^^ (i+1)) x0"
proof (induction i)
case 0
  then show ?case by (auto simp add: assms(2))
next
  case (Suc i)
  have "(f ^^ Suc i) x0 = f ((f ^^ i) x0)" by auto
  also have "\<dots> \<le> f ((f ^^ (i + 1)) x0)" by (intro assms(1), rule Suc)
  also have "\<dots> = (f ^^ (Suc i + 1)) x0" by auto
  finally show ?case .
qed

text\<open>
\endexercise

\exercise% needs Lattice_Syntax
Let @{typ 'a} be a complete lattice and
let @{text "f :: 'a \<Rightarrow> 'a"} be a monotone function.
Give a readable proof that if @{text P} is a set of pre-fixpoints of @{text f}
then @{text"\<Sqinter>P"} is also a pre-fixpoint of @{text f}:
\<close>

lemma fixes P :: "'a::complete_lattice set"
assumes "mono f" and "\<forall>p \<in> P. f p \<le> p"
shows "f(\<Sqinter> P) \<le> \<Sqinter> P" (is "f ?m \<le> ?m")
proof (intro Inf_greatest)
  fix p
  assume Hp: "p \<in> P"
  then have "?m \<le> p" by (rule Inf_lower)
  with assms(1) have "f ?m \<le> f p" unfolding mono_def by simp
  also from Hp assms(2) have "f p \<le> p" by simp
  finally show "f ?m \<le> p" .
qed

text\<open>
Sledgehammer should give you a proof you can start from.
\endexercise
\<close>

end

