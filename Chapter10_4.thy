theory Chapter10_4
imports "HOL-IMP.Live_True" "HOL-IMP.Vars"
begin

lemma "(let b = Less (N 0) (V ''x''); c = ''x'' ::= V ''y'';; ''y'' ::= V ''z''
  in L (WHILE b DO c) {}) = {''x'', ''y'', ''z''}"
by eval

text \<open>That there are live variables before the loop is not weird, even though
there are no live variables after the loop; the fixpoint adds in the vars including those in
the loop that are needed in the computation of the test (vars b) to the set of live variables.
For checking termination before the first loop, pre-loop value of x from before is needed,
for check inf just after the first loop, pre-loop value of y decides, and after that value of
z is needed\<close>


text \<open>Ex 10.12 WHILE b (relying on e\<^sub>1) DO e\<^sub>1 ::= e\<^sub>2;; e\<^sub>2 ::= e\<^sub>3 ...\<close>

text\<open>
\exercise
In the context of ordinary live variable analysis, elimination of dead variables
(@{text bury}) is not idempotent (Exercise~\ref{exe:bury-not-idemp}).
Now define the textually identical function @{text bury} in the context
of true liveness analysis (theory @{theory "HOL-IMP.Live_True"})
and prove that it is idempotent.
\<close>

fun bury :: "com \<Rightarrow> vname set \<Rightarrow> com" where
"bury SKIP X = SKIP" |
"bury (x ::= a) X = (if x \<in> X then x ::= a else SKIP)" |
"bury (c\<^sub>1;; c\<^sub>2) X = (bury c\<^sub>1 (L c\<^sub>2 X);; bury c\<^sub>2 X)" |
"bury (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = IF b THEN bury c\<^sub>1 X ELSE bury c\<^sub>2 X" |
"bury (WHILE b DO c) X = WHILE b DO bury c (L (WHILE b DO c) X)"

text\<open> The following two tweaks improve proof automation: \<close>

declare L.simps(5)[simp]
lemmas L_mono2 = L_mono[unfolded mono_def]

text\<open> To show that @{const bury} is idempotent we need a key lemma: \<close>

lemma L_bury: "X \<subseteq> Y \<Longrightarrow> L (bury c Y) X = L c X"
proof (induct c arbitrary: X Y)
  case (Seq c1 c2)
  from Seq(3) have "(L c2 X) \<subseteq> (L c2 Y)" by (simp add: L_mono2)
  with Seq(1) have "L (bury c1 (L c2 Y)) (L c2 X) = L c1 (L c2 X)" by simp
  moreover from Seq(2, 3) have "L (bury c2 Y) X = L c2 X" by simp
  ultimately have "L (bury c1 (L c2 Y)) (L (bury c2 Y) X) = L c1 (L c2 X)" by simp
  then show ?case by simp
next
  case (While x1 c)
  let ?x = "\<lambda>U. vars x1 \<union> X \<union> L c U" and ?y = "\<lambda>V. vars x1 \<union> Y \<union> L c V"
  let ?xb = "\<lambda>U. vars x1 \<union> X \<union> L (bury c (lfp ?y)) U"
  have "mono ?x" and "mono ?xb" by (auto intro: mono_union_L)
  then have fpx: "?x (lfp ?x) = lfp ?x" and fpxb: "?xb (lfp ?xb) = lfp ?xb" by (auto intro!: lfp_fixpoint)
  from While(2) have x_s_y: "lfp ?x \<subseteq> lfp ?y" by (auto intro!: lfp_mono)
  with While(1) have "L (bury c (lfp ?y)) (lfp ?x) = L c (lfp ?x)" by simp
  with fpx have "?xb (lfp ?x) = lfp ?x" by simp
  then have xb_s_x: "lfp ?xb \<subseteq> lfp ?x" by (auto intro!: lfp_lowerbound)
  with x_s_y have "lfp ?xb \<subseteq> lfp ?y" by simp
  with While(1) have "L (bury c (lfp ?y)) (lfp ?xb) = L c (lfp ?xb)" by simp
  with fpxb have "?x (lfp ?xb) = lfp ?xb" by simp
  then have x_s_xb: "lfp ?x \<subseteq> lfp ?xb" by (auto intro!: lfp_lowerbound)
  with xb_s_x show ?case by simp
qed auto

text\<open> The proof is straightforward except for the case
\noquotes{@{term[source] "While b c"}} where reasoning about @{const lfp}
is required. Sledgehammer should help with the details.

Now we can prove idempotence of @{const bury}, again by induction on @{text c}:
\<close>

theorem bury_idemp: "bury (bury c X) X = bury c X"
proof (induct c arbitrary: X)
  case (Seq c1 c2)
  show ?case
  proof (simp, intro conjI)
    from Seq(2) show "bury (bury c2 X) X = bury c2 X" .
    have "bury (bury c1 (L c2 X)) (L (bury c2 X) X) = bury (bury c1 (L c2 X)) (L c2 X)" by (simp add: L_bury)
    also from Seq(1) have "\<dots> = bury c1 (L c2 X)" by simp
    finally show "bury (bury c1 (L c2 X)) (L (bury c2 X) X) = bury c1 (L c2 X)" .
  qed
next
case (While x1 c)
  let ?x = "\<lambda>Y. vars x1 \<union> X \<union> L c Y"
  let ?xb = "\<lambda>Y. vars x1 \<union> X \<union> L (bury c (lfp ?x)) Y"
  have "mono ?x" and "mono ?xb" by (simp add: mono_union_L)+
  then have fpx: "?x (lfp ?x) = lfp ?x" and fpxb: "?xb (lfp ?xb) = lfp ?xb" by (auto intro!: lfp_fixpoint)
  then have "?xb (lfp ?x) = lfp ?x" by (simp add: L_bury)
  then have xb_s_x: "lfp ?xb \<subseteq> lfp ?x" by (auto intro!: lfp_lowerbound)
  then have "L (bury c (lfp ?x)) (lfp ?xb) = L c (lfp ?xb)" by (simp add: L_bury)
  then have "?xb (lfp ?xb) = ?x (lfp ?xb)" by simp
  with fpxb have "?x (lfp ?xb) = lfp ?xb" by simp
  then have x_s_xb: "lfp ?x \<subseteq> lfp ?xb" by (auto intro!: lfp_lowerbound)
  with xb_s_x have "lfp ?x = lfp ?xb" by simp
  moreover from While have "bury (bury c (lfp ?x)) (lfp ?x) = bury c (lfp ?x)" by simp
  ultimately have "bury (bury c (lfp ?x)) (lfp ?xb) = bury c (lfp ?x)" by simp
  then show ?case by simp
qed auto
(* your definition/proof here *)

text\<open>
Due to lemma @{thm[source] L_bury}, even the @{text While} case should be easy.
\endexercise
\<close>

end

