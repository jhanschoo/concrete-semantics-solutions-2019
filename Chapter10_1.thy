theory Chapter10_1
imports "HOL-IMP.Def_Init"
begin

text\<open>
\section*{Chapter 10}

\exercise
Define the definite initialisation analysis as two recursive functions
\<close>

fun ivars :: "com \<Rightarrow> vname set" where
  "ivars SKIP = {}" |
  "ivars (x ::= _) = {x}" |
  "ivars (c\<^sub>1;; c\<^sub>2) = ivars c\<^sub>1 \<union> ivars c\<^sub>2" |
  "ivars (IF _ THEN c\<^sub>1 ELSE c\<^sub>2) = ivars c\<^sub>1 \<inter> ivars c\<^sub>2" |
  "ivars (WHILE _ DO _) = {}"

fun ok :: "vname set \<Rightarrow> com \<Rightarrow> bool" where
  "ok A SKIP = True" |
  "ok A (x ::= a) \<longleftrightarrow> vars a \<subseteq> A" |
  "ok A (c\<^sub>1;; c\<^sub>2) \<longleftrightarrow> ok A c\<^sub>1 \<and> ok (A \<union> ivars c\<^sub>1) c\<^sub>2" |
  "ok A (IF b THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> vars b \<subseteq> A \<and> ok A c\<^sub>1 \<and> ok A c\<^sub>2" |
  "ok A (WHILE b DO c) \<longleftrightarrow> vars b \<subseteq> A \<and> ok A c"

text\<open>
such that @{const ivars} computes the set of definitely initialised variables
and @{const ok} checks that only initialised variable are accessed.
Prove
\<close>

lemma "D A c A' \<Longrightarrow> A' = A \<union> ivars c \<and> ok A c"
  by (induct A c A' rule: D.induct) auto

lemma "ok A c \<Longrightarrow> D A c (A \<union> ivars c)"
proof (induct A c rule: ok.induct)
  case (3 A c\<^sub>1 c\<^sub>2)
  then show ?case by (auto simp add: Un_assoc intro: D.intros)
next
  case (4 A b c\<^sub>1 c\<^sub>2)
  then show ?case by (auto simp add: sup_inf_distrib1 intro: D.intros)
qed (auto intro: D.intros)

text\<open>
\endexercise
\<close>

end

