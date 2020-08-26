theory Bool_Fold imports "HOL-IMP.Fold" begin

notation Map.empty ("empty")

text \<open>
\exercise
Strengthen and re-prove the congruence rules for conditional semantic equivalence
to take the value of boolean expressions into account in the \texttt{IF} and
\texttt{WHILE} cases. As a reminder, the weaker rules are:

@{thm [display] equiv_up_to_if_weak}

@{thm [display] equiv_up_to_while_weak}

Find a formulation that takes @{text b} into account for equivalences about @{term c} or @{term d}.
\<close>

lemma equiv_up_to_if_lemma:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "(\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c'"
  assumes d: "(\<lambda>s. P s \<and> (\<not> bval b s)) \<Turnstile> d \<sim> d'"
  assumes H: "(IF b THEN c ELSE d, s) \<Rightarrow> s'" "P s"
  shows "(IF b' THEN c' ELSE d', s) \<Rightarrow> s'"
proof (insert H(1), elim IfE)
  assume H': "(c, s) \<Rightarrow> s'" "bval b s"
  from b H(2) H'(2) have "bval b' s" by (simp add: bequiv_up_to_subst)
  moreover from c H' H(2) have "(c', s) \<Rightarrow> s'" by (simp add: equiv_up_toD1)
  ultimately show ?thesis by auto
next
  assume H': "(d, s) \<Rightarrow> s'" "\<not>bval b s"
  from b H(2) H'(2) have "\<not>bval b' s" by (simp add: bequiv_up_to_subst)
  moreover from d H' H(2) have "(d', s) \<Rightarrow> s'" by (simp add: equiv_up_toD1)
  ultimately show ?thesis by auto
qed

lemma equiv_up_to_if:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "(\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c'"
  assumes d: "(\<lambda>s. P s \<and> (\<not> bval b s)) \<Turnstile> d \<sim> d'"
  shows "P \<Turnstile> IF b THEN c ELSE d \<sim> IF b' THEN c' ELSE d'"
proof (clarsimp simp add: equiv_up_to_def)
  fix s s'
  assume H: "P s"
  show "(IF b THEN c ELSE d, s) \<Rightarrow> s' = (IF b' THEN c' ELSE d', s) \<Rightarrow> s'"
  proof
    assume "(IF b THEN c ELSE d, s) \<Rightarrow> s'"
    with b c d H show "(IF b' THEN c' ELSE d', s) \<Rightarrow> s'" by (simp add: equiv_up_to_if_lemma)
  next
    from b have b': "P \<Turnstile> b' <\<sim>> b" by (simp add: bequiv_up_to_sym)
    from b c have c': "(\<lambda>s. P s \<and> bval b' s) \<Turnstile> c' \<sim> c"
      by (auto elim: equiv_up_to_weaken simp add: equiv_up_to_sym bequiv_up_to_def)
    from b d have d': "(\<lambda>s. P s \<and> \<not>bval b' s) \<Turnstile> d' \<sim> d"
      by (auto elim: equiv_up_to_weaken simp add: equiv_up_to_sym bequiv_up_to_def)
    assume "(IF b' THEN c' ELSE d', s) \<Rightarrow> s'"
    with b' c' d' H show "(IF b THEN c ELSE d, s) \<Rightarrow> s'" by (simp add: equiv_up_to_if_lemma)
  qed
qed

lemma equiv_up_to_while_lemma:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "(\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c'"
  assumes I: "\<And>s s'. \<lbrakk>(c, s) \<Rightarrow> s'; P s; bval b s\<rbrakk> \<Longrightarrow> P s'"
  assumes H: "(WHILE b DO c, s) \<Rightarrow> s'" "P s"
  shows "(WHILE b' DO c', s) \<Rightarrow> s'"
proof (insert H, induct "WHILE b DO c" s s' rule: big_step_induct)
  case (WhileFalse s)
  with b show ?case by (auto simp add: bequiv_up_to_def)
next
  case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
  from c WhileTrue(1, 2, 6) have Hc: "(c', s\<^sub>1) \<Rightarrow> s\<^sub>2" by (auto simp add: equiv_up_toD1)
  moreover from I WhileTrue(1, 2, 5, 6) have Hw: "(WHILE b' DO c', s\<^sub>2) \<Rightarrow> s\<^sub>3" by auto
  moreover from b WhileTrue(1, 6) have "bval b' s\<^sub>1" by (auto simp add: bequiv_up_to_def)
  ultimately show ?case by auto
qed

lemma equiv_up_to_while:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "(\<lambda>s. P s \<and> bval b s) \<Turnstile> c \<sim> c'"
  assumes I: "\<And>s s'. \<lbrakk>(c, s) \<Rightarrow> s'; P s; bval b s\<rbrakk> \<Longrightarrow> P s'"
  shows "P \<Turnstile> WHILE b DO c \<sim> WHILE b' DO c'"
proof (clarsimp simp add: equiv_up_to_def)
  fix s s'
  assume H: "P s"
  show "(WHILE b DO c, s) \<Rightarrow> s' = (WHILE b' DO c', s) \<Rightarrow> s'"
  proof
    assume "(WHILE b DO c, s) \<Rightarrow> s'"
    with b c I H show "(WHILE b' DO c', s) \<Rightarrow> s'" by (simp add: equiv_up_to_while_lemma)
  next
    from b have b': "P \<Turnstile> b' <\<sim>> b" by (simp add: bequiv_up_to_sym)
    from b c have c': "(\<lambda>s. P s \<and> bval b' s) \<Turnstile> c' \<sim> c"
      by (auto elim: equiv_up_to_weaken simp add: equiv_up_to_sym bequiv_up_to_def)
    from b c I have I': "\<And>s s'. \<lbrakk>(c', s) \<Rightarrow> s'; P s; bval b' s\<rbrakk> \<Longrightarrow> P s'"
      by (auto simp add: bequiv_up_to_def equiv_up_to_def)
    assume "(WHILE b' DO c', s) \<Rightarrow> s'"
    with b' c' I' H show "(WHILE b DO c, s) \<Rightarrow> s'" by (simp add: equiv_up_to_while_lemma)
  qed
qed

text \<open>
\endexercise

\exercise
Extend constant folding with analysing boolean expressions
and eliminate dead \texttt{IF} branches as well as loops whose body is
never executed. Use the contents of theory @{theory "HOL-IMP.Fold"} as a blueprint.
\<close>

lemma equiv_up_to_pre_skip [intro!]: "P \<Turnstile> SKIP;; c \<sim> c"
proof (intro equiv_up_toI)
  fix s s'
  show "(SKIP;; c, s) \<Rightarrow> s' = (c, s) \<Rightarrow> s'" by auto
qed

lemma equiv_up_to_post_skip [intro!]: "P \<Turnstile> c;; SKIP \<sim> c"
proof (intro equiv_up_toI)
  fix s s'
  show "(c;; SKIP, s) \<Rightarrow> s' = (c, s) \<Rightarrow> s'" by auto
qed

fun bfold :: "bexp \<Rightarrow> tab \<Rightarrow> bexp"  where
  "bfold (Bc v) t = Bc v" |
  "bfold (Not b) t = (case bfold b t of
    Bc v \<Rightarrow> Bc (\<not>v) |
    b' \<Rightarrow> Not b')" |
  "bfold (And b\<^sub>1 b\<^sub>2) t = (case (bfold b\<^sub>1 t, bfold b\<^sub>2 t) of
    (Bc v\<^sub>1, b\<^sub>2') \<Rightarrow> (if v\<^sub>1 then b\<^sub>2' else (Bc False)) |
    (b\<^sub>1', Bc v\<^sub>2) \<Rightarrow> (if v\<^sub>2 then b\<^sub>1' else (Bc False)) |
    (b\<^sub>1', b\<^sub>2') \<Rightarrow> And b\<^sub>1' b\<^sub>2')" |
  "bfold (Less a\<^sub>1 a\<^sub>2) t = (case (afold a\<^sub>1 t, afold a\<^sub>2 t) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> Bc (n\<^sub>1 < n\<^sub>2) |
    (a\<^sub>1', a\<^sub>2') \<Rightarrow> Less a\<^sub>1' a\<^sub>2')"

lemma bequiv_up_to_not: "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> Not b <\<sim>> Not b'"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_not_bc: "P \<Turnstile> b <\<sim>> Bc v \<Longrightarrow> P \<Turnstile> Not b <\<sim>> Bc (\<not>v)"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_and: "\<lbrakk>P \<Turnstile> b\<^sub>1 <\<sim>> b\<^sub>1'; P \<Turnstile> b\<^sub>2 <\<sim>> b\<^sub>2'\<rbrakk> \<Longrightarrow> P \<Turnstile> (And b\<^sub>1 b\<^sub>2) <\<sim>> (And b\<^sub>1' b\<^sub>2')"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_and_True1: "\<lbrakk>P \<Turnstile> b\<^sub>1 <\<sim>> Bc True; P \<Turnstile> b\<^sub>2 <\<sim>> b\<^sub>2'\<rbrakk> \<Longrightarrow> P \<Turnstile> (And b\<^sub>1 b\<^sub>2) <\<sim>> b\<^sub>2'"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_and_True2: "\<lbrakk>P \<Turnstile> b\<^sub>1 <\<sim>> b\<^sub>1'; P \<Turnstile> b\<^sub>2 <\<sim>> Bc True\<rbrakk> \<Longrightarrow> P \<Turnstile> (And b\<^sub>1 b\<^sub>2) <\<sim>> b\<^sub>1'"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_and_False1: "\<lbrakk>P \<Turnstile> b\<^sub>1 <\<sim>> Bc False\<rbrakk> \<Longrightarrow> P \<Turnstile> (And b\<^sub>1 b\<^sub>2) <\<sim>> Bc False"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_and_False2: "\<lbrakk>P \<Turnstile> b\<^sub>2 <\<sim>> Bc False\<rbrakk> \<Longrightarrow> P \<Turnstile> (And b\<^sub>1 b\<^sub>2) <\<sim>> Bc False"
  by (simp add: bequiv_up_to_def)

lemma bequiv_up_to_less_n: "P \<Turnstile> (Less (N n\<^sub>1) (N n\<^sub>2)) <\<sim>> Bc (n\<^sub>1 < n\<^sub>2)"
  by (simp add: bequiv_up_to_def)

lemma afold_less: "\<lbrakk>afold a\<^sub>1 t = a\<^sub>1'; afold a\<^sub>2 t = a\<^sub>2'\<rbrakk> \<Longrightarrow>
  approx t \<Turnstile> Less a\<^sub>1 a\<^sub>2 <\<sim>> Less a\<^sub>1' a\<^sub>2'"
  by (auto simp add: bequiv_up_to_def)

lemma bfold_equiv [intro!]: "approx t \<Turnstile> b <\<sim>> bfold b t"
proof (induct b)
case (Bc x)
  then show ?case by auto
next
  case (Not b)
  then show ?case
    by (auto split: bexp.split intro: bequiv_up_to_not bequiv_up_to_not_bc)
next
  case (And b1 b2)
  then show ?case
    by (auto split: bexp.split
        intro: bequiv_up_to_and
        bequiv_up_to_and_True1
        bequiv_up_to_and_True2
        bequiv_up_to_and_False1
        bequiv_up_to_and_False2)
next
  case (Less x1a x2a)
  then show ?case
    by (auto simp add: afold_less split: aexp.split intro: bequiv_up_to_less_n)
      (simp add: aval_afold_N bequiv_up_to_def)
qed

theorem bval_bfold_N:
assumes "approx t s"
shows "bfold b t = Bc v \<Longrightarrow> bval b s = v"
  by (metis assms bval.simps(1) bfold_equiv bequiv_up_to_def)

(*note that we do not fold skips*)
primrec fold' :: "com \<Rightarrow> tab \<Rightarrow> com" where
  "fold' SKIP _ = SKIP" |
  "fold' (x ::= a) t = (x ::= afold a t)" |
  "fold' (c\<^sub>1;; c\<^sub>2) t = (fold' c\<^sub>1 t;; fold' c\<^sub>2 (defs c\<^sub>1 t))" |
  "fold' (IF b THEN c\<^sub>1 ELSE c\<^sub>2) t = (case bfold b t of
    Bc v \<Rightarrow> (if v then fold' c\<^sub>1 t else fold' c\<^sub>2 t) |
    b' \<Rightarrow> IF b' THEN fold' c\<^sub>1 t ELSE fold' c\<^sub>2 t)" |
  "fold' (WHILE b DO c) t = (case bfold b t of
    Bc v \<Rightarrow> (if v then (WHILE bfold b (t |` (-lvars c)) DO fold' c (t |` (-lvars c))) else SKIP) |
    _ \<Rightarrow> WHILE bfold b (t |` (-lvars c)) DO fold' c (t |` (-lvars c)))"

text \<open>
  Hint: you will need to make use of stronger congruence rules
        for conditional semantic equivalence.
\<close>

lemma bfold_if_True: "bfold b t = Bc True \<Longrightarrow> approx t \<Turnstile> IF b THEN c1 ELSE c2 \<sim> c1"
  by (insert bfold_equiv [of t b], auto simp add: bequiv_up_to_def)

lemma bfold_if_False: "bfold b t = Bc False \<Longrightarrow> approx t \<Turnstile> IF b THEN c1 ELSE c2 \<sim> c2"
  by (insert bfold_equiv [of t b], auto simp add: bequiv_up_to_def)

lemma bfold_while_False: "bfold b t = Bc False \<Longrightarrow> approx t \<Turnstile> WHILE b DO c1 \<sim> SKIP"
  by (insert bfold_equiv [of t b], auto simp add: bequiv_up_to_def)

lemma fold'_equiv: "approx t \<Turnstile> c \<sim> fold' c t"
proof (induct c arbitrary: t)
  case SKIP
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by (simp add: equiv_up_to_def)
next
  case (Seq c1 c2)
  then show ?case
    by (auto intro!: equiv_up_to_seq big_step_pres_approx)
next
  case (If x1 c1 c2)
  have "approx t \<Turnstile> x1 <\<sim>> bfold x1 t" by auto
  with If show ?case
    by (auto split: bexp.split intro: equiv_up_to_if_weak)
    (auto simp add: equiv_up_to_trans
      dest: bfold_if_True [of x1 t c1 c2]
       bfold_if_False [of x1 t c1 c2])
next
  case (While x1 c)
  moreover let ?tr = "t |` (-lvars c)"
  have H1: "approx ?tr \<Turnstile> x1 <\<sim>> bfold x1 ?tr" by auto
  moreover have H2: "\<And>s s'. \<lbrakk>(c, s) \<Rightarrow> s'; approx ?tr s; bval x1 s\<rbrakk> \<Longrightarrow> approx ?tr s'"
    by (auto intro: big_step_pres_approx_restrict)
  ultimately have "approx ?tr \<Turnstile>
         WHILE x1 DO c \<sim> WHILE bfold x1 ?tr DO fold' c ?tr"
    by (auto intro!: equiv_up_to_while_weak)
  with While have Hweak: "approx t \<Turnstile> WHILE x1 DO c \<sim> WHILE bfold x1 ?tr DO fold' c ?tr"
    by (auto intro: equiv_up_to_weaken approx_map_le)
  show ?case
    by (auto simp add: bval_bfold_N intro: Hweak split: bexp.split)
qed

theorem constant_folding_equiv': "fold' c empty \<sim> c"
  using fold'_equiv [of empty c]
  by (simp add: equiv_up_to_True)

text \<open> \endexercise \<close>

end

