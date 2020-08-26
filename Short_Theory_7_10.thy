theory Short_Theory_7_10
  imports "HOL-IMP.BExp" "HOL-IMP.Star"
begin

datatype com =
  SKIP
  | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
  | Seq    com  com         ("_;;/ _"  [60, 61] 60)
  | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
  | THROW
  | Try    com  com         ("(TRY _/ CATCH _)" [60, 61] 61)

inductive
  big_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
  where
    Skip: "(SKIP, s) \<Rightarrow> (SKIP, s)" |
    Assign: "(x ::= a, s) \<Rightarrow> (SKIP, s(x := aval a s))" |
    SeqSkip: "\<lbrakk>(c\<^sub>1, s\<^sub>1) \<Rightarrow> (SKIP, s\<^sub>2); (c\<^sub>2, s\<^sub>2) \<Rightarrow> (x, s\<^sub>3)\<rbrakk> \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s\<^sub>1) \<Rightarrow> (x, s\<^sub>3)" |
    SeqThrow: "\<lbrakk>(c\<^sub>1, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2)\<rbrakk> \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2)" |
    IfTrue: "\<lbrakk>bval b s; (c\<^sub>1, s) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> (x, t)" |
    IfFalse: "\<lbrakk>\<not>bval b s;  (c\<^sub>2, s) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> (x, t)" |
    WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> (SKIP, s)" |
    WhileTrueSkip: "\<lbrakk>bval b s\<^sub>1; (c, s\<^sub>1) \<Rightarrow> (SKIP, s\<^sub>2); (WHILE b DO c, s\<^sub>2) \<Rightarrow> (x, s\<^sub>3)\<rbrakk>
      \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> (x, s\<^sub>3)" |
    WhileTrueThrow: "\<lbrakk>bval b s\<^sub>1; (c, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2)\<rbrakk>
      \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2)" |
    Throw: "(THROW, s) \<Rightarrow> (THROW, s)" |
    TrySkip: "(c\<^sub>1, s) \<Rightarrow> (SKIP, t) \<Longrightarrow> (TRY c\<^sub>1 CATCH c\<^sub>2, s) \<Rightarrow> (SKIP, t)" |
    TryThrow: "\<lbrakk>(c\<^sub>1, s\<^sub>1) \<Rightarrow> (THROW, s\<^sub>2); (c\<^sub>2, s\<^sub>2) \<Rightarrow> (x, s\<^sub>3)\<rbrakk> \<Longrightarrow> (TRY c\<^sub>1 CATCH c\<^sub>2, s\<^sub>1) \<Rightarrow> (x, s\<^sub>3)"

lemmas big_step_induct = big_step.induct[split_format(complete)]
declare big_step.intros [intro]

lemma BS_SkipE [elim!]: "\<lbrakk>(SKIP, s) \<Rightarrow> (x, t); \<lbrakk>x = SKIP; t = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_AssignE [elim!]: "\<lbrakk>
  (y ::= a, s) \<Rightarrow> (x, t);
  \<lbrakk>x = SKIP; t = s(y := aval a s)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_SeqE [elim!]: "\<lbrakk>
  (c\<^sub>1;; c\<^sub>2, s) \<Rightarrow> (x, t);
  \<And>s\<^sub>2. \<lbrakk>(c\<^sub>1, s) \<Rightarrow> (SKIP, s\<^sub>2); (c\<^sub>2, s\<^sub>2) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>(c\<^sub>1, s) \<Rightarrow> (THROW, t); x = THROW\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_IfE [elim!]: "\<lbrakk>
  (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> (x, t);
  \<lbrakk>bval b s; (c\<^sub>1, s) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>\<not> bval b s; (c\<^sub>2, s) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_WhileE [elim]: "\<lbrakk>
  (WHILE b DO c, s) \<Rightarrow> (x, t);
  \<lbrakk>\<not> bval b t; x = SKIP; s = t\<rbrakk> \<Longrightarrow> P;
  \<And>s\<^sub>2. \<lbrakk>bval b s; (c, s) \<Rightarrow> (SKIP, s\<^sub>2);
  (WHILE b DO c, s\<^sub>2) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>bval b s; (c, s) \<Rightarrow> (THROW, t); x = THROW\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_Throw [elim!]: "\<lbrakk>(THROW, s) \<Rightarrow> (x, t); \<lbrakk>x = THROW; t = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_Try [elim!]: "\<lbrakk>
  (TRY c\<^sub>1 CATCH c\<^sub>2, s) \<Rightarrow> (x, t);
  \<lbrakk>(c\<^sub>1, s) \<Rightarrow> (SKIP, t); x = SKIP\<rbrakk> \<Longrightarrow> P;
  \<And>s\<^sub>2. \<lbrakk>(c\<^sub>1, s) \<Rightarrow> (THROW, s\<^sub>2); (c\<^sub>2, s\<^sub>2) \<Rightarrow> (x, t)\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto

inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
  where
    Assign: "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |
    SeqSkip: "(SKIP;; c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" |
    SeqThrow: "(THROW;; c\<^sub>2, s) \<rightarrow> (THROW, s)" |
    SeqNext: "(c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<rightarrow> (c\<^sub>1';; c\<^sub>2, s')" |
    IfTrue: "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)" |
    IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" |
    While: "(WHILE b DO c, s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, s)" |
    TrySkip: "(TRY SKIP CATCH c\<^sub>2, s) \<rightarrow> (SKIP, s)" |
    TryThrow: "(TRY THROW CATCH c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" |
    TryNext: "(c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s') \<Longrightarrow> (TRY c\<^sub>1 CATCH c\<^sub>2, s) \<rightarrow> (TRY c\<^sub>1' CATCH c\<^sub>2, s')"

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y"

lemmas small_step_induct = small_step.induct[split_format(complete)]
declare small_step.intros[simp,intro]

lemma SS_SkipE [elim!]: "(SKIP, s) \<rightarrow> ct \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_AssignE [elim!]: "\<lbrakk>(x ::= a, s) \<rightarrow> ct; ct = (SKIP, s(x := aval a s)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_SeqE [elim]: "\<lbrakk>
  (c\<^sub>1;; c\<^sub>2, s) \<rightarrow> ct;
  \<lbrakk>ct = (c\<^sub>2, s); c\<^sub>1 = SKIP\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>ct = (THROW, s); c\<^sub>1 = THROW\<rbrakk> \<Longrightarrow> P;
  \<And>c\<^sub>1' s'. \<lbrakk>ct = (c\<^sub>1';; c\<^sub>2, s'); (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_IfE [elim!]: "\<lbrakk>
  (IF b THEN c1 ELSE c2, s) \<rightarrow> ct;
  \<lbrakk>ct = (c1, s); bval b s\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>ct = (c2, s); \<not> bval b s\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_WhileE [elim]: "\<lbrakk>
  (WHILE b DO c, s) \<rightarrow> ct;
  ct = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_ThrowE [elim!]: "(THROW, s) \<rightarrow> ct \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_TryE [elim]: "\<lbrakk>
  (TRY c\<^sub>1 CATCH c\<^sub>2, s) \<rightarrow> ct;
  \<lbrakk>ct = (SKIP, s); c\<^sub>1 = SKIP\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>ct = (c\<^sub>2, s); c\<^sub>1 = THROW\<rbrakk> \<Longrightarrow> P;
  \<And>c\<^sub>1' s'. \<lbrakk>ct = (TRY c\<^sub>1' CATCH c\<^sub>2, s'); (c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s')\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto

lemma star_seq2: "(c1, s) \<rightarrow>* (c1', s') \<Longrightarrow> (c1;; c2, s) \<rightarrow>* (c1';;c2, s')"
  by (induct rule: star_induct) (simp, blast intro: star.step)

lemma seq_comp_skip: "\<lbrakk>(c1, s1) \<rightarrow>* (SKIP, s2); (c2, s2) \<rightarrow>* (x, s3)\<rbrakk>
  \<Longrightarrow> (c1;; c2, s1) \<rightarrow>* (x, s3)"
  by (blast intro: star.step star_seq2 star_trans)

lemma seq_comp_throw: "\<lbrakk>(c1, s1) \<rightarrow>* (THROW, s2)\<rbrakk>
  \<Longrightarrow> (c1;; c2, s1) \<rightarrow>* (THROW, s2)"
  by (blast intro: star.step star_seq2 star_trans)

lemma star_try2: "(c1, s) \<rightarrow>* (c1', s') \<Longrightarrow> (TRY c1 CATCH c2, s) \<rightarrow>* (TRY c1' CATCH c2, s')"
  by (induct rule: star_induct) (simp, blast intro: star.step)

lemma try_comp_skip: "\<lbrakk>(c1, s1) \<rightarrow>* (SKIP, s2)\<rbrakk>
  \<Longrightarrow> (TRY c1 CATCH c2, s1) \<rightarrow>* (SKIP, s2)"
  by (blast intro: star.step star_try2 star_trans)

lemma try_comp_throw: "\<lbrakk>(c1, s1) \<rightarrow>* (THROW, s2); (c2, s2) \<rightarrow>* (x, s3)\<rbrakk>
  \<Longrightarrow> (TRY c1 CATCH c2, s1) \<rightarrow>* (x, s3)"
  by (blast intro: star.step star_try2 star_trans)

lemma big_to_small: "cs \<Rightarrow> (x, t) \<Longrightarrow> cs \<rightarrow>* (x, t)"
  by (induct cs "(x, t)" arbitrary: x t rule: big_step.induct)
    (blast intro: seq_comp_skip seq_comp_throw try_comp_skip try_comp_throw star.step)+

lemma big_final: "cs \<Rightarrow> (x, t) \<Longrightarrow> x = SKIP \<or> x = THROW"
  by (induct cs "(x, t)" arbitrary: x t rule: big_step.induct) blast+

lemma small1_big_continue: "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> (x, t) \<Longrightarrow> cs \<Rightarrow> (x, t)"
  by (induct arbitrary: x t rule: small_step.induct) auto

lemma small_to_big_skip: "cs \<rightarrow>* (SKIP, t) \<Longrightarrow> cs \<Rightarrow> (SKIP, t)"
  by (induct cs "(SKIP,t)" rule: star.induct) (auto intro: small1_big_continue)

lemma small_to_big_throw: "cs \<rightarrow>* (THROW, t) \<Longrightarrow> cs \<Rightarrow> (THROW, t)"
  by (induct cs "(THROW, t)" rule: star.induct) (auto intro: small1_big_continue)

theorem big_iff_small_skip: "cs \<Rightarrow> (SKIP, t) = cs \<rightarrow>* (SKIP,t)"
  by (blast intro: big_to_small small_to_big_skip)

theorem big_iff_small_throw: "cs \<Rightarrow> (THROW, t) = cs \<rightarrow>* (THROW,t)"
  by (blast intro: big_to_small small_to_big_throw)

definition "final cs \<longleftrightarrow> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP \<or> c = THROW"
proof -
  assume "final (c, s)"
  then have "\<not>(\<exists>c' s'. (c, s) \<rightarrow> (c', s'))" using final_def by simp
  then show "c = SKIP \<or> c = THROW"
  proof (induct c)
    case (Seq c1 c2)
    show ?case
    proof (cases "\<exists>c' s'. (c1, s) \<rightarrow> (c', s')")
      case True
      with Seq(3) show ?thesis by blast
    next
      case False
      with Seq(1) consider "c1 = SKIP" | "c1 = THROW" by blast
      then show ?thesis using Seq(3) by cases blast+
    qed
  next
    case (Try c1 c2)
    then show ?case
    proof (cases "\<exists>c' s'. (c1, s) \<rightarrow> (c', s')")
      case True
      with Try(3) show ?thesis by blast
    next
      case False
      with Try(1) consider "c1 = SKIP" | "c1 = THROW" by blast
      then show ?thesis using Try(3) by cases blast+
    qed
  qed blast+
qed

lemma final_iff_SKIP_or_THROW: "final (c,s) = (c = SKIP \<or> c = THROW)"
  by (metis SS_SkipE SS_ThrowE finalD final_def)

lemma big_iff_small_termination: "(\<exists> cs'. cs \<Rightarrow> cs') \<longleftrightarrow> (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
proof
  assume "\<exists>cs'. cs \<Rightarrow> cs'"
  then obtain cs' where "cs \<Rightarrow> cs'" by blast
  moreover from surj_pair [of cs'] obtain x t where "cs' = (x, t)" by blast
  ultimately have "cs \<Rightarrow> (x, t)" by blast
  then have "cs \<rightarrow>* (x, t)" and "x = SKIP \<or> x = THROW" using big_to_small big_final by simp+
  with final_iff_SKIP_or_THROW show "\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs'" by auto
next
  assume "\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs'"
  then obtain cs' where "cs \<rightarrow>* cs' \<and> final cs'" by blast
  moreover from surj_pair [of cs'] obtain x t where "cs' = (x, t)" by blast
  ultimately have H1: "cs \<rightarrow>* (x, t)" and H2: "final (x, t)" by blast+
  from H2 consider "x = SKIP" | "x = THROW" using final_iff_SKIP_or_THROW by blast 
  then have "cs \<Rightarrow> (x, t)"
  proof cases
    case 1
    then show ?thesis using H1 small_to_big_skip by blast
  next
    case 2
    then show ?thesis using H1 small_to_big_throw by blast
  qed
  then show "\<exists>cs'. cs \<Rightarrow> cs'" by blast
qed


end