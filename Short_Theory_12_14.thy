theory Short_Theory_12_14
  imports "HOL-IMP.BExp" "HOL-IMP.Star"
begin

datatype
  com = SKIP
  | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
  | Seq    com  com         ("_;;/ _"  [60, 61] 60)
  | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 60, 61] 61)
  | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
  | Repeat com bexp         ("(REPEAT _/ UNTIL _)" [60, 0] 61)

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
  where
    Skip: "(SKIP,s) \<Rightarrow> s" |
    Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
    Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
    IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
    IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
    WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
    WhileTrue: "\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk>
      \<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
    RepeatTrue: "\<lbrakk> bval b t; (c, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t" |
    RepeatFalse: "\<lbrakk> \<not>bval b s\<^sub>2; (c, s\<^sub>1) \<Rightarrow> s\<^sub>2; (REPEAT c UNTIL b, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk>
      \<Longrightarrow> (REPEAT c UNTIL b, s\<^sub>1) \<Rightarrow> s\<^sub>3"
lemmas big_step_induct = big_step.induct[split_format(complete)]
declare big_step.intros [intro]

lemma BS_SkipE[elim!]: "\<lbrakk>(SKIP, s) \<Rightarrow> t; t = s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_AssignE[elim!]: "\<lbrakk>(x ::= a, s) \<Rightarrow> t; t = s(x := aval a s) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_SeqE[elim!]: "\<lbrakk>(c\<^sub>1;; c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3;
 \<And>s\<^sub>2. \<lbrakk>(c\<^sub>1, s\<^sub>1) \<Rightarrow> s\<^sub>2; (c\<^sub>2, s\<^sub>2) \<Rightarrow> s\<^sub>3\<rbrakk> \<Longrightarrow> P\<rbrakk>
\<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_IfE[elim!]: "\<lbrakk>
  (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t;
  \<lbrakk>bval b s; (c\<^sub>1, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>\<not> bval b s; (c\<^sub>2, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_WhileE[elim]: "\<lbrakk>
  (WHILE b DO c, s) \<Rightarrow> t;
  \<lbrakk>\<not> bval b t; s = t\<rbrakk> \<Longrightarrow> P;
  \<And>s\<^sub>2. \<lbrakk>bval b s; (c, s) \<Rightarrow> s\<^sub>2; (WHILE b DO c, s\<^sub>2) \<Rightarrow> t\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto
lemma BS_RepeatE[elim]: "\<lbrakk>
  (REPEAT c UNTIL b, s) \<Rightarrow> t;
  \<lbrakk>bval b t; (c, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> P;
  \<And>s\<^sub>2. \<lbrakk>\<not> bval b s\<^sub>2; (c, s) \<Rightarrow> s\<^sub>2; (REPEAT c UNTIL b, s\<^sub>2) \<Rightarrow> t\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: big_step.cases) auto

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induct arbitrary: u rule: big_step.induct) blast+

lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  \<comment> \<open>to show the equivalence, we look at the derivation tree for\<close>
  \<comment> \<open>each side and from that construct a derivation tree for the other side\<close>
  have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases \<comment> \<open>rule inversion on \<open>(?w, s) \<Rightarrow> t\<close>\<close>
      case WhileFalse
      thus ?thesis by blast
    next
      case WhileTrue
      from \<open>bval b s\<close> \<open>(?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      \<comment> \<open>now we can build a derivation tree for the \<^text>\<open>IF\<close>\<close>
      \<comment> \<open>first, the body of the True-branch:\<close>
      hence "(c;; ?w, s) \<Rightarrow> t" by (rule Seq)
      \<comment> \<open>then the whole \<^text>\<open>IF\<close>\<close>
      with \<open>bval b s\<close> show ?thesis by (rule IfTrue)
    qed
  qed
  moreover
  \<comment> \<open>now the other direction:\<close>
  have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases \<comment> \<open>rule inversion on \<open>(?iw, s) \<Rightarrow> t\<close>\<close>
      case IfFalse
      hence "s = t" using \<open>(?iw, s) \<Rightarrow> t\<close> by blast
      thus ?thesis using \<open>\<not>bval b s\<close> by blast
    next
      case IfTrue
      \<comment> \<open>and for this, only the Seq-rule is applicable:\<close>
      from \<open>(c;; ?w, s) \<Rightarrow> t\<close> obtain s' where
        "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      \<comment> \<open>with this information, we can build a derivation tree for \<^text>\<open>WHILE\<close>\<close>
      with \<open>bval b s\<close> show ?thesis by (rule WhileTrue)
    qed
  qed
  ultimately
  show ?thesis by blast
qed

lemma unfold_repeat:
  "(REPEAT c UNTIL b) \<sim> (c;; IF b THEN SKIP ELSE REPEAT c UNTIL b)" (is "?r \<sim> ?sr")
proof -
  {
    fix s t
    assume "(?r, s) \<Rightarrow> t"
    then have "(?sr, s) \<Rightarrow> t"
    proof cases
      case RepeatTrue
      thus ?thesis by blast
    next
      case (RepeatFalse s\<^sub>2)
      from RepeatFalse(1, 2) have "\<not>(bval b t \<and> (c, s) \<Rightarrow> t)"
        by (cases "s\<^sub>2 = t") (auto simp add: big_step_determ)
      with \<open>(?r, s) \<Rightarrow> t\<close> obtain s' where
        "\<not> bval b s'" "(c, s) \<Rightarrow> s'" and "(?r, s') \<Rightarrow> t" by auto
      from this(1, 3) have "(IF b THEN SKIP ELSE ?r, s') \<Rightarrow> t" by (rule IfFalse)
      with \<open>(c, s) \<Rightarrow> s'\<close> show ?thesis by (rule Seq)
    qed
  }
  moreover
  {
    fix s t
    assume "(?sr, s) \<Rightarrow> t"
    then have "(?r, s) \<Rightarrow> t"
    proof cases \<comment> \<open>rule inversion on \<open>(?iw, s) \<Rightarrow> t\<close>\<close>
      case (Seq s\<^sub>2)
      from Seq(2) show "(?r, s) \<Rightarrow> t"
      proof cases
        case IfTrue
        from IfTrue(2) have "s\<^sub>2 = t" by auto
        with Seq(1) IfTrue(1) show ?thesis by auto
      next
        case IfFalse
        with Seq(1) show ?thesis by auto
      qed
    qed
  }
  ultimately
  show ?thesis by blast
qed

type_synonym assn = "state \<Rightarrow> bool"

definition hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile> {P}c{Q} = (\<forall>s t. P s \<and> (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999) where
  "s[a/x] == s(x := aval a s)"

inductive hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50) where
  Skip: "\<turnstile> {P} SKIP {P}" |
  Assign: "\<turnstile> {\<lambda>s. P(s[a/x])} x::=a {P}" |
  Seq: "\<lbrakk> \<turnstile> {P} c\<^sub>1 {Q}; \<turnstile> {Q} c\<^sub>2 {R} \<rbrakk> \<Longrightarrow> \<turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}" |
  If: "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
    \<Longrightarrow> \<turnstile> {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}" |
  While: "\<lbrakk>\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P}\<rbrakk> \<Longrightarrow> \<turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}" |
  Repeat: "\<lbrakk>\<turnstile> {P} c {Q}; \<forall>s. Q s \<and> \<not>bval b s \<longrightarrow> P s\<rbrakk> \<Longrightarrow> \<turnstile> {P} REPEAT c UNTIL b {\<lambda>s. Q s \<and> bval b s}" |
  conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
    \<Longrightarrow> \<turnstile> {P'} c {Q'}"

lemmas [simp] = hoare.Skip hoare.Assign hoare.Seq If

lemmas [intro!] = hoare.Skip hoare.Assign hoare.Seq hoare.If

lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P'} c {Q}"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> {P} c {Q'}"
by (blast intro: conseq)

text\<open>The assignment and While rule are awkward to use in actual proofs
because their pre and postcondition are of a very special form and the actual
goal would have to match this form exactly. Therefore we derive two variants
with arbitrary pre and postconditions.\<close>

lemma Assign': "\<forall>s. P s \<longrightarrow> Q(s[a/x]) \<Longrightarrow> \<turnstile> {P} x ::= a {Q}"
by (simp add: strengthen_pre[OF _ Assign])

lemma While':
assumes "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P}" and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile> {P} WHILE b DO c {Q}"
  by(rule weaken_post[OF While[OF assms(1)] assms(2)])

lemma Repeat':
  assumes "\<turnstile> {P} c {Q}" and "\<forall>s. Q s \<and> \<not>bval b s \<longrightarrow> P s" and "\<forall>s. Q s \<and> bval b s \<longrightarrow> Q' s"
  shows "\<turnstile> {P} REPEAT c UNTIL b {Q'}"
  by (rule weaken_post [OF Repeat [OF assms(1) assms(2)] assms(3)])

lemma hoare_sound: "\<turnstile> {P} c {Q} \<Longrightarrow> \<Turnstile> {P} c {Q}"
proof(induction rule: hoare.induct)
  case (While P b c)
  have "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow>  P s  \<Longrightarrow>  P t \<and> \<not> bval b t" for s t
  proof(induction "WHILE b DO c" s t rule: big_step_induct)
    case WhileFalse thus ?case by blast
  next
    case WhileTrue thus ?case
      using While.IH unfolding hoare_valid_def by blast
  qed
  thus ?case unfolding hoare_valid_def by blast
next
  case (Repeat P c Q b)
  have "(REPEAT c UNTIL b, s) \<Rightarrow> t \<Longrightarrow> P s \<Longrightarrow> Q t \<and> bval b t" for s t
  proof (induct "REPEAT c UNTIL b" s t rule: big_step_induct) (* note: case analysis sufficed *)
    case (RepeatTrue t s)
    from Repeat(3) RepeatTrue(1, 2, 4) show ?case unfolding hoare_valid_def by blast 
  next
    case (RepeatFalse s\<^sub>2 s\<^sub>1 s\<^sub>3)
    from Repeat(2, 3) RepeatFalse(1, 2, 5, 6) show ?case unfolding hoare_valid_def by blast
  qed
  thus ?case unfolding hoare_valid_def by blast
qed (auto simp: hoare_valid_def)

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
  by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
  by (rule ext) (auto simp: wp_def)

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
  by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
  "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q =
  (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
  by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
  "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
  unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
  by(simp add: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
  by(simp add: wp_While_If)

lemma wp_Repeat_If:
  "wp (REPEAT c UNTIL b) Q s =
  wp (c;; IF b THEN SKIP ELSE REPEAT c UNTIL b) Q s"
  unfolding wp_def by (metis unfold_repeat)

lemma wp_Repeat [simp]: "wp c (\<lambda>s. wp (REPEAT c UNTIL b) Q s \<and> \<not>bval b s \<or> Q s \<and> bval b s) s = wp (REPEAT c UNTIL b) Q s"
  unfolding wp_def by (auto simp add: wp_Repeat_If)

lemma wp_c_bval_or: "wp c (bval b) s \<or> wp c (\<lambda>s. \<not>bval b s) s"
  unfolding wp_def
proof (cases "\<forall>t. (c, s) \<Rightarrow> t \<longrightarrow> bval b t")
  case False
  then obtain t\<^sub>0 where H: "(c, s) \<Rightarrow> t\<^sub>0" "\<not>bval b t\<^sub>0" by blast
  then show "(\<forall>t. (c, s) \<Rightarrow> t \<longrightarrow> bval b t) \<or> (\<forall>t. (c, s) \<Rightarrow> t \<longrightarrow> \<not> bval b t)" (is "?L \<or> ?R")
  proof -
    have "?R"
    proof (intro allI impI)
      fix t
      assume "(c, s) \<Rightarrow> t"
      with H(1) have "t = t\<^sub>0" by (simp add: big_step_determ)
      with H(2) show "\<not>bval b t" by simp
    qed
    then show ?thesis by blast
  qed
qed simp

lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof(induction c arbitrary: Q)
  case If thus ?case by(auto intro: conseq)
next
  case (While b c)
  let ?w = "WHILE b DO c"
  show "\<turnstile> {wp ?w Q} ?w {Q}"
  proof(rule While')
    show "\<turnstile> {\<lambda>s. wp ?w Q s \<and> bval b s} c {wp ?w Q}"
    proof(rule strengthen_pre[OF _ While.IH])
      show "\<forall>s. wp ?w Q s \<and> bval b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
    show "\<forall>s. wp ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
  qed
next
  case (Repeat c b)
  let ?r = "REPEAT c UNTIL b"
  show "\<turnstile> {wp ?r Q} ?r {Q}"
  proof (rule Repeat')
    show "\<turnstile> {wp (REPEAT c UNTIL b) Q} c {\<lambda>s. (wp (REPEAT c UNTIL b) Q s \<and> \<not>bval b s) \<or> (Q s \<and> bval b s)}"
      by (rule strengthen_pre [OF _ Repeat]) simp
  qed auto
qed auto

lemma hoare_complete: assumes "\<Turnstile> {P}c{Q}" shows "\<turnstile> {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "\<turnstile> {wp c Q} c {Q}" by(rule wp_is_pre)
qed

corollary hoare_sound_complete: "\<turnstile> {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
  by (metis hoare_complete hoare_sound)

end