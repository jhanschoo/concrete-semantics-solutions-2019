theory Short_Theory_7_8
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

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induct arbitrary: u rule: big_step.induct) blast+

inductive small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
  where
    Assign: "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |
    Seq1: "(SKIP;; c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" |
    Seq2: "(c\<^sub>1, s) \<rightarrow> (c\<^sub>1', s') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, s) \<rightarrow> (c\<^sub>1';; c\<^sub>2, s')" |
    IfTrue: "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)" |
    IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" |
    While: "(WHILE b DO c, s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, s)" |
    Repeat: "(REPEAT c UNTIL b, s) \<rightarrow> (c;; IF b THEN SKIP ELSE REPEAT c UNTIL b, s)"

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y"

lemmas small_step_induct = small_step.induct[split_format(complete)]
declare small_step.intros[simp,intro]

lemma SS_SkipE[elim!]: "(SKIP, s) \<rightarrow> ct \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_AssignE[elim!]: "\<lbrakk>(x ::= a, s) \<rightarrow> ct; ct = (SKIP, s(x := aval a s)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_SeqE[elim]: "\<lbrakk>
  (c1;; c2, s) \<rightarrow> ct;
  \<lbrakk>ct = (c2, s); c1 = SKIP\<rbrakk> \<Longrightarrow> P;
  \<And>c\<^sub>1' s'. \<lbrakk>ct = (c\<^sub>1';; c2, s'); (c1, s) \<rightarrow> (c\<^sub>1', s')\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_IfE[elim!]: "\<lbrakk>
  (IF b THEN c1 ELSE c2, s) \<rightarrow> ct;
  \<lbrakk>ct = (c1, s); bval b s\<rbrakk> \<Longrightarrow> P;
  \<lbrakk>ct = (c2, s); \<not> bval b s\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_WhileE[elim]: "\<lbrakk>
  (WHILE b DO c, s) \<rightarrow> ct;
  ct = (IF b THEN c;; WHILE b DO c ELSE SKIP, s) \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto
lemma SS_RepeatE[elim]: "\<lbrakk>
  (REPEAT c UNTIL b, s) \<rightarrow> ct;
  ct = (c;; IF b THEN SKIP ELSE REPEAT c UNTIL b, s) \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
  by (cases rule: small_step.cases) auto

lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
  by (induct rule: star_induct) (simp, blast intro: star.step)

lemma seq_comp: "\<lbrakk>(c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3)\<rbrakk>
  \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
  by (blast intro: star.step star_seq2 star_trans)

lemma big_to_small: "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
  by (induction rule: big_step.induct) (blast intro: seq_comp star.step)+

lemma small1_big_continue: "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
  by (induct arbitrary: t rule: small_step.induct) auto

lemma small_to_big: "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
  by (induct cs "(SKIP,t)" rule: star.induct) (auto intro: small1_big_continue)

theorem big_iff_small: "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
  by (blast intro: big_to_small small_to_big)

end