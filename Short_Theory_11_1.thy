theory Short_Theory_11_1
  imports "HOL-IMP.BExp" "HOL-IMP.Star"
begin

datatype
  com = SKIP
  | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
  | Seq    com  com         ("_;;/ _"  [60, 61] 60)
  | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 60, 61] 61)
  | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
  | Repeat com bexp         ("(REPEAT _/ UNTIL _)" [60, 0] 61)

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
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

section \<open>Denotational\<close>

type_synonym com_den = "(state \<times> state) set"

definition W :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
  "W db dc = (\<lambda>dw. {(s, t). if db s then (s,t) \<in> dc O dw else s=t})"

definition R :: "com_den \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> (com_den \<Rightarrow> com_den)" where
  "R dc db = (\<lambda>dr. dc O {(s, t). if db s then s = t else (s, t) \<in> dr})"

fun D :: "com \<Rightarrow> com_den" where
  "D SKIP = Id" |
  "D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
  "D (c1;; c2)  = D c1 O D c2" |
  "D (IF b THEN c1 ELSE c2)
    = {(s,t). if bval b s then (s, t) \<in> D c1 else (s, t) \<in> D c2}" |
  "D (WHILE b DO c) = lfp (W (bval b) (D c))" |
  "D (REPEAT c UNTIL b) = lfp (R (D c) (bval b))"

lemma W_mono: "mono (W b c)"
  by (unfold W_def mono_def) auto

lemma R_mono: "mono (R c b)"
  by (unfold R_def mono_def) auto

lemma D_While_If:
  "D (WHILE b DO c) = D (IF b THEN c;; WHILE b DO c ELSE SKIP)"
proof-
  let ?w = "WHILE b DO c" let ?f = "W (bval b) (D c)"
  have "D ?w = lfp ?f" by simp
  also have "\<dots> = ?f (lfp ?f)" by(rule lfp_unfold [OF W_mono])
  also have "\<dots> = D(IF b THEN c;;?w ELSE SKIP)" by (simp add: W_def)
  finally show ?thesis .
qed

lemma D_Repeat_If:
  "D (REPEAT c UNTIL b) = D (c;; IF b THEN SKIP ELSE REPEAT c UNTIL b)"
proof-
  let ?r = "REPEAT c UNTIL b" let ?f = "R (D c) (bval b)"
  have "D ?r = lfp ?f" by simp
  also have "\<dots> = ?f (lfp ?f)" by(rule lfp_unfold [OF R_mono])
  also have "\<dots> = D (c;; IF b THEN SKIP ELSE ?r)" by (simp add: R_def)
  finally show ?thesis .
qed

text\<open>Equivalence of denotational and big-step semantics:\<close>

lemma D_if_big_step:  "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> D(c)"
proof (induction rule: big_step_induct)
  case (WhileFalse b s c)
  show ?case unfolding D_While_If using WhileFalse by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  show ?case unfolding D_While_If using WhileTrue(1, 4, 5) by auto
next
  case (RepeatTrue b t c s)
  show ?case unfolding D_Repeat_If using RepeatTrue(1, 3) by auto
next
  case (RepeatFalse b s\<^sub>2 c s\<^sub>1 s\<^sub>3)
  show ?case unfolding D_Repeat_If using RepeatFalse(1, 4, 5) by auto
qed auto

abbreviation Big_step :: "com \<Rightarrow> com_den" where
"Big_step c \<equiv> {(s,t). (c,s) \<Rightarrow> t}"

lemma Big_step_if_D:  "(s,t) \<in> D(c) \<Longrightarrow> (s,t) \<in> Big_step c"
proof (induction c arbitrary: s t)
  case (Seq c1 c2) thus ?case by fastforce
next
  case (While b c)
  let ?B = "Big_step (WHILE b DO c)" let ?f = "W (bval b) (D c)"
  have "?f ?B \<subseteq> ?B" using While.IH by (auto simp: W_def)
  from lfp_lowerbound[where ?f = "?f", OF this] While.prems
  show ?case by auto
next
  case (Repeat c b)
  let ?B = "Big_step (REPEAT c UNTIL b)" let ?f = "R (D c) (bval b)"
  have "?f ?B \<subseteq> ?B" using Repeat.IH by (auto simp: R_def)
  from lfp_lowerbound[where ?f = "?f", OF this] Repeat.prems
  show ?case by auto
qed (auto split: if_splits)

theorem denotational_is_big_step:
  "(s,t) \<in> D(c)  =  ((c,s) \<Rightarrow> t)"
by (metis D_if_big_step Big_step_if_D[simplified])

corollary equiv_c_iff_equal_D: "(c1 \<sim> c2) \<longleftrightarrow> D c1 = D c2"
  by(simp add: denotational_is_big_step[symmetric] set_eq_iff)


subsection "Continuity"

definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
"chain S = (\<forall>i. S i \<subseteq> S(Suc i))"

lemma chain_total: "chain S \<Longrightarrow> S i \<le> S j \<or> S j \<le> S i"
by (metis chain_def le_cases lift_Suc_mono_le)

definition cont :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
"cont f = (\<forall>S. chain S \<longrightarrow> f(UN n. S n) = (UN n. f(S n)))"

lemma mono_if_cont: fixes f :: "'a set \<Rightarrow> 'b set"
  assumes "cont f" shows "mono f"
proof
  fix a b :: "'a set" assume "a \<subseteq> b"
  let ?S = "\<lambda>n::nat. if n=0 then a else b"
  have "chain ?S" using \<open>a \<subseteq> b\<close> by(auto simp: chain_def)
  hence "f(UN n. ?S n) = (UN n. f(?S n))"
    using assms by (simp add: cont_def del: if_image_distrib)
  moreover have "(UN n. ?S n) = b" using \<open>a \<subseteq> b\<close> by (auto split: if_splits)
  moreover have "(UN n. f(?S n)) = f a \<union> f b" by (auto split: if_splits)
  ultimately show "f a \<subseteq> f b" by (metis Un_upper1)
qed

lemma chain_iterates: fixes f :: "'a set \<Rightarrow> 'a set"
  assumes "mono f" shows "chain(\<lambda>n. (f^^n) {})"
proof-
  have "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" for n
  proof (induction n)
    case 0 show ?case by simp
  next
    case (Suc n) thus ?case using assms by (auto simp: mono_def)
  qed
  thus ?thesis by(auto simp: chain_def assms)
qed

theorem lfp_if_cont:
  assumes "cont f" shows "lfp f = (UN n. (f^^n) {})" (is "_ = ?U")
proof
  from assms mono_if_cont
  have mono: "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" for n
    using funpow_decreasing [of n "Suc n"] by auto
  show "lfp f \<subseteq> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (UN n. (f^^Suc n){})"
      using chain_iterates[OF mono_if_cont[OF assms]] assms
      by(simp add: cont_def)
    also have "\<dots> = (f^^0){} \<union> \<dots>" by simp
    also have "\<dots> = ?U"
      using mono by auto (metis funpow_simps_right(2) funpow_swap1 o_apply)
    finally show "f ?U \<subseteq> ?U" by simp
  qed
next
  have "(f^^n){} \<subseteq> p" if "f p \<subseteq> p" for n p
  proof -
    show ?thesis
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_cont[OF assms] Suc] \<open>f p \<subseteq> p\<close>
      show ?case by simp
    qed
  qed
  thus "?U \<subseteq> lfp f" by(auto simp: lfp_def)
qed

lemma cont_W: "cont(W b r)"
by(auto simp: cont_def W_def)

lemma cont_R: "cont(R c b)"
  by(auto simp: cont_def R_def)


subsection\<open>The denotational semantics is deterministic\<close>

lemma single_valued_UN_chain:
  assumes "chain S" "(\<And>n. single_valued (S n))"
  shows "single_valued(UN n. S n)"
proof(auto simp: single_valued_def)
  fix m n x y z assume "(x, y) \<in> S m" "(x, z) \<in> S n"
  with chain_total[OF assms(1), of m n] assms(2)
  show "y = z" by (auto simp: single_valued_def)
qed

lemma single_valued_lfp: fixes f :: "com_den \<Rightarrow> com_den"
assumes "cont f" "\<And>r. single_valued r \<Longrightarrow> single_valued (f r)"
shows "single_valued(lfp f)"
unfolding lfp_if_cont[OF assms(1)]
proof(rule single_valued_UN_chain[OF chain_iterates[OF mono_if_cont[OF assms(1)]]])
  fix n show "single_valued ((f ^^ n) {})"
  by(induction n)(auto simp: assms(2))
qed

lemma single_valued_D: "single_valued (D c)"
proof(induction c)
  case Seq thus ?case by(simp add: single_valued_relcomp)
next
  case (While b c)
  let ?f = "W (bval b) (D c)"
  have "single_valued (lfp ?f)"
  proof(rule single_valued_lfp[OF cont_W])
    show "\<And>r. single_valued r \<Longrightarrow> single_valued (?f r)"
      using While.IH by(force simp: single_valued_def W_def)
  qed
  thus ?case by simp
next
  case (Repeat c b)
  let ?f = "R (D c) (bval b)"
  have "single_valued (lfp ?f)"
  proof(rule single_valued_lfp[OF cont_R])
    show "\<And>r. single_valued r \<Longrightarrow> single_valued (?f r)"
      using Repeat.IH by(force simp: single_valued_def R_def)
  qed
  thus ?case by simp
qed (auto simp add: single_valued_def)


end