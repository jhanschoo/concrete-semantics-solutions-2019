theory Chapter9_2
imports "HOL-IMP.Sec_Typing"
begin

text \<open>
\exercise
Reformulate the inductive predicate @{const sec_type}
as a recursive function and prove the equivalence of the two formulations:
\<close>

fun ok :: "level \<Rightarrow> com \<Rightarrow> bool" where
  "ok l SKIP = True" |
  "ok l (x ::= a) \<longleftrightarrow> sec x \<ge> sec a \<and> sec x \<ge> l" |
  "ok l (c\<^sub>1;; c\<^sub>2) \<longleftrightarrow> ok l c\<^sub>1 \<and> ok l c\<^sub>2" |
  "ok l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> ok (max (sec b) l) c\<^sub>1 \<and> ok (max (sec b) l) c\<^sub>2" |
  "ok l (WHILE b DO c) = ok (max (sec b) l) c"

thm sec_type.intros
theorem "(l \<turnstile> c) = ok l c"
proof
  assume "l \<turnstile> c"
  then show "ok l c" by (induct rule: sec_type.induct) auto
next
  assume "ok l c"
  then show "l \<turnstile> c" by (induct l c rule: ok.induct) (auto intro: sec_type.intros)
qed

text\<open>
Try to reformulate the bottom-up system @{prop "\<turnstile> c : l"}
as a function that computes @{text l} from @{text c}. What difficulty do you face?
\endexercise
\<close>

(* "Problem": need to use quantifiers *)

text\<open>
\exercise
Define a bottom-up termination insensitive security type system
@{text"\<turnstile>' c : l"} with subsumption rule:
\<close>

inductive sec_type2' :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile>' _ : _)" [0,0] 50) where
Skip2': "\<turnstile>' SKIP : l" |
Assign2': "sec x \<ge> sec a \<Longrightarrow> \<turnstile>' x ::= a : sec x" |
Seq2': "\<lbrakk>\<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l\<rbrakk> \<Longrightarrow> \<turnstile>' c\<^sub>1;;c\<^sub>2 : l" |
If2': "\<lbrakk>sec b \<le> l;  \<turnstile>' c\<^sub>1 : l;  \<turnstile>' c\<^sub>2 : l\<rbrakk>
  \<Longrightarrow> \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2 : l" |
While2': "\<lbrakk>sec b \<le> l;  \<turnstile>' c : l\<rbrakk> \<Longrightarrow> \<turnstile>' WHILE b DO c : l" |
anti_mono2': "\<lbrakk>\<turnstile>' c : l; l' \<le> l\<rbrakk> \<Longrightarrow> \<turnstile>' c : l'"

text\<open>
Prove equivalence with the bottom-up system @{prop "\<turnstile> c : l"}
without subsumption rule:
\<close>

lemma "\<turnstile> c : l \<Longrightarrow> \<turnstile>' c : l"
proof (induct rule: sec_type2.induct)
  case (Seq2 c\<^sub>1 l\<^sub>1 c\<^sub>2 l\<^sub>2)
  from Seq2(2, 4) have "\<turnstile>' c\<^sub>1 : min l\<^sub>1 l\<^sub>2" and "\<turnstile>' c\<^sub>2 : min l\<^sub>1 l\<^sub>2" by (auto intro: sec_type2'.intros)
  then show ?case by (auto intro: sec_type2'.intros)
next
  case (If2 b l\<^sub>1 l\<^sub>2 c\<^sub>1 c\<^sub>2)
  from If2(3, 5) have "\<turnstile>' c\<^sub>1 : min l\<^sub>1 l\<^sub>2" and "\<turnstile>' c\<^sub>2 : min l\<^sub>1 l\<^sub>2" by (auto intro: sec_type2'.intros)
  with If2(1) show ?case by (auto intro: sec_type2'.intros)
qed (auto intro: sec_type2'.intros)

lemma "\<turnstile>' c : l \<Longrightarrow> \<exists>l' \<ge> l. \<turnstile> c : l'"
proof (induct rule: sec_type2'.induct)
  case (Seq2' c\<^sub>1 l c\<^sub>2)
  then show ?case by (auto intro: sec_type2.intros min.boundedI)
next
  case (If2' b l c\<^sub>1 c\<^sub>2)
  then show ?case by (auto dest: le_trans intro: sec_type2.intros min.boundedI)
next
  case (While2' b l c)
  then show ?case by (auto dest: le_trans intro: sec_type2.intros)
next
  case (anti_mono2' c l l')
  then show ?case by (auto dest: le_trans)
qed (auto intro: sec_type2.intros)

text\<open>
\endexercise

\exercise
Define a function that erases those parts of a command that
contain variables above some security level: \<close>

fun erase :: "level \<Rightarrow> com \<Rightarrow> com" where
  "erase l SKIP = SKIP" |
  "erase l (x ::= a) = (if sec x < l then (x ::= a) else SKIP)" |
  "erase l (c\<^sub>1;; c\<^sub>2) = erase l c\<^sub>1;; erase l c\<^sub>2" |
  "erase l (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (if sec b < l then IF b THEN erase l c\<^sub>1 ELSE erase l c\<^sub>2 else SKIP)" |
  "erase l (WHILE b DO c) = (if sec b < l then WHILE b DO erase l c else SKIP)"

text\<open>
Function @{term "erase l"} should replace all assignments to variables with
security level @{text"\<ge> l"} by @{const SKIP}.
It should also erase certain @{text IF}s and @{text WHILE}s,
depending on the security level of the boolean condition. Now show
that @{text c} and @{term "erase l c"} behave the same on the variables up
to level @{text l}: \<close>

lemma aval_eq_if_eq_less: "\<lbrakk> s\<^sub>1 = s\<^sub>2 (< l);  sec a < l \<rbrakk> \<Longrightarrow> aval a s\<^sub>1 = aval a s\<^sub>2"
  by (induct a) auto

lemma bval_eq_if_eq_less: "\<lbrakk> s\<^sub>1 = s\<^sub>2 (< l);  sec b < l \<rbrakk> \<Longrightarrow> bval b s\<^sub>1 = bval b s\<^sub>2"
  by (induct b) (auto simp add: aval_eq_if_eq_less)

theorem erase_correct: "\<lbrakk>(c,s) \<Rightarrow> s'; (erase l c, t) \<Rightarrow> t'; 0 \<turnstile> c; s = t (< l)\<rbrakk>
   \<Longrightarrow> s' = t' (< l)"
proof (induct arbitrary: t t' rule: big_step_induct)
  case (Skip s)
  then show ?case by auto
next
  case (Assign x a s)
  then show ?case by (cases "sec x < l") (auto intro!: aval_eq_if_eq_less)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by fastforce
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  from IfTrue(5) have Hsec: "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" by auto
  show ?case
  proof (cases "sec b < l")
    case True
    from True IfTrue(6) have "s = t (< sec b)" by simp
    moreover from True IfTrue(1, 6) have "bval b t" by (auto simp add: bval_eq_if_eq_less)
    ultimately show ?thesis using True IfTrue(4, 6) Hsec(1)
      by (intro IfTrue(3)) (auto dest: anti_mono)
  next
    case False
    with IfTrue(4) have Htt': "t = t'" by auto
    thm anti_mono [of "sec b" _ l]
    with False Hsec have "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
      by (intro anti_mono [of "sec b" _ l]) (auto intro: sec_type.intros)
    with IfTrue(1, 2) have "s = s' (< l)" by (auto dest: confinement)
    with IfTrue(4, 6) Htt' show ?thesis by auto
  qed
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  from IfFalse(5) have Hsecc: "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" by auto
  show ?case
  proof (cases "sec b < l")
    case True
    from True IfFalse(6) have "s = t (< sec b)" by simp
    moreover from True IfFalse(1, 6) have "\<not> bval b t" by (auto simp add: bval_eq_if_eq_less)
    ultimately show ?thesis using True IfFalse(4, 6) Hsecc(2)
      by (intro IfFalse(3)) (auto dest: anti_mono)
  next
    case False
    with IfFalse(4) have Htt': "t = t'" by auto
    thm anti_mono [of "sec b" _ l]
    with False Hsecc have "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
      by (intro anti_mono [of "sec b" _ l]) (auto intro: sec_type.intros)
    with IfFalse(1, 2) have "s = s' (< l)" by (auto dest: confinement)
    with IfFalse(4, 6) Htt' show ?thesis by auto
  qed
next
  case (WhileFalse b s c)
  then show ?case by (cases "sec b < l") (auto simp add: bval_eq_if_eq_less)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue(7) have Hsecc: "sec b \<turnstile> c" by auto
  then show ?case
  proof (cases "sec b < l")
    case True
    with WhileTrue(1, 8) have "bval b t" by (auto simp add: bval_eq_if_eq_less)
    with True WhileTrue(6) obtain ti where H: "(erase l c, t) \<Rightarrow> ti" "(WHILE b DO erase l c, ti) \<Rightarrow> t'" by auto
    from this(1) Hsecc WhileTrue(8) have "s\<^sub>2 = ti (< l)" by (intro WhileTrue(3)) (auto intro: anti_mono)
    with True H(2) WhileTrue(7) show ?thesis by (intro WhileTrue(5)) auto
  next
    case False
    with WhileTrue(2) Hsecc have H1: "s\<^sub>1 = s\<^sub>2 (< l)" by (auto dest: confinement)
    from False Hsecc have "l \<turnstile> WHILE b DO c" by (intro anti_mono [of "sec b" _ l]) (auto intro: sec_type.intros)
    with WhileTrue(4) have H2: "s\<^sub>2 = s\<^sub>3 (< l)" by (simp add: confinement)
    from False WhileTrue(6) have "t = t'" by auto
    with WhileTrue(8) H1 H2 show ?thesis by simp
  qed
qed

text\<open> This theorem looks remarkably like the noninterference lemma from
theory \mbox{@{theory "HOL-IMP.Sec_Typing"}} (although @{text"\<le>"} has been replaced by @{text"<"}).
You may want to start with that proof and modify it.
The structure should remain the same. You may also need one or
two simple additional lemmas.

In the theorem above we assume that both @{term"(c,s)"}
and @{term "(erase l c,t)"} terminate. How about the following two properties: \<close>

(* Idea: only problem is with loops whose conditional decides on confidential
  data. But these loops get erased so that the erased program always terminates
  once the original program terminates
*)
lemma "\<lbrakk> (c,s) \<Rightarrow> s';  0 \<turnstile> c;  s = t (< l) \<rbrakk>
  \<Longrightarrow> \<exists>t'. (erase l c, t) \<Rightarrow> t' \<and> s' = t' (< l)"
proof (induct arbitrary: t rule: big_step_induct)
  case (Skip s)
  then show ?case by auto
next
  case (Assign x a s)
  then show ?case
  proof (cases "sec x < l")
    case True
    then have H1: "(erase l (x ::= a), t) \<Rightarrow> t(x := aval a t)" by auto
    moreover have H2: "(x ::= a, s) \<Rightarrow> s(x := aval a s)" by auto
    ultimately show ?thesis using Assign by (meson erase_correct)
  qed auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case by fastforce
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  from IfTrue(4) have Hsecc: "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" by auto
  show ?case
  proof (cases "sec b < l")
    case True
    with IfTrue(1, 5) have H1: "bval b t" by (auto simp add: bval_eq_if_eq_less)
    from IfTrue(3, 5) Hsecc(1) obtain t' where H2: "(erase l c\<^sub>1, t) \<Rightarrow> t'" "s' = t' (< l)" by (meson zero_le anti_mono)
    from H1 H2(1) have "((IF b THEN erase l c\<^sub>1 ELSE erase l c\<^sub>2), t) \<Rightarrow> t'" by auto
    with True H2(2) show ?thesis by auto
  next
    case False
    then have "(erase l (IF b THEN c\<^sub>1 ELSE c\<^sub>2), t) \<Rightarrow> t" by auto
    moreover
    from False Hsecc have "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
      by (intro anti_mono [of "sec b" _ l]) (auto intro: sec_type.intros)
    with IfTrue(1, 2) have "s = s' (< l)" by (auto dest: confinement)
    with IfTrue(5) have "s' = t (< l)" by auto
    ultimately show ?thesis by blast
  qed
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  from IfFalse(4) have Hsecc: "sec b \<turnstile> c\<^sub>1" "sec b \<turnstile> c\<^sub>2" by auto
  show ?case
  proof (cases "sec b < l")
    case True
    with IfFalse(1, 5) have H1: "\<not>bval b t" by (auto simp add: bval_eq_if_eq_less)
    from IfFalse(3, 5) Hsecc(2) obtain t' where H2: "(erase l c\<^sub>2, t) \<Rightarrow> t'" "s' = t' (< l)" by (meson zero_le anti_mono)
    from H1 H2(1) have "((IF b THEN erase l c\<^sub>1 ELSE erase l c\<^sub>2), t) \<Rightarrow> t'" by auto
    with True H2(2) show ?thesis by auto
  next
    case False
    then have "(erase l (IF b THEN c\<^sub>1 ELSE c\<^sub>2), t) \<Rightarrow> t" by auto
    moreover
    from False Hsecc have "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
      by (intro anti_mono [of "sec b" _ l]) (auto intro: sec_type.intros)
    with IfFalse(1, 2) have "s = s' (< l)" by (auto dest: confinement)
    with IfFalse(5) have "s' = t (< l)" by auto
    ultimately show ?thesis by blast
  qed
next
  case (WhileFalse b s c)
  then show ?case by (cases "sec b < l") (auto simp add: bval_eq_if_eq_less)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue(6) have Hsecc: "sec b \<turnstile> c" by auto
  then show ?case
  proof (cases "sec b < l")
    case True
    with WhileTrue(1, 7) have Hb: "bval b t" by (auto simp add: bval_eq_if_eq_less)
    from Hsecc WhileTrue(3, 7) obtain ti where H1: "(erase l c, t) \<Rightarrow> ti" "s\<^sub>2 = ti (< l)" by (force intro: anti_mono)
    from WhileTrue(5, 6) H1(2) obtain t' where H2: "(erase l (WHILE b DO c), ti) \<Rightarrow> t'" "s\<^sub>3 = t' (< l)" by meson
    with True Hb H1(1) show ?thesis by auto
  next
    case False
    with WhileTrue(2) Hsecc have H1: "s\<^sub>1 = s\<^sub>2 (< l)" by (auto dest: confinement)
    from False Hsecc have "l \<turnstile> WHILE b DO c" by (intro anti_mono [of "sec b" _ l]) (auto intro: sec_type.intros)
    with WhileTrue(4) have H2: "s\<^sub>2 = s\<^sub>3 (< l)" by (simp add: confinement)
    from False have "(erase l (WHILE b DO c), t) \<Rightarrow> t" by auto
    with WhileTrue(7) H1 H2 show ?thesis by auto
  qed
qed

lemma "\<not>(\<forall> l c s s' t. (erase l c, s) \<Rightarrow> s' \<longrightarrow> 0 \<turnstile> c \<longrightarrow> s = t (< l) \<longrightarrow> (\<exists>t'. (c,t) \<Rightarrow> t' \<and> s' = t' (< l)))"
proof
  let ?l = "2 :: nat"
  let ?b = "Less (N 0) (V ''ab'')"
  let ?w = "WHILE ?b DO SKIP"
  let ?a = "''a'' ::= (N 0)"
  let ?c = "?w;; ?a"
  let ?s = "(\<lambda> _. 1) :: state"
  let ?s' = "?s (''a'' := 0)"
  have [simp]: "sec ''ab'' = 2" using sec_list_def [of "''ab''"] by simp
  have [simp]: "sec ''a'' = 1" using sec_list_def [of "''a''"] by simp
  have "(erase ?l ?w, ?s) \<Rightarrow> ?s" by auto
  moreover have "(?a, ?s) \<Rightarrow> ?s (''a'' := aval (N 0) ?s)" by blast
  then have "(erase ?l ?a, ?s) \<Rightarrow> ?s'" by auto
  ultimately have "(erase ?l ?w;; erase ?l ?a, ?s) \<Rightarrow> ?s'" by blast
  then have H1: "(erase ?l ?c, ?s) \<Rightarrow> ?s'" by simp
  have "?l \<turnstile> ?w" by (auto intro: sec_type.intros)
  then have "0 \<turnstile> ?w" by (intro anti_mono [of 2 _ 0]) auto
  moreover have "1 \<turnstile> ?a" by (auto intro: sec_type.intros)
  then have "0 \<turnstile> ?a" by (intro anti_mono [of 1 _ 0]) auto
  ultimately have H2: "0 \<turnstile> ?c" by (auto intro: sec_type.intros)
  have H3: "?s = ?s (< ?l)" by auto
  assume "\<forall>l c s s' t. (erase l c, s) \<Rightarrow> s' \<longrightarrow> 0 \<turnstile> c \<longrightarrow> s = t (< l) \<longrightarrow> (\<exists>t'. (c, t) \<Rightarrow> t' \<and> s' = t' (< l))"
  then obtain HC: "\<And>l c s s' t. \<lbrakk>(erase l c, s) \<Rightarrow> s'; 0 \<turnstile> c; s = t (< l)\<rbrakk> \<Longrightarrow> (\<exists>t'. (c, t) \<Rightarrow> t' \<and> s' = t' (< l))" by blast
  from HC [OF H1 H2 H3] obtain t' where "(?c, ?s) \<Rightarrow> t'" by blast
  then obtain ti where "(?w, ?s) \<Rightarrow> ti" by blast
  then show False
  by (induct ?w ?s ti rule: big_step_induct) auto
qed

text\<open> Give proofs or counterexamples.
\endexercise
\<close>

end

