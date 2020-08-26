theory Chapter10_3
imports
  "HOL-IMP.Live"
  "HOL-IMP.Small_Step"
begin

text\<open>
\exercise
Prove the following termination-insensitive version of the correctness of
@{const L}:
\<close>

theorem "\<lbrakk>(c, s) \<Rightarrow> s'; (c, t) \<Rightarrow> t'; s = t on L c X\<rbrakk> \<Longrightarrow> s' = t' on X"
proof (induct arbitrary: t t' X rule: big_step_induct)
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq(5) obtain ti where HSeqt: "(c\<^sub>1, t) \<Rightarrow> ti" "(c\<^sub>2, ti) \<Rightarrow> t'" by auto
  from HSeqt(1) Seq(2, 6) have "s\<^sub>2 = ti on (L c\<^sub>2 X)" by auto
  with HSeqt(2) Seq(4) show "s\<^sub>3 = t' on X" by auto
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  from IfTrue(5) have H: "s = t on vars b" "s = t on L c\<^sub>1 X" by auto
  from bval_eq_if_eq_on_vars [OF H(1)] IfTrue(1) have "bval b t" by auto
  with IfTrue(4) have "(c\<^sub>1, t) \<Rightarrow> t'" by auto
  with IfTrue(3) H(2) show "s' = t' on X" by auto
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  from IfFalse(5) have H: "s = t on vars b" "s = t on L c\<^sub>2 X" by auto
  from bval_eq_if_eq_on_vars [OF H(1)] IfFalse(1) have "\<not>bval b t" by auto
  with IfFalse(4) have "(c\<^sub>2, t) \<Rightarrow> t'" by auto
  with IfFalse(3) H(2) show "s' = t' on X" by auto
next
  case (WhileFalse b s c)
  from WhileFalse(3) have H: "s = t on vars b" using L_While_vars by blast
  from bval_eq_if_eq_on_vars [OF H] WhileFalse(1) have "\<not>bval b t" by auto
  with WhileFalse(2) have "t = t'" by auto
  with WhileFalse(3) show ?case using L_While_X by blast
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue(7) have H1: "s\<^sub>1 = t on vars b" "s\<^sub>1 = t on L c (L (WHILE b DO c) X)"
    using L_While_vars L_While_pfp by blast+
  from bval_eq_if_eq_on_vars [OF H1(1)] WhileTrue(1) have "bval b t" by auto
  with WhileTrue(6) obtain ti where H2: "(c, t) \<Rightarrow> ti" "(WHILE b DO c, ti) \<Rightarrow> t'" by auto
  from WhileTrue(3) H2(1) H1(2) have "s\<^sub>2 = ti on L (WHILE b DO c) X" by simp
  with H2(2) WhileTrue(5) show "s\<^sub>3 = t' on X" by simp
qed auto

text\<open>
Do not derive it as a corollary of the original correctness theorem
but prove it separately. Hint: modify the original proof.
\endexercise

\exercise\label{exe:bury-not-idemp}
Find a command @{text c} such that @{prop"bury (bury c {}) {} \<noteq> bury c {}"}.
For an arbitrary command, can you put a limit on the amount of burying needed
until everything that is dead is also buried?
\<close>

value "bury (''y'' ::= (V ''x'');; ''z'' ::= (V ''y'')) {}"
value "bury (bury (''y'' ::= (V ''x'');; ''z'' ::= (V ''y'')) {}) {}"
(* Amount of burying bounded above by the number of assignment statements,
  since the only transformation that bury does is removing assignment statements
*)

text\<open>
\endexercise

\exercise
Let @{term"lvars c"} / @{term"rvars c"} be the set of variables that
occur on the left-hand / right-hand side of an assignment in @{text c}.
Let @{term "rvars c"} additionally including those variables mentioned in
the conditionals of @{text IF} and @{text WHILE}.
Both functions are predefined in theory @{short_theory "Vars"}.
Show the following two properties of the small-step semantics.
Variables that are not assigned to do not change their value:
\<close>

lemma "\<lbrakk>(c,s) \<rightarrow>* (c',s'); lvars c \<inter> X = {}\<rbrakk> \<Longrightarrow> s = s' on X"
proof (induct rule: star_induct)
  case (step c s c' s' c'' s'')
  from step(1, 4) have "s = s' on X" by (induct rule: small_step_induct) auto
  moreover from step(1, 4) have "lvars c' \<inter> X = {}" by (induct rule: small_step_induct) auto
  with step(3) have "s' = s'' on X" by simp
  ultimately show ?case by simp
qed simp

text\<open>
The reduction behaviour of a command is only influenced by the variables
read by the command:
\<close>

lemma "\<lbrakk>(c,s) \<rightarrow>* (c',s'); s = t on X; rvars c \<subseteq> X\<rbrakk>
  \<Longrightarrow> \<exists>t'. (c,t) \<rightarrow>* (c',t') \<and> s' = t' on X"
proof (induct arbitrary: t rule: star_induct)
  case (step c s c' s' c'' s'')
    (* a stronger conclusion than necessary; that a step corresponds to a step,
    not several steps *)
  from step(1, 4, 5) have "\<exists>t'. (c, t) \<rightarrow> (c', t') \<and> s' = t' on X"
  proof (induct arbitrary: t rule: small_step_induct)
    case (Assign x a s)
    have "(x ::= a, t) \<rightarrow> (SKIP, t(x := aval a t))" by auto
    moreover from Assign have "s = t on vars a" by auto
    then have Hav: "aval a s = aval a t" by auto
    with Assign have "s(x := aval a s) = t(x := aval a t) on X" by auto
    ultimately show ?case by blast
  next
    case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
    from Seq2(2-4) obtain t' where H: "(c\<^sub>1, t) \<rightarrow> (c\<^sub>1', t')" "s' = t' on X" by fastforce
    from H(1) have "(c\<^sub>1;; c\<^sub>2, t) \<rightarrow> (c\<^sub>1';; c\<^sub>2, t')" by auto
    with H(2) show ?case by auto
  next
    case (IfTrue b s c\<^sub>1 c\<^sub>2)
    from IfTrue(2, 3) have "s = t on vars b" by auto
    from IfTrue(1) bval_eq_if_eq_on_vars [OF this] have "bval b t" by auto
    then have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<rightarrow> (c\<^sub>1, t)" by auto
    with IfTrue(2) show ?case by auto
  next
    case (IfFalse b s c\<^sub>1 c\<^sub>2)
    from IfFalse(2, 3) have "s = t on vars b" by auto
    from IfFalse(1) bval_eq_if_eq_on_vars [OF this] have "\<not>bval b t" by auto
    then have "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, t) \<rightarrow> (c\<^sub>2, t)" by auto
    with IfFalse(2) show ?case by auto
  qed auto
  then obtain t' where H1: "(c, t) \<rightarrow> (c', t')" "s' = t' on X" by auto
  from step(1, 5) have "rvars c' \<subseteq> X" by (induct rule: small_step_induct) auto
  with H1(2) step(3) obtain t'' where H2: "(c', t') \<rightarrow>* (c'', t'')" "s'' = t'' on X" by fastforce
  from H1(1) H2(1) have "(c, t) \<rightarrow>* (c'', t'')" by (simp add: star.step)
  with H2(2) show ?case by blast
qed auto

text\<open>
Hint: prove single step versions of the lemmas first.
\endexercise

\exercise
An \concept{available definitions} analysis determines which previous
assignments \texttt{x := a} are valid equalities \texttt{x = a} at later
program points.  For example, after \texttt{x := y+1} the equality \texttt{x =
y+1} is available, but after \mbox{\texttt{x := y+1;}} \texttt{y := 2} the equality \texttt{x = y+1} is
no longer available. The motivation for the analysis is that if \texttt{x =
a} is available before \texttt{v := a} then \mbox{\texttt{v := a}} can be replaced by
\texttt{v := x}.

Define an available definitions analysis as a gen/kill analysis,
for suitably defined @{text gen} and @{text kill} (which may need to be
mutually recursive):
\<close>
hide_const (open) gen "kill"
fun gen :: "com \<Rightarrow> (vname * aexp) set" and
  "kill" :: "com \<Rightarrow> (vname * aexp) set" where
  "gen SKIP = {}" |
  "gen (x ::= a) = (if x \<in> vars a then {} else {(x, a)})" |
  "gen (c\<^sub>1;; c\<^sub>2) = (gen c\<^sub>1 - kill c\<^sub>2) \<union> gen c\<^sub>2" |
  "gen (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = gen c\<^sub>1 \<inter> gen c\<^sub>2" |
  "gen (WHILE b DO c) = {}" |
  "kill SKIP = {}" |
  "kill (x ::= a) = {(x', a')| x' a'. x = x' \<or> x \<in> vars a'}" |
  "kill (c\<^sub>1;; c\<^sub>2) = kill c\<^sub>1 \<union> kill c\<^sub>2" |
  "kill (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = kill c\<^sub>1 \<union> kill c\<^sub>2" |
  "kill (WHILE b DO c) = kill c"

definition AD :: "(vname * aexp) set \<Rightarrow> com \<Rightarrow> (vname * aexp) set" where
"AD A c = gen c \<union> (A - kill c)"

text\<open>
The defining equations for both @{const gen} and @{const kill} follow
the \isacom{where} and are separated by ``@{text "|"}'' as usual.

A call \ @{term"AD A c"} \ should compute the available definitions
after the execution of @{text c} assuming that the definitions in @{text A}
are available before the execution of @{text c}.

Prove correctness of the analysis:
\<close>

theorem "\<lbrakk> (c,s) \<Rightarrow> s';  \<forall> (x,a) \<in> A. s x = aval a s \<rbrakk>
  \<Longrightarrow> \<forall> (x,a) \<in> AD A c. s' x = aval a s'"
proof (induct arbitrary: A rule: big_step_induct)
  case (Skip s)
  then show ?case by (auto simp add: AD_def)
next
  case (Assign x a s)
  show ?case
  proof (intro ballI, unfold AD_def)
    fix p' :: "vname \<times> aexp"
    assume Hin: "p' \<in> gen (x ::= a) \<union> (A - kill (x ::= a))"
    obtain x' a' where HP: "p' = (x', a')" using prod.split_sel by blast
    with Hin consider (Bgen) "(x', a') \<in> gen (x ::= a)" | (BA) "(x', a') \<in> (A - kill (x ::= a))" by auto
    then have "(s(x := aval a s)) x' = aval a' (s(x := aval a s))"
    proof cases
      case Bgen
      with Assign show ?thesis by (auto split: if_split_asm)
    next
      case BA
      with Assign have "s x' = aval a' s" "x' \<noteq> x" "x \<notin> vars a'" by auto
      then show ?thesis by auto
    qed
    with HP show "case p' of (x', a') \<Rightarrow> (s(x := aval a s)) x' = aval a' (s(x := aval a s))" by auto
  qed
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq(2, 5) have "\<forall>(x, a) \<in> AD A c\<^sub>1. s\<^sub>2 x = aval a s\<^sub>2" by (auto simp add: AD_def)
  with Seq(4) have "\<forall>(x, a) \<in> AD (AD A c\<^sub>1) c\<^sub>2. s\<^sub>3 x = aval a s\<^sub>3" by (auto simp add: AD_def)
  then show ?case by (auto simp add: AD_def)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  from WhileTrue(3, 6) have "\<forall>(x, a) \<in> AD A c. s\<^sub>2 x = aval a s\<^sub>2" by (auto simp add: AD_def)
  with WhileTrue(5) show ?case by (auto simp add: AD_def)
qed (auto simp add: AD_def)

text\<open>
\endexercise
\<close>



end

