theory Chapter7
imports "HOL-IMP.Small_Step"
begin

text\<open>
\section*{Chapter 7}

\exercise
Define a function that computes the set of variables that are assigned to
in a command:
\<close>

(* We use static analysis semantics for the notion of "assigned".
  A more precise semantics will use an auxillary function that reasons in terms
  of states, and take the union of assignments among its terminating states.
*)
fun assigned :: "com \<Rightarrow> vname set" where
  "assigned SKIP = {}" |
  "assigned (x ::= _) = {x}" |
  "assigned (c\<^sub>1;;c\<^sub>2) = assigned c\<^sub>1 \<union> assigned c\<^sub>2" |
  "assigned (IF _ THEN c\<^sub>1 ELSE c\<^sub>2) = assigned c\<^sub>1 \<union> assigned c\<^sub>2" | 
  "assigned (WHILE _ DO c) = assigned c"

text\<open>
Prove that if some variable is not assigned to in a command,
then that variable is never modified by the command:
\<close>

lemma "\<lbrakk> (c, s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"
  by (induct rule: big_step_induct) auto

text \<open>
\endexercise

\exercise
Define a recursive function that determines if a command behaves like @{const SKIP}
and prove its correctness:
\<close>

(* Honestly, the skip property is better captured by reasoning about states,
which does not require the function to be defined recursively.
*)
fun skip :: "com \<Rightarrow> bool" where
  "skip SKIP \<longleftrightarrow> True" |
  "skip (_ ::= _) \<longleftrightarrow> False" |
  "skip (c\<^sub>1;;c\<^sub>2) \<longleftrightarrow> skip c\<^sub>1 \<and> skip c\<^sub>2" |
  "skip (IF _ THEN c\<^sub>1 ELSE c\<^sub>2) \<longleftrightarrow> skip c\<^sub>1 \<and> skip c\<^sub>2" |
  "skip (WHILE _ DO c) \<longleftrightarrow> False"
  (* equivalence requires that the while loop terminates. The while loop terminates
  without mutating state IFF the bexp is contradictory. (Otherwise, there is a state
  that either never terminates, or gets mutated in order to eventually fail the
  guard and proceed. In conventional static analysis semantics, which I presume
  the question means by "behaves like", this means that while loops never
  behaves like skip.
 *)

(* because we have written off while, we can simply induct on the
  inductive definition of c
  *)
lemma "skip c \<Longrightarrow> c \<sim> SKIP"
proof (intro allI)
  fix s t
  assume "skip c"
  then have Hs: "(c, s) \<Rightarrow> s" by (induct c) auto
  show "(c, s) \<Rightarrow> t = (SKIP, s) \<Rightarrow> t"
  proof
    assume "(c, s) \<Rightarrow> t"
    with Hs have "s = t" using big_step_determ by simp
    then show "(SKIP, s) \<Rightarrow> t" using Skip by simp
  next
    assume "(SKIP, s) \<Rightarrow> t"
    moreover have "(SKIP, s) \<Rightarrow> s" by auto
    ultimately have "s = t" using big_step_determ by simp
    with Hs show "(c, s) \<Rightarrow> t" by simp
  qed
qed

text\<open>
\endexercise

\exercise
Define a recursive function
\<close>

fun deskip :: "com \<Rightarrow> com" where
  "deskip (SKIP;;c) = c" |
  "deskip (c;;SKIP) = c" |
  "deskip (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = IF b THEN deskip c\<^sub>1 ELSE deskip c\<^sub>2" |
  "deskip (WHILE b DO c) = WHILE b DO deskip c" |
  "deskip c = c"

text\<open>
that eliminates as many @{const SKIP}s as possible from a command. For example:
@{prop[display]"deskip (SKIP;; WHILE b DO (x::=a;; SKIP)) = WHILE b DO x::=a"}
Prove its correctness by induction on @{text c}: \<close>

lemma "deskip c \<sim> c"
  by (induct c rule: deskip.induct) (auto simp add: sim_while_cong)

text\<open>
Remember lemma @{thm[source]sim_while_cong} for the @{text WHILE} case.
\endexercise

\exercise
A small-step semantics for the evaluation of arithmetic expressions
can be defined like this:
\<close>

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x, s) \<leadsto> N (s x)" |
"(Plus (N i) (N j), s) \<leadsto> N (i + j)" |
"(a\<^sub>1, s) \<leadsto> a\<^sub>1' \<Longrightarrow> (Plus a\<^sub>1 a\<^sub>2, s) \<leadsto> Plus a\<^sub>1' a\<^sub>2" |
"(a\<^sub>2, s) \<leadsto> a\<^sub>2' \<Longrightarrow> (Plus (N i) a\<^sub>2, s) \<leadsto> Plus (N i) a\<^sub>2'"

text\<open>
Complete the definition with two rules for @{const Plus}
that model a left-to-right evaluation strategy:
reduce the first argument with @{text"\<leadsto>"} if possible,
reduce the second argument with @{text"\<leadsto>"} if the first argument is a number.
Prove that each @{text"\<leadsto>"} step preserves the value of the expression:
\<close>

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
proof (induction rule: astep.induct [split_format (complete)])
  fix x s
  show "aval (V x) s = aval (N (s x)) s" by simp
next
  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by simp
next
  fix a\<^sub>1 s a\<^sub>1' a\<^sub>2
  assume "(a\<^sub>1, s) \<leadsto> a\<^sub>1'" "aval a\<^sub>1 s = aval a\<^sub>1' s"
  then show "aval (Plus a\<^sub>1 a\<^sub>2) s = aval (Plus a\<^sub>1' a\<^sub>2) s" by simp
next
  fix a\<^sub>2 s a\<^sub>2' i
  assume "(a\<^sub>2, s) \<leadsto> a\<^sub>2'" "aval a\<^sub>2 s = aval a\<^sub>2' s"
  then show "aval (Plus (N i) a\<^sub>2) s = aval (Plus (N i) a\<^sub>2') s" by simp
qed

text\<open>
Do not use the \isacom{case} idiom but write down explicitly what you assume
and show in each case: \isacom{fix} \dots \isacom{assume} \dots \isacom{show} \dots.
\endexercise

\exercise
Prove or disprove (by giving a counterexample):
\<close>

lemma "IF And b\<^sub>1 b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 \<sim>
          IF b\<^sub>1 THEN IF b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 ELSE c\<^sub>2"
proof (intro allI)
  fix s t
  show "(IF And b\<^sub>1 b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t =
           (IF b\<^sub>1 THEN IF b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 ELSE c\<^sub>2, s) \<Rightarrow> t"
  proof
    assume "(IF And b\<^sub>1 b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t"
    then show "(IF b\<^sub>1 THEN IF b\<^sub>2 THEN c\<^sub>1 ELSE c\<^sub>2 ELSE c\<^sub>2, s) \<Rightarrow> t"
    proof
      assume Hb: "\<not>bval (And b\<^sub>1 b\<^sub>2) s"
      show "(c\<^sub>2, s) \<Rightarrow> t \<Longrightarrow> ?thesis"
      proof (cases "bval b\<^sub>1 s")
        case True
        with Hb have "\<not>bval b\<^sub>2 s" by auto
        with True show "(c\<^sub>2, s) \<Rightarrow> t \<Longrightarrow> ?thesis" by auto
      qed auto
    qed auto
  qed auto
qed

lemma "\<exists> b\<^sub>1 b\<^sub>2 c. ~WHILE And b\<^sub>1 b\<^sub>2 DO c \<sim> WHILE b\<^sub>1 DO WHILE b\<^sub>2 DO c"
proof (intro exI notI)
  let ?b\<^sub>1 = "(Less (V ''a'') (N 1))"
  let ?b\<^sub>2 = "(Less (V ''b'') (N 2))"
  let ?c  = "''a'' ::= (Plus (V ''a'') (N 1));; ''b'' ::= (Plus (V ''b'') (N 1))"
  assume Hc: "WHILE And ?b\<^sub>1 ?b\<^sub>2 DO ?c \<sim> WHILE ?b\<^sub>1 DO WHILE ?b\<^sub>2 DO ?c"
  let ?s = "<>"
  let ?t\<^sub>1 = "<''a'':=1,''b'':=1>"
  let ?t\<^sub>2 = "<''a'':=2,''b'':=2>"
  have H1: "(WHILE And ?b\<^sub>1 ?b\<^sub>2 DO ?c, ?s) \<Rightarrow> ?t\<^sub>1"
  proof (rule WhileTrue)
    show "bval (And ?b\<^sub>1 ?b\<^sub>2) <>" by (auto simp add: null_state_def)
    show "(?c, <>) \<Rightarrow> ?t\<^sub>1" by (auto simp add: assign_simp null_state_def)
    show "(WHILE And ?b\<^sub>1 ?b\<^sub>2 DO ?c, ?t\<^sub>1) \<Rightarrow> ?t\<^sub>1" by (rule WhileFalse) (auto simp add: null_state_def)
  qed
  with Hc have H1: "(WHILE ?b\<^sub>1 DO WHILE ?b\<^sub>2 DO ?c, ?s) \<Rightarrow> ?t\<^sub>1" by auto
  moreover have H2: "(WHILE ?b\<^sub>1 DO WHILE ?b\<^sub>2 DO ?c, ?s) \<Rightarrow> ?t\<^sub>2"
  proof (rule WhileTrue)
    show "bval ?b\<^sub>1 ?s" by (auto simp add: null_state_def)
    show "(WHILE ?b\<^sub>2 DO ?c, ?s) \<Rightarrow> ?t\<^sub>2"
    proof (rule WhileTrue)
      show "bval ?b\<^sub>2 ?s" by (auto simp add: null_state_def)
      show "(?c, ?s) \<Rightarrow> ?t\<^sub>1" by (auto simp add: assign_simp null_state_def)
      show "(WHILE ?b\<^sub>2 DO ?c, ?t\<^sub>1) \<Rightarrow> ?t\<^sub>2"
      proof
        show "bval ?b\<^sub>2 ?t\<^sub>1" by auto
        show "(?c, ?t\<^sub>1) \<Rightarrow> ?t\<^sub>2" by (auto simp add: assign_simp)
        show "(WHILE ?b\<^sub>2 DO ?c, ?t\<^sub>2) \<Rightarrow> ?t\<^sub>2" by (rule WhileFalse) (auto)
      qed
    qed
    show "(WHILE ?b\<^sub>1 DO WHILE ?b\<^sub>2 DO ?c, ?t\<^sub>2) \<Rightarrow> ?t\<^sub>2" by (rule WhileFalse) (auto)
  qed
  show False using big_step_determ [OF H1 H2, THEN fun_cong, of "''a''"] by simp
qed

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b\<^sub>1 b\<^sub>2 = Not (And (Not b\<^sub>1) (Not b\<^sub>2))"

lemma while_inv: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not> bval b t"
  by (induct "WHILE b DO c" s t arbitrary: b c rule: big_step_induct) simp

lemma "WHILE Or b\<^sub>1 b\<^sub>2 DO c \<sim>
          WHILE Or b\<^sub>1 b\<^sub>2 DO c;; WHILE b\<^sub>1 DO c"
proof (intro allI)
  fix s t
  show "(WHILE Or b\<^sub>1 b\<^sub>2 DO c, s) \<Rightarrow> t =
             (WHILE Or b\<^sub>1 b\<^sub>2 DO c;; WHILE b\<^sub>1 DO c, s) \<Rightarrow> t"
  proof
    assume HW: "(WHILE Or b\<^sub>1 b\<^sub>2 DO c, s) \<Rightarrow> t"
    show "(WHILE Or b\<^sub>1 b\<^sub>2 DO c;; WHILE b\<^sub>1 DO c, s) \<Rightarrow> t"
    proof (rule Seq)
      from HW show "(WHILE Or b\<^sub>1 b\<^sub>2 DO c, s) \<Rightarrow> t" .
      from HW while_inv have "\<not> bval (Or b\<^sub>1 b\<^sub>2) t" by simp
      then have "\<not> bval b\<^sub>1 t" using Or_def by auto
      then show "(WHILE b\<^sub>1 DO c, t) \<Rightarrow> t" by auto
    qed
  next
    assume "(WHILE Or b\<^sub>1 b\<^sub>2 DO c;; WHILE b\<^sub>1 DO c, s) \<Rightarrow> t"
    then obtain s' where H1: "(WHILE Or b\<^sub>1 b\<^sub>2 DO c, s) \<Rightarrow> s'" and H2: "(WHILE b\<^sub>1 DO c, s') \<Rightarrow> t" by auto
    from H1 while_inv have "\<not> bval (Or b\<^sub>1 b\<^sub>2) s'" by simp
    then have "\<not> bval b\<^sub>1 s'" using Or_def by auto
    then have "s' = t" using H2 big_step_determ by auto
    with H1 show "(WHILE Or b\<^sub>1 b\<^sub>2 DO c, s) \<Rightarrow> t" by simp
  qed
qed

text\<open>
\endexercise

\exercise
Define a new loop construct @{text "DO c WHILE b"} (where @{text c} is
executed once before @{text b} is tested) in terms of the
existing constructs in @{typ com}:
\<close>

definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
  "DO c WHILE b = c;; WHILE b DO c"

text\<open>
Define a translation on commands that replaces all @{term "WHILE b DO c"}
by suitable commands that use @{term "DO c WHILE b"} instead:
\<close>

fun dewhile :: "com \<Rightarrow> com" where
  "dewhile (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = IF b THEN dewhile c\<^sub>1 ELSE dewhile c\<^sub>2" |
  "dewhile (WHILE b DO c) = IF b THEN DO dewhile c WHILE b ELSE SKIP" |
  "dewhile c = c"

text\<open> Prove that your translation preserves the semantics: \<close>

lemma sim_seq_cong: "\<lbrakk>c\<^sub>1 \<sim> c\<^sub>1'; c\<^sub>2 \<sim> c\<^sub>2'\<rbrakk> \<Longrightarrow> c\<^sub>1 ;; c\<^sub>2 \<sim> c\<^sub>1' ;; c\<^sub>2'" by blast
lemma sim_if_cong: "\<lbrakk>c\<^sub>1 \<sim> c\<^sub>1'; c\<^sub>2 \<sim> c\<^sub>2'\<rbrakk> \<Longrightarrow> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<sim> IF b THEN c\<^sub>1' ELSE c\<^sub>2'" by blast

declare sim_trans [trans add]

lemma "dewhile c \<sim> c"
proof (induct rule: dewhile.induct)
  case (2 b c)
  have "dewhile (WHILE b DO c) \<sim>
    IF b THEN dewhile c;; WHILE b DO dewhile c ELSE SKIP" using Do_def by simp
  also have "IF b THEN dewhile c;; WHILE b DO dewhile c ELSE SKIP \<sim>
    IF b THEN c;; WHILE b DO c ELSE SKIP" using 2 by (auto simp add: sim_if_cong sim_seq_cong sim_while_cong)
  also have "IF b THEN c;; WHILE b DO c ELSE SKIP \<sim> WHILE b DO c" by blast
  finally show ?case .
qed auto

declare sim_trans [trans del]

text\<open>
\endexercise

\exercise
Let @{text "C :: nat \<Rightarrow> com"} be an infinite sequence of commands and
@{text "S :: nat \<Rightarrow> state"} an infinite sequence of states such that
@{prop"C(0::nat) = c;;d"} and \mbox{@{prop"\<forall>n. (C n, S n) \<rightarrow> (C(Suc n), S(Suc n))"}}.
Then either all @{text"C n"} are of the form \mbox{@{term"c\<^sub>n;;d"}}
and it is always @{text c\<^sub>n} that is reduced or @{text c\<^sub>n} eventually becomes @{const SKIP}.
Prove
\<close>

lemma assumes H0: "C 0 = c;;d" and HI: "\<forall>n. (C n, S n) \<rightarrow> (C(Suc n), S(Suc n))"
shows "(\<forall>n. \<exists>c\<^sub>1 c\<^sub>2. C n = c\<^sub>1;;d \<and> C(Suc n) = c\<^sub>2;;d \<and>
                         (c\<^sub>1, S n) \<rightarrow> (c\<^sub>2, S(Suc n)))
     \<or> (\<exists>k. C k = SKIP;;d)" (is "(\<forall>i. ?P i) \<or> ?Q")
proof (cases ?Q)
  assume HnSKIP: "\<not>?Q"
  have "\<forall>i. ?P i"
  proof
    fix i
    show "?P i"
    proof (induct i)
      case 0
      from HI have "(C 0, S 0) \<rightarrow> (C (Suc 0), S (Suc 0))" by blast
      with H0 have "(c;;d, S 0) \<rightarrow> (C (Suc 0), S (Suc 0))" by simp
      then show ?case
      proof (cases rule: small_step.cases)
        case Seq1
        then have "C 0 = SKIP;; d" using H0 by simp
        with HnSKIP show ?thesis by blast
      next
        case (Seq2 c\<^sub>1')
        with H0 show ?thesis by simp
      qed
    next
      case (Suc i)
      then obtain c\<^sub>1 c\<^sub>2 where Hi: "C i = c\<^sub>1;; d"
        and HSi: "C (Suc i) = c\<^sub>2;; d"
        and HSS: "(c\<^sub>1, S i) \<rightarrow> (c\<^sub>2, S (Suc i))" by blast+
      from HI have "(C (Suc i), S (Suc i)) \<rightarrow> (C (Suc (Suc i)), S (Suc (Suc i)))" by blast
      with HSi have "(c\<^sub>2;; d, S (Suc i)) \<rightarrow> (C (Suc (Suc i)), S (Suc (Suc i)))" by simp
      then show ?case using HSi HnSKIP by (cases rule: small_step.cases) auto
    qed
  qed
  then show ?thesis by simp
qed simp

text\<open>
\endexercise
\bigskip

For the following exercises copy theories
@{short_theory "Com"}, @{short_theory "Big_Step"} and @{short_theory "Small_Step"}
and modify them as required. Those parts of the theories
that do not contribute to the results required in the exercise can be discarded.
If there are multiple proofs of the same result, you may update any one of them.

\begin{exercise}\label{exe:IMP:REPEAT}
Extend IMP with a @{text "REPEAT c UNTIL b"} command by adding the constructor
\begin{alltt}
  Repeat com bexp   ("(REPEAT _/ UNTIL _)"  [0, 61] 61)
\end{alltt}
to datatype @{typ com}.
Adjust the definitions of big-step and small-step semantics,
the proof that the big-step semantics is deterministic and
the equivalence proof between the two semantics.
\end{exercise}

\begin{exercise}\label{exe:IMP:OR}
Extend IMP with a new command @{text "c\<^sub>1 OR c\<^sub>2"} that is a
nondeterministic choice: it may execute either @{text
"c\<^sub>1"} or @{text "c\<^sub>2"}. Add the constructor
\begin{alltt}
  Or com com   ("_ OR/ _" [60, 61] 60)
\end{alltt}
to datatype @{typ com}. Adjust the definitions of big-step
and small-step semantics, prove @{text"(c\<^sub>1 OR c\<^sub>2) \<sim> (c\<^sub>2 OR c\<^sub>1)"}
and update the equivalence proof between the two semantics.
\end{exercise}

\begin{exercise}
Extend IMP with exceptions. Add two constructors @{text THROW} and
@{text "TRY c\<^sub>1 CATCH c\<^sub>2"} to datatype @{typ com}:
\begin{alltt}
  THROW  |  Try com com   ("(TRY _/ CATCH _)"  [0, 61] 61)
\end{alltt}
Command @{text THROW} throws an exception. The only command that can
catch an execption is @{text "TRY c\<^sub>1 CATCH c\<^sub>2"}: if an execption
is thrown by @{text c\<^sub>1}, execution continues with @{text c\<^sub>2},
otherwise @{text c\<^sub>2} is ignored.
Adjust the definitions of big-step and small-step semantics as follows.

The big-step semantics is now of type @{typ "com \<times> state \<Rightarrow> com \<times> state"}.
In a big step @{text "(c,s) \<Rightarrow> (x,t)"}, @{text x} can only be @{term SKIP}
(signalling normal termination) or @{text THROW} (signalling that an exception
was thrown but not caught).

The small-step semantics is of the same type as before. There are two final
configurations now, @{term "(SKIP, t)"} and @{term "(THROW, t)"}.
Exceptions propagate upwards until an enclosing handler is found.
That is, until a configuration @{text "(TRY THROW CATCH c, s)"}
is reached and @{text THROW} can be caught.

Adjust the equivalence proof between the two semantics such that you obtain
@{text "cs \<Rightarrow> (SKIP,t)  \<longleftrightarrow>  cs \<rightarrow>* (SKIP,t)"}
and @{text "cs \<Rightarrow> (THROW,t)  \<longleftrightarrow>  cs \<rightarrow>* (THROW,t)"}.
Also revise the proof of
\noquotes{@{prop [source] "(\<exists>cs'. cs \<Rightarrow> cs')  \<longleftrightarrow>  (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"}}.
\end{exercise}
\<close>

(* Short_Theory_7_8.thy *)
(* Short_Theory_7_9.thy *)
(* Short_Theory_7_10.thy *)

end

