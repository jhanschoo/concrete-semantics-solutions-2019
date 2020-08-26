theory Short_Theory_8_2
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

lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

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

declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))" |
  "[] !! i = undefined"

lemma inth_append [simp]: "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induct xs arbitrary: i) (auto simp: algebra_simps)

lemma nth_inth: "i < length (x # xs) \<Longrightarrow> (x # xs) !! i = (x # xs) ! i"
proof (induct xs arbitrary: i x)
  case (Cons a xs)
  then show ?case
  proof (cases "i = 0")
    case False
    from Cons False have Hl: "i - 1 < length (a # xs)" by auto
    from Cons(2) False have "(x # a # xs) !! int i = (a # xs) !! (int (i - 1))" using int_ops(6) by auto
    also from Cons(1) Hl have "\<dots> = (a # xs) ! (i - 1)" by blast
    also from Cons(2) False have "\<dots> = (x # a # xs) ! i" by simp
    finally show ?thesis .
  qed simp
qed simp

abbreviation (output)
  "isize xs == int (length xs)"

notation isize ("size")

datatype instr = 
  LOADI int | LOAD vname |
  ADD |
  STORE vname |
  JMP int | JMPLESS int | JMPGE int

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs == hd (tl xs)"
abbreviation "tl2 xs == tl (tl xs)"

(* note: by using hd / tl functions rather than pattern matching, we limit
  reliance on the structure of stk in the behavior of iexec, allowing us
  to simplify preconditions on lemmas that don't rely on the structure of
  the stack
*)
fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec (LOADI n) (i, s, stk) = (i + 1, s, n # stk)" |
  "iexec (LOAD x) (i, s, stk) = (i + 1, s, s x # stk)" |
  "iexec ADD (i, s, stk) = (i + 1, s, (hd2 stk + hd stk) # tl2 stk)" |
  "iexec (STORE x) (i, s, stk) = (i + 1, s(x := hd stk), tl stk)" |
  "iexec (JMP n) (i, s, stk) = (i + 1 + n, s, stk)" |
  "iexec (JMPLESS n) (i, s, stk) = (if hd2 stk < hd stk then i + 1 + n else i + 1, s, tl2 stk)" |
  "iexec (JMPGE n) (i, s, stk) = (if hd2 stk >= hd stk then i + 1 + n else i + 1, s, tl2 stk)"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60)  where
  "P \<turnstile> c \<rightarrow> c' \<longleftrightarrow>
  (\<exists>i s stk. c = (i, s, stk) \<and> c' = iexec (P !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P)"

(* an introduction rule that expects the LHS config parameters to already be known *)
lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P !! i) (i, s, stk) \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < size P \<Longrightarrow>
  P \<turnstile> (i, s, stk) \<rightarrow> c'"
  by (simp add: exec1_def)
code_pred exec1 by (metis exec1_def)

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50) where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

(* proof by case analysis on instructions, and that each case changes the PC relative to its
  initial value
*)
lemma iexec_shift [simp]: 
  "(n + i', s') = iexec x (n + i, s) \<longleftrightarrow>
  (i', s') = iexec x (i, s)"
proof -
  {
    fix fs' ss' fs ss
    have "(n + i', fs', ss') = iexec x (n + i, fs, ss) \<longleftrightarrow>
    (i', fs', ss') = iexec x (i, fs, ss)"
      by (cases x, auto)
  }
  then have "(n + i', fst s', snd s') = iexec x (n + i, fst s, snd s) \<longleftrightarrow>
  (i', fst s', snd s') = iexec x (i, fst s, snd s)" .
  then show "(n + i', s') = iexec x (n + i, s) \<longleftrightarrow>
  (i', s') = iexec x (i, s)" by simp
qed

(* trivial: iexec (P !! i) depends only on first i elements of P, and 0 \<le> i < size P *)
lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow> c'"
  by (auto simp add: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow>* c'"
  by (induct rule: star.induct) (blast intro: star.step exec1_appendR)+

lemma exec1_appendL: "P \<turnstile> (i, s, stk) \<rightarrow> (i', s', stk') \<Longrightarrow>
  P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow> (size P' + i', s', stk')"
  by (auto simp add: exec1_def)

lemma exec_appendL: "P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow>* (size P' + i', s', stk')"
  by (induct rule: exec_induct) (blast intro: star.step exec1_appendL)+

(* specialize append lemmas to discuss execution through concrete instructions
  while assuming the execution of preceding and following code.
*)
lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0, s, stk) \<rightarrow>* (j, t, stk') \<Longrightarrow>
  instr # P \<turnstile> (1, s, stk) \<rightarrow>* (1 + j, t, stk')"
  by (drule exec_appendL [where P'="[instr]"]) simp

(* as exec_appendL, with (i := i - size P'), precondition necessary to satisfy exec1 precondition *)
lemma exec_appendL_if [intro]:
  "size P' <= i \<Longrightarrow>
    P \<turnstile> (i - size P', s, stk) \<rightarrow>* (j, s', stk') \<Longrightarrow>
    i' = size P' + j \<Longrightarrow>
    P' @ P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')"
  by (drule exec_appendL [where P'=P']) simp

lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows "P \<turnstile> (0, s, stk) \<rightarrow>* (i', s', stk') \<Longrightarrow>
    size P \<le> i' \<Longrightarrow>
    P' \<turnstile>  (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk'') \<Longrightarrow>
    j'' = size P + i'' \<Longrightarrow>
    P @ P' \<turnstile> (0, s, stk) \<rightarrow>* (j'', s'', stk'')"
  by(metis star_trans [OF exec_appendR exec_appendL_if])
                                               
declare Let_def[simp]

subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
  "acomp (N n) = [LOADI n]" |
  "acomp (V x) = [LOAD x]" |
  "acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0, s, stk) \<rightarrow>* (size (acomp a), s, aval a s # stk)"
  by (induction a arbitrary: stk) fastforce+

(* f = True means that we intend to jump n spaces upon the expression evaluating to True, and
  step to next instruction upon the expression evaluating to False
  f = False means vice versa

  Suppose f = True in bcomp (And b1 b2). Then we want b1 to jump to just past b2 on False,
  (we know early that the And expression evaluates to False),
  and to continue with b2 on True. Thus we let cb1 = bcomp b1 False (size cb2)

  suppose f = False in bcomp (And b1 b2). Then we want b1 to jump to (size cb2 + n) on False
  (we know early that the And expression evaluates to False),
  and to continue with b2 on True.

  we have to have a JMP instruction to avoid jumping back from within the compiled bexp,
  since our analysis so far has assumed that we always jump forward
*)
fun bcomp :: "bexp \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> instr list" where
  "bcomp (Bc v) f n = (if v = f then [JMP n] else [])" |
  "bcomp (Not b) f n = bcomp b (\<not>f) n" |
  "bcomp (And b1 b2) f n = (let
    cb2 = bcomp b2 f n;
    m = if f
      then size cb2
      else size cb2 + n;
    cb1 = bcomp b1 False m in
    cb1 @ cb2)" |
  "bcomp (Less a1 a2) f n =
    acomp a1 @ acomp a2 @ (if f then [JMPLESS n] else [JMPGE n])"

lemma bcomp_correct[intro]:
  fixes n :: int
  shows
  "0 \<le> n \<Longrightarrow>
  bcomp b f n \<turnstile>
 (0, s, stk) \<rightarrow>* (size (bcomp b f n) + (if f = bval b s then n else 0), s, stk)"
proof (induct b arbitrary: f n)
  case Not
  from Not(1) [where f="\<not>f"] Not(2) show ?case by fastforce
next
  case (And b1 b2)
  from And(1)
    [of "if f then size (bcomp b2 f n) else size (bcomp b2 f n) + n" "False"]
    And(2) [of n f] And(3)
  show ?case by fastforce
qed fastforce+

fun ccomp :: "com \<Rightarrow> instr list" where
  "ccomp SKIP = []" |
  "ccomp (x ::= a) = acomp a @ [STORE x]" |
  "ccomp (c\<^sub>1;; c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
  "ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (let
    cc\<^sub>1 = ccomp c\<^sub>1;
    cc\<^sub>2 = ccomp c\<^sub>2;
    cb = bcomp b False (size cc\<^sub>1 + 1) in
    cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
  "ccomp (WHILE b DO c) = (let
    cc = ccomp c;
    cb = bcomp b False (size cc + 1) in
    cb @ cc @ [JMP (-(size cb + size cc + 1))])" |
  "ccomp (REPEAT c UNTIL b) = (let
    cc = ccomp c;
    cb = bcomp b True 1 in
    cc @ cb @ [JMP (-(size cc + size cb + 1))])"

lemma shift_bcomp: "\<And>m n. size (bcomp b f m) = size (bcomp b f n)"
proof (induct b arbitrary: f)
  case (And b1 b2)
  then show ?case
  proof auto
    assume H1: "\<And>f m n. length (bcomp b1 f m) = length (bcomp b1 f n)"
    assume H2: "\<And>f m n. length (bcomp b2 f m) = length (bcomp b2 f n)"
    from H2 have "size (bcomp b1 False (size (bcomp b2 True m))) + size (bcomp b2 True m) =
      size (bcomp b1 False (size (bcomp b2 True m))) + size (bcomp b2 True n)" by simp
    also from H1 have "\<dots> =
      size (bcomp b1 False (size (bcomp b2 True n))) + size (bcomp b2 True n)" by simp
    finally show "size (bcomp b1 False (size (bcomp b2 True m))) + size (bcomp b2 True m) =
      size (bcomp b1 False (size (bcomp b2 True n))) + size (bcomp b2 True n)" .
    from H2 have "size (bcomp b1 False (size (bcomp b2 False m) + m)) + size (bcomp b2 False m) =
      size (bcomp b1 False (size (bcomp b2 False m) + m)) + size (bcomp b2 False n)" by simp
    also from H1 have "\<dots> =
      size (bcomp b1 False (size (bcomp b2 False n) + n)) + size (bcomp b2 False n)" by simp
    finally show "size (bcomp b1 False (size (bcomp b2 False m) + m)) + size (bcomp b2 False m) =
      size (bcomp b1 False (size (bcomp b2 False n) + n)) + size (bcomp b2 False n)" .
  qed
qed simp+

lemma ccomp_bigstep:
  "(c, s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp c), t, stk)"
proof(induct arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1" and ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0, s1 ,stk) \<rightarrow>* (size ?cc1, s2, stk)"
    using Seq(2) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1, s2, stk) \<rightarrow>* (size (?cc1 @ ?cc2), s3, stk)"
    using Seq(4) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  and ?cw = "ccomp (WHILE b DO c)"
  have "?cw \<turnstile> (0, s1, stk) \<rightarrow>* (size ?cb, s1, stk)"
    using \<open>bval b s1\<close> by fastforce
  moreover have "?cw \<turnstile> (size ?cb, s1, stk) \<rightarrow>* (size ?cb + size ?cc, s2, stk)"
    using WhileTrue(3) by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc, s2, stk) \<rightarrow>* (0, s2, stk)" by fastforce
  ultimately show ?case using WhileTrue(5) by (blast intro: star_trans)
next
  case (RepeatFalse b s\<^sub>2 c s\<^sub>1 s\<^sub>3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b True 1"
    and ?cr = "ccomp (REPEAT c UNTIL b)"
  have "?cr \<turnstile> (0, s\<^sub>1, stk) \<rightarrow>* (size ?cc, s\<^sub>2, stk)" using RepeatFalse(3) by fastforce
  moreover have "?cr \<turnstile> (size ?cc, s\<^sub>2, stk) \<rightarrow>* (size ?cc + size ?cb, s\<^sub>2, stk)"
    using \<open>\<not> bval b s\<^sub>2\<close> by fastforce
  moreover have "?cr \<turnstile> (size ?cc + size ?cb, s\<^sub>2, stk) \<rightarrow>* (0, s\<^sub>2, stk)" by fastforce
  ultimately show ?case using RepeatFalse(5) by (blast intro: star_trans)
qed fastforce+

text \<open>
The preservation of the source code semantics is already shown in the 
parent theory \<open>Compiler\<close>. This here shows the second direction.
\<close>

subsection \<open>Definitions\<close>

text \<open>Execution in \<^term>\<open>n\<close> steps for simpler induction\<close>
primrec 
  exec_n :: "instr list \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" 
  ("_/ \<turnstile> (_ \<rightarrow>^_/ _)" [65,0,1000,55] 55)
where 
  "P \<turnstile> c \<rightarrow>^0 c' = (c'=c)" |
  "P \<turnstile> c \<rightarrow>^(Suc n) c'' = (\<exists>c'. (P \<turnstile> c \<rightarrow> c') \<and> P \<turnstile> c' \<rightarrow>^n c'')"

(* Note: big-step notation causes parsing ambiguity that isn't well-typed *)
text \<open>The possible successor PCs of an instruction at position \<^term>\<open>n\<close>\<close>

definition isuccs :: "instr \<Rightarrow> int \<Rightarrow> int set" where
  "isuccs i n = (case i of
    JMP j \<Rightarrow> {n + 1 + j} |
    JMPLESS j \<Rightarrow> {n + 1 + j, n + 1} |
    JMPGE j \<Rightarrow> {n + 1 + j, n + 1} |
    _ \<Rightarrow> {n +1})"

text \<open>The possible successors PCs of an instruction list starting from position n of P to its end\<close>
definition succs :: "instr list \<Rightarrow> int \<Rightarrow> int set" where
  "succs P n = {s. \<exists>i\<ge>0. i < size P \<and> s \<in> isuccs (P !! i) (n + i)}" 

text \<open>Possible exit PCs of a program\<close>
definition exits :: "instr list \<Rightarrow> int set" where
  "exits P = succs P 0 - {0..<size P}"

  
subsection \<open>Basic properties of \<^term>\<open>exec_n\<close>\<close>

lemma exec_n_exec:
  "P \<turnstile> c \<rightarrow>^n c' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c'"
  by (induct n arbitrary: c) (auto intro: star.step)

lemma exec_0 [intro!]: "P \<turnstile> c \<rightarrow>^0 c" by simp

lemma exec_Suc:
  "\<lbrakk>P \<turnstile> c \<rightarrow> c'; P \<turnstile> c' \<rightarrow>^n c''\<rbrakk> \<Longrightarrow> P \<turnstile> c \<rightarrow>^(Suc n) c''" 
  by (fastforce simp del: split_paired_Ex)

lemma exec_exec_n:
  "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> \<exists>n. P \<turnstile> c \<rightarrow>^n c'"
  by (induct rule: star.induct) (auto intro: exec_Suc)
    
lemma exec_eq_exec_n:
  "(P \<turnstile> c \<rightarrow>* c') = (\<exists>n. P \<turnstile> c \<rightarrow>^n c')"
  by (blast intro: exec_exec_n exec_n_exec)

lemma exec_n_Nil [simp]:
  "[] \<turnstile> c \<rightarrow>^k c' = (c' = c \<and> k = 0)"
  by (induct k) (auto simp: exec1_def)

lemma exec1_exec_n [intro!]:
  "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c \<rightarrow>^1 c'"
  by (cases c') simp


subsection \<open>Concrete symbolic execution steps\<close>

lemma exec_n_step:
  "n \<noteq> n' \<Longrightarrow> 
  P \<turnstile> (n,stk,s) \<rightarrow>^k (n',stk',s') = 
  (\<exists>c. P \<turnstile> (n,stk,s) \<rightarrow> c \<and> P \<turnstile> c \<rightarrow>^(k - 1) (n',stk',s') \<and> 0 < k)"
  by (cases k) auto

text \<open>Note: fst c refers to the program counter\<close>
lemma exec1_end:
  "size P \<le> fst c \<Longrightarrow> \<not> P \<turnstile> c \<rightarrow> c'"
  by (auto simp: exec1_def)

lemma exec_n_end:
  "size P \<le> (n::int) \<Longrightarrow> 
  P \<turnstile> (n,s,stk) \<rightarrow>^k (n',s',stk') = (n' = n \<and> stk'=stk \<and> s'=s \<and> k =0)"
  by (cases k) (auto simp: exec1_end)

lemmas exec_n_simps = exec_n_step exec_n_end

subsection \<open>Basic properties of \<^term>\<open>succs\<close>\<close>

lemma succs_simps [simp]: 
  "succs [ADD] n = {n + 1}"
  "succs [LOADI v] n = {n + 1}"
  "succs [LOAD x] n = {n + 1}"
  "succs [STORE x] n = {n + 1}"
  "succs [JMP i] n = {n + 1 + i}"
  "succs [JMPGE i] n = {n + 1 + i, n + 1}"
  "succs [JMPLESS i] n = {n + 1 + i, n + 1}"
  by (auto simp: succs_def isuccs_def)

lemma succs_empty [iff]: "succs [] n = {}"
  by (simp add: succs_def)

lemma succs_Cons:
  "succs (x # xs) n = isuccs x n \<union> succs xs (1 + n)" (is "_ = ?x \<union> ?xs")
proof
  let ?isuccs = "\<lambda>p P n i::int. 0 \<le> i \<and> i < size P \<and> p \<in> isuccs (P!!i) (n+i)"
  have "p \<in> ?x \<union> ?xs" if assm: "p \<in> succs (x#xs) n" for p
  proof -
    from assm obtain i::int where isuccs: "?isuccs p (x#xs) n i"
      unfolding succs_def by auto
    show ?thesis
    proof cases
      assume "i = 0" with isuccs show ?thesis by simp
    next
      assume "i \<noteq> 0" 
      with isuccs 
      have "?isuccs p xs (1+n) (i - 1)" by auto
      hence "p \<in> ?xs" unfolding succs_def by blast
      thus ?thesis .. 
    qed
  qed
  thus "succs (x#xs) n \<subseteq> ?x \<union> ?xs" ..

  have "p \<in> succs (x#xs) n" if assm: "p \<in> ?x \<or> p \<in> ?xs" for p
  proof -
    from assm show ?thesis
    proof
      assume "p \<in> ?x" thus ?thesis by (fastforce simp: succs_def)
    next
      assume "p \<in> ?xs"
      then obtain i where "?isuccs p xs (1+n) i"
        unfolding succs_def by auto
      hence "?isuccs p (x#xs) n (1+i)"
        by (simp add: algebra_simps)
      thus ?thesis unfolding succs_def by blast
    qed
  qed
  thus "?x \<union> ?xs \<subseteq> succs (x#xs) n" by blast
qed

lemma succs_iexec1:
  assumes "c' = iexec (P!!i) (i, s, stk)" "0 \<le> i" "i < size P"
  shows "fst c' \<in> succs P 0"
  using assms by (cases "P !! i", auto simp: succs_def isuccs_def)

lemma succs_shift:
  "(p - n \<in> succs P 0) = (p \<in> succs P n)" 
  by (fastforce simp: succs_def isuccs_def split: instr.split)
  
lemma inj_op_plus [simp]:
  "inj ((+) (i::int))"
  by (rule Fun.cancel_semigroup_add_class.inj_add_left)

lemma succs_set_shift [simp]:
  "(+) i ` succs xs 0 = succs xs i"
  by (force simp: succs_shift [where n=i, symmetric] intro: set_eqI)

lemma succs_append [simp]:
  "succs (xs @ ys) n = succs xs n \<union> succs ys (n + size xs)"
  by (induct xs arbitrary: n) (auto simp: succs_Cons algebra_simps)

lemma exits_append [simp]:
  "exits (xs @ ys) = exits xs \<union> ((+) (size xs)) ` exits ys - 
                     {0..<size xs + size ys}" 
  by (auto simp: exits_def image_set_diff)
  
lemma exits_single:
  "exits [x] = isuccs x 0 - {0}"
  by (auto simp: exits_def succs_def)
  
lemma exits_Cons:
  "exits (x # xs) = (isuccs x 0 - {0}) \<union> ((+) 1) ` exits xs - 
                     {0..<1 + size xs}" 
  using exits_append [of "[x]" xs]
  by (simp add: exits_single)

lemma exits_empty [iff]: "exits [] = {}" by (simp add: exits_def)

lemma exits_simps [simp]:
  "exits [ADD] = {1}"
  "exits [LOADI v] = {1}"
  "exits [LOAD x] = {1}"
  "exits [STORE x] = {1}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMP i] = {1 + i}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMPGE i] = {1 + i, 1}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMPLESS i] = {1 + i, 1}"
  by (auto simp: exits_def)

lemma acomp_succs [simp]:
  "succs (acomp a) n = {n + 1 .. n + size (acomp a)}"
  by (induct a arbitrary: n) auto

lemma acomp_size:
  "(1::int) \<le> size (acomp a)"
  by (induct a) auto

(* consequence of acomp_succs *)
lemma acomp_exits [simp]:
  "exits (acomp a) = {size (acomp a)}"
  using [[simp_trace]]
  by (auto simp: exits_def acomp_size)

(* successors of bcomp bounded above by bcomp instructions themselves (plus one),
  and the jumped-to address *)
lemma bcomp_succs: "0 \<le> i \<Longrightarrow>
  succs (bcomp b f i) n \<subseteq> {n..n + size (bcomp b f i)} \<union> {n + i + size (bcomp b f i)}" 
proof (induction b arbitrary: f i n)
  case (And b1 b2)
  from And.prems
  show ?case 
    by (cases f)
       (auto dest: And.IH(1) [THEN subsetD, rotated] 
                   And.IH(2) [THEN subsetD, rotated])
qed auto

lemmas bcomp_succsD [dest!] = bcomp_succs [THEN subsetD, rotated]

lemma bcomp_exits:
  "0 \<le> i \<Longrightarrow>
  exits (bcomp b f i) \<subseteq> {size (bcomp b f i), i + size (bcomp b f i)}" 
  by (auto simp: exits_def)
  
lemma bcomp_exitsD [dest!]:
  "p \<in> exits (bcomp b f i) \<Longrightarrow> 0 \<le> i \<Longrightarrow> 
  p = size (bcomp b f i) \<or> p = i + size (bcomp b f i)"
  using bcomp_exits by auto

lemma ccomp_succs:
  "succs (ccomp c) n \<subseteq> {n..n + size (ccomp c)}"
proof (induction c arbitrary: n)
  case SKIP thus ?case by simp
next
  case Assign thus ?case by simp
next
  case (Seq c1 c2)
  from Seq.prems
  show ?case 
    by (fastforce dest: Seq.IH [THEN subsetD])
next
  case (If b c1 c2)
  from If.prems
  show ?case
    by (auto dest!: If.IH [THEN subsetD] simp: isuccs_def succs_Cons)
next
  case (While b c)
  from While.prems
  show ?case by (auto dest!: While.IH [THEN subsetD])
next
  case (Repeat c x2)
  from Repeat.prems
  show ?case by (auto dest!: Repeat.IH [THEN subsetD])
qed

lemma ccomp_exits:
  "exits (ccomp c) \<subseteq> {size (ccomp c)}"
  using ccomp_succs [of c 0] by (auto simp: exits_def)

lemma ccomp_exitsD [dest!]:
  "p \<in> exits (ccomp c) \<Longrightarrow> p = size (ccomp c)"
  using ccomp_exits by auto


subsection \<open>Splitting up machine executions\<close>

lemma exec1_split:
  fixes i j :: int
  shows
  "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (j,s') \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size c \<Longrightarrow> 
  c \<turnstile> (i,s) \<rightarrow> (j - size P, s')"
proof -
  assume assm: "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (j, s')" "0 \<le> i" "i < size c"
  from assm(1) have "(\<exists>ii ss stk. (size P + i, s) = (ii, ss, stk) \<and>
    (j, s') = iexec ((P @ c @ P') !! ii) (ii, ss, stk) \<and>
    0 \<le> ii \<and> ii < size (P @ c @ P'))"
    using exec1_def by simp
  then obtain ii ss stk where assm1: "(size P + i, s) = (ii, ss, stk)"
    "(j, s') = iexec ((P @ c @ P') !! ii) (ii, ss, stk)"
    "0 \<le> ii" "ii < size (P @ c @ P')" by auto
  from assm1(1) assm(2, 3) have "(P @ c @ P') !! ii = c !! i" by auto
  with assm1(2) have "(j, s') = iexec (c !! i) (ii, ss, stk)" by simp
  with assm1(1) have "(j, s') = iexec (c !! i) (size P + i, ss, stk)" by simp
  then have "((- size P) + j, s') = iexec (c !! i) ((- size P) + (size P + i), ss, stk)"
    using iexec_shift by (fastforce intro: iexec_shift)
  then have "(j - size P, s') = iexec (c !! i) (i, ss, stk)" by simp
  with assm(2, 3) assm1(1) show "c \<turnstile> (i, s) \<rightarrow> (j - size P, s')" by auto
qed

lemma exec_n_split:
  fixes i j :: int
  assumes "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow>^n (j, s')"
          "0 \<le> i" "i < size c" 
          "j \<notin> {size P ..< size P + size c}"
  shows "\<exists>s'' (i'::int) k m. 
                   c \<turnstile> (i, s) \<rightarrow>^k (i', s'') \<and>
                   i' \<in> exits c \<and> 
                   P @ c @ P' \<turnstile> (size P + i', s'') \<rightarrow>^m (j, s') \<and>
                   n = k + m" 
using assms proof (induction n arbitrary: i j s)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have i: "0 \<le> i" "i < size c" by fact+
  from Suc.prems
  have j: "\<not> (size P \<le> j \<and> j < size P + size c)" by simp
  from Suc.prems 
  obtain i0 s0 where
    step: "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (i0,s0)" and
    rest: "P @ c @ P' \<turnstile> (i0,s0) \<rightarrow>^n (j, s')"
    by clarsimp

  from step i
  have c: "c \<turnstile> (i,s) \<rightarrow> (i0 - size P, s0)" by (rule exec1_split)

  have "i0 = size P + (i0 - size P) " by simp
  then obtain j0::int where j0: "i0 = size P + j0"  ..

  note split_paired_Ex [simp del]

  have ?case if assm: "j0 \<in> {0 ..< size c}"
  proof -
    from assm j0 j rest c show ?case
      by (fastforce dest!: Suc.IH intro!: exec_Suc)
  qed
  moreover
  have ?case if assm: "j0 \<notin> {0 ..< size c}"
  proof -
    from c j0 have "j0 \<in> succs c 0"
      by (auto dest: succs_iexec1 simp: exec1_def simp del: iexec.simps)
    with assm have "j0 \<in> exits c" by (simp add: exits_def)
    with c j0 rest show ?case by fastforce
  qed
  ultimately
  show ?case by cases
qed

lemma exec_n_drop_right:
  fixes j :: int
  assumes "c @ P' \<turnstile> (0, s) \<rightarrow>^n (j, s')" "j \<notin> {0..<size c}"
  shows "\<exists>s'' i' k m. 
          (if c = [] then s'' = s \<and> i' = 0 \<and> k = 0
           else c \<turnstile> (0, s) \<rightarrow>^k (i', s'') \<and>
           i' \<in> exits c) \<and> 
           c @ P' \<turnstile> (i', s'') \<rightarrow>^m (j, s') \<and>
           n = k + m"
  using assms
  by (cases "c = []")
     (auto dest: exec_n_split [where P="[]", simplified])
  

text \<open>
  Dropping the left context of a potentially incomplete execution of \<^term>\<open>c\<close>.
\<close>

lemma exec1_drop_left:
  fixes i n :: int
  assumes "P1 @ P2 \<turnstile> (i, s, stk) \<rightarrow> (n, s', stk')" and "size P1 \<le> i"
  shows "P2 \<turnstile> (i - size P1, s, stk) \<rightarrow> (n - size P1, s', stk')"
proof -
  have "i = size P1 + (i - size P1)" by simp 
  then obtain i' :: int where "i = size P1 + i'" ..
  moreover
  have "n = size P1 + (n - size P1)" by simp 
  then obtain n' :: int where "n = size P1 + n'" ..
  ultimately 
  show ?thesis using assms 
    by (clarsimp simp: exec1_def simp del: iexec.simps)
qed

lemma exec_n_drop_left:
  fixes i n :: int
  assumes "P @ P' \<turnstile> (i, s, stk) \<rightarrow>^k (n, s', stk')"
          "size P \<le> i" "exits P' \<subseteq> {0..}"
  shows "P' \<turnstile> (i - size P, s, stk) \<rightarrow>^k (n - size P, s', stk')"
using assms proof (induction k arbitrary: i s stk)
  case 0 thus ?case by simp
next
  case (Suc k)
  from Suc.prems
  obtain i' s'' stk'' where
    step: "P @ P' \<turnstile> (i, s, stk) \<rightarrow> (i', s'', stk'')" and
    rest: "P @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^k (n, s', stk')"
    by auto
  from step \<open>size P \<le> i\<close>
  have *: "P' \<turnstile> (i - size P, s, stk) \<rightarrow> (i' - size P, s'', stk'')" 
    by (rule exec1_drop_left)
  then have "i' - size P \<in> succs P' 0"
    by (fastforce dest!: succs_iexec1 simp: exec1_def simp del: iexec.simps)
  with \<open>exits P' \<subseteq> {0..}\<close>
  have "size P \<le> i'" by (auto simp: exits_def)
  from rest this \<open>exits P' \<subseteq> {0..}\<close>     
  have "P' \<turnstile> (i' - size P, s'', stk'') \<rightarrow>^k (n - size P, s', stk')"
    by (rule Suc.IH)
  with * show ?case by auto
qed

lemmas exec_n_drop_Cons = 
  exec_n_drop_left [where P="[instr]", simplified] for instr

definition
  "closed P \<longleftrightarrow> exits P \<subseteq> {size P}" 

lemma ccomp_closed [simp, intro!]: "closed (ccomp c)"
  using ccomp_exits by (auto simp: closed_def)

lemma acomp_closed [simp, intro!]: "closed (acomp c)"
  by (simp add: closed_def)

lemma exec_n_split_full:
  fixes j :: int
  assumes exec: "P @ P' \<turnstile> (0,s,stk) \<rightarrow>^k (j, s', stk')"
  assumes P: "size P \<le> j" 
  assumes closed: "closed P"
  assumes exits: "exits P' \<subseteq> {0..}"
  shows "\<exists>k1 k2 s'' stk''. P \<turnstile> (0,s,stk) \<rightarrow>^k1 (size P, s'', stk'') \<and> 
                           P' \<turnstile> (0,s'',stk'') \<rightarrow>^k2 (j - size P, s', stk')"
proof (cases "P")
  case Nil with exec
  show ?thesis by fastforce
next
  case Cons
  hence "0 < size P" by simp
  with exec P closed
  obtain k1 k2 s'' stk'' where
    1: "P \<turnstile> (0,s,stk) \<rightarrow>^k1 (size P, s'', stk'')" and
    2: "P @ P' \<turnstile> (size P,s'',stk'') \<rightarrow>^k2 (j, s', stk')"
    by (auto dest!: exec_n_split [where P="[]" and i=0, simplified] 
             simp: closed_def)
  moreover
  have "j = size P + (j - size P)" by simp
  then obtain j0 :: int where "j = size P + j0" ..
  ultimately
  show ?thesis using exits
    by (fastforce dest: exec_n_drop_left)
qed


subsection \<open>Correctness theorem\<close>

lemma acomp_neq_Nil [simp]:
  "acomp a \<noteq> []"
  by (induct a) auto

lemma acomp_exec_n [dest!]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>^n (size (acomp a),s',stk') \<Longrightarrow> 
  s' = s \<and> stk' = aval a s#stk"
proof (induction a arbitrary: n s' stk stk')
  case (Plus a1 a2)
  let ?sz = "size (acomp a1) + (size (acomp a2) + 1)"
  from Plus.prems
  have "acomp a1 @ acomp a2 @ [ADD] \<turnstile> (0,s,stk) \<rightarrow>^n (?sz, s', stk')" 
    by (simp add: algebra_simps)
      
  then obtain n1 s1 stk1 n2 s2 stk2 n3 where 
    "acomp a1 \<turnstile> (0,s,stk) \<rightarrow>^n1 (size (acomp a1), s1, stk1)"
    "acomp a2 \<turnstile> (0,s1,stk1) \<rightarrow>^n2 (size (acomp a2), s2, stk2)" 
       "[ADD] \<turnstile> (0,s2,stk2) \<rightarrow>^n3 (1, s', stk')"
    by (auto dest!: exec_n_split_full)

  thus ?case by (fastforce dest: Plus.IH simp: exec_n_simps exec1_def)
qed (auto simp: exec_n_simps exec1_def)

lemma bcomp_split:
  fixes i j :: int
  assumes "bcomp b f i @ P' \<turnstile> (0, s, stk) \<rightarrow>^n (j, s', stk')" 
          "j \<notin> {0..<size (bcomp b f i)}" "0 \<le> i"
  shows "\<exists>s'' stk'' (i'::int) k m. 
           bcomp b f i \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'') \<and>
           (i' = size (bcomp b f i) \<or> i' = i + size (bcomp b f i)) \<and>
           bcomp b f i @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^m (j, s', stk') \<and>
           n = k + m"
  using assms by (cases "bcomp b f i = []") (fastforce dest!: exec_n_drop_right)+

lemma bcomp_exec_n [dest]:
  fixes i j :: int
  assumes "bcomp b f j \<turnstile> (0, s, stk) \<rightarrow>^n (i, s', stk')"
          "size (bcomp b f j) \<le> i" "0 \<le> j"
  shows "i = size(bcomp b f j) + (if f = bval b s then j else 0) \<and>
         s' = s \<and> stk' = stk"
using assms proof (induction b arbitrary: f j i n s' stk')
  case Bc thus ?case 
    by (simp split: if_split_asm add: exec_n_simps exec1_def)
next
  case (Not b) 
  from Not.prems show ?case
    by (fastforce dest!: Not.IH) 
next
  case (And b1 b2)
  
  let ?b2 = "bcomp b2 f j" 
  let ?m  = "if f then size ?b2 else size ?b2 + j"
  let ?b1 = "bcomp b1 False ?m" 

  have j: "size (bcomp (And b1 b2) f j) \<le> i" "0 \<le> j" by fact+
  
  from And.prems
  obtain s'' stk'' and i'::int and k m where 
    b1: "?b1 \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'')"
        "i' = size ?b1 \<or> i' = ?m + size ?b1" and
    b2: "?b2 \<turnstile> (i' - size ?b1, s'', stk'') \<rightarrow>^m (i - size ?b1, s', stk')"
    by (auto dest!: bcomp_split dest: exec_n_drop_left)
  from b1 j
  have "i' = size ?b1 + (if \<not>bval b1 s then ?m else 0) \<and> s'' = s \<and> stk'' = stk"
    by (auto dest!: And.IH)
  with b2 j
  show ?case 
    by (fastforce dest!: And.IH simp: exec_n_end split: if_split_asm)
next
  case Less
  thus ?case by (auto dest!: exec_n_split_full simp: exec_n_simps exec1_def) (* takes time *) 
qed

lemma ccomp_empty [elim!]:
  "ccomp c = [] \<Longrightarrow> (c,s) \<Rightarrow> s"
  by (induct c) auto

declare assign_simp [simp]

lemma ccomp_exec_n:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>^n (size(ccomp c),t,stk')
  \<Longrightarrow> (c,s) \<Rightarrow> t \<and> stk'=stk"
proof (induction c arbitrary: s t stk stk' n)
  case SKIP
  thus ?case by auto
next
  case (Assign x a)
  thus ?case
    by simp (fastforce dest!: exec_n_split_full simp: exec_n_simps exec1_def)
next
  case (Seq c1 c2)
  thus ?case by (fastforce dest!: exec_n_split_full)
next
  case (If b c1 c2)
  note If.IH [dest!]

  let ?if = "IF b THEN c1 ELSE c2"
  let ?cs = "ccomp ?if"
  let ?bcomp = "bcomp b False (size (ccomp c1) + 1)"
  
  from \<open>?cs \<turnstile> (0,s,stk) \<rightarrow>^n (size ?cs,t,stk')\<close>
  obtain i' :: int and k m s'' stk'' where
    cs: "?cs \<turnstile> (i',s'',stk'') \<rightarrow>^m (size ?cs,t,stk')" and
        "?bcomp \<turnstile> (0,s,stk) \<rightarrow>^k (i', s'', stk'')" 
        "i' = size ?bcomp \<or> i' = size ?bcomp + size (ccomp c1) + 1"
    by (auto dest!: bcomp_split)

  hence i':
    "s''=s" "stk'' = stk" 
    "i' = (if bval b s then size ?bcomp else size ?bcomp+size(ccomp c1)+1)"
    by auto
  
  with cs have cs':
    "ccomp c1@JMP (size (ccomp c2))#ccomp c2 \<turnstile> 
       (if bval b s then 0 else size (ccomp c1)+1, s, stk) \<rightarrow>^m
       (1 + size (ccomp c1) + size (ccomp c2), t, stk')"
    by (fastforce dest: exec_n_drop_left simp: exits_Cons isuccs_def algebra_simps)
     
  show ?case
  proof (cases "bval b s")
    case True with cs'
    show ?thesis
      by simp
         (fastforce dest: exec_n_drop_right 
                   split: if_split_asm
                   simp: exec_n_simps exec1_def)
  next
    case False with cs'
    show ?thesis
      by (auto dest!: exec_n_drop_Cons exec_n_drop_left 
               simp: exits_Cons isuccs_def)
  qed
next
  case (While b c)

  from While.prems
  show ?case
  proof (induction n arbitrary: s rule: nat_less_induct)
    case (1 n)

    have ?case if assm: "\<not> bval b s"
    proof -
      from assm "1.prems"
      show ?case
        by simp (fastforce dest!: bcomp_split simp: exec_n_simps)
    qed
    moreover
    have ?case if b: "bval b s"
    proof -
      let ?c0 = "WHILE b DO c"
      let ?cs = "ccomp ?c0"
      let ?bs = "bcomp b False (size (ccomp c) + 1)"
      let ?jmp = "[JMP (-((size ?bs + size (ccomp c) + 1)))]"
      
      from "1.prems" b
      obtain k where
        cs: "?cs \<turnstile> (size ?bs, s, stk) \<rightarrow>^k (size ?cs, t, stk')" and
        k:  "k \<le> n"
        by (fastforce dest!: bcomp_split)
      
      show ?case
      proof cases
        assume "ccomp c = []"
        with cs k
        obtain m where
          "?cs \<turnstile> (0,s,stk) \<rightarrow>^m (size (ccomp ?c0), t, stk')"
          "m < n"
          by (auto simp: exec_n_step [where k=k] exec1_def)
        with "1.IH"
        show ?case by blast
      next
        assume "ccomp c \<noteq> []"
        with cs
        obtain m m' s'' stk'' where
          c: "ccomp c \<turnstile> (0, s, stk) \<rightarrow>^m' (size (ccomp c), s'', stk'')" and 
          rest: "?cs \<turnstile> (size ?bs + size (ccomp c), s'', stk'') \<rightarrow>^m 
                       (size ?cs, t, stk')" and
          m: "k = m + m'"
          by (auto dest: exec_n_split [where i=0, simplified])
        from c
        have "(c,s) \<Rightarrow> s''" and stk: "stk'' = stk"
          by (auto dest!: While.IH)
        moreover
        from rest m k stk
        obtain k' where
          "?cs \<turnstile> (0, s'', stk) \<rightarrow>^k' (size ?cs, t, stk')"
          "k' < n"
          by (auto simp: exec_n_step [where k=m] exec1_def)
        with "1.IH"
        have "(?c0, s'') \<Rightarrow> t \<and> stk' = stk" by blast
        ultimately
        show ?case using b by blast
      qed
    qed
    ultimately show ?case by cases
  qed
next
  case (Repeat c x2)
  from Repeat.prems
  show ?case
  proof (induction n arbitrary: s rule: nat_less_induct)
    case (1 n)
    then show ?case sorry
  qed
qed

theorem ccomp_exec:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk') \<Longrightarrow> (c,s) \<Rightarrow> t"
  by (auto dest: exec_exec_n ccomp_exec_n)

corollary ccomp_sound:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)  \<longleftrightarrow>  (c,s) \<Rightarrow> t"
  by (blast intro!: ccomp_exec ccomp_bigstep)

end