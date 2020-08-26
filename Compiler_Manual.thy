theory Compiler_Manual
  imports "HOL-IMP.Big_Step" "HOL-IMP.Star"
begin
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))" |
  "[] !! i = undefined"

lemma inth_append [simp]: "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof (cases "i = 0")
    case True
    then show ?thesis by auto
  next
    case False
    with Cons(2) have Hle: "0 \<le> i - 1" by simp
    have "i - 1 - int (length xs) = i - (int (length xs) + 1)" by simp
    also have "\<dots> = i - int (length xs + 1)" by simp
    also have "\<dots> = i - int (length (a # xs))" by simp
    finally have 0: "i - 1 - int (length xs) = i - int (length (a # xs))" .
    have "((a # xs) @ ys) !! i = (a # xs @ ys) !! i" by simp
    also from False have "\<dots> = (xs @ ys) !! (i - 1)" by simp
    also from Cons(1) Hle have "\<dots> = (if i - 1 < int (length xs) then xs !! (i - 1) else ys !! (i - 1 - int (length xs)))" by simp
    also have "\<dots> = (if i < int (length xs) + 1 then xs !! (i - 1) else ys !! (i - int (length (a # xs))))" by (simp add: 0)
    also have "\<dots> = (if i < int (length (a # xs)) then xs !! (i - 1) else ys !! (i - int (length (a # xs))))" by simp
    also from Hle have "\<dots> = (if i < int (length (a # xs)) then (a # xs) !! i else ys !! (i - int (length (a # xs))))" by simp
    finally show ?thesis .
  qed
qed

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
code_pred exec1
proof -
  assume "x \<turnstile> (xa, xb, xc) \<rightarrow> (xd, xe, xf)"
  with exec1_def have "\<exists>i s stk. (xa, xb, xc) = (i, s, stk) \<and> (xd, xe, xf) = iexec (x !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size x" by simp
  then obtain xa' xb' xc' where "(xa, xb, xc) = (xa', xb', xc')" and "(xd, xe, xf) = iexec (x !! xa') (xa', xb', xc')" and "0 \<le> xa'" and "xa' < size x" by blast+
  then have 0: "(xd, xe, xf) = iexec (x !! xa) (xa, xb, xc)" and 1: "0 \<le> xa" and 2: "xa < size x" by auto
  assume "\<And>P i s stk c'. \<lbrakk>x = P; (xa, xb, xc) = (i, s, stk); (xd, xe, xf) = c'; c' = iexec (P !! i) (i, s, stk); 0 \<le> i; i < size P\<rbrakk> \<Longrightarrow> thesis"
  with refl [of "x"] refl [of "(xa, xb, xc)"] refl [of "(xd, xe, xf)"] 0 1 2 show thesis by simp
qed

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50) where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

(* proof by case analysis on instructions, and that each case changes the PC relative to its
  initial value
*)
lemma iexec_shift [simp]: 
  "(n + i', s', stk') = iexec x (n + i, s, stk) \<longleftrightarrow>
  (i', s', stk') = iexec x (i, s, stk)"
  by (cases x, auto)

(* trivial: iexec (P !! i) depends only on first i elements of P, and 0 \<le> i < size P *)
lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow> c'" unfolding exec1_def
proof -
  assume "\<exists>i s stk. c = (i, s, stk) \<and> c' = iexec (P !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P"
  then obtain i s stk where "c = (i, s, stk)" and "c' = iexec (P !! i) (i, s, stk)" and "0 \<le> i" and "i < size P" by blast+
  then have "c = (i, s, stk) \<and> c' = iexec ((P @ P') !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size (P @ P')" by auto+
  then show "\<exists>i s stk. c = (i, s, stk) \<and> c' = iexec ((P @ P') !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size (P @ P')" by blast
qed

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow>* c'"
proof (induct rule: star.induct)
  case (refl x)
  then show ?case by (rule star.refl)
next
  case (step x y z)
  from step(1) exec1_appendR have "P @ P' \<turnstile> x \<rightarrow> y" by simp
  with step(3) show ?case by (simp add: star.step)
qed

lemma exec1_appendL:
  fixes i i' :: int 
  shows "P \<turnstile> (i, s, stk) \<rightarrow> (i', s', stk') \<Longrightarrow>
    P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow> (size P' + i', s', stk')"
  by (auto simp add: exec1_def)

lemma exec_appendL:
  fixes i i' :: int 
  shows "P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')  \<Longrightarrow>
    P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow>* (size P' + i', s', stk')"
proof (induct rule: exec_induct)
  case (refl a aa b)
  then show ?case by (rule star.refl)
next
  case (step aa ab ac ba bb bc ca cb cc)
  from step(1) exec1_appendL have "P' @ P \<turnstile> (size P' + aa, ab, ac) \<rightarrow> (size P' + ba, bb, bc)" by simp
  with step(3) show ?case by (simp add: star.step)
qed

(* specialize append lemmas to discuss execution through concrete instructions
  while assuming the execution of preceding and following code.
*)
lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0, s, stk) \<rightarrow>* (j, t, stk') \<Longrightarrow>
  instr # P \<turnstile> (1, s, stk) \<rightarrow>* (1 + j, t, stk')"
proof (drule exec_appendL [where P'="[instr]"]) qed simp

(* as exec_appendL, with (i := i - size P'), precondition necessary to satisfy exec1 precondition *)
lemma exec_appendL_if [intro]:
  fixes i i' j :: int
  shows "size P' <= i \<Longrightarrow>
    P \<turnstile> (i - size P', s, stk) \<rightarrow>* (j, s', stk') \<Longrightarrow>
    i' = size P' + j \<Longrightarrow>
    P' @ P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')"
proof (drule exec_appendL [where P'=P']) qed simp

(* extend exec_appendL_if with an execution on the LHS. Note the premises here that are needed
  to satisfy the preconditions for exec_appendL
*)
lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows "P \<turnstile> (0, s, stk) \<rightarrow>* (i', s', stk') \<Longrightarrow>
    size P \<le> i' \<Longrightarrow>
    P' \<turnstile>  (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk'') \<Longrightarrow>
    j'' = size P + i'' \<Longrightarrow>
    P @ P' \<turnstile> (0, s, stk) \<rightarrow>* (j'', s'', stk'')"
proof (rule star_trans [OF exec_appendR exec_appendL_if])
  assume 0: "P \<turnstile> (0, s, stk) \<rightarrow>* (i', s', stk')"
    and 1: "size P \<le> i'"
    and 2: "P' \<turnstile> (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk'')"
    and 3: "j'' = size P + i''"
  from 0 show "P \<turnstile> (0, s, stk) \<rightarrow>* (i', s', stk')" .
  from 1 show "size P \<le> i'" .
  from 2 show "P' \<turnstile> (i' - size P, s', stk') \<rightarrow>* (i'', s'', stk'')" .
  from 3 show "j'' = size P + i''" .
qed
                                               
declare Let_def[simp]

subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
  "acomp (N n) = [LOADI n]" |
  "acomp (V x) = [LOAD x]" |
  "acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0, s, stk) \<rightarrow>* (size(acomp a), s, aval a s # stk)"
  by (induction a arbitrary: stk) fastforce+

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
proof(induction b arbitrary: f n)
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
  "ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
  "ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (let
    cc\<^sub>1 = ccomp c\<^sub>1;
    cc\<^sub>2 = ccomp c\<^sub>2;
    cb = bcomp b False (size cc\<^sub>1 + 1) in
    cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
  "ccomp (WHILE b DO c) = (let
    cc = ccomp c;
    cb = bcomp b False (size cc + 1) in
    cb @ cc @ [JMP (-(size cb + size cc + 1))])"

lemma ccomp_bigstep:
  "(c, s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp c), t, stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1" and ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0, s1 ,stk) \<rightarrow>* (size ?cc1, s2, stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1, s2, stk) \<rightarrow>* (size (?cc1 @ ?cc2), s3, stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  and ?cw = "ccomp(WHILE b DO c)"
  have "?cw \<turnstile> (0, s1, stk) \<rightarrow>* (size ?cb, s1, stk)"
    using \<open>bval b s1\<close> by fastforce
  moreover have "?cw \<turnstile> (size ?cb, s1, stk) \<rightarrow>* (size ?cb + size ?cc, s2, stk)"
    using WhileTrue.IH(1) by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc, s2, stk) \<rightarrow>* (0, s2, stk)"
    by fastforce
  moreover have "?cw \<turnstile> (0, s2, stk) \<rightarrow>* (size ?cw, s3, stk)" by (rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
qed fastforce+

end