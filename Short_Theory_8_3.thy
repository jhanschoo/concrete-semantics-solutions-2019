theory Short_Theory_8_3_2
  imports "HOL-IMP.Big_Step" "HOL-IMP.Star"
begin
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))" |
  "[] !! i = undefined"

lemma inth_append [simp]: "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induct xs arbitrary: i) (auto simp: algebra_simps)

abbreviation (output)
  "isize xs == int (length xs)"

notation isize ("size")

datatype instr = 
  LOADI int | LOAD vname |
  ADD |
  STORE vname |
  JMP int | JMPLESS int | JMPGE int

fun vars_in :: "instr list \<Rightarrow> vname list" where
  "vars_in [] = []" |
  "vars_in (LOAD x # P) = List.insert x (vars_in P)" |
  "vars_in (STORE x # P) = List.insert x (vars_in P)" |
  "vars_in (i # P) = vars_in P"

type_synonym addr = int
lemma vars_in_distinct: "distinct (vars_in P)"
proof (induct P)
  case (Cons a P)
  {
    fix x
    from Cons have "distinct (List.insert x (vars_in P))"
      by (cases "x \<in> set (vars_in P)") (auto simp add: Cons)
  }
  then show ?case  by (cases a) (auto simp add: Cons)
qed simp

fun nth_inv_P :: "instr list \<Rightarrow> vname \<Rightarrow> nat" where
  "nth_inv_P P = the_inv_into {..<length (vars_in P)} ((!) (vars_in P))"

fun addr_of :: "instr list \<Rightarrow> vname \<Rightarrow> int" where
  "addr_of P v = (if v \<in> set (vars_in P)
    then (int \<circ> nth_inv_P P) v
    else -1)"

lemma bij_addr_of: "bij_betw (addr_of P) (set (vars_in P)) (int ` {..<length (vars_in P)})"
proof -
  have "bij_betw ((!) (vars_in P)) {..<length (vars_in P)} (set (vars_in P))"
    by (rule bij_betw_nth, auto simp add: vars_in_distinct)
  then have 0: "bij_betw (nth_inv_P P) (set (vars_in P)) {..<length (vars_in P)}" (is ?P0)
    by (simp add: bij_betw_the_inv_into)
  have 1: "bij_betw int {..<length (vars_in P)} (int ` {..<length (vars_in P)})" (is ?P1) by simp
  thm bij_betw_comp_iff [OF 0, of int "(int ` {..<length (vars_in P)})"]
  have "?P1 \<longleftrightarrow>
    bij_betw (int \<circ> nth_inv_P P) (set (vars_in P)) (int ` {..<length (vars_in P)})" (is "?P1 \<longleftrightarrow> ?P2")
    by (rule bij_betw_comp_iff [OF 0])
  with 1 have 2: ?P2 by blast
  have "bij_betw (addr_of P) (set (vars_in P)) (int ` {..<length (vars_in P)}) \<longleftrightarrow> ?P2"
    by (rule bij_betw_cong, simp)
  with 2 show ?thesis by blast
qed

type_synonym stack = "val list"
type_synonym mem_state = "addr \<Rightarrow> val"
type_synonym addrs = "vname \<Rightarrow> addr"
type_synonym config = "int \<times> mem_state \<times> stack"

abbreviation "hd2 xs == hd (tl xs)"
abbreviation "tl2 xs == tl (tl xs)"

fun iexec :: "addrs \<Rightarrow> instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec a (LOADI n) (i, s, stk) = (i + 1, s, n # stk)" |
  "iexec a (LOAD x) (i, s, stk) = (i + 1, s, s (a x) # stk)" |
  "iexec a ADD (i, s, stk) = (i + 1, s, (hd2 stk + hd stk) # tl2 stk)" |
  "iexec a (STORE x) (i, s, stk) = (i + 1, s(a x := hd stk), tl stk)" |
  "iexec a (JMP n) (i, s, stk) = (i + 1 + n, s, stk)" |
  "iexec a (JMPLESS n) (i, s, stk) = (if hd2 stk < hd stk then i + 1 + n else i + 1, s, tl2 stk)" |
  "iexec a (JMPGE n) (i, s, stk) = (if hd2 stk >= hd stk then i + 1 + n else i + 1, s, tl2 stk)"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60)  where
  "P \<turnstile> c \<rightarrow> c' \<longleftrightarrow>
  (\<exists>i s stk. c = (i, s, stk) \<and> c' = iexec (addr_of P) (P !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P)"

(* an introduction rule that expects the LHS config parameters to already be known *)
lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (addr_of P) (P !! i) (i, s, stk) \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < size P \<Longrightarrow>
  P \<turnstile> (i, s, stk) \<rightarrow> c'"
  by (simp add: exec1_def)
code_pred exec1 by (metis exec1_def)

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50) where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

lemma iexec_shift [simp]: 
  "(n + i', s', stk') = iexec a x (n + i, s, stk) \<longleftrightarrow>
  (i', s', stk') = iexec a x (i, s, stk)"
  by (cases x, auto)

(* trivial: iexec (P !! i) depends only on first i elements of P, and 0 \<le> i < size P *)
lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow> c'" unfolding exec1_def
proof -
  assume "\<exists> i s stk. c = (i, s, stk) \<and> c' = iexec (addr_of P) (P !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P"
  then obtain i s stk where 0: "c = (i, s, stk)"
    and 1: "c' = iexec (addr_of P) (P !! i) (i, s, stk)"
    and 2: "0 \<le> i" and 3: "i < size P" by blast+
  from 3 have 4: "i < size (P @ P')" by auto
qed

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow>* c'"
  by (induct rule: star.induct) (blast intro: star.step exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int 
  shows "P \<turnstile> (i, s, stk) \<rightarrow> (i', s', stk') \<Longrightarrow>
    P' @ P \<turnstile> (size P' + i, s, stk) \<rightarrow> (size P' + i', s', stk')"
  by (auto simp add: exec1_def)

lemma exec_appendL:
  fixes i i' :: int 
  shows "P \<turnstile> (i, s, stk) \<rightarrow>* (i', s', stk')  \<Longrightarrow>
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
  fixes i i' j :: int
  shows "size P' <= i \<Longrightarrow>
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
  "acomp a \<turnstile> (0, s, stk) \<rightarrow>* (size(acomp a), s, aval a s # stk)"
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
    cb @ cc @ [JMP (-(size cb + size cc + 1))])"

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
  have "?cw \<turnstile> (0, s1, stk) \<rightarrow>* (size ?cb, s1, stk)" using \<open>bval b s1\<close> by fastforce
  moreover have "?cw \<turnstile> (size ?cb, s1, stk) \<rightarrow>* (size ?cb + size ?cc, s2, stk)"
    using WhileTrue(3) by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc, s2, stk) \<rightarrow>* (0, s2, stk)" by fastforce
  ultimately show ?case using WhileTrue(5) by(blast intro: star_trans)
qed fastforce+

end