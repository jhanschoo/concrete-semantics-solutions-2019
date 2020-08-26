theory Short_Theory_8_3_1
  imports "HOL-IMP.Big_Step" "HOL-IMP.Star"
begin
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

subsection "mmap setup"

lemma bij_cancel_r [simp]: "\<lbrakk>bij b; f \<circ> b = g \<circ> b\<rbrakk> \<Longrightarrow> f = g"
  by (metis bij_betw_def surj_fun_eq)

lemma bij_comp_update [simp]: "bij b \<Longrightarrow> (f \<circ> b) (x := y) = (f ((b x) := y)) \<circ> b"
proof
  fix xa
  assume "bij b"
  show "((f \<circ> b)(x := y)) xa = (f(b x := y) \<circ> b) xa"
  proof (cases "xa = x")
    case False
    then have "((f \<circ> b)(x := y)) xa = f (b xa)" by simp
    also from \<open>bij b\<close> False have "b xa \<noteq> b x" by (meson bij_def inj_def)
    then have "f (b xa) = (f(b x := y) \<circ> b) xa" by simp
    finally show ?thesis .
  qed simp
qed

lemma bij_cancel_r2: "bij b \<Longrightarrow> \<exists> g. f = g \<circ> b" by (metis bij_is_inj o_inv_o_cancel)

subsection "List setup"

fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))" |
  "[] !! i = undefined"

lemma inth_append [simp]: "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induct xs arbitrary: i) (auto simp: algebra_simps)

abbreviation (output) "isize xs == int (length xs)"

notation isize ("size")

subsection "Instructions and Stack Machine"

type_synonym addr = int

datatype instr = 
  LOADI int | LOAD addr |
  ADD |
  STORE addr |
  JMP int | JMPLESS int | JMPGE int

type_synonym stack = "val list"
type_synonym mem_state = "addr \<Rightarrow> val"
type_synonym mmap = "vname \<Rightarrow> addr"
type_synonym config = "int \<times> mem_state \<times> stack"

abbreviation "hd2 xs == hd (tl xs)"
abbreviation "tl2 xs == tl (tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec (LOADI n) (i, s, stk) = (i + 1, s, n # stk)" |
  "iexec (LOAD a) (i, s, stk) = (i + 1, s, s a # stk)" |
  "iexec ADD (i, s, stk) = (i + 1, s, (hd2 stk + hd stk) # tl2 stk)" |
  "iexec (STORE a) (i, s, stk) = (i + 1, s(a := hd stk), tl stk)" |
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

subsection\<open>Verification infrastructure\<close>

lemma iexec_shift [simp]: 
  "(n + i', s', stk') = iexec x (n + i, s, stk) \<longleftrightarrow>
  (i', s', stk') = iexec x (i, s, stk)"
  by (cases x, auto)

(* trivial: iexec (P !! i) depends only on first i elements of P, and 0 \<le> i < size P *)
lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow> c'"
  by (auto simp add: exec1_def)

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

fun acomp :: "mmap \<Rightarrow> aexp \<Rightarrow> instr list" where
  "acomp m (N n) = [LOADI n]" |
  "acomp m (V x) = [LOAD (m x)]" |
  "acomp m (Plus a1 a2) = acomp m a1 @ acomp m a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp m a \<turnstile> (0, s, stk) \<rightarrow>* (size (acomp m a), s, aval a (s \<circ> m) # stk)"
  by (induction a arbitrary: stk) fastforce+

fun bcomp :: "mmap \<Rightarrow> bexp \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> instr list" where
  "bcomp m (Bc v) f n = (if v = f then [JMP n] else [])" |
  "bcomp m (Not b) f n = bcomp m b (\<not>f) n" |
  "bcomp m (And b1 b2) f n = (let
    cb2 = bcomp m b2 f n;
    n' = if f
      then size cb2
      else size cb2 + n;
    cb1 = bcomp m b1 False n' in
    cb1 @ cb2)" |
  "bcomp m (Less a1 a2) f n =
    acomp m a1 @ acomp m a2 @ (if f then [JMPLESS n] else [JMPGE n])"

lemma bcomp_correct[intro]:
  fixes n :: int
  shows
  "0 \<le> n \<Longrightarrow>
  bcomp m b f n \<turnstile>
 (0, s, stk) \<rightarrow>* (size (bcomp m b f n) + (if f = bval b (s \<circ> m) then n else 0), s, stk)"
proof (induct b arbitrary: f n)
  case (Not b)
  from Not(1) Not(2) have "bcomp m b (\<not> f) n \<turnstile> (0, s, stk) \<rightarrow>* (size (bcomp m b (\<not> f) n) + (if (\<not> f) = bval b (s \<circ> m) then n else 0), s, stk)" .
  moreover have "?this \<longleftrightarrow> (bcomp m (bexp.Not b) f n \<turnstile> (0, s, stk) \<rightarrow>* (size (bcomp m (bexp.Not b) f n) + (if f = bval (bexp.Not b) (s \<circ> m) then n else 0), s, stk))" by simp
  ultimately show ?case by blast
next
  case (And b1 b2)
  let ?sm = "s \<circ> m"
  let ?bc2 = "bcomp m b2 f n" and ?bv2 = "bval b2 ?sm"
  let ?sizeb2 = "size ?bc2"

  let ?n' = "if f then ?sizeb2 else ?sizeb2 + n"
  let ?bc1 = "bcomp m b1 False ?n'" and ?bv1 = "bval b1 ?sm"
  let ?sizeb1 = "size ?bc1"

  let ?bcAnd = "bcomp m (And b1 b2) f n"
    and ?bvAnd = "bval (And b1 b2) ?sm"
  let ?sizeAnd = "size ?bcAnd"

  from And(2) And(3) have H2: "?bc2 \<turnstile> (0, s, stk) \<rightarrow>* (?sizeb2 + (if f = ?bv2 then n else 0), s, stk)" .
  from And(3) And(1) [of ?n' "False"] have H1: "?bc1 \<turnstile>
    (0, s, stk) \<rightarrow>* (?sizeb1 + (if False = ?bv1 then ?n' else 0), s, stk)" by fastforce
  show "?bcAnd \<turnstile> (0, s, stk) \<rightarrow>* (?sizeAnd + (if f = ?bvAnd then n else 0), s, stk)" (is ?P)
  proof (cases ?bv1)
    case True
    with H1 H2 show ?thesis by auto
  next
    case Hbv1: False
    show ?thesis
    proof (cases f)
      case Hf: True
      with Hbv1 Hf H1 show ?thesis by auto
    next
      case Hf: False
      from Hf Hbv1 H1 have H1': "?bc1 \<turnstile> (0, s, stk) \<rightarrow>* (?sizeAnd + n, s, stk)" by (simp add: add.assoc)
      then have "?bcAnd \<turnstile> (0, s, stk) \<rightarrow>* (?sizeAnd + n, s, stk)" using exec_appendR by auto
      with Hbv1 Hf H1 show ?thesis by auto
    qed
  qed
qed fastforce+

fun ccomp :: "mmap \<Rightarrow> com \<Rightarrow> instr list" where
  "ccomp m SKIP = []" |
  "ccomp m (x ::= a) = acomp m a @ [STORE (m x)]" |
  "ccomp m (c\<^sub>1;; c\<^sub>2) = ccomp m c\<^sub>1 @ ccomp m c\<^sub>2" |
  "ccomp m (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = (let
    cc\<^sub>1 = ccomp m c\<^sub>1;
    cc\<^sub>2 = ccomp m c\<^sub>2;
    cb = bcomp m b False (size cc\<^sub>1 + 1) in
    cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
  "ccomp m (WHILE b DO c) = (let
    cc = ccomp m c;
    cb = bcomp m b False (size cc + 1) in
    cb @ cc @ [JMP (-(size cb + size cc + 1))])"

lemma ccomp_bigstep:
  "\<lbrakk>(c, s \<circ> m) \<Rightarrow> (t \<circ> m); bij m\<rbrakk> \<Longrightarrow> ccomp m c \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp m c), t, stk)"
proof (induct c "s \<circ> m" "t \<circ> m" arbitrary: s t m stk rule: big_step_induct)
  case (Skip s)
  then have "s = t" by simp
  then show ?case by simp
next
  case (Assign x a s)
  then have "s((m x) := aval a (s \<circ> m)) = t" by simp
  then show ?case by fastforce
next
  case (Seq c\<^sub>1 s\<^sub>2m c\<^sub>2)
  from Seq(5) obtain s\<^sub>2 where Hs\<^sub>2: "s\<^sub>2m = s\<^sub>2 \<circ> m" using bij_cancel_r2 by auto
  with Seq(2, 5) have H1: "ccomp m c\<^sub>1 \<turnstile> (0, s, stk) \<rightarrow>* (size (ccomp m c\<^sub>1), s\<^sub>2, stk)" by auto
  from Hs\<^sub>2 Seq(4, 5) have H2: "ccomp m c\<^sub>2 \<turnstile> (0, s\<^sub>2, stk) \<rightarrow>* (size (ccomp m c\<^sub>2), t, stk)" by auto
  from H1 H2 show ?case by auto
next
  case (WhileFalse b c)
  from WhileFalse(2, 3) have "s = t" by simp
  with WhileFalse(1) show ?case by fastforce
next
  case (WhileTrue b c s\<^sub>2m)
  let ?cc = "ccomp m c" and ?cw = "ccomp m (WHILE b DO c)"
  let ?cb = "bcomp m b False (size ?cc + 1)"
  from WhileTrue(1) have "?cw \<turnstile> (0, s, stk) \<rightarrow>* (size ?cb, s, stk)" by fastforce
  moreover from WhileTrue(6) obtain s\<^sub>2 where Hs\<^sub>2: "s\<^sub>2m = s\<^sub>2 \<circ> m" using bij_cancel_r2 by auto
  with WhileTrue(3, 6) have "?cw \<turnstile> (size ?cb, s, stk) \<rightarrow>* (size ?cb + size ?cc, s\<^sub>2, stk)" by fastforce
  moreover have "?cw \<turnstile> (size ?cb + size ?cc, s\<^sub>2, stk) \<rightarrow>* (0, s\<^sub>2, stk)" by fastforce
  moreover from Hs\<^sub>2 WhileTrue(5, 6) have "?cw \<turnstile> (0, s\<^sub>2, stk) \<rightarrow>* (size (ccomp m (WHILE b DO c)), t, stk)" by simp
  ultimately show ?case by (blast intro: star_trans)
qed fastforce+

end