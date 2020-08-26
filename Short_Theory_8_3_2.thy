theory Short_Theory_8_3_2
  imports "HOL-IMP.Big_Step" "HOL-IMP.Star"
begin
declare [[coercion_enabled]]
declare [[coercion "int :: nat \<Rightarrow> int"]]

(* TODO *)

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

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P !! i) (i, s, stk) \<Longrightarrow>
  0 \<le> i \<Longrightarrow> i < size P \<Longrightarrow>
  P \<turnstile> (i, s, stk) \<rightarrow> c'"
  by (simp add: exec1_def)
code_pred exec1 by (metis exec1_def)

lemma exec1D [dest!]: "P \<turnstile> (i, s, stk) \<rightarrow> c' \<Longrightarrow> c' = iexec (P !! i) (i, s, stk) \<and> 0 \<le> i \<and> i < size P"
  using exec1_def by auto


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
  shows "size P' \<le> i \<Longrightarrow>
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

subsection "mmap existence"

lemma remdups_subset: "set a \<subseteq> set b \<Longrightarrow> set a \<subseteq> set (remdups b)" by simp

fun vars_in_aexp :: "aexp \<Rightarrow> vname list" where
  "vars_in_aexp (N _) = []" |
  "vars_in_aexp (V x) = [x]" |
  "vars_in_aexp (Plus a\<^sub>1 a\<^sub>2) = vars_in_aexp a\<^sub>1 @ vars_in_aexp a\<^sub>2"

fun vars_in_bexp :: "bexp \<Rightarrow> vname list" where
  "vars_in_bexp (Bc _) = []" |
  "vars_in_bexp (Not b) = vars_in_bexp b" |
  "vars_in_bexp (And b\<^sub>1 b\<^sub>2) = vars_in_bexp b\<^sub>1 @ vars_in_bexp b\<^sub>2" |
  "vars_in_bexp (Less a\<^sub>1 a\<^sub>2) = vars_in_aexp a\<^sub>1 @ vars_in_aexp a\<^sub>2"

fun vars_in_com :: "com \<Rightarrow> vname list" where
  "vars_in_com SKIP = []" |
  "vars_in_com (x ::= a) = x # vars_in_aexp a" |
  "vars_in_com (c\<^sub>1;; c\<^sub>2) = vars_in_com c\<^sub>1 @ vars_in_com c\<^sub>2" |
  "vars_in_com (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = vars_in_bexp b @ vars_in_com c\<^sub>1 @ vars_in_com c\<^sub>2" |
  "vars_in_com (WHILE b DO c) = vars_in_bexp b @ vars_in_com c"

abbreviation vars_in :: "com \<Rightarrow> vname list" where
  "vars_in c \<equiv> remdups (vars_in_com c)"

abbreviation svars_in :: "com \<Rightarrow> vname set" where
  "svars_in c \<equiv> set (vars_in c)"

abbreviation addrs_in :: "com \<Rightarrow> int set" where
  "addrs_in c \<equiv> int ` {..<length (vars_in c)}"

lemma vars_in_distinct: "distinct (vars_in c)" by auto

fun nth_inv_c :: "com \<Rightarrow> vname \<Rightarrow> nat" where
  "nth_inv_c c = the_inv_into {..<length (vars_in c)} ((!) (vars_in c))"

fun addr_of :: "com \<Rightarrow> vname \<Rightarrow> int" where
  "addr_of c v = (if v \<in> svars_in c
    then (int \<circ> nth_inv_c c) v
    else -1)"

lemma bij_addr_of: "bij_betw (addr_of c) (svars_in c) (addrs_in c)"
proof -
  have "bij_betw ((!) (vars_in c)) {..<length (vars_in c)} (svars_in c)"
    by (rule bij_betw_nth, auto simp add: vars_in_distinct)
  then have 0: "bij_betw (nth_inv_c c) (svars_in c) {..<length (vars_in c)}" (is ?P0)
    by (simp add: bij_betw_the_inv_into)
  have 1: "bij_betw int {..<length (vars_in c)} (addrs_in c)" (is ?P1) by simp
  have "?P1 \<longleftrightarrow>
    bij_betw (int \<circ> nth_inv_c c) (svars_in c) (addrs_in c)" (is "?P1 \<longleftrightarrow> ?P2")
    by (rule bij_betw_comp_iff [OF 0])
  with 1 have 2: ?P2 by blast
  have "bij_betw (addr_of c) (svars_in c) (addrs_in c) \<longleftrightarrow> ?P2"
    by (rule bij_betw_cong, simp)
  with 2 show ?thesis by blast
qed

corollary inj_on_addr_of: "inj_on (addr_of c) (svars_in c)" using bij_betw_def by (blast intro: bij_addr_of)

subsection "mmap setup"

lemma inj_on_cancel_r: "\<lbrakk>inj_on b A; f \<circ> b = g \<circ> b\<rbrakk> \<Longrightarrow> \<forall> x \<in> b ` A. f x = g x" using comp_eq_dest by fastforce

lemma inj_on_comp_update: "inj_on b A \<Longrightarrow> \<forall> x \<in> A. \<forall> z \<in> A. ((f \<circ> b) (x := y)) z = (f (b x := y) \<circ> b) z"
proof
  fix x
  assume H1: "x \<in> A"
  assume H2: "inj_on b A"
  {
    fix z
    assume H3: "z \<in> A"
    have "((f \<circ> b) (x := y)) z = (f (b x := y) \<circ> b) z"
    proof (cases "z = x")
      case False
      then have "((f \<circ> b) (x := y)) z = f (b z)" by simp
      also from H1 H2 H3 have "b z \<noteq> b x" by (meson False inj_on_def)
      then have "f (b z) = (f(b x := y) \<circ> b) z" by simp
      finally show ?thesis .
    qed simp
  }
  then show "\<forall>z\<in>A. ((f \<circ> b)(x := y)) z = (f(b x := y) \<circ> b) z" by blast
qed

lemma inj_on_cancel_r2: "inj_on b A \<Longrightarrow> \<exists> g. \<forall> x \<in> A. f x = (g \<circ> b) x"
proof -
  assume "inj_on b A"
  then have "bij_betw b A (b ` A)" using bij_betw_def by blast
  then show ?thesis by (metis bij_betw_inv_into_left comp_apply comp_def)
qed

subsection "Compilation"

fun acomp :: "mmap \<Rightarrow> aexp \<Rightarrow> instr list" where
  "acomp m (N n) = [LOADI n]" |
  "acomp m (V x) = [LOAD (m x)]" |
  "acomp m (Plus a1 a2) = acomp m a1 @ acomp m a2 @ [ADD]"

lemma acomp_correct[intro]:
  "(\<forall> v \<in> set (vars_in_aexp a). s v = s' (m v)) \<Longrightarrow> (acomp m a \<turnstile> (0, s', stk) \<rightarrow>* (size (acomp m a), s', aval a s # stk))"
proof (induct a arbitrary: stk s')
  case (Plus a1 a2)
  from Plus(1, 3) have "acomp m a1 \<turnstile> (0, s', stk) \<rightarrow>* (size (acomp m a1), s', aval a1 s # stk)" by simp
  moreover from Plus(2, 3) have "acomp m a2 \<turnstile> (0, s', aval a1 s # stk) \<rightarrow>* (size (acomp m a2), s', aval a2 s # aval a1 s # stk)" by simp
  ultimately show ?case by fastforce
qed fastforce+

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
  (\<forall> v \<in> set (vars_in_bexp b). (s v = s' (m v))) \<Longrightarrow>
  bcomp m b f n \<turnstile>
 (0, s', stk) \<rightarrow>* (size (bcomp m b f n) + (if f = bval b s then n else 0), s', stk)"
proof (induct b arbitrary: f n)
  case (Not b)
  then have "bcomp m b (\<not> f) n \<turnstile> (0, s', stk) \<rightarrow>* (size (bcomp m b (\<not> f) n) + (if (\<not> f) = bval b s then n else 0), s', stk)" by simp
  then show ?case by fastforce
next
  case (And b1 b2)
  let ?bc2 = "bcomp m b2 f n" and ?bv2 = "bval b2 s"
  let ?sizeb2 = "size ?bc2"

  let ?n' = "if f then ?sizeb2 else ?sizeb2 + n"
  let ?bc1 = "bcomp m b1 False ?n'" and ?bv1 = "bval b1 s"
  let ?sizeb1 = "size ?bc1"

  let ?bcAnd = "bcomp m (And b1 b2) f n"
    and ?bvAnd = "bval (And b1 b2) s"
  let ?sizeAnd = "size ?bcAnd"

  from And(2-4) have H2: "?bc2 \<turnstile> (0, s', stk) \<rightarrow>* (?sizeb2 + (if f = ?bv2 then n else 0), s', stk)" by simp
  from And(1) [of ?n' "False"] And(3, 4) have H1: "?bc1 \<turnstile>
    (0, s', stk) \<rightarrow>* (?sizeb1 + (if False = ?bv1 then ?n' else 0), s', stk)" by fastforce
  show "?bcAnd \<turnstile> (0, s', stk) \<rightarrow>* (?sizeAnd + (if f = ?bvAnd then n else 0), s', stk)" (is ?P)
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
      from Hf Hbv1 H1 have H1': "?bc1 \<turnstile> (0, s', stk) \<rightarrow>* (?sizeAnd + n, s', stk)" by (simp add: add.assoc)
      then have "?bcAnd \<turnstile> (0, s', stk) \<rightarrow>* (?sizeAnd + n, s', stk)" using exec_appendR by auto
      with Hbv1 Hf H1 show ?thesis by auto
    qed
  qed
next
  case (Less x1a x2a)
  from Less(2) have "(acomp m x1a \<turnstile> (0, s', stk) \<rightarrow>* (size (acomp m x1a), s', aval x1a s # stk))" by auto
  moreover from Less(2) have "(acomp m x2a \<turnstile>
    (0, s', aval x1a s # stk) \<rightarrow>* (size (acomp m x2a), s', aval x2a s # aval x1a s # stk))" by auto
  moreover have "(if f then [JMPLESS n] else [JMPGE n]) \<turnstile>
    (0, s', aval x2a s # aval x1a s # stk) \<rightarrow>* (1 + (if f = bval (Less x1a x2a) s then n else 0), s', stk)" by fastforce
  ultimately show ?case by fastforce
qed fastforce

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

(* to each big-step that brings a var-val map A to a var-val map B,
  our compiled program non-deterministically brings every addr-val A' state that agrees with A on the variables appearing in the program
  to an addr-val B' state that agrees with B on the variables appearing in the program that yet agrees with A
  on the variables not appearing in the program
*)

(* The notion of the var-val map, on vars not appearing in the commands being preserved is significant here,
  but is not important in the results proven in Big Step. Hence we prove that here.
*)

lemma bigstep_state_invariance: "(c, s) \<Rightarrow> t \<Longrightarrow> (\<forall> v. v \<notin> svars_in c \<longrightarrow> s v = t v)"
  by (induct rule: big_step_induct) simp+

lemma map_invariance: "\<lbrakk>
  inj_on m (svars_in c);
  (c\<^sub>1, s) \<Rightarrow> t;
  svars_in c\<^sub>1 \<subseteq> svars_in c;
  \<forall> v \<in> svars_in c. s v = s' (m v);
  \<forall> v \<in> svars_in c\<^sub>1. t v = t' (m v);
  \<forall> a. (\<nexists> v. v \<in> svars_in c\<^sub>1 \<and> a = m v) \<longrightarrow> s' a = t' a
\<rbrakk> \<Longrightarrow> \<forall> v \<in> svars_in c. t v = t' (m v)"
proof
  assume H1: "inj_on m (svars_in c)"
    and H2: "(c\<^sub>1, s) \<Rightarrow> t"
    and H3: "svars_in c\<^sub>1 \<subseteq> svars_in c"
    and H4: "\<forall> v \<in> svars_in c. s v = s' (m v)"
    and H5: "\<forall> v \<in> svars_in c\<^sub>1. t v = t' (m v)"
    and H6: "\<forall> a. (\<nexists> v. v \<in> svars_in c\<^sub>1 \<and> a = m v) \<longrightarrow> s' a = t' a"
  fix v
  assume H7: "v \<in> svars_in c"
  show "t v = t' (m v)"
  proof (cases "v \<in> svars_in c\<^sub>1")
    case False
    with H3 H7 H1 have H8: "\<nexists>v'. v' \<in> svars_in c\<^sub>1 \<and> (m v) = m v'" using inj_on_eq_iff by fastforce
    from H2 False have "t v = s v" using bigstep_state_invariance by fastforce
    also from H4 H7 have "\<dots> = s' (m v)" by simp
    also from H6 H8 have "\<dots> = t' (m v)" by simp
    finally show ?thesis .
  qed (simp add: H5)
qed

lemma ccomp_bigstep: "\<lbrakk>(c, s) \<Rightarrow> t; inj_on m (svars_in c)\<rbrakk> \<Longrightarrow>
    (\<And> s'. (\<forall> v \<in> svars_in c. s v = s' (m v)) \<Longrightarrow>
      (\<exists> t'. (ccomp m c \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m c), t', stk)) \<and>
          (\<forall> v \<in> svars_in c. t v = t' (m v)) \<and>
          (\<forall> a. (\<nexists> v. v \<in> svars_in c \<and> a = m v) \<longrightarrow> s' a = t' a)))"
proof (induct c s t arbitrary: stk rule: big_step_induct)
  case (Skip s)
  show ?case
  proof (intro exI conjI)
    show "ccomp m SKIP \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m SKIP), s', stk)" by simp
    show "\<forall>v \<in> svars_in SKIP. s v = s' (m v)" by simp
    show "\<forall>a. (\<nexists>v. v \<in> svars_in SKIP \<and> a = m v) \<longrightarrow> s' a = s' a" by simp
  qed
next
  case (Assign x a s)
  show ?case
  proof (intro exI conjI)
    from Assign(2) have "acomp m a \<turnstile> (0, s', stk) \<rightarrow>* (size (acomp m a), s', aval a s # stk)" by auto
    moreover have "[STORE (m x)] \<turnstile> (0, s', aval a s # stk) \<rightarrow>* (1, s'(m x := aval a s), stk)" by fastforce
    ultimately show "ccomp m (x ::= a) \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m (x ::= a)), s'(m x := aval a s), stk)" by auto
    have H1: "x \<in> svars_in (x ::= a)" by simp
    show "\<forall>v \<in> svars_in (x ::= a). (s(x := aval a s)) v = (s'(m x := aval a s)) (m v)"
    proof
      fix v
      assume H2: "v \<in> svars_in (x ::= a)"
      show "(s(x := aval a s)) v = (s'(m x := aval a s)) (m v)"
      proof (cases "v = x")
        case False
        then have "(s(x := aval a s)) v = s v" by simp
        also from Assign(2) H2 have "\<dots> = s' (m v)" by simp
        also from Assign(1) H1 H2 False have "m v \<noteq> m x" by (meson inj_onD)
        then have "s' (m v) = (s'(m x := aval a s)) (m v)" by simp
        finally show ?thesis .
      qed simp
    qed
    show "\<forall>aa. (\<nexists>v. v \<in> svars_in (x ::= a) \<and> aa = m v) \<longrightarrow> s' aa = (s'(m x := aval a s)) aa"
    proof (intro allI impI)
      fix aa
      assume "\<nexists>v. v \<in> svars_in (x ::= a) \<and> aa = m v"
      with H1 have "aa \<noteq> m x" by simp
      then show "s' aa = (s'(m x := aval a s)) aa" by simp
    qed
  qed
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  have Hs1: "svars_in c\<^sub>1 \<subseteq> svars_in (c\<^sub>1;; c\<^sub>2)" by simp
  with Seq(5) have "inj_on m (svars_in c\<^sub>1)" using inj_on_subset by blast
  moreover from Hs1 Seq(6) have "\<forall>v\<in>svars_in c\<^sub>1. s\<^sub>1 v = s' (m v)" by simp
  ultimately have "\<exists>t'. (ccomp m c\<^sub>1 \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m c\<^sub>1), t', stk)) \<and>
             (\<forall>v\<in>svars_in c\<^sub>1. s\<^sub>2 v = t' (m v)) \<and> (\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>1 \<and> a = m v) \<longrightarrow> s' a = t' a)" using Seq(2) by fastforce
  then obtain s\<^sub>2' where H1: "ccomp m c\<^sub>1 \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m c\<^sub>1), s\<^sub>2', stk)"
    and H2: "\<forall> v \<in> svars_in c\<^sub>1. s\<^sub>2 v = s\<^sub>2' (m v)"
    and H3: "\<forall> a. (\<nexists> v. v \<in> svars_in c\<^sub>1 \<and> a = m v) \<longrightarrow> s' a = s\<^sub>2' a" by blast
  have Hs2: "svars_in c\<^sub>2 \<subseteq> svars_in (c\<^sub>1;; c\<^sub>2)" by simp
  with Seq(5) have "inj_on m (svars_in c\<^sub>2)" using inj_on_subset by blast
  moreover from Seq(1, 5, 6) Hs1 H2 H3 have H4: "\<forall> v \<in> svars_in (c\<^sub>1;; c\<^sub>2). s\<^sub>2 v = s\<^sub>2' (m v)" using map_invariance by blast
  then have "\<forall> v \<in> svars_in c\<^sub>2. s\<^sub>2 v = s\<^sub>2' (m v)" by simp
  ultimately have "\<exists>t'. (ccomp m c\<^sub>2 \<turnstile> (0, s\<^sub>2', stk) \<rightarrow>* (size (ccomp m c\<^sub>2), t', stk)) \<and>
             (\<forall>v\<in>svars_in c\<^sub>2. s\<^sub>3 v = t' (m v)) \<and> (\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>2 \<and> a = m v) \<longrightarrow> s\<^sub>2' a = t' a)" using Seq(4) by fastforce
  then obtain s\<^sub>3' where H5: "ccomp m c\<^sub>2 \<turnstile> (0, s\<^sub>2', stk) \<rightarrow>* (size (ccomp m c\<^sub>2), s\<^sub>3', stk)"
    and H6: "\<forall>v\<in>svars_in c\<^sub>2. s\<^sub>3 v = s\<^sub>3' (m v)"
    and H7: "\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>2 \<and> a = m v) \<longrightarrow> s\<^sub>2' a = s\<^sub>3' a" by blast
  show ?case
  proof (intro exI conjI)
    from H1 H5 show "ccomp m (c\<^sub>1;; c\<^sub>2) \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m (c\<^sub>1;; c\<^sub>2)), s\<^sub>3', stk)" by fastforce
    from Seq(3, 5) H4 Hs2 H6 H7 show "\<forall>v\<in>svars_in (c\<^sub>1;; c\<^sub>2). s\<^sub>3 v = s\<^sub>3' (m v)" using map_invariance by blast
    show "\<forall>a. (\<nexists>v. v \<in> svars_in (c\<^sub>1;; c\<^sub>2) \<and> a = m v) \<longrightarrow> s' a = s\<^sub>3' a"
    proof (intro allI impI)
      fix a
      assume "\<nexists>v. v \<in> svars_in (c\<^sub>1;; c\<^sub>2) \<and> a = m v"
      then have HH1: "\<nexists>v. v \<in> svars_in c\<^sub>1 \<and> a = m v"
        and HH2: "\<nexists>v. v \<in> svars_in c\<^sub>2 \<and> a = m v" by auto
      from HH1 H3 have "s' a = s\<^sub>2' a" by simp
      also from HH2 H7 have "s\<^sub>2' a = s\<^sub>3' a" by simp
      finally show "s' a = s\<^sub>3' a" .
    qed
  qed
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  let ?cc\<^sub>1 = "ccomp m c\<^sub>1" and ?cc\<^sub>2 = "ccomp m c\<^sub>2" and ?ci = "ccomp m (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
  let ?cb = "bcomp m b False (size ?cc\<^sub>1 + 1)"
  have "0 \<le> (size ?cc\<^sub>1 + 1)" by simp
  moreover from IfTrue(5) have "\<forall>v\<in>set (vars_in_bexp b). s' (m v) = s v" by simp
  ultimately have H1: "?cb \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb, s', stk)"
    using IfTrue(1) bcomp_correct [of "size ?cc\<^sub>1 + 1" b s s' m False stk] by fastforce
  have Hs1: "svars_in c\<^sub>1 \<subseteq> svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2)" by auto
  with IfTrue(4) have "inj_on m (svars_in c\<^sub>1)" using inj_on_subset by blast
  moreover from Hs1 IfTrue(5) have "\<forall>v \<in> svars_in c\<^sub>1. s' (m v) = s v" by simp
  ultimately have "\<exists>t'. (?cc\<^sub>1 \<turnstile> (0, s', stk) \<rightarrow>* (size ?cc\<^sub>1, t', stk)) \<and>
    (\<forall>v \<in> svars_in c\<^sub>1. t v = t' (m v)) \<and> (\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>1 \<and> a = m v) \<longrightarrow> s' a = t' a)" using IfTrue(3) by simp
  then obtain t' where H2: "?cc\<^sub>1 \<turnstile> (0, s', stk) \<rightarrow>* (size ?cc\<^sub>1, t', stk)"
    and H3: "\<forall>v\<in>svars_in c\<^sub>1. t v = t' (m v)"
    and H4: "\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>1 \<and> a = m v) \<longrightarrow> s' a = t' a" by auto
  have H5: "JMP (size ?cc\<^sub>2) # ?cc\<^sub>2 \<turnstile> (0, t', stk) \<rightarrow>* (size ?cc\<^sub>2 + 1, t', stk)"  by fastforce
  from H1 H2 have "?cb @ ?cc\<^sub>1 \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb + size ?cc\<^sub>1, t', stk)" by fastforce
  with H5 have H6: "?cb @ ?cc\<^sub>1 @ JMP (size ?cc\<^sub>2) # ?cc\<^sub>2 \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb + size ?cc\<^sub>1 + (size ?cc\<^sub>2 + 1), t', stk)"
    using exec_append_trans [of "?cb @ ?cc\<^sub>1"] by fastforce
  have "size ?ci = size ?cb + size ?cc\<^sub>1 + (size ?cc\<^sub>2 + 1)" by simp
  with H6 have H7: "?cb @ ?cc\<^sub>1 @ JMP (size ?cc\<^sub>2) # ?cc\<^sub>2 \<turnstile> (0, s', stk) \<rightarrow>* (size ?ci, t', stk)" by presburger
  show ?case
  proof (intro exI conjI)
    from H7 show "?ci \<turnstile> (0, s', stk) \<rightarrow>* (size ?ci, t', stk)" by simp
    from IfTrue(2, 4, 5) Hs1 H3 H4 show "\<forall>v\<in>svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2). t v = t' (m v)" using map_invariance by blast
    from H4 show "\<forall>a. (\<nexists>v. v \<in> svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2) \<and> a = m v) \<longrightarrow> s' a = t' a" by auto
  qed
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  let ?cc\<^sub>1 = "ccomp m c\<^sub>1" and ?cc\<^sub>2 = "ccomp m c\<^sub>2" and ?ci = "ccomp m (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
  let ?cb = "bcomp m b False (size ?cc\<^sub>1 + 1)"
  have "0 \<le> (size ?cc\<^sub>1 + 1)" by simp
  moreover from IfFalse(5) have "\<forall>v\<in>set (vars_in_bexp b). s' (m v) = s v" by simp
  ultimately have H1: "?cb @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)] \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb + (size ?cc\<^sub>1 + 1), s', stk)"
    using IfFalse(1) bcomp_correct [of "size ?cc\<^sub>1 + 1" b s s' m False stk] by fastforce
  have Hs2: "svars_in c\<^sub>2 \<subseteq> svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2)" by auto
  with IfFalse(4) have "inj_on m (svars_in c\<^sub>2)" using inj_on_subset by blast
  with IfFalse(3, 5) have "\<exists>t'. (?cc\<^sub>2 \<turnstile> (0, s', stk) \<rightarrow>* (size ?cc\<^sub>2, t', stk)) \<and>
    (\<forall>v\<in>svars_in c\<^sub>2. t v = t' (m v)) \<and> (\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>2 \<and> a = m v) \<longrightarrow> s' a = t' a)" by simp
  then obtain t' where H2: "?cc\<^sub>2 \<turnstile> (0, s', stk) \<rightarrow>* (size ?cc\<^sub>2, t', stk)"
    and H3: "\<forall>v\<in>svars_in c\<^sub>2. t v = t' (m v)"
    and H4: "\<forall>a. (\<nexists>v. v \<in> svars_in c\<^sub>2 \<and> a = m v) \<longrightarrow> s' a = t' a" by auto
  have H5: "size (?cb @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)]) \<le> size ?cb + (size ?cc\<^sub>1 + 1)" by simp
  have "size ?cb + (size ?cc\<^sub>1 + 1) - size (?cb @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)]) = 0" by simp
  with H2 have H6: "?cc\<^sub>2 \<turnstile> (size ?cb + (size ?cc\<^sub>1 + 1) - size (?cb @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)]), s', stk) \<rightarrow>* (size ?cc\<^sub>2, t', stk)" by simp
  have H7: "size ?ci = size (?cb @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)]) + size ?cc\<^sub>2" by simp
  thm exec_append_trans [OF H1 H5 H6 H7]
  have H8: "?cb @ ?cc\<^sub>1 @ [JMP (size ?cc\<^sub>2)] @ ?cc\<^sub>2 \<turnstile> (0, s', stk) \<rightarrow>* (size ?ci, t', stk)"
    using exec_append_trans [OF H1 H5 H6 H7] by simp
  show ?case
  proof (intro exI conjI)
    from H8 show "?ci \<turnstile> (0, s', stk) \<rightarrow>* (size ?ci, t', stk)" by simp
    from IfFalse(2, 4, 5) Hs2 H3 H4 show "\<forall>v\<in>svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2). t v = t' (m v)" using map_invariance by blast
    from H4 show "\<forall>a. (\<nexists>v. v \<in> svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2) \<and> a = m v) \<longrightarrow> s' a = t' a" by auto
  qed
next
  case (WhileFalse b s c)
  let ?cc = "ccomp m c"
  let ?cb = "bcomp m b False (size ?cc + 1)"
  let ?cw = "ccomp m (WHILE b DO c)"
  have H1: "0 \<le> size ?cc + 1" by simp
  from WhileFalse(3) have H2: "\<forall>v\<in>set (vars_in_bexp b). s v = s' (m v)" by simp

  show ?case
  proof (intro exI conjI)
    from WhileFalse(1) bcomp_correct [OF H1, of b s s' m, OF H2, of False stk]
    show "?cw \<turnstile> (0, s', stk) \<rightarrow>* (size ?cw, s', stk)" by auto
    from WhileFalse(3) show "\<forall>v\<in>svars_in (WHILE b DO c). s v = s' (m v)" .
    show "\<forall>a. (\<nexists>v. v \<in> svars_in (WHILE b DO c) \<and> a = m v) \<longrightarrow> s' a = s' a" by simp
  qed
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?cc = "ccomp m c"
  let ?cb = "bcomp m b False (size ?cc + 1)"
  let ?cw = "ccomp m (WHILE b DO c)"
  have H1: "0 \<le> size ?cc + 1" by simp
  from WhileTrue(7) have H2: "\<forall>v\<in>set (vars_in_bexp b). s\<^sub>1 v = s' (m v)" by simp
  from WhileTrue(1) bcomp_correct [OF H1, of b s\<^sub>1 s' m, OF H2, of False stk]
  have H3: "?cb \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb, s', stk)" by fastforce

  thm WhileTrue(3)
  have Hs: "svars_in c \<subseteq> svars_in (WHILE b DO c)" by simp
  with WhileTrue(6) have H4: "inj_on m (svars_in c)" using inj_on_subset by blast
  from WhileTrue(7) have H5: "\<forall>v\<in>svars_in c. s\<^sub>1 v = s' (m v)" by simp
  from WhileTrue(3) [OF H4 H5]
  have "\<exists>t'. (?cc \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m c), t', stk)) \<and>
    (\<forall>v\<in>svars_in c. s\<^sub>2 v = t' (m v)) \<and>
    (\<forall>a. (\<nexists>v. v \<in> svars_in c \<and> a = m v) \<longrightarrow> s' a = t' a)" by simp
  then obtain s\<^sub>2' where H6: "?cc \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp m c), s\<^sub>2', stk)"
    and H7: "\<forall>v\<in>svars_in c. s\<^sub>2 v = s\<^sub>2' (m v)"
    and H8: "\<forall>a. (\<nexists>v. v \<in> svars_in c \<and> a = m v) \<longrightarrow> s' a = s\<^sub>2' a" by auto
  have H9: "size ?cb \<le> size ?cb" by simp
  from H6 have H10: "?cc \<turnstile> (size ?cb - size ?cb, s', stk) \<rightarrow>* (size (ccomp m c), s\<^sub>2', stk)" by simp
  have H11: "size ?cb + size ?cc = size ?cb + size ?cc" by simp
  from exec_append_trans [OF H3 H9 H10 H11]
  have "?cb @ ?cc \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb + size ?cc, s\<^sub>2', stk)" by fastforce
  then have "?cw \<turnstile> (0, s', stk) \<rightarrow>* (size ?cb + size ?cc, s\<^sub>2', stk)" using exec_appendR
    by (metis append.assoc ccomp.simps(5))

  moreover have "?cw \<turnstile> (size ?cb + size ?cc, s\<^sub>2', stk) \<rightarrow>* (0, s\<^sub>2', stk)" by fastforce
  ultimately have H12: "?cw \<turnstile> (0, s', stk) \<rightarrow>* (0, s\<^sub>2', stk)" by (meson star_trans)

  have H13: "\<forall>v\<in>svars_in (WHILE b DO c). s\<^sub>2 v = s\<^sub>2' (m v)"
    using map_invariance [OF WhileTrue(6) WhileTrue(2) Hs WhileTrue(7) H7 H8] .
  moreover from WhileTrue(5) [OF WhileTrue(6) H13] have "\<exists>t'.
    (ccomp m (WHILE b DO c) \<turnstile> (0, s\<^sub>2', stk) \<rightarrow>* (size (ccomp m (WHILE b DO c)), t', stk)) \<and>
    (\<forall>v\<in>svars_in (WHILE b DO c). s\<^sub>3 v = t' (m v)) \<and>
    (\<forall>a. (\<nexists>v. v \<in> svars_in (WHILE b DO c) \<and> a = m v) \<longrightarrow> s\<^sub>2' a = t' a)" .
  then obtain s\<^sub>3' where H14: "?cw \<turnstile> (0, s\<^sub>2', stk) \<rightarrow>* (size ?cw, s\<^sub>3', stk)"
    and H15: "\<forall>v\<in>svars_in (WHILE b DO c). s\<^sub>3 v = s\<^sub>3' (m v)"
    and H16: "\<forall>a. (\<nexists>v. v \<in> svars_in (WHILE b DO c) \<and> a = m v) \<longrightarrow> s\<^sub>2' a = s\<^sub>3' a" by auto
  show ?case
  proof (intro exI conjI)
    from H12 H14 show "?cw \<turnstile> (0, s', stk) \<rightarrow>* (size ?cw, s\<^sub>3', stk)" by (meson star_trans)
    from H15 show "\<forall>v\<in>svars_in (WHILE b DO c). s\<^sub>3 v = s\<^sub>3' (m v)" .
    from Hs H8 H16 show "\<forall>a. (\<nexists>v. v \<in> svars_in (WHILE b DO c) \<and> a = m v) \<longrightarrow> s' a = s\<^sub>3' a"
      using in_mono by auto
  qed
qed

lemma ccomp_bigstep_addr_of: "(c, s) \<Rightarrow> t \<Longrightarrow>
    (\<And> s'. (\<forall> v \<in> svars_in c. s v = s' (addr_of c v)) \<Longrightarrow>
      (\<exists> t'. (ccomp (addr_of c) c \<turnstile> (0, s', stk) \<rightarrow>* (size (ccomp (addr_of c) c), t', stk)) \<and>
          (\<forall> v \<in> svars_in c. t v = t' (addr_of c v)) \<and>
          (\<forall> a. (\<nexists> v. v \<in> svars_in c \<and> a = addr_of c v) \<longrightarrow> s' a = t' a)))"
  using ccomp_bigstep inj_on_addr_of by blast

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
  "succs P n = {s :: int. \<exists>i\<ge>0. i < size P \<and> s \<in> isuccs (P !! i) (n + i)}" 

text \<open>Possible exit PCs of a program\<close>
definition exits :: "instr list \<Rightarrow> int set" where
  "exits P = succs P 0 - {0..<size P}"

subsection \<open>Basic properties of \<^term>\<open>exec_n\<close>\<close>

lemma exec_n_exec:
  "P \<turnstile> c \<rightarrow>^n c' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c'"
  by (induct n arbitrary: c) (auto intro: star.step)

lemma exec_0 [intro!]: "P \<turnstile> c \<rightarrow>^0 c" by simp

lemma exec_Suc: "\<lbrakk>P \<turnstile> c \<rightarrow> c'; P \<turnstile> c' \<rightarrow>^n c''\<rbrakk> \<Longrightarrow> P \<turnstile> c \<rightarrow>^(Suc n) c''" 
  by (fastforce simp del: split_paired_Ex)

lemma exec_exec_n: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> \<exists>n. P \<turnstile> c \<rightarrow>^n c'"
  by (induct rule: star.induct) (auto intro: exec_Suc)
    
lemma exec_eq_exec_n: "(P \<turnstile> c \<rightarrow>* c') = (\<exists>n. P \<turnstile> c \<rightarrow>^n c')"
  by (blast intro: exec_exec_n exec_n_exec)

lemma exec_n_Nil [simp]: "[] \<turnstile> c \<rightarrow>^k c' = (c' = c \<and> k = 0)"
  by (induct k) (auto simp: exec1_def)

lemma exec1_exec_n [intro!]: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c \<rightarrow>^1 c'"
  by (cases c') simp


subsection \<open>Concrete symbolic execution steps\<close>

lemma exec_n_step: "n \<noteq> n' \<Longrightarrow> 
  P \<turnstile> (n, s, stk) \<rightarrow>^k (n', s', stk') \<longleftrightarrow> (\<exists>c. P \<turnstile> (n, s, stk) \<rightarrow> c \<and> P \<turnstile> c \<rightarrow>^(k - 1) (n', s', stk') \<and> 0 < k)"
  by (cases k) auto

text \<open>Note: fst c refers to the program counter\<close>
lemma exec1_end: "size P \<le> fst c \<Longrightarrow> \<not> P \<turnstile> c \<rightarrow> c'"
  by (auto simp: exec1_def)

lemma exec_n_end: "size P \<le> n \<Longrightarrow> P \<turnstile> (n, s, stk) \<rightarrow>^k (n', s', stk') = (n' = n \<and> stk' = stk \<and> s' = s \<and> k = 0)"
  by (cases k) (auto simp: exec1_end)

lemmas exec_n_simps = exec_n_step exec_n_end

subsection \<open>Basic properties of \<^term>\<open>succs\<close>\<close>

(* follows directly from isuccs_def *)
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
  show "succs (x#xs) n \<subseteq> isuccs x n \<union> succs xs (1 + n)"
  proof
    fix p
    assume "p \<in> succs (x#xs) n"
    then have "\<exists>i\<ge>0. i < size (x # xs) \<and> p \<in> isuccs ((x # xs) !! i) (n + i)" unfolding succs_def by simp
    then obtain i where isuccs: "0 \<le> i" "i < size (x # xs)" "p \<in> isuccs ((x # xs) !! i) (n + i)" by auto
    (* iff i = 0, our p in succs (x # xn) is produced by the instruction x; hence we case split on whether input pc is 0 *)
    show "p \<in> isuccs x n \<union> succs xs (1 + n)"
    proof cases
      assume "i = 0"
      with isuccs(3) show ?thesis by simp
    next
      assume "i \<noteq> 0" 
      with isuccs
      have "0 \<le> i - 1" "i - 1 < size xs" "p \<in> isuccs (xs !! (i - 1)) (1 + n + (i - 1))" by auto
      then have "p \<in> ?xs" unfolding succs_def by blast
      thus ?thesis ..
    qed
  qed

  show "isuccs x n \<union> succs xs (1 + n) \<subseteq> succs (x#xs) n"
  proof
    fix p
    assume "p \<in> isuccs x n \<union> succs xs (1 + n)"
    then consider "p \<in> ?x" | "p \<in> ?xs" by auto
    then show "p \<in> succs (x#xs) n"
    proof cases
      assume "p \<in> isuccs x n"
      then show ?thesis by (fastforce simp: succs_def)
    next
      assume "p \<in> succs xs (1 + n)"
      then obtain i where "0 \<le> i" "i < size xs" "p \<in> isuccs (xs !! i) (1 + n + i)"
        unfolding succs_def by auto
      then have "0 \<le> 1 + i" "1 + i < size (x # xs)" "p \<in> isuccs ((x # xs) !! (1 + i)) (n + (1 + i))"
        by (simp add: algebra_simps)+
      thus ?thesis unfolding succs_def by blast
    qed
  qed
qed

text \<open>the pc at the end of an instruction execution in P are indeed in the successors of P\<close>
lemma succs_iexec1:
  assumes "c' = iexec (P!!i) (i, s, stk)" "0 \<le> i" "i < size P"
  shows "fst c' \<in> succs P 0"
  using assms by (cases "P !! i", auto simp: succs_def isuccs_def)

text \<open>Successor of an instruction of P as a subprogram at the 0th index of a larger program is
  is the same successor shifted n places if we consider P as a subprogram at the nth index instead\<close>
lemma succs_shift:
  "p - n \<in> succs P 0 \<longleftrightarrow> p \<in> succs P n" 
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
  "succs (acomp m a) n = {n + 1 .. n + size (acomp m a)}"
  by (induct a arbitrary: n) auto

lemma acomp_size:
  "(1::int) \<le> size (acomp m a)"
  by (induct a) auto

(* consequence of acomp_succs *)
lemma acomp_exits [simp]:
  "exits (acomp m a) = {size (acomp m a)}"
  using [[simp_trace]]
  by (auto simp: exits_def acomp_size)

(* successors of bcomp bounded above by bcomp instructions themselves (plus one),
  and the jumped-to address *)
lemma bcomp_succs: "0 \<le> i \<Longrightarrow>
  succs (bcomp m b f i) n \<subseteq> {n..n + size (bcomp m b f i)} \<union> {n + i + size (bcomp m b f i)}" 
proof (induct b arbitrary: f i n)
  case (And b1 b2)
  from And(3)
  \<comment> \<open>subsetD converts a subset conclusion into a membership in subset if in superset conclusion\<close>
  \<comment> \<open>rotated rotates the order of the premises\<close>
  show ?case
    by (cases f)
       (auto dest: And(1) [THEN subsetD, rotated] 
                   And(2) [THEN subsetD, rotated])
qed auto

lemmas bcomp_succsD [dest!] = bcomp_succs [THEN subsetD, rotated]

lemma bcomp_exits:
  "0 \<le> i \<Longrightarrow>
  exits (bcomp m b f i) \<subseteq> {size (bcomp m b f i), i + size (bcomp m b f i)}" 
  by (auto simp: exits_def)
  
lemma bcomp_exitsD [dest!]:
  "p \<in> exits (bcomp m b f i) \<Longrightarrow> 0 \<le> i \<Longrightarrow>
  p = size (bcomp m b f i) \<or> p = i + size (bcomp m b f i)"
  using bcomp_exits by fastforce

lemma ccomp_succs:
  "succs (ccomp m c) n \<subseteq> {n..n + size (ccomp m c)}"
proof (induct c arbitrary: n)
  case SKIP thus ?case by simp
next
  case Assign thus ?case by simp
next
  case (Seq c1 c2)
  show ?case
    by (fastforce dest: Seq [THEN subsetD])
next
  case (If b c1 c2)
  show ?case
    by (auto dest!: If [THEN subsetD] simp: isuccs_def succs_Cons)
next
  case (While b c)
  show ?case by (auto dest!: While [THEN subsetD])
qed

lemma ccomp_exits:
  "exits (ccomp m c) \<subseteq> {size (ccomp m c)}"
  using ccomp_succs [of m c 0] by (auto simp: exits_def)

lemma ccomp_exitsD [dest!]:
  "p \<in> exits (ccomp m c) \<Longrightarrow> p = size (ccomp m c)"
  using ccomp_exits by auto

subsection \<open>Splitting up machine executions\<close>

lemma exec1_split:
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
    using iexec_shift by fastforce
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
  assumes "P1 @ P2 \<turnstile> (i, s, stk) \<rightarrow> (n, s', stk')" "size P1 \<le> i"
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

lemma ccomp_closed [simp, intro!]: "closed (ccomp m c)"
  using ccomp_exits by (auto simp: closed_def)

lemma acomp_closed [simp, intro!]: "closed (acomp m c)"
  by (simp add: closed_def)

text \<open>An execution of P @ P', where P is closed starting from start of P must pass through
a state where the pc is at the start of P'\<close>
lemma exec_n_split_full:
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
  "acomp m a \<noteq> []"
  by (induct a) auto

lemma acomp_exec_n [dest!]:
  "acomp m a \<turnstile> (0, s, stk) \<rightarrow>^n (size (acomp m a), s', stk') \<Longrightarrow> 
  s' = s \<and> stk' = aval a (s \<circ> m) # stk"
proof (induction a arbitrary: n s' stk stk')
  case (Plus a1 a2)
  let ?sz = "size (acomp m a1) + (size (acomp m a2) + 1)"
  from Plus.prems
  have "acomp m a1 @ acomp m a2 @ [ADD] \<turnstile> (0, s, stk) \<rightarrow>^n (?sz, s', stk')" 
    by (simp add: algebra_simps)
  then obtain n1 s1 stk1 n2 s2 stk2 n3 where
    "acomp m a1 \<turnstile> (0, s, stk) \<rightarrow>^n1 (size (acomp m a1), s1, stk1)"
    "acomp m a2 \<turnstile> (0, s1, stk1) \<rightarrow>^n2 (size (acomp m a2), s2, stk2)" 
       "[ADD] \<turnstile> (0,s2,stk2) \<rightarrow>^n3 (1, s', stk')"
    by (auto dest!: exec_n_split_full)
  thus ?case by (fastforce dest: Plus.IH simp: exec_n_simps exec1_def)
qed (auto simp: exec_n_simps exec1_def)

text \<open>Execution of a bcomp @ P' to outside the bcomp, where the bcomp jump is forward
must pass through a state where the pc is at start of P', or at the jumped-to address\<close>
lemma bcomp_split:
  assumes "bcomp mp b f i @ P' \<turnstile> (0, s, stk) \<rightarrow>^n (j, s', stk')" 
          "j \<notin> {0..<size (bcomp mp b f i)}" "0 \<le> i"
  shows "\<exists>s'' stk'' (i'::int) k m. 
           bcomp mp b f i \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'') \<and>
           (i' = size (bcomp mp b f i) \<or> i' = i + size (bcomp mp b f i)) \<and>
           bcomp mp b f i @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^m (j, s', stk') \<and>
           n = k + m"
  using assms by (cases "bcomp mp b f i = []") (fastforce dest!: exec_n_drop_right)+

text \<open>Execution of a bcomp to outside the bcomp, where the jump is forward
must end in a state where the pc is at the start of P', or at the jumped-to address\<close>
lemma bcomp_exec_n [dest]:
  fixes i j :: int
  assumes "bcomp m b f j \<turnstile> (0, s, stk) \<rightarrow>^n (i, s', stk')"
          "size (bcomp m b f j) \<le> i" "0 \<le> j"
  shows "i = size (bcomp m b f j) + (if f = bval b (s \<circ> m) then j else 0) \<and>
         s' = s \<and> stk' = stk"
using assms proof (induct b arbitrary: f j i n s' stk')
  case Bc thus ?case
    by (simp split: if_split_asm add: exec_n_simps exec1_def)
next
  case (Not b)
  from Not(2-4) show ?case
    by (fastforce dest!: Not(1))
next
  case (And b1 b2)
  
  let ?cb2 = "bcomp m b2 f j"
  let ?n  = "if f then size ?cb2 else size ?cb2 + j"
  let ?cb1 = "bcomp m b1 False ?n"
  let ?cbAnd = "bcomp m (And b1 b2) f j"

  from And(3-5) obtain s'' stk'' i' k k' where 
    Hb1: "?cb1 \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'')"
        "i' = size ?cb1 \<or> i' = ?n + size ?cb1" and
    Hb2: "?cb1 @ ?cb2 \<turnstile> (i', s'', stk'') \<rightarrow>^k' (i, s', stk')"
    "n = k + k'"
    by (auto dest!: bcomp_split dest: exec_n_drop_left)
  from Hb2 Hb1(2) And(5) (*ccomp_closed, automatically used*)
  have Hb2': "?cb2 \<turnstile> (i' - size ?cb1, s'', stk'') \<rightarrow>^k' (i - size ?cb1, s', stk')"
    by (auto dest: exec_n_drop_left)
  from Hb1(1, 2) And(1, 5)
  have HCb1: "i' = size ?cb1 + (if \<not>bval b1 (s \<circ> m) then ?n else 0)"
    "s'' = s" "stk'' = stk" by fastforce+
  show ?case
  proof (cases "bval b1 (s \<circ> m)")
    case True
    with HCb1 have "i' = size ?cb1" by simp
    with And(2, 4, 5) Hb2' HCb1(2,3) have HCb2: "i - size ?cb1 = size (bcomp m b2 f j) + (if f = bval b2 (s \<circ> m) then j else 0)"
      "s' = s" "stk' = stk"
      by fastforce+
    from HCb2(1) have "i = size ?cbAnd + (if f = bval b2 (s \<circ> m) then j else 0)" by auto
    with True HCb2(2, 3) bval.simps(3) show ?thesis by presburger
  next
    case False
    with HCb1 have "i' - size ?cb1 = ?n" by simp
    moreover from And(5) have "size ?cb2 \<le> ?n" by simp
    ultimately have HCb2: "i = i'" "stk' = stk''" "s' = s''" "k' = 0" using And(5) Hb2' exec_n_end by fastforce+
    from HCb2(1) HCb1(1) False have "i = size (bcomp m (And b1 b2) f j) + (if f = bval (And b1 b2) (s \<circ> m) then j else 0)" by simp
    with HCb1(2, 3) HCb2(2, 3) show ?thesis by blast
  qed
next
  case (Less x1a x2a)
  thm exec_n_split_full
  thm exec1_def
  let ?ca1 = "acomp m x1a" and ?ca2 = "acomp m x2a" and ?jmp = "(if f then [JMPLESS j] else [JMPGE j])"
  let ?cbLess = "bcomp m (Less x1a x2a) f j"
  from Less(3) have Hexits23: "exits (?ca2 @ ?jmp) \<subseteq> {0..}" by auto
  from exec_n_split_full [OF _ _ _ Hexits23] Less(1, 2) have "\<exists>k1 k23 s'' stk''.
    ?ca1 \<turnstile> (0, s, stk) \<rightarrow>^k1 (size ?ca1, s'', stk'') \<and>
    ?ca2 @ ?jmp \<turnstile> (0, s'', stk'') \<rightarrow>^k23 (i - size ?ca1, s', stk')"
    by auto
  then obtain k1 k23 s'' stk'' where He1: "?ca1 \<turnstile> (0, s, stk) \<rightarrow>^k1 (size ?ca1, s'', stk'')"
    and He2: "?ca2 @ ?jmp \<turnstile> (0, s'', stk'') \<rightarrow>^k23 (i - size ?ca1, s', stk')"
    by meson
  from He1 have "s'' = s" "stk'' = aval x1a (s \<circ> m) # stk" by auto
  with He2 have He2': "?ca2 @ ?jmp \<turnstile> (0, s, aval x1a (s \<circ> m) # stk) \<rightarrow>^k23 (i - size ?ca1, s', stk')" by simp
  from exec_n_split_full He2' Less(2, 3) have "\<exists>k2 k3 s''' stk'''.
    ?ca2 \<turnstile> (0, s, aval x1a (s \<circ> m) # stk) \<rightarrow>^k2 (size ?ca2, s''', stk''') \<and>
    ?jmp \<turnstile> (0, s''', stk''') \<rightarrow>^k3 (i - size ?ca1 - size ?ca2, s', stk')" by auto
  then obtain k2 k3 s''' stk''' where He2: "?ca2 \<turnstile> (0, s, aval x1a (s \<circ> m) # stk) \<rightarrow>^k2 (size ?ca2, s''', stk''')"
    and He3: "?jmp \<turnstile> (0, s''', stk''') \<rightarrow>^k3 (i - size ?ca1 - size ?ca2, s', stk')" by meson
  from He2 have "s''' = s" "stk''' = aval x2a (s \<circ> m) # aval x1a (s \<circ> m) # stk" by auto
  with He3 have He3': "?jmp \<turnstile> (0, s, aval x2a (s \<circ> m) # aval x1a (s \<circ> m) # stk) \<rightarrow>^k3 (i - size ?ca1 - size ?ca2, s', stk')" by simp
  from exec_n_simps(1) He3' Less(2) have "\<exists>c. ?jmp \<turnstile> (0, s, aval x2a (s \<circ> m) # aval x1a (s \<circ> m) # stk) \<rightarrow> c \<and> ?jmp \<turnstile> c \<rightarrow>^(k3 - 1) (i - size ?ca1 - size ?ca2, s', stk') \<and> 0 < k3"
    by auto
  then obtain c where He3'': "?jmp \<turnstile> (0, s, aval x2a (s \<circ> m) # aval x1a (s \<circ> m) # stk) \<rightarrow> c" and He4: "?jmp \<turnstile> c \<rightarrow>^(k3 - 1) (i - size ?ca1 - size ?ca2, s', stk')" and "0 < k3" by auto
  let ?jpc = "if f \<longleftrightarrow> aval x1a (s \<circ> m) < aval x2a (s \<circ> m) then (1 + j) else 1"
  from He3'' have "c = iexec (?jmp !! 0) (0, s, aval x2a (s \<circ> m) # aval x1a (s \<circ> m) # stk)" by auto
  then have "c = (?jpc, s, stk)" by simp
  with He4 have He4': "?jmp \<turnstile> (?jpc, s, stk) \<rightarrow>^(k3 - 1) (i - size ?ca1 - size ?ca2, s', stk')" by simp
  with exec_n_simps(2) Less(3) have HC: "i - size ?ca1 - size ?ca2 = (if f \<longleftrightarrow> aval x1a (s \<circ> m) < aval x2a (s \<circ> m) then (1 + j) else 1)"
    "s' = s" "stk' = stk" "k3 - 1 = 0" by auto
  from HC(1) have "i = size ?cbLess + (if f = bval (Less x1a x2a) (s \<circ> m) then j else 0)" by auto
  with HC(2, 3) show ?case by blast
qed

lemma ccomp_empty [elim!]:
  "ccomp m c = [] \<Longrightarrow> (c,s) \<Rightarrow> s"
  by (induct c) auto

declare assign_simp [simp]

lemma ccomp_exec_n:
  "ccomp m c \<turnstile> (0, s, stk) \<rightarrow>^n (size (ccomp m c), t, stk')
  \<Longrightarrow> inj_on m (svars_in c)
  \<Longrightarrow> (c, s \<circ> m) \<Rightarrow> (t \<circ> m) \<and> stk' = stk"
proof (induction c arbitrary: s t stk stk' n)
  case SKIP
  thus ?case by auto
next
  case (Assign x a)
  value "ccomp m (x ::= a)"
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
qed

theorem ccomp_exec:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk') \<Longrightarrow> (c,s) \<Rightarrow> t"
  by (auto dest: exec_exec_n ccomp_exec_n)

corollary ccomp_sound:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)  \<longleftrightarrow>  (c,s) \<Rightarrow> t"
  by (blast intro!: ccomp_exec ccomp_bigstep)

end
*)