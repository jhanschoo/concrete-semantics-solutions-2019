theory Short_Theory_8_4
  imports "HOL-IMP.Big_Step" "HOL-IMP.Star"
begin
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

subsection "List setup"

primrec (nonexhaustive) inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
  "(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

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
type_synonym config = "int \<times> mem_state \<times> int"

abbreviation "hd2 xs == hd (tl xs)"
abbreviation "tl2 xs == tl (tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
  "iexec (LOADI n) (pc, s, sp) = (pc + 1, s(sp - 1 := n), sp - 1)" |
  "iexec (LOAD a) (pc, s, sp) = (pc + 1, s(sp - 1 := s a), sp - 1)" |
  "iexec ADD (pc, s, sp) = (pc + 1, s(sp + 1 := s (sp + 1) + s sp), sp + 1)" |
  "iexec (STORE a) (pc, s, sp) = (pc + 1, s(a := s sp), sp + 1)" |
  "iexec (JMP n) (pc, s, sp) = (pc + 1 + n, s, sp)" |
  "iexec (JMPLESS n) (pc, s, sp) = (if s (sp + 1) < s sp then pc + 1 + n else pc + 1, s, sp + 2)" |
  "iexec (JMPGE n) (pc, s, sp) = (if s (sp + 1) >= s sp then pc + 1 + n else pc + 1, s, sp + 2)"

abbreviation stack_eq :: "int \<Rightarrow> mem_state \<Rightarrow> mem_state \<Rightarrow> bool"
  where "stack_eq sp s t \<equiv> (\<forall> a. (sp \<le> a \<and> a < 0) \<longrightarrow> s a = t a)"

definition exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60)  where
  "P \<turnstile> c \<rightarrow> c' \<longleftrightarrow>
  (\<exists>pc s sp. c = (pc, s, sp) \<and>
    (\<forall> a. (P !! pc) = STORE a \<longrightarrow> 0 \<le> a) \<and>
    0 \<le> pc \<and> pc < size P \<and>
    sp \<le> 0 \<and>
    c' = iexec (P !! pc) (pc, s, sp))"
  (* While we can check  *)

lemma exec1I [intro, code_pred_intro]:
  "\<lbrakk>c' = iexec (P !! pc) (pc, s, sp);
    \<forall> a. (P !! pc) = STORE a \<longrightarrow> 0 \<le> a;
    0 \<le> pc; pc < size P;
    sp \<le> 0
  \<rbrakk> \<Longrightarrow> P \<turnstile> (pc, s, sp) \<rightarrow> c'"
  using exec1_def by blast

code_pred exec1 by (simp add: exec1_def)

abbreviation exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
  ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50) where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

lemma iexec_shift [simp]: 
  "(n + pc', s', sp') = iexec x (n + pc, s, sp) \<longleftrightarrow>
  (pc', s', sp') = iexec x (pc, s, sp)"
  by (cases x, auto)

(* trivial: iexec (P !! i) depends only on first i elements of P, and 0 \<le> i < size P *)
lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow> c'"
  by (auto simp add: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P @ P' \<turnstile> c \<rightarrow>* c'"
  by (induct rule: star.induct) (blast intro: star.step exec1_appendR)+

lemma exec1_appendL: "P \<turnstile> (pc, s, sp) \<rightarrow> (pc', s', sp') \<Longrightarrow>
  P' @ P \<turnstile> (size P' + pc, s, sp) \<rightarrow> (size P' + pc', s', sp')"
  by (auto simp add: exec1_def)

lemma exec_appendL: "P \<turnstile> (pc, s, sp) \<rightarrow>* (pc', s', sp') \<Longrightarrow>
  P' @ P \<turnstile> (size P' + pc, s, sp) \<rightarrow>* (size P' + pc', s', sp')"
  by (induct rule: exec_induct) (blast intro: star.step exec1_appendL)+

(* specialize append lemmas to have tools automatically reason about execution
  in certain safe and uninteresting cases.
*)
lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0, s, sp) \<rightarrow>* (pc', t, sp') \<Longrightarrow>
  instr # P \<turnstile> (1, s, sp) \<rightarrow>* (1 + pc', t, sp')"
  by (drule exec_appendL [where P'="[instr]"]) simp

(* as exec_appendL, with (i := i - size P'), precondition necessary to satisfy exec1 precondition *)
lemma exec_appendL_if [intro]:
  "\<lbrakk>size P' \<le> pc;
    P \<turnstile> (pc - size P', s, sp) \<rightarrow>* (pci, s', sp');
    pc' = size P' + pci
  \<rbrakk> \<Longrightarrow> P' @ P \<turnstile> (pc, s, sp) \<rightarrow>* (pc', s', sp')"
  by (drule exec_appendL [where P'=P']) simp

lemma exec_append_trans [intro]:
  "\<lbrakk>P \<turnstile> (0, s, sp) \<rightarrow>* (pci, si, spi);
    size P \<le> pci;
    P' \<turnstile>  (pci - size P, si, spi) \<rightarrow>* (pci', s', sp');
    pc' = size P + pci'
  \<rbrakk> \<Longrightarrow> P @ P' \<turnstile> (0, s, sp) \<rightarrow>* (pc', s', sp')"
  by(metis star_trans [OF exec_appendR exec_appendL_if])
                                               
declare Let_def [simp]

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
  "addrs_in c \<equiv> int ` (Suc ` {..<length (vars_in c)})"

abbreviation on_eq :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "on_eq A f g \<equiv> (\<forall> a \<in> A. f a = g a)"

abbreviation nneg_int :: "int set" where
  "nneg_int \<equiv> {n\<in>\<int>. n \<ge> 0}"

lemma vars_in_distinct: "distinct (vars_in c)" by auto

fun nth_inv_c :: "com \<Rightarrow> vname \<Rightarrow> nat" where
  "nth_inv_c c = the_inv_into ({..<length (vars_in c)}) ((!) (vars_in c))"

fun addr_of :: "com \<Rightarrow> vname \<Rightarrow> int" where
  "addr_of c v = (if v \<in> svars_in c
    then (int \<circ> Suc \<circ> nth_inv_c c) v
    else 0)"

lemma bij_addr_of: "bij_betw (addr_of c) (svars_in c) (addrs_in c)"
proof -
  have "bij_betw ((!) (vars_in c)) {..<length (vars_in c)} (svars_in c)"
    by (rule bij_betw_nth, auto simp add: vars_in_distinct)
  then have 0: "bij_betw (nth_inv_c c) (svars_in c) {..<length (vars_in c)}" (is ?P0)
    by (simp add: bij_betw_the_inv_into)
  have 1: "bij_betw Suc {..<length (vars_in c)} (Suc ` {..<length (vars_in c)})" by simp
  with bij_betw_comp_iff [OF 0] have 2: "bij_betw (Suc \<circ> nth_inv_c c) (svars_in c) (Suc ` {..<length (vars_in c)})" by blast
  have 3: "bij_betw int (Suc ` {..<length (vars_in c)}) (addrs_in c)" (is ?P1) by simp
  with 1 bij_betw_comp_iff [OF 2, of int "addrs_in c"] have "bij_betw (int \<circ> (Suc \<circ> nth_inv_c c)) (svars_in c) (addrs_in c)" by auto
  then have 4: "bij_betw (int \<circ> Suc \<circ> nth_inv_c c) (svars_in c) (addrs_in c)" by (simp add: comp_assoc)
  have 5: "\<And>a. a \<in> svars_in c \<Longrightarrow> (int \<circ> Suc \<circ> nth_inv_c c) a = addr_of c a" by simp
  from bij_betw_cong [of "svars_in c" "int \<circ> Suc \<circ> nth_inv_c c" "addr_of c" "addrs_in c", OF 5] 4
  show 6: "bij_betw (addr_of c) (svars_in c) (addrs_in c)" by blast
qed

corollary inj_on_addr_of: "inj_on (addr_of c) (svars_in c)" using bij_addr_of bij_betw_def by blast

subsection "mmap setup"

lemma inj_on_cancel_r: "\<lbrakk>inj_on b A; f \<circ> b = g \<circ> b\<rbrakk> \<Longrightarrow> on_eq (b ` A) f g" using comp_eq_dest by fastforce

lemma inj_on_comp_update: "inj_on b A \<Longrightarrow> \<forall> x \<in> A. on_eq A ((f \<circ> b)(x := y)) (f(b x := y) \<circ> b)"
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
  then show "on_eq A ((f \<circ> b)(x := y)) (f(b x := y) \<circ> b)" by blast
qed

lemma inj_on_cancel_r2: "inj_on b A \<Longrightarrow> \<exists> g. on_eq A f (g \<circ> b)"
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
  "\<lbrakk>sp \<le> 0;
    \<forall>a\<in>range m. a \<ge> 0;
    on_eq (set (vars_in_aexp a)) s (s' \<circ> m)
  \<rbrakk> \<Longrightarrow> \<exists>t'. (acomp m a \<turnstile> (0, s', sp) \<rightarrow>* (size (acomp m a), t', sp - 1)) \<and>
    stack_eq sp s' t' \<and>
    (\<forall>a\<ge>0. s' a = t' a) \<and>
    t' (sp - 1) = aval a s"
proof (induct a arbitrary: s' sp)
  case (Plus a1 a2)
  let ?ac1 = "acomp m a1" and ?av1 = "aval a1 s"
    and ?ac2 = "acomp m a2" and ?av2 = "aval a2 s"
    and ?cap = "acomp m (Plus a1 a2)"
  from Plus(1, 3-5) have "\<exists>t'. (?ac1 \<turnstile> (0, s', sp) \<rightarrow>* (size ?ac1, t', sp - 1)) \<and>
    stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a) \<and> t' (sp - 1) = ?av1" by simp
  then obtain si where He1: "?ac1 \<turnstile> (0, s', sp) \<rightarrow>* (size ?ac1, si, sp - 1)"
    and Hs1: "stack_eq sp s' si"
    and Ha1: "\<And>a. a \<ge> 0 \<Longrightarrow> s' a = si a"
    and Hv1: "si (sp - 1) = ?av1" by auto
  from Plus(3) have H1: "sp - 1 \<le> 0" by simp
  from Plus(4, 5) Ha1 have H2: "on_eq (set (vars_in_aexp a2)) s (si \<circ> m)" by simp
  from Plus(2) [OF H1 Plus(4) H2] have "\<exists>t'. (?ac2 \<turnstile> (0, si, sp - 1) \<rightarrow>* (size ?ac2, t', sp - 2)) \<and>
    stack_eq (sp - 1) si t' \<and> (\<forall>a\<ge>0. si a = t' a) \<and> t' (sp - 2) = aval a2 s" by simp
  then obtain t' where He2: "?ac2 \<turnstile> (0, si, sp - 1) \<rightarrow>* (size ?ac2, t', sp - 2)"
    and Hs2: "stack_eq (sp - 1) si t'"
    and Ha2: "\<And>a. 0 \<le> a \<Longrightarrow> si a = t' a"
    and Hv2: "t' (sp - 2) = ?av2" by auto
  show ?case
  proof (intro exI conjI)
    from Plus(3) have "[ADD] \<turnstile> (0, t', sp - 2) \<rightarrow>* (1, t'(sp - 1 := t' (sp - 2) + t' (sp - 1)), sp - 1)" by fastforce
    with He1 He2 show "?cap \<turnstile> (0, s', sp) \<rightarrow>* (size ?cap, t'(sp - 1 := t' (sp - 2) + t' (sp - 1)), sp - 1)" by fastforce
    from Hs1 Hs2 show "stack_eq sp s' (t'(sp - 1 := t' (sp - 2) + t' (sp - 1)))" by simp
    from Plus(3) Ha1 Ha2 show "\<forall>a\<ge>0. s' a = (t'(sp - 1 := t' (sp - 2) + t' (sp - 1))) a" by simp
    from Plus(3) Hv1 Hs2 Hv2 show "(t'(sp - 1 := t' (sp - 2) + t' (sp - 1))) (sp - 1) = aval (Plus a1 a2) s" by auto
  qed
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
  "\<lbrakk>sp \<le> 0;
    \<forall>a\<in>range m. a \<ge> 0;
    on_eq (set (vars_in_bexp b)) s (s' \<circ> m);
    0 \<le> n
  \<rbrakk> \<Longrightarrow> \<exists>t'. (bcomp m b f n \<turnstile> (0, s', sp) \<rightarrow>* (size (bcomp m b f n) + (if f = bval b s then n else 0), t', sp)) \<and>
    stack_eq sp s' t' \<and>
    (\<forall>a\<ge>0. s' a = t' a)"
proof (induct b arbitrary: f n s')
  case (Not b)
  then have "\<exists>t'. (bcomp m b (\<not> f) n \<turnstile> (0, s', sp) \<rightarrow>* (size (bcomp m b (\<not> f) n) + (if (\<not> f) = bval b s then n else 0), t', sp)) \<and>
    stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by simp
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

  from And(1) [of s' ?n' False] And(3-6) have "\<exists> t'. (?bc1 \<turnstile> (0, s', sp) \<rightarrow>* (?sizeb1 + (if False = ?bv1 then ?n' else 0), t', sp)) \<and>
    stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by simp
  then obtain si where He1: "?bc1 \<turnstile> (0, s', sp) \<rightarrow>* (?sizeb1 + (if False = ?bv1 then ?n' else 0), si, sp)"
    and Hs1: "stack_eq sp s' si"
    and Hv1: "\<forall>a\<ge>0. s' a = si a" by auto
  from And(2-6) Hv1 have "\<exists>t'. (?bc2 \<turnstile> (0, si, sp) \<rightarrow>* (?sizeb2 + (if f = ?bv2 then n else 0), t', sp)) \<and>
    stack_eq sp si t' \<and> (\<forall>a\<ge>0. si a = t' a)" by simp
  then obtain t' where He2: "?bc2 \<turnstile> (0, si, sp) \<rightarrow>* (?sizeb2 + (if f = ?bv2 then n else 0), t', sp)"
    and Hs2: "stack_eq sp si t'"
    and Hv2: "\<forall>a\<ge>0. si a = t' a" by auto
  from Hs1 Hs2 have Hs3: "stack_eq sp s' t'" by simp
  from Hv1 Hv2 have Hv3: "\<forall>a\<ge>0. s' a = t' a" by simp
  show ?case
  proof (cases ?bv1)
    case Hbv1: True
    from Hbv1 He1 He2 Hs3 Hv3 show ?thesis by fastforce
  next
    case Hbv1: False
    then show ?thesis
    proof (cases f)
      case Hf: True
      from Hbv1 Hf He1 Hs1 Hv1 show ?thesis by fastforce
    next
      case Hf: False
      from Hbv1 Hf He1 And(6) Hs1 Hv1 show ?thesis by (fastforce simp add: add.assoc)
    qed
  qed
next
  case (Less x1a x2a)
  let ?ac1 = "acomp m x1a" and ?av1 = "aval x1a s"
    and ?ac2 = "acomp m x2a" and ?av2 = "aval x2a s"
    and ?jmp = "if f then [JMPLESS n] else [JMPGE n]"
    and ?bcLess = "bcomp m (Less x1a x2a) f n"
    and ?bvLess = "bval (Less x1a x2a) s"
  from Less(1-3) have "\<exists>t'. (?ac1 \<turnstile> (0, s', sp) \<rightarrow>* (size ?ac1, t', sp - 1)) \<and> stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a) \<and> t' (sp - 1) = ?av1" by auto
  then obtain si where He1: "?ac1 \<turnstile> (0, s', sp) \<rightarrow>* (size ?ac1, si, sp - 1)"
    and Hs1: "stack_eq sp s' si"
    and Ha1: "\<forall>a\<ge>0. s' a = si a"
    and Hv1: "si (sp - 1) = ?av1" by auto
  from Less(2, 3) Ha1 have Heq1: "on_eq (set (vars_in_bexp (Less x1a x2a))) s (si \<circ> m)" by simp
  from Less(1,2) Heq1 have "\<exists>t'. (?ac2 \<turnstile> (0, si, sp - 1) \<rightarrow>* (size ?ac2, t', sp - 2)) \<and> stack_eq (sp - 1) si t' \<and> (\<forall>a\<ge>0. si a = t' a) \<and> t' (sp - 2) = ?av2"
    using acomp_correct [of "sp - 1"] by simp
  then obtain t' where He2: "?ac2 \<turnstile> (0, si, sp - 1) \<rightarrow>* (size ?ac2, t', sp - 2)"
    and Hs2: "stack_eq (sp - 1) si t'"
    and Ha2: "\<forall>a\<ge>0. si a = t' a"
    and Hv2: "t' (sp - 2) = ?av2" by auto
  value "iexec (JMPLESS n) (0, t', sp - 2)"
  show ?case
  proof (intro exI conjI)
    from Hv1 Hv2 Hs2 Less(1) have He3: "?jmp \<turnstile> (0, t', sp - 2) \<rightarrow>* (1 + (if f = ?bvLess then n else 0), t', sp)" by fastforce
    from He1 He2 He3 show "?bcLess \<turnstile> (0, s', sp) \<rightarrow>* (size ?bcLess + (if f = ?bvLess then n else 0), t', sp)" by (fastforce simp add: add.assoc)
    from Hs1 Hs2 show "stack_eq sp s' t'" by simp
    from Ha1 Ha2 show "\<forall>a\<ge>0. s' a = t' a" by simp
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

(* to each big-step that brings a var-val map A to a var-val map B,
  our compiled program non-deterministically brings every addr-val A' state that agrees with A on the variables appearing in the program
  to an addr-val B' state that agrees with B on the variables appearing in the program that yet agrees with A
  on the variables not appearing in the program
*)

(* The notion of the var-val map, on vars not appearing in the commands being preserved is significant here,
  but is not important in the results proven in Big Step. Hence we prove that here.
*)

lemma bigstep_state_invariance: "(c, s) \<Rightarrow> t \<Longrightarrow> on_eq (-(svars_in c)) s t"
  by (induct rule: big_step_induct) simp+

lemma map_invariance: "\<lbrakk>
  inj_on m (svars_in c);
  \<forall>a\<in>range m. a \<ge> 0;
  (c\<^sub>1, s) \<Rightarrow> t;
  svars_in c\<^sub>1 \<subseteq> svars_in c;
  on_eq (svars_in c) s (s' \<circ> m);
  on_eq (svars_in c\<^sub>1) t (t' \<circ> m);
  \<forall>a\<ge>0. a \<notin> m ` (svars_in c\<^sub>1) \<longrightarrow> s' a = t' a
\<rbrakk> \<Longrightarrow> \<forall> v \<in> svars_in c. t v = t' (m v)"
proof
  assume H: "inj_on m (svars_in c)"
    "\<forall>a\<in>range m. a \<ge> 0"
    "(c\<^sub>1, s) \<Rightarrow> t"
    "svars_in c\<^sub>1 \<subseteq> svars_in c"
    "on_eq (svars_in c) s (s' \<circ> m)"
    "on_eq (svars_in c\<^sub>1) t (t' \<circ> m)"
    "\<forall>a\<ge>0. a \<notin> m ` (svars_in c\<^sub>1) \<longrightarrow> s' a = t' a"
  fix v
  assume H1: "v \<in> svars_in c"
  show "t v = t' (m v)"
  proof (cases "v \<in> svars_in c\<^sub>1")
    case False
    from H(1, 2, 4) H1 False have H2: "m v \<ge> 0 \<and> m v \<notin> m ` svars_in c\<^sub>1"
      by (meson inj_on_image_mem_iff_alt range_eqI)
    from H(3, 4) False have "t v = s v" using bigstep_state_invariance by fastforce
    also from H(5) H1 have "\<dots> = s' (m v)" by simp
    also from H(7) H2 have "\<dots> = t' (m v)" by simp
    finally show ?thesis .
  qed (simp add: H(6))
qed

lemma ccomp_bigstep: "\<lbrakk>
  (c, s) \<Rightarrow> t;
  inj_on m (svars_in c);
  sp \<le> 0;
  \<forall>a\<in>range m. a \<ge> 0;
  on_eq (svars_in c) s (s' \<circ> m)
\<rbrakk> \<Longrightarrow> \<exists> t'. (ccomp m c \<turnstile> (0, s', sp) \<rightarrow>* (size (ccomp m c), t', sp)) \<and>
  on_eq (svars_in c) t (t' \<circ> m) \<and>
  (\<forall> a \<ge> 0. a \<notin> m ` (svars_in c) \<longrightarrow> s' a = t' a)"
proof (induct c s t arbitrary: sp s' rule: big_step_induct)
  case (Skip s)
  show ?case
  proof (intro exI conjI)
    show "ccomp m SKIP \<turnstile> (0, s', sp) \<rightarrow>* (size (ccomp m SKIP), s', sp)" by simp
    show "on_eq (svars_in SKIP) s (s' \<circ> m)" by simp
    show "\<forall>a\<ge>0. a \<notin> m ` svars_in SKIP \<longrightarrow> s' a = s' a" by simp
  qed
next
  case (Assign x a s)
  thm acomp_correct
  let ?ac = "acomp m a" and ?av = "aval a s" and ?cc = "ccomp m (x ::= a)"
  from Assign(2, 3, 4) have "\<exists>t'. (?ac \<turnstile> (0, s', sp) \<rightarrow>* (size ?ac, t', sp - 1)) \<and>
    stack_eq sp s' t' \<and>
    (\<forall>a\<ge>0. s' a = t' a) \<and>
    t' (sp - 1) = ?av" by auto
  then obtain si where He1: "?ac \<turnstile> (0, s', sp) \<rightarrow>* (size ?ac, si, sp - 1)"
    and Hs1: "stack_eq sp s' si"
    and Ha1: "\<forall>a\<ge>0. s' a = si a"
    and Hv1: "si (sp - 1) = ?av" by auto
  show ?case
  proof (intro exI conjI)
    let ?t' = "si(m x := si (sp - 1))"
    from Assign(2, 3) have "[STORE (m x)] \<turnstile> (0, si, sp - 1) \<rightarrow>* (1, ?t', sp)" by fastforce
    with He1 show "?cc \<turnstile> (0, s', sp) \<rightarrow>* (size ?cc, ?t', sp)" by auto
    have H1: "x \<in> svars_in (x ::= a)" by simp
    show "on_eq (svars_in (x ::= a)) (s(x := aval a s)) (si(m x := si (sp - 1)) \<circ> m)"
    proof
      fix v
      assume H2: "v \<in> svars_in (x ::= a)"
      show "(s(x := aval a s)) v = (si(m x := si (sp - 1)) \<circ> m) v"
      proof (cases "v = x")
        case False
        then have "(s(x := aval a s)) v = s v" by simp
        also from Assign(4) H2 have "\<dots> = s' (m v)" by simp
        also from Assign(3,4) Ha1 H2 have "\<dots> = si (m v)" by simp
        also from Assign(1) H1 H2 False have "\<dots> = (si(m x := si (sp - 1)) \<circ> m) v" using inj_onD by fastforce
        finally show ?thesis .
      qed (simp add: Hv1)
    qed
    from Ha1 H1 show "\<forall>a'\<ge>0. a' \<notin> m ` svars_in (x ::= a) \<longrightarrow> s' a' = (si(m x := si (sp - 1))) a'" by auto
  qed
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  let ?c1 = "ccomp m c\<^sub>1" and ?c2 = "ccomp m c\<^sub>2" and ?cs = "ccomp m (c\<^sub>1;; c\<^sub>2)"
    and ?s1 = "svars_in c\<^sub>1" and ?s2 = "svars_in c\<^sub>2" and ?ss = "svars_in (c\<^sub>1;; c\<^sub>2)"
  from Seq(2, 5-8) have "\<exists>t'. (?c1 \<turnstile> (0, s', sp) \<rightarrow>* (size ?c1, t', sp)) \<and>
    on_eq ?s1 s\<^sub>2 (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?s1 \<longrightarrow> s' a = t' a)" using inj_on_subset by fastforce
  then obtain s\<^sub>2' where He1: "?c1 \<turnstile> (0, s', sp) \<rightarrow>* (size ?c1, s\<^sub>2', sp)"
    and Hv1: "on_eq ?s1 s\<^sub>2 (s\<^sub>2' \<circ> m)"
    and Ha1: "\<forall>a\<ge>0. a \<notin> m ` ?s1 \<longrightarrow> s' a = s\<^sub>2' a" by auto
  have Hv1': "on_eq ?ss s\<^sub>2 (s\<^sub>2' \<circ> m)"
    using map_invariance [OF Seq(5) Seq(7) Seq(1) _ Seq(8) Hv1 Ha1] by simp
  from Seq(4, 5-7) Hv1' have "\<exists>t'. (?c2 \<turnstile> (0, s\<^sub>2', sp) \<rightarrow>* (size ?c2, t', sp)) \<and>
    on_eq ?s2 s\<^sub>3 (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?s2 \<longrightarrow> s\<^sub>2' a = t' a)" using inj_on_subset by fastforce
  then obtain s\<^sub>3' where He2: "?c2 \<turnstile> (0, s\<^sub>2', sp) \<rightarrow>* (size ?c2, s\<^sub>3', sp)"
    and Hv2: "on_eq ?s2 s\<^sub>3 (s\<^sub>3' \<circ> m)"
    and Ha2: "\<forall>a\<ge>0. a \<notin> m ` ?s2 \<longrightarrow> s\<^sub>2' a = s\<^sub>3' a" by auto
  show ?case
  proof (intro exI conjI)
    from He1 He2 show "?cs \<turnstile> (0, s', sp) \<rightarrow>* (size ?cs, s\<^sub>3', sp)" by auto
    show "on_eq ?ss s\<^sub>3 (s\<^sub>3' \<circ> m)"
      using map_invariance [OF Seq(5) Seq(7) Seq(3) _ Hv1' Hv2 Ha2] by simp
    from Ha1 Ha2 show "\<forall>a\<ge>0. a \<notin> m ` ?ss \<longrightarrow> s' a = s\<^sub>3' a" by fastforce
  qed
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  let ?cc1 = "ccomp m c\<^sub>1" and ?cc2 = "ccomp m c\<^sub>2" and ?ci = "ccomp m (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
    and ?sb = "set (vars_in_bexp b)" and ?sc1 = "svars_in c\<^sub>1" and ?sc2 = "svars_in c\<^sub>2"
    and ?si = "svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
  let ?cb = "bcomp m b False (size ?cc1 + 1)"
  from bcomp_correct [OF IfTrue(5) IfTrue(6) _ _, of b s s' "size ?cc1 + 1" False] IfTrue(1, 7)
  have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb, t', sp)) \<and>
         stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by simp
  then obtain si where Heb: "?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb, si, sp)"
    and Hsb: "stack_eq sp s' si"
    and Hab: "\<forall>a\<ge>0. s' a = si a" by auto
  from IfTrue(6, 7) Hab have Heqb': "on_eq ?si s (si \<circ> m)" by simp
  then have Heqc: "on_eq ?sc1 s (si \<circ> m)" by simp
  from IfTrue(3) [OF _ IfTrue(5) IfTrue(6) Heqc] IfTrue(4)
  have "\<exists>t'. (?cc1 \<turnstile> (0, si, sp) \<rightarrow>* (size ?cc1, t', sp)) \<and>
       on_eq ?sc1 t (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?sc1 \<longrightarrow> si a = t' a)"
    using inj_on_subset by auto
  then obtain t' where Hec: "?cc1 \<turnstile> (0, si, sp) \<rightarrow>* (size ?cc1, t', sp)"
    and Hsc: "on_eq ?sc1 t (t' \<circ> m)"
    and Hac: "\<forall>a\<ge>0. a \<notin> m ` ?sc1 \<longrightarrow> si a = t' a" by auto
  show ?case
  proof (intro exI conjI)
    from IfTrue(5) have "JMP (size ?cc2) # ?cc2 \<turnstile> (0, t', sp) \<rightarrow> (size ?cc2 + 1, t', sp)" by fastforce
    with Heb Hec show "?ci \<turnstile> (0, s', sp) \<rightarrow>* (size ?ci, t', sp)" by (fastforce simp add: add.assoc)
    from map_invariance [OF IfTrue(4) IfTrue(6) IfTrue(2) _ Heqb' Hsc Hac]
    show "on_eq ?si t (t' \<circ> m)" by auto
    from Hab Hac show "\<forall>a\<ge>0. a \<notin> m ` ?si \<longrightarrow> s' a = t' a" by auto
  qed
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  let ?cc1 = "ccomp m c\<^sub>1" and ?cc2 = "ccomp m c\<^sub>2" and ?ci = "ccomp m (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
    and ?sb = "set (vars_in_bexp b)" and ?sc1 = "svars_in c\<^sub>1" and ?sc2 = "svars_in c\<^sub>2"
    and ?si = "svars_in (IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
  let ?cb = "bcomp m b False (size ?cc1 + 1)"
  from bcomp_correct [OF IfFalse(5) IfFalse(6), of b s s' "size ?cc1 + 1" False] IfFalse(7)
  have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + (if False = bval b s then size ?cc1 + 1 else 0), t', sp)) \<and>
         stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by fastforce
  then have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + size ?cc1 + 1, t', sp)) \<and>
         stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by (smt IfFalse(1))
  then obtain si where Heb: "?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + size ?cc1 + 1, si, sp)"
    and Hsb: "stack_eq sp s' si"
    and Hab: "\<forall>a\<ge>0. s' a = si a" by auto
  from IfFalse(6, 7) Hab have Heqb': "on_eq ?si s (si \<circ> m)" by simp
  from IfFalse(3) [OF _ IfFalse(5) IfFalse(6), of si] IfFalse(4) Heqb'
  have "\<exists>t'. (?cc2 \<turnstile> (0, si, sp) \<rightarrow>* (size ?cc2, t', sp)) \<and>
             on_eq ?sc2 t (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?sc2 \<longrightarrow> si a = t' a)"
    using inj_on_subset by fastforce
  then have "\<exists>t'. (?cc1 @ JMP (size ?cc2) # ?cc2 \<turnstile> (size ?cc1 + 1, si, sp) \<rightarrow>* (size ?cc1 + 1 + size ?cc2, t', sp)) \<and>
             on_eq ?sc2 t (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?sc2 \<longrightarrow> si a = t' a)"
    by fastforce
  then obtain t' where Hec: "?cc1 @ JMP (size ?cc2) # ?cc2 \<turnstile> (size ?cc1 + 1, si, sp) \<rightarrow>* (size ?cc1 + 1 + size ?cc2, t', sp)"
    and Hsc: "on_eq ?sc2 t (t' \<circ> m)"
    and Hac: "\<forall>a\<ge>0. a \<notin> m ` ?sc2 \<longrightarrow> si a = t' a" by auto
  show ?case
  proof (intro exI conjI)
    from Heb Hec show "?ci \<turnstile> (0, s', sp) \<rightarrow>* (size ?ci, t', sp)" by fastforce
    from map_invariance [OF IfFalse(4) IfFalse(6) IfFalse(2) _ Heqb' Hsc Hac]
    show "on_eq ?si t (t' \<circ> m)" by auto
    from Hab Hac show "\<forall>a\<ge>0. a \<notin> m ` ?si \<longrightarrow> s' a = t' a" by auto
  qed
next
  case (WhileFalse b s c)
  let ?cc = "ccomp m c" and ?cw = "ccomp m (WHILE b DO c)" and ?sw = "svars_in (WHILE b DO c)"
  let ?cb = "bcomp m b False (size ?cc + 1)"
  from bcomp_correct [OF WhileFalse(3) WhileFalse(4), of b s s' "size ?cc + 1" False] WhileFalse(5)
  have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + (if False = bval b s then size ?cc + 1 else 0), t', sp)) \<and>
             stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by auto
  then have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + size ?cc + 1, t', sp)) \<and>
             stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by (smt WhileFalse(1))
  then have "\<exists>t'. (?cw \<turnstile> (0, s', sp) \<rightarrow>* (size ?cw, t', sp)) \<and>
             stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by fastforce
  then obtain si where Heb: "?cw \<turnstile> (0, s', sp) \<rightarrow>* (size ?cw, si, sp)"
    and Hsb: "stack_eq sp s' si"
    and Hab: "\<forall>a\<ge>0. s' a = si a" by auto
  show ?case
  proof (intro exI conjI)
    from Heb show "?cw \<turnstile> (0, s', sp) \<rightarrow>* (size ?cw, si, sp)" .
    from WhileFalse(4, 5) Hab show "on_eq ?sw s (si \<circ> m)" by simp
    from Hab show "\<forall>a\<ge>0. a \<notin> m ` svars_in (WHILE b DO c) \<longrightarrow> s' a = si a" by simp
  qed
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?cc = "ccomp m c" and ?cw = "ccomp m (WHILE b DO c)" and ?sc = "svars_in c" and ?sw = "svars_in (WHILE b DO c)"
  let ?cb = "bcomp m b False (size ?cc + 1)"
  from bcomp_correct [OF WhileTrue(7) WhileTrue(8), of b s\<^sub>1 s' "size ?cc + 1" False] WhileTrue(9)
  have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + (if False = bval b s\<^sub>1 then size ?cc + 1 else 0), t', sp)) \<and>
             stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by auto
  then have "\<exists>t'. (?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb, t', sp)) \<and>
             stack_eq sp s' t' \<and> (\<forall>a\<ge>0. s' a = t' a)" by (smt WhileTrue(1))
  then obtain si where He1: "?cb \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb, si, sp)"
    and Hs1: "stack_eq sp s' si"
    and Ha1: "\<forall>a\<ge>0. s' a = si a" by auto

  from Ha1 WhileTrue(8, 9) have Heq1: "on_eq ?sw s\<^sub>1 (si \<circ> m)" by simp
  from WhileTrue(3) [OF _ WhileTrue(7) WhileTrue(8), of si] WhileTrue(6) Heq1
  have "\<exists>t'. (?cc \<turnstile> (0, si, sp) \<rightarrow>* (size ?cc, t', sp)) \<and>
           on_eq ?sc s\<^sub>2 (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?sc \<longrightarrow> si a = t' a)"
    using inj_on_subset by auto
  then obtain s\<^sub>2' where He2: "?cc \<turnstile> (0, si, sp) \<rightarrow>* (size ?cc, s\<^sub>2', sp)"
    and Hs2: "on_eq ?sc s\<^sub>2 (s\<^sub>2' \<circ> m)"
    and Ha2: "\<forall>a\<ge>0. a \<notin> m ` ?sc \<longrightarrow> si a = s\<^sub>2' a" by auto

  from He1 He2 have "?cw \<turnstile> (0, s', sp) \<rightarrow>* (size ?cb + size ?cc, s\<^sub>2', sp)" by fastforce
  moreover from WhileTrue(7) have "?cw \<turnstile> (size ?cb + size ?cc, s\<^sub>2', sp) \<rightarrow>* (0, s\<^sub>2', sp)" by fastforce
  ultimately have He12: "?cw \<turnstile> (0, s', sp) \<rightarrow>* (0, s\<^sub>2', sp)" using star_trans by auto

  have Heq2: "on_eq (svars_in (WHILE b DO c)) s\<^sub>2 (s\<^sub>2' \<circ> m)"
    using map_invariance [OF WhileTrue(6) WhileTrue(8) WhileTrue(2) _ Heq1 Hs2 Ha2] by simp
  from WhileTrue(5) [OF WhileTrue(6) WhileTrue(7) WhileTrue(8) Heq2]
  have "\<exists>t'. (?cw \<turnstile> (0, s\<^sub>2', sp) \<rightarrow>* (size ?cw, t', sp)) \<and>
     on_eq ?sw s\<^sub>3 (t' \<circ> m) \<and> (\<forall>a\<ge>0. a \<notin> m ` ?sw \<longrightarrow> s\<^sub>2' a = t' a)" .
  then obtain s\<^sub>3' where He3: "?cw \<turnstile> (0, s\<^sub>2', sp) \<rightarrow>* (size ?cw, s\<^sub>3', sp)"
    and Hs3: "on_eq ?sw s\<^sub>3 (s\<^sub>3' \<circ> m)"
    and Ha3: "\<forall>a\<ge>0. a \<notin> m ` ?sw \<longrightarrow> s\<^sub>2' a = s\<^sub>3' a" by auto
  show ?case
  proof (intro exI conjI)
    from He12 He3 show "?cw \<turnstile> (0, s', sp) \<rightarrow>* (size ?cw, s\<^sub>3', sp)" using star_trans by auto
    from Hs3 show "on_eq ?sw s\<^sub>3 (s\<^sub>3' \<circ> m)" .
    from Ha1 Ha2 Ha3 show "\<forall>a\<ge>0. a \<notin> m ` ?sw \<longrightarrow> s' a = s\<^sub>3' a" by auto
  qed
qed

lemma ccomp_bigstep_addr_of: "\<lbrakk>
  (c, s) \<Rightarrow> t;
  sp \<le> 0;
  on_eq (svars_in c) s (s' \<circ> (addr_of c))
\<rbrakk> \<Longrightarrow> \<exists> t'. (ccomp (addr_of c) c \<turnstile> (0, s', sp) \<rightarrow>* (size (ccomp (addr_of c) c), t', sp)) \<and>
  on_eq (svars_in c) t (t' \<circ> (addr_of c)) \<and>
  (\<forall> a \<ge> 0. a \<notin> (addr_of c) ` (svars_in c) \<longrightarrow> s' a = t' a)" using ccomp_bigstep inj_on_addr_of by fastforce

end