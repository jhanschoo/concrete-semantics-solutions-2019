theory Chapter12_4
imports "HOL-IMP.VCG" "HOL-IMP.Hoare_Examples"
begin

text \<open>
\exercise
Let @{term "asum i"} be the annotated command \texttt{y := 0; W}
where \texttt{W} is defined in Example~12.7. Prove
\<close>
definition asum :: "int \<Rightarrow> acom"where
  "asum i = ''y'' ::= (N 0);;
    {\<lambda>s. s ''y'' + sum (s ''x'') = sum i}
    WHILE Less (N 0) (V ''x'') DO
    (''y'' ::= Plus (V ''y'') (V ''x'');; ''x'' ::= Plus (V ''x'') (N (-1)))"

lemma "\<turnstile> {\<lambda>s. s ''x'' = i} strip(asum i) {\<lambda>s. s ''y'' = sum i}"
  unfolding asum_def
  by (rule vc_sound', auto)

text \<open>
with the help of corollary @{thm[source] vc_sound'}.
\endexercise

\exercise
Solve exercises \ref{exe:Hoare:sumeq} to \ref{exe:Hoare:sqrt} using the VCG:
for every Hoare triple @{prop"\<turnstile> {P} c {Q}"} from one of those exercises
define an annotated version @{text C} of @{text c} and prove
@{prop"\<turnstile> {P} strip C {Q}"} with the help of %Corollary~\ref{cor:vc_sound}
corollary @{thm[source] vc_sound'}.
\<close>

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = (And (Not (Less a1 a2)) (Not (Less a2 a1)))"

lemma bval_Eq[simp]: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  unfolding Eq_def by auto

lemma "\<turnstile> {\<lambda>s. s ''x'' = i \<and> 0 \<le> i} strip (
  ''y'' ::= N 0;;
  {\<lambda>s. s ''y'' = sum i - sum (s ''x'') \<and> 0 \<le> s ''x''}
  WHILE Not(Eq (V ''x'') (N 0))
  DO (''y'' ::= Plus (V ''y'') (V ''x'');;
    ''x'' ::= Plus (V ''x'') (N (-1))))
  {\<lambda>s. s ''y'' = sum i}"
  by (rule vc_sound', auto)

lemma "\<turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x} strip (
  {\<lambda>s. s ''y'' - s ''x'' = y - x \<and> 0 \<le> s ''x''}
  WHILE Less (N 0) (V ''x'')
  DO (''x'' ::= Plus (V ''x'') (N (-1));;
    ''y'' ::= Plus (V ''y'') (N (-1))))
  {\<lambda>t. t ''y'' = y - x}"
  by (rule vc_sound', auto)

abbreviation cmult :: com where
  "cmult \<equiv> ''z'' ::= N 0;;
    WHILE Less (N 0) (V ''y'') DO (''y'' ::= (Plus (V ''y'') (N (-1)));; ''z'' ::= (Plus (V ''z'') (V ''x'')))"

lemma
  "\<turnstile> {\<lambda>s.  s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> y} strip (
    ''z'' ::= N 0;;
    {\<lambda>s. s ''x'' = x \<and> s ''z'' = s ''x'' * (y - s ''y'') \<and> 0 \<le> s ''y''}
    WHILE Less (N 0) (V ''y'')
    DO (''y'' ::= (Plus (V ''y'') (N (-1)));;
      ''z'' ::= (Plus (V ''z'') (V ''x''))))
  {\<lambda>t. t ''z'' = x*y}"
  by (rule vc_sound', auto simp add: algebra_simps)

lemma
  "\<turnstile> { \<lambda>s. s ''x'' = i \<and> 0 \<le> i} strip (
     ''r'' ::= N 0;; ''r2'' ::= N 1;;
     {\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> s ''r2'' = (s ''r'' + 1)\<^sup>2}
     WHILE (Not (Less (V ''x'') (V ''r2'')))
     DO (''r'' ::= Plus (V ''r'') (N 1);;
            ''r2'' ::= Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1))))
     {\<lambda>s. (s ''r'')^2 \<le> i \<and> i < (s ''r'' + 1)^2}"
proof (rule vc_sound', auto simp add: algebra_simps)
  fix s :: state
  have "\<And>x::int. 3 + (2 * x + (1 + x)\<^sup>2) = (2 + x)\<^sup>2"
  proof -
    fix x :: int
    have "(1 + x)\<^sup>2 = x\<^sup>2 + 2 * x + 1" by (simp add: power2_sum)
    then have "3 + (2 * x + (1 + x)\<^sup>2) = 3 + (2 * x + (x\<^sup>2 + 2 * x + 1))" by simp
    also have "\<dots> = 4 + 4 * x + x\<^sup>2" by simp
    also have "\<dots> = (2 + x)\<^sup>2" by (simp add: power2_sum)
    finally show "3 + (2 * x + (1 + x)\<^sup>2) = (2 + x)\<^sup>2" .
  qed
  then show "3 + (2 * s ''r'' + (1 + s ''r'')\<^sup>2) = (2 + s ''r'')\<^sup>2" by simp
qed


text \<open>
\endexercise

\exercise
Having two separate functions @{const pre} and @{const vc} is inefficient.
When computing @{const vc} one often needs to compute @{const pre} too,
leading to multiple traversals of many subcommands. Define an optimised function
\<close>
fun prevc :: "acom \<Rightarrow> assn \<Rightarrow> assn \<times> bool" where
  "prevc SKIP Q = (Q, True)" |
  "prevc (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)), True)" |
  "prevc (C\<^sub>1;; C\<^sub>2) Q = (\<lambda>(P', S'). (\<lambda>(P, S). (P, S \<and> S')) (prevc C\<^sub>1 P')) (prevc C\<^sub>2 Q)" |
  "prevc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
    (\<lambda>(P\<^sub>1, S\<^sub>1). (\<lambda>(P\<^sub>2, S\<^sub>2). (\<lambda>s. if bval b s then P\<^sub>1 s else P\<^sub>2 s, S\<^sub>1 \<and> S\<^sub>2) ) (prevc C\<^sub>2 Q)) (prevc C\<^sub>1 Q)" |
  "prevc ({I} WHILE b DO C) Q = (\<lambda>(P, S).
    (I, (\<forall>s.
      (I s \<and> bval b s \<longrightarrow> P s) \<and>
      (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and>
      S)) (prevc C I)"

text \<open> that traverses the command only once. Prove \<close>

lemma "prevc C Q = (pre C Q, vc C Q)"
  by (induct C arbitrary: Q) auto

text \<open>
\endexercise

\exercise
Design a VCG that computes post rather than preconditions.
Start by solving Exercise~\ref{exe:fwdassign}. Now modify theory
@{short_theory "VCG"} as follows. Instead of @{const pre} define a function
\<close>

fun post :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
  "post SKIP P = P" |
  "post (x ::= a) P = (\<lambda>s. \<exists> x'. P (s(x := x')) \<and> s x = aval a (s(x := x')))" |
  "post (C\<^sub>1;; C\<^sub>2) P = post C\<^sub>2 (post C\<^sub>1 P)" |
  "post (IF b THEN C\<^sub>1 ELSE C\<^sub>2) P =
  (\<lambda>t. post C\<^sub>1 (\<lambda>s. P s \<and> bval b s) t \<or> post C\<^sub>2 (\<lambda>s. P s \<and> \<not>bval b s) t)" |
  "post ({I} WHILE b DO c) P = (\<lambda>s. I s \<and> \<not>bval b s)"

text \<open>
such that (with the execption of loops) @{term "post C P"} is the strongest
postcondition of @{text C} w.r.t.\ the precondition @{text P} (see also
Exercise~\ref{exe:sp}). Now modify @{const vc} such that is uses
@{const post} instead of @{const pre} and prove its soundness
and completeness.
\<close>

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
  "vc SKIP P = True" |
  "vc (x ::= a) P = True" |
  "vc (C\<^sub>1;; C\<^sub>2) P \<longleftrightarrow> vc C\<^sub>1 P \<and> vc C\<^sub>2 (post C\<^sub>1 P)" |
  "vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) P \<longleftrightarrow> vc C\<^sub>1 (\<lambda>s. P s \<and> bval b s) \<and> vc C\<^sub>2 (\<lambda>s. P s \<and> \<not>bval b s)" |
  "vc ({I} WHILE b DO C) P =
    ((\<forall>s. (post C (\<lambda>s. I s \<and> bval b s) s \<longrightarrow> I s) \<and>
      (P s \<longrightarrow> I s)) \<and>
      vc C (\<lambda>s. I s \<and> bval b s))"

lemma vc_sound: "vc C P \<Longrightarrow> \<turnstile> {P} strip C {post C P}"
proof (induction C arbitrary: P)
  case (Aassign x x2)
  show ?case
  proof (rule strengthen_pre; (simp, rule hoare.Assign)?; simp, intro allI impI)
    fix s :: state
    let ?H = "\<lambda>x'. P (s(x := x')) \<and> aval x2 s = aval x2 (s(x := x'))"
    assume "P s"
    then have "?H (s x)" by auto
    from exI [of ?H, OF this]
    show "\<exists>x'. ?H x'" by simp
  qed
next
  case (Aif b C1 C2)
  show ?case by (simp, rule hoare.If; rule weaken_post; (rule Aif(1) | rule Aif(2))?; insert Aif(3)) auto
next
  case (Awhile I b C)
  let ?c = "strip C"
  show ?case by (simp, rule strengthen_pre; (rule hoare.While, rule weaken_post; (rule Awhile(1))?)?; insert Awhile(2); auto)
qed auto

lemma post_mono: "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> post C P s \<Longrightarrow> post C P' s"
proof (induction C arbitrary: P P' s)
  case (Aassign x1 x2)
  then show ?case by simp metis
next
  case (Aseq C1 C2)
  then show ?case by simp metis
next
  case (Aif b C1 C2)
  let ?PT = "\<lambda>P s. P s \<and> bval b s"
  let ?PF = "\<lambda>P s. P s \<and> \<not>bval b s"
  from Aif(3) have HT: "\<forall>s. ?PT P s \<longrightarrow> ?PT P' s" by simp
  from Aif(3) have HF: "\<forall>s. ?PF P s \<longrightarrow> ?PF P' s" by simp
  from Aif(4) consider (T) "post C1 (?PT P) s" | (F) "post C2 (?PF P) s" by auto
  then show ?case
  proof cases
    case T
    from Aif(1) [OF HT T] show ?thesis by simp
  next
    case F
    from Aif(2) [OF HF F] show ?thesis by simp
  qed
qed auto

lemma vc_antimono: "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> vc C P' \<Longrightarrow> vc C P"
proof(induct C arbitrary: P P')
  case (Aseq C1 C2) thus ?case by simp (metis post_mono)
next
  case (Aif b C1 C2)
  let ?PT = "\<lambda>P s. P s \<and> bval b s"
  let ?PF = "\<lambda>P s. P s \<and> \<not>bval b s"
  from Aif(3) have HT: "\<forall>s. ?PT P s \<longrightarrow> ?PT P' s" by simp
  from Aif(3) have HF: "\<forall>s. ?PF P s \<longrightarrow> ?PF P' s" by simp
  from Aif(1) [OF HT] Aif(2) [OF HF] Aif(4) show ?case by auto
qed simp_all

lemma vc_complete: "\<turnstile> {P} c {Q}
  \<Longrightarrow> \<exists>C. strip C = c \<and> vc C P \<and> (\<forall>s. post C P s \<longrightarrow> Q s)"
  (is "_ \<Longrightarrow> \<exists>C. ?G P c Q C")
proof (induct rule: hoare.induct)
  case (Skip P)
  show ?case (is "\<exists>C. ?C C")
    by (rule exI [of ?C Askip], simp)
next
  case (Assign P a x)
  show ?case (is "\<exists>C. ?C C")
  proof (rule exI [of ?C "Aassign x a"], auto)
    fix s :: state and x'
    assume "s x = aval a (s(x := x'))"
    then have "s(x := aval a (s(x := x'))) = s" by auto
    moreover assume "P (s(x := aval a (s(x := x'))))"
    ultimately show "P s" by simp
  qed
next
  case (Seq P c\<^sub>1 Q c\<^sub>2 R)
  from Seq(4) obtain C\<^sub>2 where IH2: "?G Q c\<^sub>2 R C\<^sub>2" by blast
  from Seq(2) obtain C\<^sub>1 where IH1: "?G P c\<^sub>1 Q C\<^sub>1" by blast
  have "?G P (c\<^sub>1;; c\<^sub>2) R (C\<^sub>1;; C\<^sub>2)"
  proof (intro conjI)
    from IH1 IH2 show "strip (C\<^sub>1;; C\<^sub>2) = c\<^sub>1;; c\<^sub>2" by auto
    from IH1 IH2 show "vc (C\<^sub>1;; C\<^sub>2) P" by (fastforce elim!: post_mono vc_antimono)
    show "\<forall>s. post (C\<^sub>1;; C\<^sub>2) P s \<longrightarrow> R s"
    proof (intro allI)
      fix s
      from IH1 have "post C\<^sub>2 (post C\<^sub>1 P) s \<Longrightarrow> post C\<^sub>2 Q s" by (auto elim!: post_mono)
      with IH2 show "post (C\<^sub>1;; C\<^sub>2) P s \<longrightarrow> R s" by auto
    qed
  qed
  then show ?case by blast
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  from If(2) obtain C\<^sub>1 where IH1: "?G (\<lambda>s. P s \<and> bval b s) c\<^sub>1 Q C\<^sub>1" by blast
  from If(4) obtain C\<^sub>2 where IH2: "?G (\<lambda>s. P s \<and> \<not>bval b s) c\<^sub>2 Q C\<^sub>2" by blast
  from IH1 IH2 have "?G P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q (IF b THEN C\<^sub>1 ELSE C\<^sub>2)" by simp
  then show ?case by blast
next
  case (While P b c)
  from While(2) obtain C where IH: "?G (\<lambda>s. P s \<and> bval b s) c P C" by blast
  then have "?G P (WHILE b DO c) (\<lambda>s. P s \<and> \<not>bval b s) ({P} WHILE b DO C)" by auto
  then show ?case by blast
next
  case (conseq P' P c Q Q')
  from conseq(3) obtain C where HC: "strip C = c" "vc C P" "\<forall>s. post C P s \<longrightarrow> Q s" by blast+
  from conseq(1) HC(2) have "vc C P'" by (simp add: vc_antimono)
  moreover from conseq(1, 4) HC(3) have "\<forall>s. post C P' s \<longrightarrow> Q' s" by (simp add: post_mono vc_antimono)
  ultimately show ?case using HC(1) by auto
qed

text  \<open>
\endexercise
\<close>

end

