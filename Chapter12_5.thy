theory Chapter12_5
imports "HOL-IMP.Hoare_Total"
begin

text\<open>
\exercise
Prove total correctness of the commands in exercises~\ref{exe:Hoare:sumeq} to
\ref{exe:Hoare:sqrt}.
\<close>

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = (And (Not (Less a1 a2)) (Not (Less a2 a1)))"

lemma bval_Eq[simp]: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  unfolding Eq_def by auto

lemma
  "\<turnstile>\<^sub>t {\<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''y'' ::= N 0;;
     WHILE Not(Eq (V ''x'') (N 0))
     DO (''y'' ::= Plus (V ''y'') (V ''x'');;
           ''x'' ::= Plus (V ''x'') (N (-1)))
     {\<lambda>s. s ''y'' = sum i}"
  (is "\<turnstile>\<^sub>t {?HI} ''y'' ::= ?yi;; WHILE ?bx DO (''y'' ::= ?ay;; ''x'' ::= ?ax) {?HE}")
proof (intro Seq While_fun' allI impI; (elim conjE)?)
  let ?ax = "Plus (V ''x'') (N (- 1))"
  let ?ay = "Plus (V ''y'') (V ''x'')"
  let ?P = "\<lambda>s. s ''y'' = sum i - sum (s ''x'') \<and> 0 \<le> s ''x''"
  let ?f = "\<lambda>s::state. nat (s ''x'')"
  let ?Pw' = "\<lambda>n s. ?P s \<and> ?f s < n"
  let ?Q = "\<lambda>n s. ?Pw' n (s[?ax/''x''])"
  let ?Pw = "\<lambda>n s. ?P s \<and> bval ?bx s \<and> n = ?f s"
  let ?yi = "N 0"
  {
    have "\<forall>s. ?HI s \<longrightarrow> ?P (s[?yi/''y''])"
    proof (intro allI impI, elim conjE)
      fix s
      assume Hxi: "s ''x'' = i"
      then have "(s[?yi/''y'']) ''y'' = sum i - sum ((s[?yi/''y'']) ''x'')" (is ?H1) by simp
      moreover assume Hi: "0 \<le> i"
      with Hxi have "0 \<le> (s[?yi/''y'']) ''x''" (is ?H2) by simp
      ultimately show "?H1 \<and> ?H2" by blast
    qed
    from Assign' [OF this] show "\<turnstile>\<^sub>t {?HI} ''y'' ::= ?yi {?P}" .
  next
    fix s
    assume HP: "?P s"
    assume "\<not>bval ?bx s"
    then have "s ''x'' = 0" by simp
    with HP show "s ''y'' = sum i" by simp
  next
    fix n
    show "\<turnstile>\<^sub>t {?Q n} ''x'' ::= ?ax {?Pw' n}" by (rule Assign)
  next
    fix n
    have "\<forall>s. ?Pw n s \<longrightarrow> ?Q n (s[?ay/''y''])"
    proof (intro allI impI conjI; elim conjE)
      fix s
      assume assm: "s ''y'' = sum i - sum (s ''x'')" "0 \<le> s ''x''" "bval (bexp.Not (Eq (V ''x'') (N 0))) s" "n = nat (s ''x'')"
      from assm(2, 3) have Hx0: "0 < s ''x''" by simp
      from assm(1) have "((s[?ay/''y''])[?ax/''x'']) ''y'' = sum i - sum (s ''x'') + s ''x''" by simp
      also from Hx0 have "\<dots> = sum i - sum (s ''x'' - 1)" by auto
      also have "\<dots> = sum i - sum (((s[?ay/''y''])[?ax/''x'']) ''x'')" by simp
      finally show "((s[?ay/''y''])[?ax/''x'']) ''y'' = sum i - sum (((s[?ay/''y''])[?ax/''x'']) ''x'')" .
      from Hx0 show "0 \<le> ((s[?ay/''y''])[?ax/''x'']) ''x''" by simp
      from Hx0 assm(4) show "?f ((s[?ay/''y''])[?ax/''x'']) < n" by auto
    qed
    from Assign' [OF this] show "\<turnstile>\<^sub>t {?Pw n} ''y'' ::= ?ay {?Q n}" .
  }
qed

lemma
  "\<turnstile>\<^sub>t {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x}
     WHILE Less (N 0) (V ''x'')
     DO (''x'' ::= Plus (V ''x'') (N (-1));; ''y'' ::= Plus (V ''y'') (N (-1)))
     {\<lambda>t. t ''y'' = y - x}"
proof (rule strengthen_pre; intro While_fun' Seq allI impI; (elim conjE)?)
  let ?b = "Less (N 0) (V ''x'')"
  let ?P = "\<lambda>s. s ''y'' - s ''x'' = y - x \<and> 0 \<le> s ''x''"
  let ?f = "\<lambda>s::state. nat(s ''x'')"
  let ?Pw' = "\<lambda>n s. ?P s \<and> ?f s < n"
  let ?Pw = "\<lambda>n s. ?P s \<and> bval ?b s \<and> n = ?f s"
  let ?Qold = "\<lambda>s. s ''y'' - 1 - s ''x'' = y - x \<and> 0 \<le> s ''x''"
  let ?ay = "Plus (V ''y'') (N (- 1))"
  let ?ax = "Plus (V ''x'') (N (- 1))"
  let ?Q = "\<lambda>n s. ?Pw' n (s[?ay/''y''])"
  {
    fix s
    assume "s ''x'' = x" "s ''y'' = y" "0 \<le> x"
    then show "?P s" by simp
  next
    fix s
    assume "\<not> bval (Less (N 0) (V ''x'')) s"
    then have "s ''x'' \<le> 0" by simp
    moreover assume "?P s"
    ultimately show "s ''y'' = y - x" by simp
  next
    fix n
    show "\<turnstile>\<^sub>t {?Q n} ''y'' ::= ?ay {?Pw' n}" by (rule Assign)
  next
    fix n
    have "\<forall>s. ?Pw n s \<longrightarrow> ?Q n (s[?ax/''x''])"
    proof (intro allI impI conjI; elim conjE)
      fix s
      assume assm: "s ''y'' - s ''x'' = y - x" "bval (Less (N 0) (V ''x'')) s" "n = nat (s ''x'')"
      from assm(2) have Hx0: "0 < s ''x''" by simp
      from assm(1) show "((s[?ax/''x''])[?ay/''y'']) ''y'' - ((s[?ax/''x''])[?ay/''y'']) ''x'' = y - x" by simp
      from Hx0 show "0 \<le> ((s[?ax/''x''])[?ay/''y'']) ''x''" by simp
      from assm(3) Hx0 show "?f ((s[Plus (V ''x'') (N (- 1))/''x''])[Plus (V ''y'') (N (- 1))/''y'']) < n" by simp
    qed
    then show "\<turnstile>\<^sub>t {?Pw n} ''x'' ::= ?ax {?Q n}" by (rule Assign')
  }
qed

lemma
  "\<turnstile>\<^sub>t { \<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''r'' ::= N 0;; ''r2'' ::= N 1;;
     WHILE (Not (Less (V ''x'') (V ''r2'')))
     DO (''r'' ::= Plus (V ''r'') (N 1);;
            ''r2'' ::= Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1)))
     {\<lambda>s. (s ''r'')^2 \<le> i \<and> i < (s ''r'' + 1)^2}"
proof (intro Seq While_fun' allI impI conjI; (elim conjE)?)
  let ?b = "Not (Less (V ''x'') (V ''r2''))"
  let ?ar = "Plus (V ''r'') (N 1)"
  let ?ar2 = "Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1))"
  let ?I = "\<lambda>s. s ''x'' = i \<and> 0 \<le> i"
  let ?II = "\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> 1 = (s ''r'' + 1)\<^sup>2 \<and> 0 \<le> s ''r''"
  let ?P = "\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> s ''r2'' = (s ''r'' + 1)\<^sup>2 \<and> 0 \<le> s ''r''"
  let ?f = "\<lambda>s::state. nat (s ''x'' + 1 - s ''r2'')"
  let ?Qold = "\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> s ''r2'' = (s ''r'')\<^sup>2"
  let ?Pw' = "\<lambda>n s. ?P s \<and> ?f s < n"
  let ?Q = "\<lambda>n s. ?Pw' n (s[?ar2/''r2''])"
  let ?Pw = "\<lambda>n s. ?P s \<and> bval ?b s \<and> n = ?f s"
  {
    have "\<forall>s. ?I s \<longrightarrow> ?II (s[N 0/''r''])" by auto
    then show "\<turnstile>\<^sub>t {?I} ''r'' ::= N 0 {?II}" by (rule Assign')
  next
    have "\<turnstile>\<^sub>t {\<lambda>s. ?P (s[N 1/''r2''])} ''r2'' ::= N 1 {?P}" by (rule Assign)
    then show "\<turnstile>\<^sub>t {?II} ''r2'' ::= N 1 {?P}" by simp
  next
    fix s
    assume "?P s"
    then have H: "s ''x'' = i" "(s ''r'')\<^sup>2 \<le> s ''x''" "s ''r2'' = (s ''r'' + 1)\<^sup>2" by blast+
    moreover assume "\<not> bval ?b s"
    then have "s ''x'' < s ''r2''" by auto
    ultimately show "(s ''r'')\<^sup>2 \<le> i" "i < (s ''r'' + 1)\<^sup>2" by auto
  next
    fix n
    have Heqv: "\<And>x::int. (x + 1)\<^sup>2 = x\<^sup>2 + x + x + 1" by (simp add: power2_sum)
    show "\<turnstile>\<^sub>t {?Q n} ''r2'' ::= ?ar2 {?Pw' n}" by (rule Assign)
  next
    fix n
    have "\<forall>s. ?Pw n s \<longrightarrow> ?Q n (s[?ar/''r''])"
    proof auto
      fix s :: state
      let ?r = "s ''r''"
      have "(?r + 1)\<^sup>2 + (3 + 2 * ?r) = ?r\<^sup>2 + 4 * ?r + 4" by (simp add: power2_sum)
      also have "\<dots> = (2 + ?r)\<^sup>2" by (simp add: power2_sum)
      finally show "(?r + 1)\<^sup>2 + (3 + 2 * ?r) = (2 + ?r)\<^sup>2" .
    qed
    then show "\<turnstile>\<^sub>t {?Pw n} ''r'' ::= ?ar {?Q n}" by (rule Assign')
  }
qed

text\<open>
\endexercise

\exercise
Modify the VCG to take termination into account. First modify type @{text acom}
by annotating  @{text WHILE} with a measure function in addition to an
invariant:
\<close>
datatype acom =
  Askip                  ("SKIP") |
  Aassign vname aexp     ("(_ ::= _)" [1000, 61] 61) |
  Aseq   acom acom       ("_;;/ _"  [60, 61] 60) |
  Aif bexp acom acom     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61) |
  Awhile assn "state \<Rightarrow> nat" bexp acom
    ("({_, _}/ WHILE _/ DO _)"  [0, 0, 61] 61)

notation com.SKIP ("SKIP")

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_,_} WHILE b DO C) = (WHILE b DO strip C)"

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q =
  (\<lambda>s. if bval b s then pre C\<^sub>1 Q s else pre C\<^sub>2 Q s)" |
"pre ({I,f} WHILE b DO C) Q = I"

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1;; C\<^sub>2) Q = (vc C\<^sub>1 (pre C\<^sub>2 Q) \<and> vc C\<^sub>2 Q)" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |
"vc ({I, f} WHILE b DO C) Q =
  (\<forall>n. (\<forall>s. (I s \<and> bval b s \<and> n = f s \<longrightarrow> pre C (\<lambda>s. I s \<and> f s < n) s) \<and>
        (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and>
    vc C (\<lambda>s. I s \<and> f s < n))"

text\<open>
Functions @{const strip} and @{const pre} remain almost unchanged.
The only significant change is in the @{text WHILE} case for @{const vc}.
Modify the old soundness proof to obtain
\<close>

lemmas [simp] = hoaret.Skip hoaret.Assign hoaret.Seq If

lemmas [intro!] = hoaret.Skip hoaret.Assign hoaret.Seq hoaret.If

lemma strengthen_pre: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'} c {Q}"
  by (blast intro: conseq)

lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile>\<^sub>t {pre C Q} strip C {Q}"
proof(induct C arbitrary: Q)
  case (Awhile I f b C)
  show ?case
  proof (simp, rule While_fun')
    from Awhile(2) show "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
    fix n
    from Awhile(2) have "\<forall>s. I s \<and> bval b s \<and> n = f s \<longrightarrow> pre C (\<lambda>s. I s \<and> f s < n) s" by auto
    moreover from Awhile(2) have "vc C (\<lambda>s. I s \<and> f s < n)" by auto
    with Awhile(1) have "\<turnstile>\<^sub>t {pre C (\<lambda>s. I s \<and> f s < n)} strip C {\<lambda>s. I s \<and> f s < n}" by auto
    ultimately show "\<turnstile>\<^sub>t {\<lambda>s. I s \<and> bval b s \<and> n = f s} strip C {\<lambda>s. I s \<and> f s < n}" by (rule strengthen_pre)
  qed
qed (auto intro: hoaret.conseq)

text\<open>
You may need the combined soundness and completeness of @{text"\<turnstile>\<^sub>t"}:
@{thm hoaret_sc}
\endexercise
\<close>

end

