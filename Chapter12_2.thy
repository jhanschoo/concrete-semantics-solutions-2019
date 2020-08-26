theory Chapter12_2
imports "HOL-IMP.Hoare_Examples"
begin

text\<open>
\section*{Chapter 12}

\setcounter{exercise}{1}
\<close>

lemma "\<not>(\<forall>P x a. \<Turnstile> {P} x ::= a {\<lambda>s. P (s[a/x])})"
proof (intro notI)
  assume "\<forall>P x a. \<Turnstile> {P} x ::= a {\<lambda>s. P (s[a/x])}"
  then have h: "\<And>P x a s t. \<lbrakk>P s; (x ::= a, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> P (t[a/x])" unfolding hoare_valid_def by blast
  let ?x = "''x''"
  let ?a = "Plus (N 1) (V ?x)"
  let ?P = "(\<lambda>s. s ''x'' = 0) :: assn"
  let ?s = "<> :: state"
  let ?t = "<''x'' := 1> :: state"
  let ?tt = "<''x'' := 2> :: state"
  let ?c = "?x ::= ?a"
  have h1: "?P ?s" unfolding null_state_def by simp
  moreover from big_step.Assign [of ?x ?a ?s] have h2: "(''x'' ::= ?a, <>) \<Rightarrow> ?t" unfolding null_state_def by simp
  from h [of ?P ?s, OF h1 h2] show False by simp
qed

text\<open>
\exercise
Define @{text bsubst} and prove the Substitution Lemma:
\<close>

fun asubst :: "aexp \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> aexp" where
  "asubst (N n) _ _ = N n" |
  "asubst (V v) a x = (if v = x then a else (V v))" |
  "asubst (Plus a\<^sub>1 a\<^sub>2) a x = Plus (asubst a\<^sub>1 a x) (asubst a\<^sub>2 a x)"

fun bsubst :: "bexp \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> bexp" where
  "bsubst (Bc v) _ _ = Bc v" |
  "bsubst (Not b) a x = Not (bsubst b a x)" |
  "bsubst (And b\<^sub>1 b\<^sub>2) a x = And (bsubst b\<^sub>1 a x) (bsubst b\<^sub>2 a x)" |
  "bsubst (Less a\<^sub>1 a\<^sub>2) a x = Less (asubst a\<^sub>1 a x) (asubst a\<^sub>2 a x)"

lemma asubstitution: "aval (asubst a a' x) s = aval a (s[a'/x])"
  by (induct a) simp_all

lemma bsubstitution: "bval (bsubst b a x) s = bval b (s[a/x])"
proof (induct b)
  case (Less x1a x2a)
  have "bval (bsubst (Less x1a x2a) a x) s \<longleftrightarrow> aval (asubst x1a a x) s < aval (asubst x2a a x) s" by simp
  also from asubstitution have "\<dots> \<longleftrightarrow> aval x1a (s[a/x]) < aval x2a (s[a/x])" by simp
  also have "\<dots> = bval (Less x1a x2a) (s[a/x])" by simp
  finally show ?case .
qed simp_all

text\<open>
This may require a similar definition and proof for @{typ aexp}.
\endexercise

\exercise
Define a command @{text cmax} that stores the maximum of the values of the IMP variables
@{text "x"} and @{text "y"} in the IMP variable @{text "z"} and prove that
@{text cmax} satisfies its specification:
\<close>

abbreviation cmax :: com where
  "cmax \<equiv> IF Less (V ''x'') (V ''y'') THEN ''z'' ::= V ''y'' ELSE ''z'' ::= V ''x''"

lemma "\<turnstile> {\<lambda>s. True} cmax {\<lambda>s. s ''z'' = max (s ''x'') (s ''y'')}"
proof (rule If; rule Assign'; intro allI impI; elim conjE)
  fix s
  have "(s[V ''y''/''z'']) ''z'' = s ''y''" by simp
  also assume "bval (Less (V ''x'') (V ''y'')) s"
  then have "s ''x'' < s ''y''" by simp
  then have "s ''y'' = max (s ''x'') (s ''y'')" by simp
  also have "\<dots> = max ((s[V ''y''/''z'']) ''x'') ((s[V ''y''/''z'']) ''y'')" by simp
  finally show "(s[V ''y''/''z'']) ''z'' = max ((s[V ''y''/''z'']) ''x'') ((s[V ''y''/''z'']) ''y'')" .
next
  fix s
  have "(s[V ''x''/''z'']) ''z'' = s ''x''" by simp
  also assume "\<not>bval (Less (V ''x'') (V ''y'')) s"
  then have "\<not>s ''x'' < s ''y''" by simp
  then have "s ''x'' = max (s ''x'') (s ''y'')" by simp
  also have "\<dots> = max ((s[V ''x''/''z'']) ''x'') ((s[V ''x''/''z'']) ''y'')" by simp
  finally show "(s[V ''x''/''z'']) ''z'' = max ((s[V ''x''/''z'']) ''x'') ((s[V ''x''/''z'']) ''y'')" .
qed


text\<open>
Function @{const max} is the predefined maximum function.
Proofs about @{const max} are often automatic when simplifying with @{thm[source] max_def}.
\endexercise

\exercise\label{exe:Hoare:sumeq}
Define an equality operation for arithmetic expressions
\<close>


definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = (And (Not (Less a1 a2)) (Not (Less a2 a1)))"

text\<open> such that \<close>

lemma bval_Eq[simp]: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  unfolding Eq_def by auto

text\<open> Prove the following variant of the summation command correct: \<close>

lemma
  "\<turnstile> {\<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''y'' ::= N 0;;
     WHILE Not(Eq (V ''x'') (N 0))
     DO (''y'' ::= Plus (V ''y'') (V ''x'');;
           ''x'' ::= Plus (V ''x'') (N (-1)))
     {\<lambda>s. s ''y'' = sum i}"
proof (intro Seq While' allI impI; (elim conjE)?)
  let ?ax = "Plus (V ''x'') (N (- 1))"
  let ?cx = "''x'' ::= ?ax"
  let ?ay = "Plus (V ''y'') (V ''x'')"
  let ?cy = "''y'' ::= ?ay"
  let ?bx = "(bexp.Not (Eq (V ''x'') (N 0)))"
  let ?P = "\<lambda>s. s ''y'' = sum i - sum (s ''x'') \<and> 0 \<le> s ''x''"
  let ?PS = "\<lambda>s. ?P (s[?ax/''x''])"
  let ?Q = "\<lambda>s. s ''y'' = sum i - sum (s ''x'' - 1) \<and> 0 \<le> s ''x'' - 1"
  let ?Pw = "\<lambda>s. ?P s \<and> bval ?bx s"
  let ?HI = "\<lambda>s. s ''x'' = i \<and> 0 \<le> i"
  let ?yi = "N 0"
  let ?cyi = "''y'' ::= ?yi"
  {
    fix s
    assume HP: "?P s"
    assume "\<not>bval ?bx s"
    then have "s ''x'' = 0" by simp
    with HP show "s ''y'' = sum i" by simp
  next
    have "\<turnstile> {?PS} ?cx {?P}" by (rule Assign)
    then show "\<turnstile> {?Q} ?cx {?P}" by simp
  next
    have "\<forall>s. ?Pw s \<longrightarrow> ?Q (s[?ay/''y''])"
    proof (intro allI impI, elim conjE)
      fix s
      assume "bval (bexp.Not (Eq (V ''x'') (N 0))) s"
      then have Hx0: "s ''x'' \<noteq> 0" by simp
      have "(s[?ay/''y'']) ''y'' = s ''y'' + s ''x''" by simp
      also assume "s ''y'' = sum i - sum (s ''x'')"
      then have "s ''y'' + s ''x'' = sum i - sum (s ''x'') + s ''x''" by simp
      also assume Hxp: "0 \<le> s ''x''"
      with Hx0 have "sum i - sum (s ''x'') + s ''x'' = sum i - sum (s ''x'' - 1)" by auto
      also have "\<dots> = sum i - sum ((s[?ay/''y'']) ''x'' - 1)" by simp
      finally have "(s[?ay/''y'']) ''y'' = sum i - sum ((s[?ay/''y'']) ''x'' - 1)" (is ?H1) .
      moreover from Hxp Hx0 have "0 \<le> (s[?ay/''y'']) ''x'' - 1" (is ?H2) by simp
      ultimately show "?H1 \<and> ?H2" by blast
    qed
    from Assign' [OF this] show "\<turnstile> {?Pw} ?cy {?Q}" .
  next
    have "\<forall>s. ?HI s \<longrightarrow> ?P (s[?yi/''y''])"
    proof (intro allI impI, elim conjE)
      fix s
      assume Hxi: "s ''x'' = i"
      then have "(s[N 0/''y'']) ''y'' = sum i - sum ((s[?yi/''y'']) ''x'')" (is ?H1) by simp
      moreover assume Hi: "0 \<le> i"
      with Hxi have "0 \<le> (s[N 0/''y'']) ''x''" (is ?H2) by simp
      ultimately show "?H1 \<and> ?H2" by blast
    qed
    from Assign' [OF this] show "\<turnstile> {?HI} ?cyi {?P}" .
  }
qed

text\<open>
\endexercise

\exercise
Prove that the following command computes @{prop"y - x"} if @{prop"(0::nat) \<le> x"}:
\<close>

lemma
  "\<turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x}
     WHILE Less (N 0) (V ''x'')
     DO (''x'' ::= Plus (V ''x'') (N (-1));; ''y'' ::= Plus (V ''y'') (N (-1)))
     {\<lambda>t. t ''y'' = y - x}"
proof (rule strengthen_pre; intro While' Seq allI impI; (elim conjE)?)
  let ?P = "\<lambda>s. s ''y'' - s ''x'' = y - x \<and> 0 \<le> s ''x''"
  let ?Q = "\<lambda>s. s ''y'' - 1 - s ''x'' = y - x \<and> 0 \<le> s ''x''"
  let ?b = "Less (N 0) (V ''x'')"
  let ?Pw = "\<lambda>s. ?P s \<and> bval ?b s"
  let ?ay = "Plus (V ''y'') (N (- 1))"
  let ?ax = "Plus (V ''x'') (N (- 1))"
  let ?cy = "''y'' ::= ?ay"
  let ?cx = "''x'' ::= ?ax"
  {
    fix s
    assume "\<not> bval (Less (N 0) (V ''x'')) s"
    then have "s ''x'' \<le> 0" by simp
    moreover assume "?P s"
    ultimately show "s ''y'' = y - x" by simp
  next
    have "\<turnstile> {\<lambda>s. ?P (s[?ay/''y''])} ?cy {?P}" by (rule Assign)
    then show "\<turnstile> {?Q} ?cy {?P}" by simp
  next
    have Hsle: "\<And>s::state. 0 \<le> s ''x'' - 1 \<longleftrightarrow> 0 \<le> s ''x'' \<and> bval ?b s" by auto
    have "\<turnstile> {\<lambda>s. ?Q (s[?ax/''x''])} ?cx {?Q}" by (rule Assign)
    then have "\<turnstile> {\<lambda>s. s ''y'' - s ''x'' = y - x \<and> 0 \<le> s ''x'' - 1} ?cx {?Q}" by simp
    with Hsle show "\<turnstile> {\<lambda>s. ?P s \<and> bval ?b s} ?cx {?Q}" by simp
  next
    fix s
    assume "s ''x'' = x" "s ''y'' = y" "0 \<le> x"
    then show "?P s" by simp
  }
qed

text\<open>
\endexercise

\exercise\label{exe:Hoare:mult}
Define and verify a command @{text cmult} that stores the product of
@{text "x"} and @{text "y"} in @{text "z"} assuming @{prop"(0::int)\<le>y"}:
\<close>

abbreviation cmult :: com where
  "cmult \<equiv> ''z'' ::= N 0;;
    WHILE Less (N 0) (V ''y'') DO (''y'' ::= (Plus (V ''y'') (N (-1)));; ''z'' ::= (Plus (V ''z'') (V ''x'')))"

lemma
  "\<turnstile> {\<lambda>s.  s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> y} cmult {\<lambda>t. t ''z'' = x*y}"
proof (intro Seq While' allI impI; (elim conjE)?)
  let ?I = "\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> y"
  let ?P = "\<lambda>s. s ''x'' = x \<and> s ''z'' = s ''x'' * (y - s ''y'') \<and> 0 \<le> s ''y''"
  let ?Q = "\<lambda>s. s ''x'' = x \<and> s ''z'' = s ''x'' * (y - s ''y'' - 1) \<and> 0 \<le> s ''y''"
  let ?b = "Less (N 0) (V ''y'')"
  let ?az = "Plus (V ''z'') (V ''x'')"
  let ?cz = "''z'' ::= ?az"
  let ?ay = "Plus (V ''y'') (N (- 1))"
  let ?cy = "''y'' ::= ?ay"
  {
    show "\<turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> y} ''z'' ::= N 0 {?P}" by (auto simp add: Assign')
  next
    fix s
    assume "?P s" "\<not>bval ?b s"
    then show "s ''z'' = x * y" by auto
  next
    have Heq: "\<And>s. s ''z'' + s ''x'' = s ''x'' * (y - s ''y'') \<longleftrightarrow> s ''z'' = s ''x'' * (y - s ''y'' - 1)" by (auto simp add: int_distrib(4))
    have "\<turnstile> {\<lambda>s. ?P (s[?az/''z''])} ?cz {?P}" by (rule Assign)
    with Heq show "\<turnstile> {?Q} ?cz {?P}" by simp
  next
    have Hsle: "\<And>s::state. 0 \<le> s ''y'' - 1 \<longleftrightarrow> 0 \<le> s ''y'' \<and> bval ?b s" by auto
    have "\<turnstile> {\<lambda>s. ?Q (s[?ay/''y''])} ?cy {?Q}" by (rule Assign)
    with Hsle show "\<turnstile> {\<lambda>s. ?P s \<and> bval ?b s} ?cy {?Q}" by simp
  }
qed

text\<open>
You may have to simplify with @{thm[source] algebra_simps} to deal with ``@{text"*"}''.
\endexercise

\exercise\label{exe:Hoare:sqrt}
The following command computes an integer approximation @{text r} of the square root
of @{text "i \<ge> 0"}, i.e.\ @{text"r\<^sup>2 \<le> i < (r+1)\<^sup>2"}. Prove
\<close>

lemma
  "\<turnstile> { \<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''r'' ::= N 0;; ''r2'' ::= N 1;;
     WHILE (Not (Less (V ''x'') (V ''r2'')))
     DO (''r'' ::= Plus (V ''r'') (N 1);;
            ''r2'' ::= Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1)))
     {\<lambda>s. (s ''r'')^2 \<le> i \<and> i < (s ''r'' + 1)^2}"
proof (intro Seq While' allI impI conjI; (elim conjE)?)
  let ?I = "\<lambda>s. s ''x'' = i \<and> 0 \<le> i"
  let ?II = "\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> 1 = (s ''r'' + 1)\<^sup>2"
  let ?P = "\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> s ''r2'' = (s ''r'' + 1)\<^sup>2"
  let ?Q = "\<lambda>s. s ''x'' = i \<and> (s ''r'')\<^sup>2 \<le> s ''x'' \<and> s ''r2'' = (s ''r'')\<^sup>2"
  let ?b = "Not (Less (V ''x'') (V ''r2''))"
  let ?ar = "Plus (V ''r'') (N 1)"
  let ?ar2 = "Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1))"
  {
    have "\<turnstile> {\<lambda>s. ?P (s[N 1/''r2''])} ''r2'' ::= N 1 {?P}" by (rule Assign)
    then show "\<turnstile> {?II} ''r2'' ::= N 1 {?P}" by simp
  next
    have "\<forall>s. ?I s \<longrightarrow> ?II (s[N 0/''r''])" by auto
    then show "\<turnstile> {?I} ''r'' ::= N 0 {?II}" by (rule Assign')
  next
    fix s
    assume "?P s"
    then have H: "s ''x'' = i" "(s ''r'')\<^sup>2 \<le> s ''x''" "s ''r2'' = (s ''r'' + 1)\<^sup>2" by blast+
    moreover assume "\<not> bval ?b s"
    then have "s ''x'' < s ''r2''" by auto
    ultimately show "(s ''r'')\<^sup>2 \<le> i" "i < (s ''r'' + 1)\<^sup>2" by auto
  next
    have Heqv: "\<And>x::int. (x + 1)\<^sup>2 = x\<^sup>2 + x + x + 1" by (simp add: power2_sum)
    have "\<turnstile> {\<lambda>s. ?P (s[?ar2/''r2''])} ''r2'' ::= ?ar2 {?P}" by (rule Assign)
    with Heqv show "\<turnstile> {?Q} ''r2'' ::= ?ar2 {?P}" by simp
  next
    have "\<forall>s. (\<lambda>s. ?P s \<and> bval ?b s) s \<longrightarrow> ?Q (s[?ar/''r''])" by auto
    then show "\<turnstile> {\<lambda>s. ?P s \<and> bval ?b s} ''r'' ::= ?ar {?Q}" by (rule Assign')
  }
qed

text\<open>
Figure out how @{text r2} is related to @{text r} before
formulating the invariant.
The proof may require simplification with @{thm[source] algebra_simps}
and @{thm[source] power2_eq_square}.
\endexercise

\exercise
Prove by induction:
\<close>

lemma "\<turnstile> {P} c {\<lambda>s. True}"
proof (induct c arbitrary: P)
  case SKIP
  then show ?case by (rule weaken_post, auto)
next
  case (Assign x1 x2)
  then show ?case by (rule Assign', auto)
next
  case (Seq c1 c2)
  then show ?case by (rule hoare.Seq)
next
  case (If x1 c1 c2)
  then show ?case by (rule hoare.If)
next
  case (While x1 c)
  show ?case by (rule strengthen_pre [of _ "\<lambda>_. True"], simp, rule While', auto simp add: While)
qed

text\<open>
\endexercise

\exercise\label{exe:fwdassign}
Design and prove correct a forward assignment rule of the form
\ \mbox{@{text"\<turnstile> {P} x ::= a {?}"}} \
where @{text"?"} is some suitable postcondition that depends on @{text P},
@{text x} and @{text a}. Hint: @{text"?"} may need @{text"\<exists>"}.
\<close>

lemma "\<turnstile> {P} x ::= a {\<lambda>s. \<exists> x'. P (s(x := x')) \<and> s x = aval a (s(x := x'))}"
proof (rule Assign', intro allI impI)
  fix s :: state
  let ?x' = "s x"
  assume "P s"
  then have "P ((s[a/x])(x := ?x'))" by simp
  moreover have "(s[a/x]) x = aval a ((s[a/x])(x := ?x'))" by simp
  ultimately show "\<exists>x'. P ((s[a/x])(x := x')) \<and> (s[a/x]) x = aval a ((s[a/x])(x := x'))" by blast
qed

text\<open>
(In case you wonder if your @{text Questionmark} is strong enough: see Exercise~\ref{exe:sp})
\endexercise
\<close>
end

