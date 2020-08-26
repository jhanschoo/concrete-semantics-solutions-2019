theory Chapter11
imports "HOL-IMP.Denotational" "HOL-IMP.Vars"
begin

text\<open>
\section*{Chapter 11}

\begin{exercise}
Building on Exercise~\ref{exe:IMP:REPEAT}, extend the denotational
semantics and the equivalence proof with the big-step semantics
with a @{text REPEAT} loop.
\end{exercise}

\exercise
Consider Example~11.14 and prove the following equation by induction on @{text n}:
\<close>
lemma "(W (\<lambda>s. s ''x'' \<noteq> 0) {(s,t). t = s(''x'' := s ''x'' - 1)} ^^ n) {} =
  {(s,t). 0 \<le> s ''x'' \<and> s ''x'' < int n \<and> t = s(''x'' := 0)}" (is "(W ?b ?c ^^ n) {} = ?S n")
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let "?W n" = "W ?b ?c ^^ n"
  have "?W (Suc n) {} = W ?b ?c (?W n {})" by simp
  also from Suc have "\<dots> = W ?b ?c (?S n)" by (rule arg_cong)
  also have "\<dots> = ?S (Suc n)" by (force simp add: W_def)
  finally show ?case .
qed

text\<open>
\endexercise

\exercise
Consider Example~11.14 but with the loop condition
@{prop"b = Less (N 0) (V ''x'')"}. Find a closed expression @{text M}
(containing @{text n})
for @{prop"(f ^^ n) {}"} and prove @{prop"(f ^^ n) {} = M"}.
\<close>
lemma "(W (bval (Less (N 0) (V ''x''))) {(s,t). t = s(''x'' := s ''x'' - 1)} ^^ n) {} =
  {(s,t). 0 < n \<and> s ''x'' < int n \<and> t = (if 0 < s ''x'' then s(''x'' := 0) else s)}" (is "(W ?b ?c ^^ n) {} = ?S n")
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let "?W n" = "W ?b ?c ^^ n"
  let ?S2 = "{(s, t). 0 < n \<and> s ''x'' < int n \<and> t = (if 0 < s ''x'' then s(''x'' := 0) else s)}"
  have "?W (Suc n) {} = W ?b ?c (?W n {})" by simp
  also from Suc have "\<dots> = W ?b ?c (?S n)" by (rule arg_cong)
  also have "\<dots> = {(s, t). if ?b s then (s,t) \<in> ?c O (?S n) else s=t}" by (simp add: W_def)
  also have "\<dots> = ?S (Suc n)"
  proof (cases "0 < n")
    case npos: True
    then show ?thesis
    proof (intro equalityI subsetI, fastforce split: if_split_asm)
      fix x
      assume H1: "0 < n" "x \<in> ?S (Suc n)"
      then obtain s t where H2: "x = (s, t)" "0 < Suc n" "s ''x'' < int (Suc n)" "t = (if 0 < s ''x'' then s(''x'' := 0) else s)" by auto
      let ?s' = "s(''x'' := s ''x'' - 1)"
      have "if ?b s then (s, t) \<in> ?c O ?S n else s = t"
      proof (cases "0 < s ''x''")
        case sxpos: True
        have "(s, ?s') \<in> ?c" by auto
        moreover have "(?s', t) \<in> ?S n"
        proof -
          from H1(1) have "0 < n" .
          moreover from H2(3) have "?s' ''x'' < int n" by simp
          moreover from H2(4) sxpos have "t = (if 0 < ?s' ''x'' then ?s'(''x'' := 0) else ?s')" by (auto split: if_split_asm)
          ultimately show ?thesis by simp
        qed
        ultimately have "(s, t) \<in> ?c O ?S n" by fastforce
        with sxpos show ?thesis by fastforce
      qed (simp add: H2(4))
      with H2(1) show "x \<in> {(s, t). if ?b s then (s, t) \<in> ?c O ?S n else s = t}" by auto
    qed
  next
    case npos: False
    then show ?thesis
    proof (intro equalityI subsetI, fastforce split: if_split_asm)
      fix x
      assume H1: "\<not>0 < n" "x \<in> ?S (Suc n)"
      then obtain s t where H2: "x = (s, t)" "n = 0" "s ''x'' < int (Suc n)" "t = (if 0 < s ''x'' then s(''x'' := 0) else s)" by auto
      then show "x \<in> {(s, t). if ?b s then (s, t) \<in> ?c O ?S n else s = t}" by fastforce
    qed
  qed
  finally show "?W (Suc n) {} = ?S (Suc n)" .
qed

text \<open>
\endexercise

\exercise
Define an operator @{text B} such that you
can express the equation for @{term "D (IF b THEN c1 ELSE c2)"}
in a point free way.
\<close>
definition B :: "bexp \<Rightarrow> (state \<times> state) set" where
  "B b = {(s, t). bval b s \<and> s = t}"

lemma "D (IF b THEN c1 ELSE c2) = (B b O D c1) \<union> (B (Not b) O D c2)"
  unfolding B_def by auto

text \<open>
  Similarly, find a point free equation for @{term "W (bval b) dc"}
  and use it to write down a point free version of
  @{term "D (WHILE b DO c)"} (still using @{text lfp}).
  Prove that your equations are equivalent to the old ones.
\<close>

lemma Wpf: "W (bval b) dc = (\<lambda>dw. B b O dc O dw \<union> B (Not b))"
  unfolding W_def B_def by auto

lemma "D (WHILE b DO c) = lfp (\<lambda>dw. B b O D c O dw \<union> B (Not b))"
  by (simp add: Wpf)

text\<open>
\endexercise

\exercise
Let the `thin' part of a relation be its single-valued subset:
\<close>

definition thin :: "'a rel \<Rightarrow> 'a rel" where
"thin R = {(a,b) . (a,b) \<in> R \<and> (\<forall> c. (a,c) \<in> R \<longrightarrow> c = b)}"

lemma single_valued_thin: "single_valued (thin R)"
  unfolding single_valued_def thin_def by auto

text\<open> Prove \<close>

lemma fixes f :: "'a rel \<Rightarrow> 'a rel"
assumes "mono f" and thin_f: "\<And> R. f (thin R) \<subseteq> thin (f R)"
shows "single_valued (lfp f)"
proof -
  from thin_f have "f (thin (lfp f)) \<subseteq> thin (f (lfp f))" .
  also from \<open>mono f\<close> have "thin (f (lfp f)) = thin (lfp f)" by (simp add: lfp_fixpoint)
  finally have "lfp f \<subseteq> thin (lfp f)" by (simp add: lfp_lowerbound)
  with single_valued_thin show "single_valued (lfp f)" by (blast intro: single_valued_subset)
qed

text\<open>
\endexercise

\exercise
Generalise our set-theoretic treatment of continuity and least fixpoints to
\concept{chain-complete partial order}s (\concept{cpo}s),
i.e.\ partial orders @{text"\<le>"} that have a least element @{text "\<bottom>"} and
where every chain @{text"c 0 \<le> c 1 \<le> \<dots>"} has a least upper bound
@{term"lub c"} where \noquotes{@{term[source]"c :: nat \<Rightarrow> 'a"}}.
This setting is described by the following type class @{text cpo}
which is an extension of the type class @{class order} of partial orders.
For details see the decription of type classes in Chapter~13.
\<close>

context order
begin
definition chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"chain c = (\<forall>n. c n \<le> c (Suc n))"
end

class cpo = order +
fixes bot :: 'a and lub :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
assumes bot_least: "bot \<le> x"
and lub_ub: "chain c \<Longrightarrow> c n \<le> lub c"
and lub_least: "chain c \<Longrightarrow> (\<And>n. c n \<le> u) \<Longrightarrow> lub c \<le> u"

text\<open>
A function \noquotes{@{term[source] "f :: 'a \<Rightarrow> 'b"}}
between two cpos @{typ 'a} and @{typ 'b}
is called \concept{continuous} if @{prop"f(lub c) = lub (f o c)"}.
Prove that if @{text f} is monotone and continuous then
\ \mbox{@{text"lub (\<lambda>n. (f ^^ n) \<bottom>)"}} \ is the least (pre)fixpoint of @{text f}:
\<close>


definition cont :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> bool" where
"cont f = (\<forall>c. chain c \<longrightarrow> f (lub c) = lub (f o c))"

abbreviation "fix f \<equiv> lub (\<lambda>n. (f^^n) bot)"

lemma bot_mono: fixes f :: "'a::cpo \<Rightarrow> 'a" assumes "mono f" shows "(f ^^ n) bot \<le> (f ^^ Suc n) bot"
proof (induct n)
  case (Suc n)
  with assms show ?case unfolding mono_def by simp
qed (simp add: bot_least)

lemma fix_lpfp: assumes "mono f" and "f p \<le> p" shows "fix f \<le> p"
proof (intro lub_least, simp add: chain_def, intro allI)
  from bot_mono [OF assms(1)] show "(f ^^ n) cpo_class.bot \<le> f ((f ^^ n) cpo_class.bot)" for n by simp
  show "(f ^^ n) cpo_class.bot \<le> p" for n
  proof (induct n)
    case (Suc n)
    with assms show ?case unfolding mono_def by fastforce
  qed (simp add: bot_least)
qed

theorem fix_fp: assumes "mono f" and "cont f" shows "f(fix f) = fix f"
proof -
  let ?c = "(\<lambda>n. (f^^n) bot)"
  let ?cS = "(\<lambda>n. (f^^Suc n) bot)"
  from bot_mono [OF assms(1)] have cc: "chain ?c" unfolding chain_def by simp
  then have ccS: "chain ?cS" unfolding chain_def by fastforce
  with assms(2) cc have "f (lub ?c) = lub (f \<circ> ?c)" unfolding cont_def by blast
  also have "f \<circ> ?c = ?cS" by (rule ext, auto)
  then have "lub (f \<circ> ?c) = lub ?cS" by simp
  also have "lub ?cS = fix f"
  proof (rule antisym)
    from ccS show "lub ?cS \<le> fix f"
    proof (elim lub_least)
      fix n
      from lub_ub [OF cc, of "Suc n"] show "(f ^^ Suc n) bot \<le> fix f" .
    qed
    from cc show "fix f \<le> lub (\<lambda>n. (f ^^ Suc n) bot)"
    proof (elim lub_least)
      fix n
      from cc have "(f ^^ n) bot \<le> (f ^^ Suc n) bot" unfolding chain_def by simp
      also from lub_ub [OF ccS] have "\<dots> \<le> lub (\<lambda>n. (f ^^ Suc n) bot)" .
      finally show "(f ^^ n) bot \<le> lub (\<lambda>n. (f ^^ Suc n) bot)" .
    qed
  qed
  finally show ?thesis .
qed

text\<open>
\endexercise

\exercise
We define a dependency analysis @{text Dep} that maps commands to relations
between variables such that @{term "(x,y) : Dep c"} means that in
the execution of @{text c}
the initial value of @{text x} can influence the final value of @{text y}:
\<close>

fun Dep :: "com \<Rightarrow> (vname * vname) set" where
"Dep SKIP = Id" |
"Dep (x::=a) = {(u,v). if v = x then u \<in> vars a else u = v}" |
"Dep (c1;;c2) = Dep c1 O Dep c2" |
"Dep (IF b THEN c1 ELSE c2) = Dep c1 \<union> Dep c2 \<union> vars b \<times> UNIV" |
"Dep (WHILE b DO c) = lfp(\<lambda>R. Id \<union> vars b \<times> UNIV \<union> Dep c O R)"

text\<open>
where @{text"\<times>"} is the cross product of two sets.
Prove monotonicity of the function @{const lfp} is applied to.
\<close>


text\<open> For the correctness statement define \<close>

abbreviation Deps :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"Deps c X \<equiv> (\<Union> x\<in>X. {y. (y,x) : Dep c})"

text\<open> and prove \<close>

lemma "\<lbrakk> (c,s) \<Rightarrow> s';  (c,t) \<Rightarrow> t';  s = t on Deps c X \<rbrakk> \<Longrightarrow> s' = t' on X"
proof (induct arbitrary: t t' X rule: big_step_induct)
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  from Seq(5) obtain ti where Hti: "(c\<^sub>1, t) \<Rightarrow> ti" "(c\<^sub>2, ti) \<Rightarrow> t'" by auto
  from Seq(6) have "s\<^sub>1 = t on Deps c\<^sub>1 (Deps c\<^sub>2 X)" by auto
  from Seq(2) [OF Hti(1) this] have "s\<^sub>2 = ti on Deps c\<^sub>2 X" .
  from Seq(4) [OF Hti(2) this] show ?case .
next
  case (IfTrue b s c\<^sub>1 s' c\<^sub>2)
  show ?case
  proof (cases "X = {}")
    case False
    with IfTrue(5) have Heq: "s = t on vars b" "s = t on Deps c\<^sub>1 X" by auto
    from bval_eq_if_eq_on_vars [OF Heq(1)] IfTrue(1) have "bval b t" by simp
    with IfTrue(4) have "(c\<^sub>1, t) \<Rightarrow> t'" by auto
    from IfTrue(3) [OF this Heq(2)] show ?thesis .
  qed simp
next
  case (IfFalse b s c\<^sub>2 s' c\<^sub>1)
  then show ?case
  proof (cases "X = {}")
    case False
    with IfFalse(5) have Heq: "s = t on vars b" "s = t on Deps c\<^sub>2 X" by auto
    from bval_eq_if_eq_on_vars [OF Heq(1)] IfFalse(1) have "\<not>bval b t" by simp
    with IfFalse(4) have "(c\<^sub>2, t) \<Rightarrow> t'" by auto
    from IfFalse(3) [OF this Heq(2)] show ?thesis .
  qed simp
next
  case (WhileFalse b s c)
  let ?f = "\<lambda>R. Id \<union> vars b \<times> UNIV \<union> Dep c O R"
  have monof: "mono ?f" unfolding mono_def by auto
  from lfp_fixpoint [OF this] have fpf: "?f (lfp ?f) = lfp ?f" .
  show ?case
  proof (cases "X = {}")
    case False
    then have "vars b \<subseteq> (\<Union> x\<in>X. {y. (y,x) \<in> ?f (lfp ?f)})" by auto
    also from fpf have "\<dots> \<subseteq> Deps (WHILE b DO c) X" by simp
    finally have "vars b \<subseteq> Deps (WHILE b DO c) X" .
    with WhileFalse(3) have Heq1: "s = t on vars b" by auto
    from bval_eq_if_eq_on_vars [OF Heq1] WhileFalse(1) have "\<not>bval b t" by simp
    with WhileFalse(2) have Htt': "t' = t" by auto
    from False have "X \<subseteq> (\<Union> x\<in>X. {y. (y,x) \<in> ?f (lfp ?f)})" by auto
    also from fpf have "\<dots> \<subseteq> Deps (WHILE b DO c) X" by simp
    finally have Heq2: "X \<subseteq> Deps (WHILE b DO c) X" .
    with WhileFalse(3) Htt' show ?thesis by auto
  qed simp
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  let ?f = "\<lambda>R. Id \<union> vars b \<times> UNIV \<union> Dep c O R"
  have monof: "mono ?f" unfolding mono_def by auto
  from lfp_fixpoint [OF this] have fpf: "?f (lfp ?f) = lfp ?f" .
  show ?case
  proof (cases "X = {}")
    case False
    then have "vars b \<subseteq> (\<Union> x\<in>X. {y. (y,x) \<in> ?f (lfp ?f)})" by auto
    also from fpf have "\<dots> \<subseteq> Deps (WHILE b DO c) X" by simp
    finally have "vars b \<subseteq> Deps (WHILE b DO c) X" .
    with WhileTrue(7) have Heq1: "s\<^sub>1 = t on vars b" by auto
    from bval_eq_if_eq_on_vars [OF Heq1] WhileTrue(1) have "bval b t" by simp
    with WhileTrue(6) obtain ti where Htw: "(c, t) \<Rightarrow> ti" "(WHILE b DO c, ti) \<Rightarrow> t'" by auto
    have "Deps c (Deps (WHILE b DO c) X) \<subseteq> Deps (WHILE b DO c) X" using lfp_fixpoint [OF monof] by auto
    with WhileTrue(7) have "s\<^sub>1 = t on Deps c (Deps (WHILE b DO c) X)" by blast
    from WhileTrue(3) [OF Htw(1) this] have "s\<^sub>2 = ti on Deps (WHILE b DO c) X" .
    from WhileTrue(5) [OF Htw(2) this] show ?thesis .
  qed simp
qed auto

text\<open>

Give an example that the following stronger termination-sensitive property
@{prop[display] "\<lbrakk> (c,s) \<Rightarrow> s'; s = t on Deps c X \<rbrakk>
  \<Longrightarrow> \<exists>t'. (c,t) \<Rightarrow> t' \<and> s' = t' on X"}
does not hold. Hint: @{prop"X = {}"}.
\<close>

lemma "\<exists> c s s' t X. (c, s) \<Rightarrow> s' \<and> s = t on Deps c X \<and> (\<nexists>t'. (c, t) \<Rightarrow> t')"
proof -
  let ?b = "Less (N 0) (V ''x'')"
  let ?c = "SKIP"
  let ?w = "WHILE ?b DO ?c"
  let ?s = "<> :: vname \<Rightarrow> val"
  let ?t = "<''x'' := 1> :: vname \<Rightarrow> val"
  have H1: "(?w, ?s) \<Rightarrow> ?s" unfolding null_state_def by auto
  have H2: "?s = ?t on Deps ?w {}" by simp
  have Hbt: "bval ?b ?t" by simp
  have H3: "\<nexists>t'. (?w, ?t) \<Rightarrow> t'"
  proof
    assume "\<exists>t'. (?w, ?t) \<Rightarrow> t'"
    then obtain t' where "(?w, ?t) \<Rightarrow> t'" by auto
    then show "False"
      using Hbt by (induct "?w" "?t" t' rule: big_step_induct) auto
  qed
  from H1 H2 H3 show ?thesis by blast
qed

text\<open>

In the definition of @{term"Dep(IF b THEN c1 ELSE c2)"} the variables
in @{text b} can influence all variables (@{text UNIV}). However,
if a variable is not assigned to in @{text c1} and @{text c2}
it is not influenced by @{text b} (ignoring termination).
Theory @{theory "HOL-IMP.Vars"} defines a function @{const lvars} such
that @{term"lvars c"} is the set of variables on the left-hand side
of an assignment in @{text c}.
Modify the definition of @{const Dep} as follows:
replace @{const UNIV} by @{term"lvars c1 \<union> lvars c2"}
(in the case @{term"IF b THEN c1 ELSE c2"}) and by \mbox{@{term"lvars c"}}
(in the case @{term"WHILE b DO c"}).
Adjust the proof of the above correctness statement.
\<close>

text\<open>
\endexercise
\<close>

end

