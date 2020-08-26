theory Chapter12_3
imports "HOL-IMP.Hoare_Sound_Complete"
begin

text\<open>
\exercise
Prove
\<close>

lemma "\<Turnstile> {P} c {Q} \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> wp c Q s)"
    unfolding hoare_valid_def wp_def by auto

text\<open>
\endexercise

\begin{exercise}
Replace the assignment command with a new command \mbox{@{term"Do f"}} where
@{text "f ::"} @{typ "state \<Rightarrow> state"} can be an arbitrary state transformer.
Update the big-step semantics, Hoare logic and the soundness and completeness proofs.
\end{exercise}
\<close>
text \<open>
\exercise
Which of the following rules are correct? Proof or counterexample!
\<close>

lemma "\<lbrakk>\<turnstile> {P} c {Q};  \<turnstile> {P'} c {Q'}\<rbrakk> \<Longrightarrow>
  \<turnstile> {\<lambda>s. P s \<or> P' s} c {\<lambda>s. Q s \<or> Q' s}"
proof -
  assume "\<turnstile> {P} c {Q}"
  then have "\<Turnstile> {P} c {Q}" by (rule hoare_sound)
  moreover assume "\<turnstile> {P'} c {Q'}"
  then have "\<Turnstile> {P'} c {Q'}" by (rule hoare_sound)
  ultimately have "\<Turnstile> {\<lambda>s. P s \<or> P' s} c {\<lambda>s. Q s \<or> Q' s}"
    unfolding hoare_valid_def by blast
  then show ?thesis by (rule hoare_complete)
qed

lemma "\<lbrakk>\<turnstile> {P} c {Q};  \<turnstile> {P'} c {Q'}\<rbrakk> \<Longrightarrow>
  \<turnstile> {\<lambda>s. P s \<and> P' s} c {\<lambda>s. Q s \<and> Q' s}"
proof -
  assume "\<turnstile> {P} c {Q}"
  then have "\<Turnstile> {P} c {Q}" by (rule hoare_sound)
  moreover assume "\<turnstile> {P'} c {Q'}"
  then have "\<Turnstile> {P'} c {Q'}" by (rule hoare_sound)
  ultimately have "\<Turnstile> {\<lambda>s. P s \<and> P' s} c {\<lambda>s. Q s \<and> Q' s}"
    unfolding hoare_valid_def by blast
  then show ?thesis by (rule hoare_complete)
qed

lemma "\<exists>P Q P' Q' c. \<turnstile> {P} c {Q} \<and>  \<turnstile> {P'} c {Q'} \<and> \<not> \<turnstile> {\<lambda>s. P s \<longrightarrow> P' s} c {\<lambda>s. Q s \<longrightarrow> Q' s}"
proof -
  let ?P = "\<lambda>s::state. s ''x'' = 1"
  let ?Q = "\<lambda>s::state. True"
  have "\<turnstile> {?P} SKIP {?P}" (is ?P1) by (rule Skip)
  moreover from this have "\<turnstile> {?P} SKIP {?Q}" (is ?P2) by (rule weaken_post, blast)
  moreover have "\<not> \<turnstile> {\<lambda>s. ?P s \<longrightarrow> ?P s} SKIP {\<lambda>s. ?Q s \<longrightarrow> ?P s}" (is ?P3)
  proof
    assume "\<turnstile> {\<lambda>s. ?P s \<longrightarrow> ?P s} SKIP {\<lambda>s. ?Q s \<longrightarrow> ?P s}"
    then have "\<Turnstile> {\<lambda>s. ?P s \<longrightarrow> ?P s} SKIP {\<lambda>s. ?Q s \<longrightarrow> ?P s}" by (rule hoare_sound)
    then have H1: "\<And>s t. \<lbrakk>(?P s \<longrightarrow> ?P s); (SKIP, s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (?Q t \<longrightarrow> ?P t)"
      unfolding hoare_valid_def by (intro allI impI, blast)
    have H2: "?P <> \<longrightarrow> ?P <>" unfolding null_state_def by blast
    have H3: "(SKIP, <>) \<Rightarrow> <>" by auto
    from H1 [of "<>", OF H2 H3] show False unfolding null_state_def by simp
  qed
  ultimately show ?thesis by blast
qed
text\<open>
\endexercise

\begin{exercise}
Based on Exercise~\ref{exe:IMP:OR}, extend Hoare logic and the soundness and completeness proofs
with nondeterministic choice.
\end{exercise}

\begin{exercise}
Based on Exercise~\ref{exe:IMP:REPEAT}, extend Hoare logic and the soundness and completeness proofs
with a @{text REPEAT} loop. Hint: think of @{text"REPEAT c UNTIL b"} as
equivalent to \noquotes{@{term[source]"c;; WHILE Not b DO c"}}.
\end{exercise}

\exercise\label{exe:sp}
The dual of the weakest precondition is the \concept{strongest postcondition}
@{text sp}. Define @{text sp} in analogy with @{const wp} via the big-step semantics:
\<close>

definition sp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
  "sp c P = (\<lambda>t. \<exists>s. P s \<and> (c, s) \<Rightarrow> t)"

text\<open> Prove that @{const sp} really is the strongest postcondition: \<close>

lemma "(\<Turnstile> {P} c {Q}) \<longleftrightarrow> (\<forall>s. sp c P s \<longrightarrow> Q s)"
  unfolding hoare_valid_def sp_def by blast

text\<open>
In analogy with the derived equations for @{const wp} given in the text,
give and prove equations for ``calculating'' @{const sp} for three constructs:
@{prop"sp (x ::= a) P = Q\<^sub>1"}, @{prop"sp (c\<^sub>1;;c\<^sub>2) P = Q\<^sub>2"}, and
@{prop"sp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) P = Q\<^sub>3"}.
The @{text Q\<^sub>i} must not involve the semantics and may only call
@{const sp} recursively on the subcommands @{text c\<^sub>i}.
Hint: @{text Q\<^sub>1} requires an existential quantifier.
\<close>

lemma sp_Ass [simp]: "sp (x::=a) P = (\<lambda>s. \<exists> x'. P (s(x := x')) \<and> s x = aval a (s(x := x')))"
  unfolding sp_def
proof (rule ext, auto)
  fix s :: state
  have Heq: "s(x := s x) = s" by auto
  assume "P s"
  with Heq have "P (s(x := s x)) \<and> aval a s = aval a (s(x := s x))" by auto
  then show "\<exists>x'. P (s(x := x')) \<and> aval a s = aval a (s(x := x'))" by blast
next
  fix t :: state and x'
  let ?s = "t(x := x')"
  assume H: "P (t(x := x'))" "t x = aval a ?s"
  have Heq: "t(x := t x) = t" by auto
  have "(x ::= a, ?s) \<Rightarrow> ?s(x := aval a ?s)" by (rule big_step.Assign)
  with H(2) Heq have "(x ::= a, ?s) \<Rightarrow> t" by simp
  with H have "P ?s \<and> (x ::= a, ?s) \<Rightarrow> t" by simp
  from exI [of "\<lambda>s. P s \<and> (x ::= a, s) \<Rightarrow> t", OF this]
  show "\<exists>s. P s \<and> (x ::= a, s) \<Rightarrow> t" .
qed

lemma sp_Seq [simp]: "sp (c\<^sub>1;; c\<^sub>2) P = sp c\<^sub>2 (sp c\<^sub>1 P)"
  unfolding sp_def by (rule ext) auto

lemma sp_If [simp]: "sp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) P =
  (\<lambda>t. sp c\<^sub>1 (\<lambda>s. P s \<and> bval b s) t \<or> sp c\<^sub>2 (\<lambda>s. P s \<and> \<not>bval b s) t)"
  unfolding sp_def by (rule ext) auto

text\<open>
\endexercise
\<close>

end

