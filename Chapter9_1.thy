theory Chapter9_1
imports "HOL-IMP.Types"
begin

text\<open>
\section*{Chapter 9}

\exercise
Reformulate the inductive predicates \ @{prop"\<Gamma> \<turnstile> a : \<tau>"},
\ @{prop"\<Gamma> \<turnstile> (b::bexp)"} \
and \ \mbox{@{prop"\<Gamma> \<turnstile> (c::com)"}} \ as three recursive functions
\<close>

fun atype :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty option" where
  "atype _ (Ic i) = Some Ity" |
  "atype _ (Rc r) = Some Rty" |
  "atype \<Gamma> (V x) = Some (\<Gamma> x)" |
  "atype \<Gamma> (Plus a1 a2) = (if
    atype \<Gamma> a1 = atype \<Gamma> a2
    then (atype \<Gamma> a1)
    else None)"

fun bok :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" where
  "bok _ (Bc v) = True" |
  "bok \<Gamma> (Not b) = bok \<Gamma> b" |
  "bok \<Gamma> (And b1 b2) \<longleftrightarrow> bok \<Gamma> b1 \<and> bok \<Gamma> b2" |
  "bok \<Gamma> (Less a1 a2) \<longleftrightarrow> atype \<Gamma> a1 = atype \<Gamma> a2 \<and> atype \<Gamma> a1 \<noteq> None"

fun cok :: "tyenv \<Rightarrow> com \<Rightarrow> bool" where
  "cok \<Gamma> SKIP = True" |
  "cok \<Gamma> (x ::= a) \<longleftrightarrow> atype \<Gamma> a = Some (\<Gamma> x)" |
  "cok \<Gamma> (c1;; c2) \<longleftrightarrow> cok \<Gamma> c1 \<and> cok \<Gamma> c2" |
  "cok \<Gamma> (IF b THEN c1 ELSE c2) \<longleftrightarrow> bok \<Gamma> b \<and> cok \<Gamma> c1 \<and> cok \<Gamma> c2" |
  "cok \<Gamma> (WHILE b DO c) \<longleftrightarrow> bok \<Gamma> b \<and> cok \<Gamma> c"

text\<open> and prove \<close>

lemma atyping_atype: "(\<Gamma> \<turnstile> a : \<tau>) = (atype \<Gamma> a = Some \<tau>)"
  by (induct a) auto

lemma btyping_bok: "(\<Gamma> \<turnstile> b) = bok \<Gamma> b"
  by (induct b) (auto iff add: atyping_atype)

lemma ctyping_cok: "(\<Gamma> \<turnstile> c) = cok \<Gamma> c"
  by (induct c) (auto iff add: atyping_atype btyping_bok)

text\<open>
\endexercise

\exercise
Modify the evaluation and typing of @{typ aexp} by allowing @{typ int}s to be coerced
to @{typ real}s with the predefined coercion function
\noquotes{@{term[source] "real_of_int :: int \<Rightarrow> real"}} where necessary.
Now every @{typ aexp} has a value. Define an evaluation function:
\<close>

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (Ic i) _ = Iv i" |
  "aval (Rc r) _ = Rv r" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = (case
    (aval a1 s, aval a2 s) of
    (Iv i1, Iv i2) \<Rightarrow> Iv (i1 + i2) |
    (Iv i, Rv r) \<Rightarrow> Rv (i + r) |
    (Rv r, Iv i) \<Rightarrow> Rv (r + i) |
    (Rv r1, Rv r2) \<Rightarrow> Rv (r1 + r2))"

text\<open>
Similarly, every @{typ aexp} has a type.
Define a function that computes the type of an @{typ aexp}
\<close>

fun atyp :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty" where
  "atyp _ (Ic i) = Ity" |
  "atyp _ (Rc r) = Rty" |
  "atyp \<Gamma> (V x) = \<Gamma> x" |
  "atyp \<Gamma> (Plus a1 a2) = (if
    atyp \<Gamma> a1 = Ity
    then atyp \<Gamma> a2
    else Rty)"
    

text\<open> and prove that it computes the correct type: \<close>

lemma  "\<Gamma> \<turnstile> s \<Longrightarrow> atyp \<Gamma> a = type (aval a s)"
  unfolding styping_def
  by (induct a) (auto split: val.split)

text\<open>
Note that Isabelle inserts the coercion @{typ real} automatically.
For example, if you write @{term "Rv(i+r)"} where @{text"i :: int"} and
@{text "r :: real"} then it becomes @{term "Rv(real i + x)"}.
\endexercise
\bigskip

For the following two exercises copy theory @{short_theory "Types"} and modify it as required.

\begin{exercise}
Add a @{text REPEAT} loop (see Exercise~\ref{exe:IMP:REPEAT}) to the typed version of IMP
and update the type soundness proof.
\end{exercise}

\begin{exercise}
Modify the typed version of IMP as follows. Values are now either integers or booleans.
Thus variables can have boolean values too. Merge the two expressions types
@{typ aexp} and @{typ bexp} into one new type @{text exp} of expressions
that has the constructors of both types (of course without real constants).
Combine @{const taval} and @{const tbval} into one evaluation predicate
@{text "eval :: exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool"}. Similarly combine the two typing predicates
into one: @{text "\<Gamma> \<turnstile> e : \<tau>"} where @{text "e :: exp"} and the IMP-type @{text \<tau>} can
be one of @{text Ity} or @{text Bty}.
Adjust the small-step semantics and the type soundness proof.
\end{exercise}
\<close>

end

