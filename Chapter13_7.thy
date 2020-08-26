theory Chapter13_7
imports "HOL-IMP.Abs_Int2"
begin

text\<open>
\setcounter{exercise}{15}
\exercise
Give a readable proof that if @{text "\<gamma> ::"} \noquotes{@{typ[source]"'a::lattice \<Rightarrow> 'b::lattice"}}
is a monotone function, then @{prop "\<gamma> (a\<^sub>1 \<sqinter> a\<^sub>2) \<le> \<gamma> a\<^sub>1 \<sqinter> \<gamma> a\<^sub>2"}:
\<close>

lemma fixes \<gamma> :: "'a::lattice \<Rightarrow> 'b :: lattice"
assumes mono: "\<And>x y. x \<le> y \<Longrightarrow> \<gamma> x \<le> \<gamma> y"
shows "\<gamma> (a\<^sub>1 \<sqinter> a\<^sub>2) \<le> \<gamma> a\<^sub>1 \<sqinter> \<gamma> a\<^sub>2" (is "\<gamma> ?m \<le> _")
proof -
  have "\<gamma> ?m \<le> \<gamma> a\<^sub>1" by (intro mono, auto)
  moreover 
  have "\<gamma> ?m \<le> \<gamma> a\<^sub>2" by (intro mono, auto)
  ultimately show ?thesis by simp
qed

text\<open>
Give an example of two lattices and a monotone @{text \<gamma>}
where @{prop"\<gamma> a\<^sub>1 \<sqinter> \<gamma> a\<^sub>2 \<le> \<gamma> (a\<^sub>1 \<sqinter> a\<^sub>2)"} does not hold.

Consider {a, c, t, b} of unique elements with order generated by t being top and b being bottom.
Let f be identity with codomain {a, c, d, t, b} of unique elements, with order generated by t
being top, b being bottom, and "d \<le> a", "d \<le> c".
then \<gamma> (a \<sqinter> c) = b < d = \<gamma> a \<sqinter> \<gamma> c.
\<close>

text\<open>
\endexercise

\exercise
Consider a simple sign analysis based on this abstract domain:
\<close>

datatype sign = None | Neg | Pos0 | Any

fun \<gamma> :: "sign \<Rightarrow> val set" where
"\<gamma> None = {}" |
"\<gamma> Neg = {i. i < 0}" |
"\<gamma> Pos0 = {i. i \<ge> 0}" |
"\<gamma> Any = UNIV"

text\<open>
Define inverse analyses for ``@{text"+"}'' and ``@{text"<"}''
and prove the required correctness properties:
\<close>

fun inv_plus' :: "sign \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign * sign" where
  "inv_plus' None _ _ = (None, None)" |
  "inv_plus' _ None _ = (None, None)" |
  "inv_plus' _ _ None = (None, None)" |
  "inv_plus' Neg Pos0 Pos0 = (None, None)" |
  "inv_plus' Pos0 Neg Neg = (None, None)" |
  "inv_plus' Neg Pos0 Any = (Pos0, Neg)" |
  "inv_plus' Neg Any Pos0 = (Neg, Pos0)" |
  "inv_plus' Pos0 Neg Any = (Neg, Pos0)" |
  "inv_plus' Pos0 Any Neg = (Pos0, Neg)" |
  "inv_plus' _ a b = (a, b)"

lemma
  "\<lbrakk> inv_plus' a a1 a2 = (a1',a2');  i1 \<in> \<gamma> a1;  i2 \<in> \<gamma> a2; i1+i2 \<in> \<gamma> a \<rbrakk>
  \<Longrightarrow> i1 \<in> \<gamma> a1' \<and> i2 \<in> \<gamma> a2' "
  by (cases a; cases a1; cases a2) auto

fun inv_less' :: "bool \<Rightarrow> sign \<Rightarrow> sign \<Rightarrow> sign * sign" where
  "inv_less' _ None _ = (None, None)" |
  "inv_less' _ _ None = (None, None)" |
  "inv_less' True Pos0 Neg = (None, None)" |
  "inv_less' False Neg Pos0 = (None, None)" |
  "inv_less' True Pos0 Any = (Pos0, Pos0)" |
  "inv_less' True Any Neg = (Neg, Neg)" |
  "inv_less' False Neg Any = (Neg, Neg)" |
  "inv_less' False Any Pos0 = (Pos0, Pos0)" |
  "inv_less' _ a b = (a, b)"

lemma
  "\<lbrakk> inv_less' bv a1 a2 = (a1',a2');  i1 \<in> \<gamma> a1;  i2 \<in> \<gamma> a2; (i1<i2) = bv \<rbrakk>
  \<Longrightarrow> i1 \<in> \<gamma> a1' \<and> i2 \<in> \<gamma> a2'"
  by (cases bv; cases a1; cases a2) auto

text\<open>
\indent
For the ambitious: turn the above fragment into a full-blown abstract interpreter
by replacing the interval analysis in theory @{theory "HOL-IMP.Abs_Int2"}@{text"_ivl"}
by a sign analysis.
\endexercise
\<close>

end
