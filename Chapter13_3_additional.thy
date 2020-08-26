theory Chapter13_3_additional
  imports "HOL-IMP.Complete_Lattice"
begin

text \<open>
Exercise 13.1

0:
  A0: {}
  A1: {}
  A2: {}
  A3: {}
  A4: {}

1:
  A0: {<x:=0,y:=2>}

2:
  A1: {<x:=0,y:=2>}

3:
  A2: {<x:=0,y:=2>}

4:
  A3: {<x:=2,y:=1>}

5:
  A2: {<x:=0,y:=2>, <x:=2,y:=1>}

6:
  A3: {<x:=2,y:=1>, <x:=3,y:=0>}

7:
  A4: {<x:=3,y:=0>}

8:
  Fixpoint reached

Exercise 13.3
\<close>

context Complete_Lattice
begin

definition Lub :: "'a set \<Rightarrow> 'a" where
  "Lub S = Glb {u\<in>L. \<forall>s\<in>S. s \<le> u}"

theorem Lub_greater: "\<lbrakk>A \<subseteq> L; a \<in> A\<rbrakk> \<Longrightarrow> a \<le> Lub A"
  unfolding Lub_def by (auto intro!: Glb_greatest)

theorem Lub_least: "\<lbrakk>b \<in> L; \<forall>a\<in>A. a \<le> b\<rbrakk> \<Longrightarrow> Lub A \<le> b"
  unfolding Lub_def by (auto intro!: Glb_lower)

theorem Lub_in_L: "\<lbrakk>A \<subseteq> L\<rbrakk> \<Longrightarrow> Lub A \<in> L"
  unfolding Lub_def by (auto intro!: Glb_in_L)

end

text \<open>
Exercise 13.4: The flaw in the argument is that there is no least element
in the empty set. More generally, there is no greatest lower bound of the
empty set. For if n is a lower bound of the empty set, then Suc n is a
greater lower bound of the empty set.
\<close>

text \<open>13.5: -Inf is a lower bound of any set of extended integers.
Every number that is not -Inf is an integer or +Inf, and either of these
are greater than -Inf. If a set does not have an integer glb, or has +Inf as their glb, then -Inf is
the greatest among its lower bounds.\<close>

text \<open>13.6:

Let P be a set of pre-fixpoints in a complete lattice.
Show that m = \<Sqinter>P is a pre-fixpoint.

Proof is the same as in 10.27. First, for all p \<in> P, we have
m \<le> p. By monotonicity, f m \<le> f p, and by pre-fixpoint property of p,
f p \<le> p. So f m is a lower bound of p. Since m is the greatest lower bound,
we have f m \<le> m. Thus m is a pre-fixpoint under f.

13.7.1:
Consider f: x \<mapsto> x - 1 on Z. Then f is monotone and each n is a pre-fixpoint,
but not a fixpoint.

13.7.2:
Consider the order with basis {a<b, b<c} on {a, b, c, d}. Then c and d are
both least fixpoints, but the pre-fixpoints are b, c, d, so that b and d
are least pre-fixpoints

13.8:
We show that P is a least fixpoint of f iff P is a least fixpoint of g = \<lambda>S. S \<union> f S. Then
the least fixpoint of f is also the least fixpoint of g.

First, if f P = P, we have g P = P \<union> f P = P \<union> P = P, so that
P is a fixpoint of g. So the least fixpoint of g is weakly less than the
least fixpoint of f.

Suppose that P is the least fixpoint of g. From g P = P we have P = P \<union> f P, so must have
f P \<subseteq> P. By Theorem 10.29, since f is monotone, the lfp of P is weakly less than P as well,
that is, the least fixpoint of f is weakly less than the least fixpoint of f.

By antisymmetry, we have lfp f = lfp g.
\<close>
