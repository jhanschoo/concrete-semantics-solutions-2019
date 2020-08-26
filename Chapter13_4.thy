theory Chapter13_4
  imports "HOL-IMP.Complete_Lattice"
begin

text \<open>
Exercise 13.9

to show: x \<squnion> y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z

Assume x \<squnion> y \<le> z. With x \<le> x \<squnion> y and y \<le> x \<squnion> y, we have
x \<le> z and y \<le> z.

The other direction follows by definition of leastness.
\<close>