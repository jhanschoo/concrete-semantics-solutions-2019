theory Short_Theory_13_14
  imports "HOL-IMP.Abs_Int1"
begin

datatype sign = Neg | Zero | Pos | Any

text\<open>Instantiation of class \<^class>\<open>order\<close> with type \<^typ>\<open>sign\<close>:\<close>

instantiation sign :: order
begin

text\<open>First the definition of the interface function \<open>\<le>\<close>. Note that
the header of the definition must refer to the ascii name \<^const>\<open>less_eq\<close> of the
constants as \<open>less_eq_parity\<close> and the definition is named \<open>less_eq_parity_def\<close>.  Inside the definition the symbolic names can be used.\<close>

definition less_eq_sign where
"x \<le> y = (y = Any \<or> x=y)"

text\<open>We also need \<open><\<close>, which is defined canonically:\<close>

definition less_sign where
"x < y = (x \<le> y \<and> \<not> y \<le> (x::sign))"

text\<open>\noindent(The type annotation is necessary to fix the type of the polymorphic predicates.)

Now the instance proof, i.e.\ the proof that the definition fulfills
the axioms (assumptions) of the class. The initial proof-step generates the
necessary proof obligations.\<close>

instance
proof
  fix x::sign show "x \<le> x" by(auto simp: less_eq_sign_def)
next
  fix x y z :: sign assume "x \<le> y" "y \<le> z" thus "x \<le> z"
    by(auto simp: less_eq_sign_def)
next
  fix x y :: sign assume "x \<le> y" "y \<le> x" thus "x = y"
    by(auto simp: less_eq_sign_def)
next
  fix x y :: sign show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by(rule less_sign_def)
qed

end

text\<open>Instantiation of class \<^class>\<open>semilattice_sup_top\<close> with type \<^typ>\<open>sign\<close>:\<close>

instantiation sign :: semilattice_sup_top
begin

definition sup_sign where
"x \<squnion> y = (if x = y then x else Any)"

definition top_sign where
"\<top> = Any"

text\<open>Now the instance proof. This time we take a shortcut with the help of
proof method \<open>goal_cases\<close>: it creates cases 1 ... n for the subgoals
1 ... n; in case i, i is also the name of the assumptions of subgoal i and
\<open>case?\<close> refers to the conclusion of subgoal i.
The class axioms are presented in the same order as in the class definition.\<close>

instance
proof (standard, goal_cases)
  case 1 (*sup1*) show ?case by(auto simp: less_eq_sign_def sup_sign_def)
next
  case 2 (*sup2*) show ?case by(auto simp: less_eq_sign_def sup_sign_def)
next
  case 3 (*sup least*) thus ?case by(auto simp: less_eq_sign_def sup_sign_def)
next
  case 4 (*top*) show ?case by(auto simp: less_eq_sign_def top_sign_def)
qed

end


text\<open>Now we define the functions used for instantiating the abstract
interpretation locales. Note that the Isabelle terminology is
\emph{interpretation}, not \emph{instantiation} of locales, but we use
instantiation to avoid confusion with abstract interpretation.\<close>

fun \<gamma>_sign :: "sign \<Rightarrow> val set" where
"\<gamma>_sign Neg = {i. i < 0}" |
"\<gamma>_sign Zero  = {0}" |
"\<gamma>_sign Pos  = {i. 0 < i}" |
"\<gamma>_sign Any = UNIV"

fun num_sign :: "val \<Rightarrow> sign" where
"num_sign i = (if i < 0 then Neg else if 0 < i then Pos else Zero)"

fun plus_sign :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
"plus_sign Neg Neg = Neg" |
"plus_sign Neg Zero = Neg" |
"plus_sign Zero  Neg  = Neg" |
"plus_sign Zero Zero  = Zero" |
"plus_sign Zero  Pos = Pos" |
"plus_sign Pos  Zero = Pos" |
"plus_sign Pos  Pos = Pos" |
"plus_sign _  _ = Any"

text\<open>First we instantiate the abstract value interface and prove that the
functions on type \<^typ>\<open>sign\<close> have all the necessary properties:\<close>

global_interpretation Val_semilattice
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
proof (standard, goal_cases) txt\<open>subgoals are the locale axioms\<close>
  case 1 thus ?case by(auto simp: less_eq_sign_def)
next
  case 2 show ?case by(auto simp: top_sign_def)
next
  case 3 show ?case by auto
next
  case (4 _ a1 _ a2) thus ?case
    by (induction a1 a2 rule: plus_sign.induct) auto
qed

text\<open>In case 4 we needed to refer to particular variables.
Writing (i x y z) fixes the names of the variables in case i to be x, y and z
in the left-to-right order in which the variables occur in the subgoal.
Underscores are anonymous placeholders for variable names we don't care to fix.\<close>

text\<open>Instantiating the abstract interpretation locale requires no more
proofs (they happened in the instatiation above) but delivers the
instantiated abstract interpreter which we call \<open>AI_parity\<close>:\<close>

global_interpretation Abs_Int
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
defines aval_sign = aval' and step_sign = step' and AI_sign = AI
..


subsubsection "Tests"

definition "test1_sign =
  ''x'' ::= N 1;;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 2)"
value "show_acom (the(AI_sign test1_sign))"

definition "test2_sign =
  ''x'' ::= N 1;;
  WHILE Less (V ''x'') (N 100) DO ''x'' ::= Plus (V ''x'') (N 3)"

definition "steps c i = ((step_sign \<top>) ^^ i) (bot c)"

value "show_acom (steps test2_sign 0)"
value "show_acom (steps test2_sign 1)"
value "show_acom (steps test2_sign 2)"
value "show_acom (steps test2_sign 3)"
value "show_acom (steps test2_sign 4)"
value "show_acom (steps test2_sign 5)"
value "show_acom (steps test2_sign 6)"
value "show_acom (the(AI_parity test2_sign))"


subsubsection "Termination"

global_interpretation Abs_Int_mono
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
proof (standard, goal_cases)
  case (1 _ a1 _ a2) thus ?case
    by(induction a1 a2 rule: plus_sign.induct)
      (auto simp add:less_eq_sign_def)
qed

definition m_sign :: "sign \<Rightarrow> nat" where
"m_sign x = (if x = Any then 0 else 1)"

global_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
and m = m_sign and h = "1"
proof (standard, goal_cases)
  case 1 thus ?case by(auto simp add: m_sign_def less_eq_sign_def)
next
  case 2 thus ?case by(auto simp add: m_sign_def less_eq_sign_def less_sign_def)
qed

thm AI_Some_measure

end
