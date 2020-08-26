theory Short_Theory_13_15
  imports "HOL-IMP.Abs_Int1"
begin

datatype sign' = Neg | Zero | Pos

type_synonym sign = "sign' set"

lemma sign_ext: "UNIV = {Neg, Zero, Pos}"
proof auto
  fix x
  show "\<lbrakk>x \<noteq> Neg; x \<noteq> Zero\<rbrakk> \<Longrightarrow> x = Pos"
  proof (cases x, auto)
  qed
qed

lemma card_sign' [simp]: "card (UNIV :: sign) = 3" by (auto simp: sign_ext)

lemma finite_sign' [simp, intro!]: "finite (UNIV :: sign' set)" by (auto simp: sign_ext)

lemma finite_sign [simp, intro!]: "finite (UNIV :: sign set)" by (simp add: Finite_Set.finite_set)

text\<open>Instantiation of class \<^class>\<open>order\<close> with type \<^typ>\<open>sign\<close>:\<close>

text\<open>Instantiation of class \<^class>\<open>semilattice_sup_top\<close> with type \<^typ>\<open>sign\<close>:\<close>

instantiation set :: (type) semilattice_sup_top
begin
instance ..
end

text\<open>Now we define the functions used for instantiating the abstract
interpretation locales. Note that the Isabelle terminology is
\emph{interpretation}, not \emph{instantiation} of locales, but we use
instantiation to avoid confusion with abstract interpretation.\<close>

fun \<gamma>_sign' :: "sign' \<Rightarrow> val set" where
  "\<gamma>_sign' Neg = {i. i < 0}" |
  "\<gamma>_sign' Zero  = {0}" |
  "\<gamma>_sign' Pos  = {i. 0 < i}"

fun \<gamma>_sign :: "sign \<Rightarrow> val set" where
  "\<gamma>_sign S = {i. \<exists>s\<in>S. i \<in> \<gamma>_sign' s}"

fun num_sign :: "val \<Rightarrow> sign" where
"num_sign i = (if i < 0 then {Neg} else if 0 < i then {Pos} else {Zero})"

fun plus_sign' :: "sign' \<Rightarrow> sign' \<Rightarrow> sign" where
  "plus_sign' Neg Pos = UNIV" |
  "plus_sign' Pos Neg = UNIV" |
  "plus_sign' Zero s = {s}" |
  "plus_sign' s _ = {s}"
  
fun plus_sign :: "sign \<Rightarrow> sign \<Rightarrow> sign" where
  "plus_sign S1 S2 = {s. \<exists>s1\<in>S1. \<exists>s2\<in>S2. s \<in> plus_sign' s1 s2}"

text\<open>First we instantiate the abstract value interface and prove that the
functions on type \<^typ>\<open>sign\<close> have all the necessary properties:\<close>

lemma val_tricho_0:
  fixes x :: val
  obtains (BNeg) "x < 0" | (BZero) "x = 0" | (BPos) "x > 0"
  by (rule linorder_cases)

lemma \<gamma>_sign_top [simp]: "\<gamma>_sign UNIV = UNIV"
proof auto
  fix x :: val
  show "\<exists>s. x \<in> \<gamma>_sign' s"
  proof (cases rule: val_tricho_0 [of x])
    case BNeg
    then have "x \<in> \<gamma>_sign' Neg" by auto
    then show ?thesis by blast
  next
    case BZero
    then have "x \<in> \<gamma>_sign' Zero" by auto
    then show ?thesis by blast
  next
    case BPos
    then have "x \<in> \<gamma>_sign' Pos" by auto
    then show ?thesis by blast
  qed
qed

lemma Neg_\<gamma>_sign [dest]: "\<lbrakk>x < 0; x \<in> \<gamma>_sign S\<rbrakk> \<Longrightarrow> Neg \<in> S"
proof auto
  fix s
  assume assm: "s \<in> S" "x < 0" "x \<in> \<gamma>_sign' s"
  from assm(2, 3) have "s = Neg" by (cases s) auto
  with assm(1) show "Neg \<in> S" by simp
qed

lemma Zero_\<gamma>_sign [dest]: "\<lbrakk>x = 0; x \<in> \<gamma>_sign S\<rbrakk> \<Longrightarrow> Zero \<in> S"
proof auto
  fix s
  assume assm: "s \<in> S" "0 \<in> \<gamma>_sign' s"
  from assm(2) have "s = Zero" by (cases s) auto
  with assm(1) show "Zero \<in> S" by simp
qed

lemma Pos_\<gamma>_sign [dest]: "\<lbrakk>0 < x; x \<in> \<gamma>_sign S\<rbrakk> \<Longrightarrow> Pos \<in> S"
proof auto
  fix s
  assume assm: "s \<in> S" "0 < x" "x \<in> \<gamma>_sign' s"
  from assm(2, 3) have "s = Pos" by (cases s) auto
  with assm(1) show "Pos \<in> S" by simp
qed

global_interpretation Val_semilattice
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
proof (standard, goal_cases)
  case (1 a b)
  then show ?case by auto
next
  case 2
  then show ?case
  proof auto
    fix x :: val
    show "\<exists>s. x \<in> \<gamma>_sign' s"
    proof (cases rule: val_tricho_0 [of x])
      case BNeg
      then have "x \<in> \<gamma>_sign' Neg" by auto
      then show ?thesis by blast
    next
      case BZero
      then have "x \<in> \<gamma>_sign' Zero" by auto
      then show ?thesis by blast
    next
      case BPos
      then have "x \<in> \<gamma>_sign' Pos" by auto
      then show ?thesis by blast
    qed
  qed
next
  case (3 i)
  then show ?case by auto
next
  case (4 i1 a1 i2 a2)
  show ?case
  proof (cases rule: val_tricho_0 [of i1];
      cases rule: val_tricho_0 [of i2];
      cases rule: val_tricho_0 [of "i1 + i2"];
      linarith?)
    {
      assume "i1 < 0"
      with 4(1) have H1: "Neg \<in> a1" by (simp add: Neg_\<gamma>_sign)
      {
        assume "i2 < 0"
        with 4(2) have H2: "Neg \<in> a2" by (simp add: Neg_\<gamma>_sign)
        from H1 H2 have "Neg \<in> plus_sign a1 a2" by force
        moreover assume "i1 + i2 < 0"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
      {
        assume "i2 = 0"
        with 4(2) have H2: "Zero \<in> a2" by (simp add: Zero_\<gamma>_sign)
        from H1 H2 have "Neg \<in> plus_sign a1 a2" by force
        moreover assume "i1 + i2 < 0"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
      {
        assume "i2 > 0"
        with 4(2) have H2: "Pos \<in> a2" by (simp add: Pos_\<gamma>_sign)
        from H1 H2 have "plus_sign a1 a2 = UNIV" by force
        then have "\<gamma>_sign (plus_sign a1 a2) = UNIV" using \<gamma>_sign_top by auto
        then show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by auto
        then show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" .
        then show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" .
      }
    }
    {
      assume "i1 = 0"
      with 4(1) have H1: "Zero \<in> a1" by (simp add: Zero_\<gamma>_sign)
      {
        assume "i2 < 0"
        with 4(2) have H2: "Neg \<in> a2" by (simp add: Neg_\<gamma>_sign)
        from H1 H2 have "Neg \<in> plus_sign a1 a2" by force
        moreover assume "i1 + i2 < 0"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
      {
        assume "i2 = 0"
        with 4(2) have H2: "Zero \<in> a2" by (simp add: Zero_\<gamma>_sign)
        from H1 H2 have "Zero \<in> plus_sign a1 a2" by force
        moreover assume "i1 + i2 = 0"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
      {
        assume "i2 > 0"
        with 4(2) have H2: "Pos \<in> a2" by (simp add: Pos_\<gamma>_sign)
        from H1 H2 have "Pos \<in> plus_sign a1 a2" by force
        moreover assume "0 < i1 + i2"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
    }
    {
      assume "0 < i1"
      with 4(1) have H1: "Pos \<in> a1" by (simp add: Pos_\<gamma>_sign)
      {
        assume "i2 < 0"
        with 4(2) have H2: "Neg \<in> a2" by (simp add: Neg_\<gamma>_sign)
        from H1 H2 have "plus_sign a1 a2 = UNIV" by force
        then have "\<gamma>_sign (plus_sign a1 a2) = UNIV" using \<gamma>_sign_top by auto
        then show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by auto
        then show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" .
        then show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" .
      }
      {
        assume "i2 = 0"
        with 4(2) have H2: "Zero \<in> a2" by (simp add: Zero_\<gamma>_sign)
        from H1 H2 have "Pos \<in> plus_sign a1 a2" by force
        moreover assume "0 < i1 + i2"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
      {
        assume "0 < i2"
        with 4(2) have H2: "Pos \<in> a2" by (simp add: Pos_\<gamma>_sign)
        from H1 H2 have "Pos \<in> plus_sign a1 a2" by force
        moreover assume "0 < i1 + i2"
        ultimately show "i1 + i2 \<in> \<gamma>_sign (plus_sign a1 a2)" by fastforce
      }
    }
  qed
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

global_interpretation Abs_Int_mono
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
proof (standard, goal_cases)
  case (1 a1 b1 a2 b2) thus ?case
    by(induct b1 b2 rule: plus_sign.induct) auto
qed

definition m_sign :: "sign \<Rightarrow> nat" where
"m_sign x = 3 - card x"

global_interpretation Abs_Int_measure
where \<gamma> = \<gamma>_sign and num' = num_sign and plus' = plus_sign
and m = m_sign and h = "3"
proof (standard, goal_cases)
  case (1 x) thus ?case by(auto simp add: m_sign_def)
next
  case (2 x y)
  have "y \<subseteq> UNIV" by auto
  then show ?case unfolding m_sign_def
    by (metis "2" card_sign' diff_less_mono2 finite_sign' finite_subset less_le_trans psubset_card_mono)
qed

thm AI_Some_measure

end
