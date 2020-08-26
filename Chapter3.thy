theory Chapter3
imports "HOL-IMP.BExp"
        "HOL-IMP.ASM"
        (*"Short_Theory_AExp"*)
        (*"Short_Theory_ASM"*)
begin

text \<open>
\section*{Chapter 3}

\exercise
To show that @{const asimp_const} really folds all subexpressions of the form
@{term "Plus (N i) (N j)"}, define a function
\<close>

fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N i) = True" |
  "optimal (V x) = True" |
  "optimal (Plus (N i) (N j)) = False" |
  "optimal (Plus a\<^sub>1 a\<^sub>2) \<longleftrightarrow> optimal a\<^sub>1 \<and> optimal a\<^sub>2"

text \<open>
that checks that its argument does not contain a subexpression of the form
@{term "Plus (N i) (N j)"}. Then prove that the result of @{const asimp_const}
is optimal:
\<close>

lemma "optimal (asimp_const a)"
  apply (induction a)
    apply (auto split: aexp.split)
  done

text \<open>
This proof needs the same @{text "split:"} directive as the correctness proof of
@{const asimp_const}. This increases the chance of nontermination
of the simplifier. Therefore @{const optimal} should be defined purely by
pattern matching on the left-hand side,
without @{text case} expressions on the right-hand side.
\endexercise


\exercise
In this exercise we verify constant folding for @{typ aexp}
where we sum up all constants, even if they are not next to each other.
For example, @{term "Plus (N 1) (Plus (V x) (N 2))"} becomes
@{term "Plus (V x) (N 3)"}. This goes beyond @{const asimp}.
Below we follow a particular solution strategy but there are many others.

First, define a function @{text sumN} that returns the sum of all
constants in an expression and a function @{text zeroN} that replaces all
constants in an expression by zeroes (they will be optimized away later):
\<close>

fun sumN :: "aexp \<Rightarrow> int" where
  "sumN (N i) = i" |
  "sumN (V x) = 0" |
  "sumN (Plus a\<^sub>1 a\<^sub>2) = sumN a\<^sub>1 + sumN a\<^sub>2"

fun zeroN :: "aexp \<Rightarrow> aexp" where
  "zeroN (N i) = N 0" |
  "zeroN (V x) = V x" |
  "zeroN (Plus a\<^sub>1 a\<^sub>2) = Plus (zeroN a\<^sub>1) (zeroN a\<^sub>2)"

text \<open>
Next, define a function @{text sepN} that produces an arithmetic expression
that adds the results of @{const sumN} and @{const zeroN}. Prove that
@{text sepN} preserves the value of an expression.
\<close>

definition sepN :: "aexp \<Rightarrow> aexp" where
  "sepN a = Plus (zeroN a) (N (sumN a))"

lemma aval_sepN: "aval (sepN t) s = aval t s"
  apply (induction t)
    apply (auto simp add: sepN_def)
  done

text \<open>
Finally, define a function @{text full_asimp} that uses @{const asimp}
to eliminate the zeroes left over by @{const sepN}.
Prove that it preserves the value of an arithmetic expression.
\<close>

definition full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp t = asimp (sepN t)"

lemma aval_full_asimp: "aval (full_asimp t) s = aval t s"
  apply (simp add: full_asimp_def aval_sepN)
  done

text \<open>
\endexercise


\exercise\label{exe:subst}
Substitution is the process of replacing a variable
by an expression in an expression. Define a substitution function
\<close>

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst _ _ (N i) = N i" |
  "subst x a (V y) = (if x = y then a else V y)" |
  "subst x a (Plus e\<^sub>1 e\<^sub>2) = Plus (subst x a e\<^sub>1) (subst x a e\<^sub>2)"

text \<open>
such that @{term "subst x a e"} is the result of replacing
every occurrence of variable @{text x} by @{text a} in @{text e}.
For example:
@{lemma[display] "subst ''x'' (N 3) (Plus (V ''x'') (V ''y'')) = Plus (N 3) (V ''y'')" by simp}

Prove the so-called \concept{substitution lemma} that says that we can either
substitute first and evaluate afterwards or evaluate with an updated state:
\<close>

lemma subst_lemma: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
    apply auto
  done

text \<open>
As a consequence prove that we can substitute equal expressions by equal expressions
and obtain the same result under evaluation:
\<close>
lemma "aval a1 s = aval a2 s
  \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (auto simp add: subst_lemma)
  done

text \<open>
\endexercise

\exercise
Take a copy of theory @{text "AExp"} and modify it as follows.
Extend type @{typ aexp} with a binary constructor @{text Times} that
represents multiplication. Modify the definition of the functions @{const aval}
and @{const asimp} accordingly. You can remove @{const asimp_const}.
Function @{const asimp} should eliminate 0 and 1 from multiplications
as well as evaluate constant subterms. Update all proofs concerned.
\<close>

(* See Short_Theory.thy *)

text \<open>
\endexercise

\exercise
Define a datatype @{text aexp2} of extended arithmetic expressions that has,
in addition to the constructors of @{typ aexp}, a constructor for
modelling a C-like post-increment operation $x{++}$, where $x$ must be a
variable. Define an evaluation function @{text "aval2 :: aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state"}
that returns both the value of the expression and the new state.
The latter is required because post-increment changes the state.

Extend @{text aexp2} and @{text aval2} with a division operation. Model partiality of
division by changing the return type of @{text aval2} to
@{typ "(val \<times> state) option"}. In case of division by 0 let @{text aval2}
return @{const None}. Division on @{typ int} is the infix @{text div}.
 \<close>

datatype aexp2 = N2 int | V2  vname | Plus2 aexp2 aexp2 | PIncr2 vname | Divide2 aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
  "aval2 (N2 i) s = Some (i, s)" |
  "aval2 (V2 x) s = Some (s x, s)" |
  "aval2 (Plus2 a\<^sub>1 a\<^sub>2) s =
    (case aval2 a\<^sub>2 s of
      Some (v\<^sub>2, s\<^sub>2) \<Rightarrow>
        (case (aval2 a\<^sub>1 s, aval2 a\<^sub>1 s\<^sub>2) of
          (Some (v\<^sub>1, _), Some (_, s\<^sub>1)) \<Rightarrow> Some (v\<^sub>1 + v\<^sub>2, s\<^sub>1) |
          (_, _) \<Rightarrow> None) |
      _ \<Rightarrow> None)" |
  "aval2 (PIncr2 x) s = Some (s x, s (x := s x + 1))" |
  "aval2 (Divide2 a\<^sub>1 a\<^sub>2) s =
    (case aval2 a\<^sub>2 s of
      Some (v\<^sub>2, s\<^sub>2) \<Rightarrow>
        (if v\<^sub>2 = 0 then None else
          case (aval2 a\<^sub>1 s, aval2 a\<^sub>1 s\<^sub>2) of
            (Some (v\<^sub>1, _), Some (_, s\<^sub>1)) \<Rightarrow> Some (v\<^sub>1 div v\<^sub>2, s\<^sub>1) |
            (_, _) \<Rightarrow> None) |
      _ \<Rightarrow> None)"

text \<open>
\endexercise

\exercise
The following type adds a @{text LET} construct to arithmetic expressions:
 \<close>

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

text \<open> The @{const LET} constructor introduces a local variable:
the value of @{term "LET x e\<^sub>1 e\<^sub>2"} is the value of @{text e\<^sub>2}
in the state where @{text x} is bound to the value of @{text e\<^sub>1} in the original state.
Define a function @{text lval} @{text"::"} @{typ "lexp \<Rightarrow> state \<Rightarrow> int"}
that evaluates @{typ lexp} expressions. Remember @{term"s(x := i)"}.

Define a conversion @{text inline} @{text"::"} @{typ "lexp \<Rightarrow> aexp"}.
The expression \mbox{@{term "LET x e\<^sub>1 e\<^sub>2"}} is inlined by substituting
the converted form of @{text e\<^sub>1} for @{text x} in the converted form of @{text e\<^sub>2}.
See Exercise~\ref{exe:subst} for more on substitution.
Prove that @{text inline} is correct w.r.t.\ evaluation.
 \<close>

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval (Nl i) _ = i" |
  "lval (Vl x) s = s x" |
  "lval (Plusl e\<^sub>1 e\<^sub>2) s = lval e\<^sub>1 s + lval e\<^sub>2 s" |
  "lval (LET x e\<^sub>1 e\<^sub>2) s = lval e\<^sub>2 (s (x := lval e\<^sub>1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl i) = N i" |
  "inline (Vl x) = V x" |
  "inline (Plusl e\<^sub>1 e\<^sub>2) = Plus (inline e\<^sub>1) (inline e\<^sub>2)" |
  "inline (LET x e\<^sub>1 e\<^sub>2) = subst x (inline e\<^sub>1) (inline e\<^sub>2)"

lemma "aval (inline e) s = lval e s"
  apply (induction e arbitrary: s)
     apply (auto simp add: subst_lemma)
  done

text \<open>
\endexercise


\exercise
Show that equality and less-or-equal tests on @{text aexp} are definable
 \<close>

definition Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Le a\<^sub>1 a\<^sub>2 = Not (Less a\<^sub>2 a\<^sub>1)"

definition Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "Eq a\<^sub>1 a\<^sub>2 = And (Le a\<^sub>1 a\<^sub>2) (Le a\<^sub>2 a\<^sub>1)"

text \<open>
and prove that they do what they are supposed to:
 \<close>

lemma bval_Le: "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
  apply (induction a1 arbitrary: a2)
    apply (auto simp add: Le_def)
  done

lemma bval_Eq: "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
  apply (induction a1 arbitrary: a2)
    apply (auto simp add: Eq_def Le_def)
  done

text \<open>
\endexercise

\exercise
Consider an alternative type of boolean expressions featuring a conditional:  \<close>

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

text  \<open>  First define an evaluation function analogously to @{const bval}:  \<close>

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bc2 b) _ = b" |
  "ifval (If e\<^sub>1 e\<^sub>2 e\<^sub>3) s = (if ifval e\<^sub>1 s then ifval e\<^sub>2 s else ifval e\<^sub>3 s)" |
  "ifval (Less2 a\<^sub>1 a\<^sub>2) s \<longleftrightarrow> aval a\<^sub>1 s < aval a\<^sub>2 s"
(* your definition/proof here *)

text \<open> Then define two translation functions  \<close>

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bc2 v" |
  "b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
  "b2ifexp (And b\<^sub>1 b\<^sub>2) = If (b2ifexp b\<^sub>1) (b2ifexp b\<^sub>2) (Bc2 False)" |
  "b2ifexp (Less a\<^sub>1 a\<^sub>2) = Less2 a\<^sub>1 a\<^sub>2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bc2 v) = Bc v" |
  "if2bexp (If e\<^sub>1 e\<^sub>2 e\<^sub>3) =
  Not (And (Not (And (if2bexp e\<^sub>1) (if2bexp e\<^sub>2))) (Not (And (Not (if2bexp e\<^sub>1)) (if2bexp e\<^sub>3))))" |
  "if2bexp (Less2 a\<^sub>1 a\<^sub>2) = Less a\<^sub>1 a\<^sub>2"

text \<open> and prove their correctness:  \<close>

lemma "bval (if2bexp exp) s = ifval exp s"
  apply (induction exp)
    apply auto
  done

lemma "ifval (b2ifexp exp) s = bval exp s"
  apply (induction exp)
     apply auto
  done

text \<open>
\endexercise

\exercise
We define a new type of purely boolean expressions without any arithmetic
 \<close>

datatype pbexp =
  VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

text \<open>
where variables range over values of type @{typ bool},
as can be seen from the evaluation function:
 \<close>

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x"  |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

text  \<open> Define a function that checks whether a boolean exression is in NNF
(negation normal form), i.e., if @{const NOT} is only applied directly
to @{const VAR}s:  \<close>

fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR _) = True" |
  "is_nnf (NOT (VAR _)) = True" |
  "is_nnf (NOT _) = False" |
  "is_nnf (AND b1 b2) \<longleftrightarrow> is_nnf b1 \<and> is_nnf b2" |
  "is_nnf (OR b1 b2) \<longleftrightarrow> is_nnf b1 \<and> is_nnf b2"

text \<open>
Now define a function that converts a @{text bexp} into NNF by pushing
@{const NOT} inwards as much as possible:
 \<close>

fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR x) = VAR x" |
  "nnf (NOT (VAR x)) = NOT (VAR x)" |
  "nnf (NOT (NOT b)) = nnf b" |
  "nnf (NOT (AND b1 b2)) = OR (nnf (NOT b1)) (nnf (NOT b2))" |
  "nnf (NOT (OR b1 b2)) = AND (nnf (NOT b1)) (nnf (NOT b2))" |
  "nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
  "nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"

text \<open>
Prove that @{const nnf} does what it is supposed to do:
 \<close>

lemma pbval_nnf: "pbval (nnf b) s = pbval b s"
  apply (induction b rule: nnf.induct)
        apply auto
  done

lemma is_nnf_nnf: "is_nnf (nnf b)"
  apply (induction b rule: nnf.induct)
        apply auto
  done

text \<open>
An expression is in DNF (disjunctive normal form) if it is in NNF
and if no @{const OR} occurs below an @{const AND}. Define a corresponding
test:
 \<close>

fun is_dnf :: "pbexp \<Rightarrow> bool" where
  "is_dnf (VAR _) = True" |
  "is_dnf (NOT (VAR _)) = True" |
  "is_dnf (NOT _) = False" |
  "is_dnf (OR e\<^sub>1 e\<^sub>2) \<longleftrightarrow> is_dnf e\<^sub>1 \<and> is_dnf e\<^sub>2" |
  "is_dnf (AND (OR _ _) _) = False" |
  "is_dnf (AND _ (OR _ _)) = False" |
  "is_dnf (AND e\<^sub>1 e\<^sub>2) \<longleftrightarrow> is_dnf e\<^sub>1 \<and> is_dnf e\<^sub>2"

text  \<open>
An NNF can be converted into a DNF in a bottom-up manner.
The critical case is the conversion of @{term (sub) "AND b1 b2"}.
Having converted @{text b\<^sub>1} and @{text b\<^sub>2}, apply distributivity of @{const AND}
over @{const OR}. If we write @{const OR} as a multi-argument function,
we can express the distributivity step as follows:
@{text "dist_AND (OR a\<^sub>1 ... a\<^sub>n) (OR b\<^sub>1 ... b\<^sub>m)"}
= @{text "OR (AND a\<^sub>1 b\<^sub>1) (AND a\<^sub>1 b\<^sub>2) ... (AND a\<^sub>n b\<^sub>m)"}. Define
 \<close>

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
  "dist_AND (OR e\<^sub>1 e\<^sub>2) e\<^sub>3 = OR (dist_AND e\<^sub>1 e\<^sub>3) (dist_AND e\<^sub>2 e\<^sub>3)" |
  "dist_AND e\<^sub>1 (OR e\<^sub>2 e\<^sub>3) = OR (dist_AND e\<^sub>1 e\<^sub>2) (dist_AND e\<^sub>1 e\<^sub>3)" |
  "dist_AND e\<^sub>1 e\<^sub>2 = AND e\<^sub>1 e\<^sub>2"

text  \<open> and prove that it behaves as follows:  \<close>

lemma pbval_dist: "pbval (dist_AND b1 b2) s = pbval (AND b1 b2) s"
  apply (induction b1 b2 rule: dist_AND.induct)
              apply auto
  done

lemma is_dnf_dist: "is_dnf b1 \<Longrightarrow> is_dnf b2 \<Longrightarrow> is_dnf (dist_AND b1 b2)"
  apply (induction b1 b2 rule: dist_AND.induct)
              apply auto
  done

text  \<open> Use @{const dist_AND} to write a function that converts an NNF
  to a DNF in the above bottom-up manner.
 \<close>

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
  "dnf_of_nnf (VAR x) = VAR x" |
  "dnf_of_nnf (NOT v) = NOT v" |
  "dnf_of_nnf (OR e\<^sub>1 e\<^sub>2) = OR (dnf_of_nnf e\<^sub>1) (dnf_of_nnf e\<^sub>2)" |
  "dnf_of_nnf (AND e\<^sub>1 e\<^sub>2) = dist_AND (dnf_of_nnf e\<^sub>1) (dnf_of_nnf e\<^sub>2)"

text  \<open> Prove the correctness of your function:  \<close>

lemma "pbval (dnf_of_nnf b) s = pbval b s"
  apply (induction b)
     apply (auto simp add: pbval_dist)
  done

lemma nnf_dnf_NOT: "is_nnf (NOT b) \<Longrightarrow> is_dnf (NOT b)"
  apply (cases b)
     apply auto
  done

lemma "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
  apply (induction b)
     apply (auto simp add: is_dnf_dist nnf_dnf_NOT)
  done

text \<open>
\endexercise


\exercise\label{exe:stack-underflow}
A \concept{stack underflow} occurs when executing an @{text ADD}
instruction on a stack of size less than 2. In our semantics
a term @{term "exec1 ADD s stk"} where @{prop "length stk < 2"}
is simply some unspecified value, not an error or exception --- HOL does not have those concepts.
Modify theory @{text "ASM"}
such that stack underflow is modelled by @{const None}
and normal execution by @{text Some}, i.e., the execution functions
have return type @{typ "stack option"}. Modify all theorems and proofs
accordingly.
Hint: you may find @{text"split: option.split"} useful in your proofs.
 \<close>

(* See Short_Theory_ASM.thy *)

text \<open>
\endexercise

\exercise\label{exe:register-machine}
This exercise is about a register machine
and compiler for @{typ aexp}. The machine instructions are
 \<close>
type_synonym reg = nat
datatype instr = LDI val reg | LD vname reg | ADD reg reg

text  \<open>
where type @{text reg} is a synonym for @{typ nat}.
Instruction @{term "LDI i r"} loads @{text i} into register @{text r},
@{term "LD x r"} loads the value of @{text x} into register @{text r},
and @{term[names_short] "ADD r\<^sub>1 r\<^sub>2"} adds register @{text r\<^sub>2} to register @{text r\<^sub>1}.

Define the execution of an instruction given a state and a register state;
the result is the new register state:  \<close>

type_synonym rstate = "reg \<Rightarrow> val"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec1 (LDI i r) _ rs = rs (r := i)" |
  "exec1 (LD x r) s rs = rs (r := s x)" |
  "exec1 (ADD r\<^sub>1 r\<^sub>2) s rs = rs (r\<^sub>1 := rs r\<^sub>1 + rs r\<^sub>2)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec [] _ rs = rs" |
  "exec (i # is) s rs = exec is s (exec1 i s rs)"

text \<open>
Define the execution @{const[source] exec} of a list of instructions as for the stack machine.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into @{text r}. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "< r"} should be left alone.
Define the compiler and prove it correct:
 \<close>

lemma exec_app: "exec (is\<^sub>1 @ is\<^sub>2) s rs r = exec is\<^sub>2 s (exec is\<^sub>1 s rs) r"
  apply (induction is\<^sub>1 arbitrary: rs r)
   apply auto
  done

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "comp (N i) r = [LDI i r]" |
  "comp (V x) r = [LD x r]" |
  "comp (Plus a\<^sub>1 a\<^sub>2) r = comp a\<^sub>1 r @ comp a\<^sub>2 (Suc r) @ [ADD r (Suc r)]"

lemma exec_comp_inacc: "r < r\<^sub>1 \<Longrightarrow> exec (comp a r\<^sub>1) s rs r = rs r"
  apply (induction a arbitrary: r\<^sub>1 rs)
    apply (auto simp add: exec_app)
  done

theorem "exec (comp a r) s rs r = aval a s"
  apply (induction a arbitrary: r rs)
    apply (auto simp add: exec_app exec_comp_inacc)
  done

text \<open>
\endexercise

\exercise\label{exe:accumulator}
This exercise is a variation of the previous one
with a different instruction set:
 \<close>

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

text \<open>
All instructions refer implicitly to register 0 as a source or target:
@{const LDI0} and @{const LD0} load a value into register 0, @{term "MV0 r"}
copies the value in register 0 into register @{text r}, and @{term "ADD0 r"}
adds the value in register @{text r} to the value in register 0;
@{term "MV0 0"} and @{term "ADD0 0"} are legal. Define the execution functions
 \<close>

fun exec01 :: "instr0 \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec01 (LDI0 i) _ rs = rs (0 := i)" |
  "exec01 (LD0 x) s rs = rs (0 := s x)" |
  "exec01 (MV0 r) _ rs = rs (r := rs 0)" |
  "exec01 (ADD0 r) _ rs = rs (0 := rs 0 + rs r)"

fun exec0 :: "instr0 list \<Rightarrow> state \<Rightarrow> rstate \<Rightarrow> rstate" where
  "exec0 [] _ rs = rs" |
  "exec0 (i # is) s rs = exec0 is s (exec01 i s rs)"

lemma exec0_app: "exec0 (is\<^sub>1 @ is\<^sub>2) s rs r = exec0 is\<^sub>2 s (exec0 is\<^sub>1 s rs) r"
  apply (induction is\<^sub>1 arbitrary: rs r)
   apply auto
  done

text \<open>
and @{const exec0} for instruction lists.

The compiler takes an arithmetic expression @{text a} and a register @{text r}
and produces a list of instructions whose execution places the value of @{text a}
into register 0. The registers @{text "> r"} should be used in a stack-like fashion
for intermediate results, the ones @{text "\<le> r"} should be left alone
(with the exception of 0). Define the compiler and prove it correct:
 \<close>

fun comp0 :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
  "comp0 (N i) _ = [LDI0 i]" |
  "comp0 (V x) _ = [LD0 x]" |
  "comp0 (Plus a\<^sub>1 a\<^sub>2) r = comp0 a\<^sub>1 (Suc r) @ MV0 (Suc r) # comp0 a\<^sub>2 (Suc (Suc r)) @ [ADD0 (Suc r)]"

lemma exec0_comp0_inacc: "0 < r \<Longrightarrow> r < r\<^sub>1 \<Longrightarrow> exec0 (comp0 a r\<^sub>1) s rs r = rs r"
  apply (induction a arbitrary: r r\<^sub>1 rs)
    apply (auto simp add: exec0_app)
  done

lemma exec0_comp0: "exec0 (comp0 a r) s rs 0 = aval a s"
  apply (induction a arbitrary: r rs)
    apply (auto simp add: exec0_app exec0_comp0_inacc)
  done

text \<open>
\endexercise
 \<close>

end

