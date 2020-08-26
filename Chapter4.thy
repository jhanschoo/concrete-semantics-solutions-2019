theory Chapter4
imports "HOL-IMP.ASM"
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

text \<open>
\section*{Chapter 4}

\exercise
Start from the data type of binary trees defined earlier:
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text \<open>
An @{typ "int tree"} is ordered if for every @{term "Node l i r"} in the tree,
@{text l} and @{text r} are ordered
and all values in @{text l} are @{text "< i"}
and all values in @{text r} are @{text "> i"}.
Define a function that returns the elements in a tree and one
the tests if a tree is ordered:
\<close>

fun set :: "'a tree \<Rightarrow> 'a set"  where
  "set Tip = {}" |
  "set (Node l a r) = \<Union> {set l, {a}, set r}"

fun ord :: "int tree \<Rightarrow> bool"  where
  "ord Tip = True" |
  "ord (Node l a r) \<longleftrightarrow> ord l \<and> ord r \<and> (\<forall> x \<in> set l. x < a) \<and> (\<forall> x \<in> set r. a < x)"

text \<open> Hint: use quantifiers.

Define a function @{text ins} that inserts an element into an ordered @{typ "int tree"}
while maintaining the order of the tree. If the element is already in the tree, the
same tree should be returned.
\<close>

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree"  where
  "ins x Tip = Node Tip x Tip" |
  "ins x (Node l a r) =
    (if x < a
      then Node (ins x l) a r
      else if a < x
        then Node l a (ins x r)
        else Node l a r)"

text \<open> Prove correctness of @{const ins}: \<close>

lemma set_ins: "set (ins x t) = {x} \<union> set t"
  apply (induction t)
   apply auto
  done

theorem ord_ins: "ord t \<Longrightarrow> ord (ins i t)"
  apply (induction t)
   apply (auto simp add: set_ins)
  done

text \<open>
\endexercise

\exercise
Formalize the following definition of palindromes
\begin{itemize}
\item The empty list and a singleton list are palindromes.
\item If @{text xs} is a palindrome, so is @{term "a # xs @ [a]"}.
\end{itemize}
as an inductive predicate
\<close>

inductive palindrome :: "'a list \<Rightarrow> bool" where
  palindrome_Nil: "palindrome []" |
  palindrome_singleton: "palindrome [a]" |
  palindrome_circumfix: "palindrome as \<Longrightarrow> palindrome (a # as @ [a])"

text  \<open> and prove \<close>

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply (induction rule: palindrome.induct)
    apply auto
  done

text \<open>
\endexercise

\exercise
We could also have defined @{const star} as follows:
\<close>

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

text \<open>
The single @{text r} step is performed after rather than before the @{text star'}
steps. Prove
\<close>

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
   apply assumption
  by (rule step) (* alternatively, apply (metis step) done *)

lemma "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  by (auto simp add: refl step intro: star_trans)

(* limitation: no way to change order of premises, induction works
  only on first premise *)
lemma star'_trans: "star' r y z \<Longrightarrow> star' r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
   apply assumption
  by (rule step')

lemma "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
   apply (auto intro: refl' step')
  by (blast intro: refl' step' star'_trans)

text \<open>
You may need lemmas. Note that rule induction fails
if the assumption about the inductive predicate
is not the first assumption.
\endexercise

\exercise\label{exe:iter}
Analogous to @{const star}, give an inductive definition of the @{text n}-fold iteration
of a relation @{text r}: @{term "iter r n x y"} should hold if there are @{text x\<^sub>0}, \dots, @{text x\<^sub>n}
such that @{prop"x = x\<^sub>0"}, @{prop"x\<^sub>n = y"} and @{text"r x\<^bsub>i\<^esub> x\<^bsub>i+1\<^esub>"} for
all @{prop"i < n"}:
\<close>

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0: "iter r 0 x x" |
iterS: "\<lbrakk>r x y; iter r n y z \<rbrakk> \<Longrightarrow> iter r (Suc n) x z"

text \<open>
Correct and prove the following claim:
\<close>

lemma "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply (induction rule: star.induct)
  apply (blast intro: iter0)
  by (blast intro: iterS)

text \<open>
\endexercise

\exercise\label{exe:cfg}
A context-free grammar can be seen as an inductive definition where each
nonterminal $A$ is an inductively defined predicate on lists of terminal
symbols: $A(w)$ mans that $w$ is in the language generated by $A$.
For example, the production $S \to aSb$ can be viewed as the implication
@{prop"S w \<Longrightarrow> S (a # w @ [b])"} where @{text a} and @{text b} are terminal symbols,
i.e., elements of some alphabet. The alphabet can be defined as a datatype:
\<close>

datatype alpha = alphaa | alphab

text \<open>
If you think of @{const alphaa} and @{const alphab} as ``@{text "("}'' and  ``@{text ")"}'',
the following two grammars both generate strings of balanced parentheses
(where $\varepsilon$ is the empty word):
\[
\begin{array}{r@ {\quad}c@ {\quad}l}
S &\to& \varepsilon \quad\mid\quad aSb \quad\mid\quad SS \\
T &\to& \varepsilon \quad\mid\quad TaTb
\end{array}
\]
Define them as inductive predicates and prove their equivalence:
\<close>

inductive S :: "alpha list \<Rightarrow> bool" where
S_\<epsilon>: "S []" |
S_aSb: "S w \<Longrightarrow> S (alphaa # w @ [alphab])" |
S_SS: "\<lbrakk> S v; S w \<rbrakk> \<Longrightarrow> S (v @ w)"

inductive T :: "alpha list \<Rightarrow> bool" where
T_\<epsilon>: "T []" |
T_TaTb: "\<lbrakk> T v; T w \<rbrakk> \<Longrightarrow> T (v @ [alphaa] @ w @ [alphab])"

lemma TS: "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  by (auto intro: S_\<epsilon> S_SS S_aSb)

lemma ST_aux_1: "[] @ [alphaa] @ w @ [alphab] = alphaa # w @ [alphab]"
  by simp

lemma ST_aux_2: "T v \<Longrightarrow> T w \<Longrightarrow> T (w @ v)"
  apply (induction rule: T.induct)
  apply simp
  by (subst append_assoc [THEN sym], blast intro: T_TaTb)

lemma ST: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
    apply (rule T_\<epsilon>)
   apply (subst ST_aux_1 [THEN sym], rule T_TaTb, rule T_\<epsilon>, assumption)
  by (rule ST_aux_2)

corollary SeqT: "S w \<longleftrightarrow> T w"
  by (auto intro: TS ST)

text \<open>
\endexercise
\<close>

text \<open>
\exercise
In Chapter 3 we defined a recursive evaluation function
@{text "aval ::"} @{typ "aexp \<Rightarrow> state \<Rightarrow> val"}.
Define an inductive evaluation predicate and prove that it agrees with
the recursive function:
\<close>

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
aval_N: "aval_rel (N i) s i" |
aval_V: "aval_rel (V x) s (s x)" |
aval_Plus: "\<lbrakk> aval_rel e\<^sub>1 s v\<^sub>1; aval_rel e\<^sub>2 s v\<^sub>2 \<rbrakk> \<Longrightarrow> aval_rel (Plus e\<^sub>1 e\<^sub>2) s (v\<^sub>1 + v\<^sub>2)"

lemma aval_rel_aval: "aval_rel e s v \<Longrightarrow> aval e s = v"
  apply (induction rule: aval_rel.induct)
  by auto

lemma aval_aval_rel: "aval e s = v \<Longrightarrow> aval_rel e s v"
  apply (induction e arbitrary: v)
  by (auto simp add: aval_N aval_V aval_Plus)

corollary "aval_rel e s v \<longleftrightarrow> aval e s = v"
  by (blast intro: aval_rel_aval aval_aval_rel)

text \<open>
\endexercise

\exercise
Consider the stack machine from Chapter~3
and recall the concept of \concept{stack underflow}
from Exercise~\ref{exe:stack-underflow}.
Define an inductive predicate
\<close>

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
ok_Nil: "ok 0 [] 0" |
ok_Pad: "ok n is n' \<Longrightarrow> ok (Suc n) is (Suc n')" |
ok_LOADI: "ok (Suc n) is n' \<Longrightarrow> ok n (LOADI i # is) n'" |
ok_LOAD: "ok (Suc n) is n' \<Longrightarrow> ok n (LOAD x # is) n'" |
ok_ADD: "ok (Suc n) is n' \<Longrightarrow> ok (Suc (Suc n)) (ADD # is) n'"


text \<open>
such that @{text "ok n is n'"} means that with any initial stack of length
@{text n} the instructions @{text "is"} can be executed
without stack underflow and that the final stack has length @{text n'}.

Using the introduction rules for @{const ok},
prove the following special cases: \<close>

lemma "ok 0 [LOAD x] (Suc 0)"
  by (auto intro: ok_Nil ok_Pad ok_LOAD)

lemma "ok 0 [LOAD x, LOADI v, ADD] (Suc 0)"
  apply (rule ok_LOAD)
  apply (rule ok_LOADI)
  apply (rule ok_ADD)
  apply (rule ok_Pad)
  by (rule ok_Nil)

lemma "ok (Suc (Suc 0)) [LOAD x, ADD, ADD, LOAD y] (Suc (Suc 0))"
  apply (rule ok_LOAD)
  apply (rule ok_ADD)
  apply (rule ok_ADD)
  apply (rule ok_LOAD)
  apply (rule ok_Pad)
  apply (rule ok_Pad)
  by (rule ok_Nil)

text  \<open> Prove that @{text ok} correctly computes the final stack size: \<close>

(* near impossible (probably impossible) without _tac and without using Isar *)

(* because of ok_Pad, inversion rules need to induct over that case *)
lemma ok_Nil_inv_aux: "\<lbrakk>ok n j n'; j = []\<rbrakk> \<Longrightarrow> n = n'"
  apply (induction rule: ok.induct)
  by auto

lemma ok_Nil_inv: "ok n [] n' \<Longrightarrow> n = n'"
  by (simp add: ok_Nil_inv_aux)

lemma ok_LOADI_inv_aux: "\<lbrakk>ok n j n'; j = LOADI i # iss\<rbrakk> \<Longrightarrow> ok (Suc n) iss n'"
  apply (induction rule: ok.induct)
  by (auto simp add: ok.ok_Pad)

lemma ok_LOADI_inv: "ok n (LOADI i # iss) n' \<Longrightarrow> ok (Suc n) iss n'"
  by (simp add: ok_LOADI_inv_aux)

lemma ok_LOAD_inv_aux: "\<lbrakk>ok n j n'; j = LOAD x # iss\<rbrakk> \<Longrightarrow> ok (Suc n) iss n'"
  apply (induction rule: ok.induct)
  by (auto simp add: ok.ok_Pad)

lemma ok_LOAD_inv: "ok n (LOAD x # iss) n' \<Longrightarrow> ok (Suc n) iss n'"
  by (simp add: ok_LOAD_inv_aux)

lemma ok_ADD_inv_aux: "\<lbrakk>ok n j n'; j = ADD # iss\<rbrakk> \<Longrightarrow> \<exists> k. ok (Suc k) iss n' \<and> n = (Suc (Suc k))"
  apply (induction rule: ok.induct)
  by (auto simp add: ok.ok_Pad)

lemma ok_ADD_inv: "ok n (ADD # iss) n' \<Longrightarrow> \<exists> k. ok (Suc k) iss n' \<and> n = (Suc (Suc k))"
  by (auto simp add: ok_ADD_inv_aux)

lemma "\<lbrakk>ok n inss n'; length stk = n\<rbrakk> \<Longrightarrow> length (exec inss s stk) = n'"
proof (induct inss arbitrary: n n' stk)
  case Nil
  thus ?case by (simp add: ok_Nil_inv)
next
  case (Cons a inss)
  note H = this
  thus ?case
  proof (cases a)
    case (LOADI i)
    thus ?thesis using Cons.hyps H(2) H(3) ok_LOADI_inv by fastforce
  next
    case (LOAD x)
    note Hx = this
    thus ?thesis using Cons.hyps H(2) H(3) ok_LOAD_inv by fastforce
  next
    case ADD
    note Ha = this
    from H(2) obtain k where H2': "ok (Suc k) inss n'" and H2eq: "n = (Suc (Suc k))" using Ha ok_ADD_inv by blast
    from H(3) H2eq have H3': "length stk = Suc (Suc k)" by simp
    then obtain x y stkr where Hstk: "stk = x # y # stkr" by (metis Suc_length_conv)
    hence H3'': "length ((y + x) # stkr) = Suc k" using H3' by simp
    from Ha Hstk have "length (exec (a # inss) s stk) = length (exec (ADD # inss) s (x # y # stkr))" by simp
    also have "\<dots> = length (exec inss s ((y + x) # stkr))" by simp
    also
    from H(1) H2' H3'' have "\<dots> = n'" by simp
    finally show ?thesis .
  qed
qed

text  \<open>
Lemma @{thm [source] length_Suc_conv} may come in handy.

Prove that instruction sequences generated by @{text comp}
cannot cause stack underflow: \ @{text "ok n (comp a) ?"} \ for
some suitable value of @{text "?"}.
\endexercise
\<close>


end

