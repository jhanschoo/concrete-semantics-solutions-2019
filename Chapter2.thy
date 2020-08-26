theory Chapter2
imports Main
begin

text \<open>
\section*{Chapter 2}

\exercise
Use the \textbf{value} command to evaluate the following expressions:
\<close>

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
value "[a,b] @ [c,d]"

text \<open>
\endexercise


\exercise
Recall the definition of our own addition function on @{typ nat}:
\<close>

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

text \<open>
Prove that @{const add} is associative and commutative.
You will need additional lemmas.
\<close>

lemma add_assoc: "add (add m n) p = add m (add n p)"
  apply (induction m)
   apply auto
  done


lemma add_nil2 [simp]: "add m 0 = m"
  apply (induction m)
   apply auto
  done

lemma add_Suc2 [simp]: "add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply auto
  done

lemma add_comm: "add m n = add n m"
  apply (induction m)
   apply auto
  done

text \<open> Define a recursive function \<close>

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"

text \<open> and prove that \<close>

lemma double_add: "double m = add m m"
  apply (induction m)
   apply auto
  done

text \<open>
\endexercise


\exercise
Define a function that counts the number of occurrences of
an element in a list:
\<close>

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"

text \<open>
Test your definition of @{term count} on some examples.
Prove the following inequality:
\<close>

theorem "count xs x \<le> length xs"
  apply (induction xs)
   apply auto
  done

text \<open>
\endexercise


\exercise
Define a function @{text snoc} that appends an element to the end of a list.
Do not use the existing append operator @{text "@"} for lists.
\<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]" |
  "snoc (x # xs) a = x # snoc xs a"

text \<open>
Convince yourself on some test cases that your definition
of @{term snoc} behaves as expected.
With the help of @{text snoc} define a recursive function @{text reverse}
that reverses a list. Do not use the predefined function @{const rev}.
\<close>

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"

text \<open>
Prove the following theorem. You will need an additional lemma.
\<close>
lemma reverse_snoc [simp]: "reverse (snoc xs x) = x # reverse xs"
  apply (induction xs)
   apply auto
  done

theorem "reverse (reverse xs) = xs"
  apply (induction xs)
   apply auto
  done

text \<open>
\endexercise


\exercise
The aim of this exercise is to prove the summation formula
\[ \sum_{i=0}^{n}i = \frac{n(n+1)}{2} \]
Define a recursive function @{text "sum_upto n = 0 + ... + n"}:
\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n) = (Suc n) + (sum_upto n)"

text \<open>
Now prove the summation formula by induction on @{text "n"}.
First, write a clear but informal proof by hand following the examples
in the main text. Then prove the same property in Isabelle:
\<close>

lemma "sum_upto n = n * (n+1) div 2"
  apply (induction n)
   apply auto
  done

text \<open>
\endexercise


\exercise
Starting from the type @{text "'a tree"} defined in the text, define
a function that collects all values in a tree in a list, in any order,
without removing duplicates.
\<close>

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l x r) = x # contents l @ contents r"

text \<open>
Then define a function that sums up all values in a tree of natural numbers
\<close>

fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l n r) = n + sum_tree l + sum_tree r"

text \<open> and prove \<close>

lemma "sum_tree t = sum_list(contents t)"
  apply (induction t)
   apply auto
  done

text \<open>
\endexercise

\exercise
Define a new type @{text "'a tree2"} of binary trees where values are also
stored in the leaves of the tree.  Also reformulate the
@{text mirror} function accordingly. Define two functions \<close>

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

primrec mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Tip a) = (Tip a)" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip a) = [a]" |
  "pre_order (Node l a r) = a # pre_order l @ pre_order r"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip a) = [a]" |
  "post_order (Node l a r) = post_order l @ post_order r @ [a]"

text \<open>
that traverse a tree and collect all stored values in the respective order in
a list. Prove \<close>

lemma "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
   apply auto
  done

text \<open>
\endexercise

\exercise
Define a recursive function
\<close>

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []" |
  "intersperse _ [x] = [x]" |
  "intersperse a (x # xs) = x # a # intersperse a xs"

text \<open>
such that @{text "intersperse a [x\<^sub>1, ..., x\<^sub>n] = [x\<^sub>1, a, x\<^sub>2, a, ..., a, x\<^sub>n]"}.
Prove
\<close>

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
    apply auto
  done

text \<open>
\endexercise


\exercise
Write a tail-recursive variant of the @{text add} function on @{typ nat}:
\<close>

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd m 0 = m" |
  "itadd m (Suc n) = itadd (Suc m) n"

text \<open>
Tail-recursive means that in the recursive case, @{const itadd} needs to call
itself directly: \mbox{@{term"itadd (Suc m) n"}} @{text"= itadd \<dots>"}.
Prove
\<close>

lemma "itadd m (Suc n) = Suc (add m n)"
  apply (induction n arbitrary: m)
   apply auto
  done

lemma "itadd m n = add m n"
  apply (induction n arbitrary: m)
   apply auto
  done

text \<open>
\endexercise


\exercise\label{exe:tree0}
Define a datatype @{text tree0} of binary tree skeletons which do not store
any information, neither in the inner nodes nor in the leaves.
Define a function that counts the number of all nodes (inner nodes and leaves)
in such a tree:
\<close>

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + nodes l + nodes r"

text \<open>
Consider the following recursive function:
\<close>

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

text \<open>
Experiment how @{text explode} influences the size of a binary tree
and find an equation expressing the size of a tree after exploding it
(\noquotes{@{term [source] "nodes (explode n t)"}}) as a function
of @{term "nodes t"} and @{text n}. Prove your equation.
You may use the usual arithmetic operations including the exponentiation
operator ``@{text"^"}''. For example, \noquotes{@{prop [source] "2 ^ 2 = 4"}}.

Hint: simplifying with the list of theorems @{thm[source] algebra_simps}
takes care of common algebraic properties of the arithmetic operators.
\endexercise
\<close>

lemma "nodes (explode n t) = (2 ^ n - 1) + (2 ^ n) * nodes t"
  apply (induction n arbitrary: t)
   apply (simp_all add: algebra_simps)
  done

text \<open>

\exercise
Define arithmetic expressions in one variable over integers (type @{typ int})
as a data type:
\<close>

datatype exp = Var | Const int | Add exp exp | Mult exp exp

text \<open>
Define a function @{text eval} that evaluates an expression at some value:
\<close>

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var x = x" |
  "eval (Const c) _ = c" |
  "eval (Add a b) x = eval a x + eval b x" |
  "eval (Mult a b) x = eval a x * eval b x"

text \<open>
For example, @{prop "eval (Add (Mult (Const 2) Var) (Const 3)) i = 2*i+3"}.

A polynomial can be represented as a list of coefficients, starting with
the constant. For example, @{term "[4, 2, -1, 3::int]"} represents the
polynomial $4 + 2x - x^2 + 3x^3$.
Define a function @{text evalp} that evaluates a polynomial at a given value:
\<close>

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] x = 0" |
  "evalp (a # as) x = a + x * evalp as x"

text \<open>
Define a function @{text coeffs} that transforms an expression into a polynomial.
This will require auxiliary functions.
\<close>

fun add_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "add_list [] ys = ys" |
  "add_list xs [] = xs" |
  "add_list (x # xs) (y # ys) = (x + y) # add_list xs ys"

lemma [simp]: "evalp (add_list a b) x = evalp a x + evalp b x"
  apply (induction a b rule: add_list.induct)
    apply (auto simp add: algebra_simps)
  done

definition mul_c_list :: "int list \<Rightarrow> int \<Rightarrow> int list" where
  "mul_c_list a c = map ((*) c) a"

lemma [simp]: "evalp (mul_c_list a c) x = c * evalp a x"
  apply (induction a)
   apply (auto simp add: mul_c_list_def algebra_simps)
  done

primrec mul_list :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mul_list [] ys = []" |
  "mul_list (x # xs) ys = add_list (mul_c_list ys x) (0 # mul_list xs ys)"

lemma [simp]: "evalp (mul_list a b) x = evalp a x * evalp b x"
  apply (induction a arbitrary: b)
   apply (auto simp add: algebra_simps)
  done

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const c) = [c]" |
  "coeffs (Add a b) = add_list (coeffs a) (coeffs b)" |
  "coeffs (Mult a b) = mul_list (coeffs a) (coeffs b)"

text \<open>
Prove that @{text coeffs} preserves the value of the expression:
\<close>

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
  apply (induction e)
     apply auto
  done

text \<open>
Hint: consider the hint in Exercise~\ref{exe:tree0}.
\endexercise
\<close>

end

