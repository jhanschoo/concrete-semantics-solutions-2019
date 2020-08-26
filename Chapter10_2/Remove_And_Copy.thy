theory Remove_And_Copy
  imports "HOL-IMP.Sem_Equiv" "HOL-IMP.Vars"
begin

notation Map.empty ("empty")

text \<open>
\exercise\label{exs:remove}
This exercise builds infrastructure for \autoref{exs:acopy}, where we
will have to manipulate partial maps from variable names to variable names.
\<close>
type_synonym tab = "vname \<Rightarrow> vname option"

text \<open>
  In addition to the function @{text merge} from theory @{text Fold},
  implement two functions @{text remove} and @{text remove_all} that
  remove one variable name from the range of a map, and a set of variable
  names from the domain and range of a map.
\<close>

definition merge :: "tab \<Rightarrow> tab \<Rightarrow> tab" where
  "merge t1 t2 = (\<lambda>m. if t1 m = t2 m then t1 m else None)"

definition remove :: "vname \<Rightarrow> tab \<Rightarrow> tab" where
  "remove v t = (\<lambda>m. if t m = Some v then None else t m)"

definition remove_all :: "vname set \<Rightarrow> tab \<Rightarrow> tab" where
  "remove_all vs t = (\<lambda>m. if (m \<in> vs)
    then None
    else if (t m \<in> Some ` vs)
      then None
      else t m)"

text \<open>
  Prove the following lemmas.
\<close>

lemma "ran (remove x t) = ran t - {x}"
proof (auto simp add: remove_def ran_def)
  fix xa a
  assume "xa \<noteq> x" "t a = Some xa"
  then have "t a \<noteq> Some x \<and> (t a \<noteq> Some x \<longrightarrow> t a = Some xa)" by auto
  then show "\<exists>a. t a \<noteq> Some x \<and> (t a \<noteq> Some x \<longrightarrow> t a = Some xa)" by blast
qed

lemma "ran (remove_all S t) \<subseteq> -S"
  by (auto simp add: remove_all_def ran_def)

lemma "dom (remove_all S t) \<subseteq> -S"
  by (auto simp add: remove_all_def dom_def)

lemma remove_all_update[simp]:
"remove_all {x} (t (x:= y)) = remove_all {x} t"
  by (auto simp add: remove_all_def)

lemma remove_all_remove[simp]:
"remove_all {x} (remove x t) = remove_all {x} t"
  by (auto simp add: remove_all_def remove_def)

lemma remove_all_Un[simp]:
"remove_all A (remove_all B t) = remove_all (A \<union> B) t"
  by (intro ext, auto simp add: remove_all_def)

lemma remove_all_in_dom [simp]: "a \<in> A \<Longrightarrow> remove_all A t a = None"
  by (auto simp add: remove_all_def)

lemma remove_all_in_range [simp]: "t a \<in> Some ` A \<Longrightarrow> remove_all A t a = None"
  by (auto simp add: remove_all_def)

lemma remove_all_in_range_singleton [simp]: "remove_all {x} t a \<noteq> Some x"
  by (auto simp add: remove_all_def)

lemma remove_all_notin [simp]: "\<lbrakk>a \<notin> A; t a \<notin> Some ` A\<rbrakk> \<Longrightarrow> remove_all A t a = t a"
  by (auto simp add: remove_all_def)

lemma remove_all_map_le [intro]: "remove_all A t \<subseteq>\<^sub>m t"
  by (auto simp add: remove_all_def map_le_def split: if_split_asm)

lemma map_leD1 [dest]: "\<lbrakk>f \<subseteq>\<^sub>m g; f x = Some y\<rbrakk> \<Longrightarrow> g x = Some y"
  by (auto simp add: map_le_def Ball_def)

lemma map_leD2 [dest]: "\<lbrakk>f \<subseteq>\<^sub>m g; g x = None\<rbrakk> \<Longrightarrow> f x = None"
  by (auto simp add: map_le_def Ball_def)

lemma remove_all_map_le1 [dest]: "remove_all A t a = Some k \<Longrightarrow> t a = Some k"
  by (auto intro: map_leD1)

lemma remove_all_map_le2 [dest]: "t a = None \<Longrightarrow> remove_all A t a = None"
  by (auto intro: map_leD2)

lemma merge_in: "(merge t1 t2) x \<in> Some ` S \<Longrightarrow> t1 x \<in> Some ` S \<and> t2 x \<in> Some ` S"
  by (auto simp add: merge_def split: if_split_asm)

lemma remove_all_merge_in_range: "(merge t1 t2) x \<in> Some ` S \<Longrightarrow> remove_all S t1 x = None \<and> remove_all S t2 x = None"
  by (auto dest!: merge_in)

lemma remove_all_merge1_none [simp]: "remove_all S t1 x = None \<Longrightarrow> remove_all S (merge t1 t2) x = None"
  by (auto simp add: remove_all_def merge_def)

lemma remove_all_merge2_none [simp]: "remove_all S t2 x = None \<Longrightarrow> remove_all S (merge t1 t2) x = None"
  by (auto simp add: remove_all_def merge_def)

lemma merge_map_le1 [intro]: "merge t1 t2 \<subseteq>\<^sub>m t1"
  by (auto simp add: merge_def map_le_def)

lemma merge_map_le2 [intro]: "merge t1 t2 \<subseteq>\<^sub>m t2"
  by (auto simp add: merge_def map_le_def)

lemma merge_remove_all:
  assumes "remove_all S t1 = remove_all S t"
  assumes "remove_all S t2 = remove_all S t"
  shows "remove_all S (merge t1 t2) = remove_all S t"
proof
  fix x
  from assms(1) [THEN fun_cong, of x] assms(2) [THEN fun_cong, of x]
  show "remove_all S (merge t1 t2) x = remove_all S t x"
    by (auto simp add: remove_all_def merge_def split: if_split_asm)
qed

text \<open>
  \endexercise

  \exercise\label{exs:acopy}
  This is a more challenging exercise.
  Define and prove correct \emph{copy propagation}. Copy propagation is
similar to constant folding, but propagates the right-hand side of assignments
if these right-hand sides are just variables. For instance, the program
\texttt{x := y; z := x + z} will be transformed into
\texttt{x := y; z := y + z}.
The assignment \texttt{x := y} can then be eliminated in a liveness
analysis. Copy propagation is useful for cleaning up after other optimisation
phases.

  To do this, take the definitions for constant folding from theory
  @{text Fold} and adjust
  them to do copy propagation instead (without constant folding).
  Use the functions from \autoref{exs:remove} in your definition.
  The general proof idea and structure of constant folding remains
  applicable. Adjust it according to your new definitions.
\<close>

definition "approx t s \<longleftrightarrow> (\<forall>x k. t x = Some k \<longrightarrow> s x = s k)"

primrec acopy :: "aexp \<Rightarrow> tab \<Rightarrow> aexp" where
  "acopy (N n) _ = N n" |
  "acopy (V x) t = (case t x of None \<Rightarrow> V x | Some x' \<Rightarrow> V x')" |
  "acopy (Plus e1 e2) t = (Plus (acopy e1 t) (acopy e2 t))"

primrec bcopy :: "bexp \<Rightarrow> tab \<Rightarrow> bexp" where
  "bcopy (Bc v) _ = Bc v" |
  "bcopy (Not b) t = Not (bcopy b t)" |
  "bcopy (And b1 b2) t = And (bcopy b1 t) (bcopy b2 t)" |
  "bcopy (Less e1 e2) t = Less (acopy e1 t) (acopy e2 t)"

fun copy :: "com \<Rightarrow> tab \<Rightarrow> com" and
  defs :: "com \<Rightarrow> tab \<Rightarrow> tab" where
  "copy SKIP _ = SKIP" |
  "defs SKIP t = t" |
  "copy (x ::= a) t = (x ::= acopy a t)" |
  "defs (x ::= a) t = (case acopy a t of V x' \<Rightarrow> (remove_all {x} t) (x \<mapsto> x') | _ \<Rightarrow> remove_all {x} t)" |
  "copy (c1;; c2) t = (copy c1 t;; copy c2 (defs c1 t))" |
  "defs (c1;; c2) t = (defs c2 (defs c1 t))" |
  "copy (IF b THEN c1 ELSE c2) t = IF bcopy b t THEN copy c1 t ELSE copy c2 t" |
  "defs (IF b THEN c1 ELSE c2) t = merge (defs c1 t) (defs c2 t)" |
  "copy (WHILE b DO c) t = WHILE bcopy b (remove_all (lvars c) t) DO copy c (remove_all (lvars c) t)" |
  "defs (WHILE b DO c) t = remove_all (lvars c) t"

value "copy (''x'' ::= V ''y'';; ''z'' ::= Plus (V ''x'') (V ''z'')) Map.empty"

lemma approx_merge:
  "approx t1 s \<or> approx t2 s \<Longrightarrow> approx (merge t1 t2) s"
  by (fastforce simp: merge_def approx_def)

lemma approx_map_le:
  "approx t2 s \<Longrightarrow> t1 \<subseteq>\<^sub>m t2 \<Longrightarrow> approx t1 s"
  by (clarsimp simp: approx_def map_le_def dom_def)

theorem aval_acopy [simp]: "approx t s \<Longrightarrow> aval (acopy a t) s = aval a s"
  by (induct a) (auto simp add: approx_def split: aexp.split option.split)

lemma acopy_VD [dest]: "acopy a t = V x \<Longrightarrow> (a = V x \<and> t x = None) \<or> (\<exists> x'. a = V x' \<and> t x' = Some x)"
  by (cases a, auto split: option.split_asm)

lemma remove_all_lvars_defs: "remove_all (lvars c) (defs c t) = remove_all (lvars c) t"
proof (induct c arbitrary: t)
  case (Assign x1 x2)
  then show ?case by (auto split: aexp.split)
next
  case (Seq c1 c2)
  then show ?case
  proof (auto)
    assume H1: "\<And>t. remove_all (lvars c1) (defs c1 t) = remove_all (lvars c1) t"
    assume H2: "\<And>t. remove_all (lvars c2) (defs c2 t) = remove_all (lvars c2) t"
    have "remove_all (lvars c1 \<union> lvars c2) (defs c2 (defs c1 t)) =
      remove_all (lvars c1) (remove_all (lvars c2) (defs c2 (defs c1 t)))" by simp
    also from H2 have "\<dots> = remove_all (lvars c1) (remove_all (lvars c2) (defs c1 t))" by simp
    also have "\<dots> = remove_all (lvars c2 \<union> lvars c1) (defs c1 t)" by (simp add: Un_commute)
    also have "\<dots> = remove_all (lvars c2) (remove_all (lvars c1) (defs c1 t))" by simp
    also from H1 have "\<dots> = remove_all (lvars c2) (remove_all (lvars c1) t)" by simp
    also have "\<dots> = remove_all (lvars c1 \<union> lvars c2) t" by (simp add: Un_commute)
    finally show "remove_all (lvars c1 \<union> lvars c2) (defs c2 (defs c1 t)) = remove_all (lvars c1 \<union> lvars c2) t" .
  qed
next
  case (If x1 c1 c2)
  then show ?case
  proof (auto intro!: merge_remove_all)
    assume "\<And>t. remove_all (lvars c1) (defs c1 t) = remove_all (lvars c1) t"
    then have "remove_all (lvars c2) (remove_all (lvars c1) (defs c1 t)) = remove_all (lvars c2) (remove_all (lvars c1) t)" by simp
    then show "remove_all (lvars c1 \<union> lvars c2) (defs c1 t) = remove_all (lvars c1 \<union> lvars c2) t" by (simp add: Un_commute)
    assume "\<And>t. remove_all (lvars c2) (defs c2 t) = remove_all (lvars c2) t"
    then have "remove_all (lvars c1) (remove_all (lvars c2) (defs c2 t)) = remove_all (lvars c1) (remove_all (lvars c2) t)" by simp
    then show "remove_all (lvars c1 \<union> lvars c2) (defs c2 t) = remove_all (lvars c1 \<union> lvars c2) t" by simp
  qed
qed auto

lemma big_step_pres_approx: "\<lbrakk>(c, s) \<Rightarrow> s'; approx t s\<rbrakk> \<Longrightarrow> approx (defs c t) s'"
proof (induct c s s' arbitrary: t rule: big_step_induct)
  case (Assign x a s)
  then show ?case by (auto simp add: approx_def split: aexp.split)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case
  proof auto
    assume "approx t s\<^sub>1"
    moreover assume "\<And>t. approx t s\<^sub>1 \<Longrightarrow> approx (defs c t) s\<^sub>2"
    ultimately have "approx (defs c t) s\<^sub>2" by auto
    moreover assume "\<And>t. approx t s\<^sub>2 \<Longrightarrow> approx (remove_all (lvars c) t) s\<^sub>3"
    ultimately have "approx (remove_all (lvars c) (defs c t)) s\<^sub>3" by auto
    then show "approx (remove_all (lvars c) t) s\<^sub>3" by (simp add: remove_all_lvars_defs)
  qed
qed (auto intro: approx_map_le)

lemma big_step_pres_approx_remove_all_lvars:
  "(c, s) \<Rightarrow> s' \<Longrightarrow> approx (remove_all (lvars c) t) s \<Longrightarrow> approx (remove_all (lvars c) t) s'"
proof -
  assume "(c, s) \<Rightarrow> s'" "approx (remove_all (lvars c) t) s"
  then have "approx (defs c (remove_all (lvars c) t)) s'" by (simp add: big_step_pres_approx)
  then have "approx (remove_all (lvars c) (defs c (remove_all (lvars c) t))) s'" by (auto intro: approx_map_le)
  then have "approx (remove_all (lvars c) (remove_all (lvars c) t)) s'" by (simp add: remove_all_lvars_defs)
  then show "approx (remove_all (lvars c) t) s'" by simp
qed

theorem approx_bcopy [intro]: "approx t \<Turnstile> b <\<sim>> bcopy b t" by (induct b) (auto simp add: bequiv_up_to_def)

theorem copy_equiv: "approx t \<Turnstile> c \<sim> copy c t"
proof (induct c arbitrary: t)
case (Assign x1 x2)
  then show ?case
  proof (auto simp add: equiv_up_to_def)
    fix s :: state
    assume "approx t s"
    have "(x1 ::= acopy x2 t, s) \<Rightarrow> s(x1 := aval (acopy x2 t) s)" by auto
    with \<open>approx t s\<close> show "(x1 ::= acopy x2 t, s) \<Rightarrow> s(x1 := aval x2 s)" by auto
  qed
next
  case (Seq c1 c2)
  then show ?case by (auto intro!: equiv_up_to_seq big_step_pres_approx)
next
  case (If x1 c1 c2)
  then show ?case by (auto intro!: equiv_up_to_if_weak)
next
  case (While x1 c)
  moreover let ?tr = "remove_all (lvars c) t"
  have H1: "approx ?tr \<Turnstile> x1 <\<sim>> bcopy x1 ?tr" by auto
  moreover have H2: "\<And>s s'. \<lbrakk>(c, s) \<Rightarrow> s'; approx ?tr s; bval x1 s\<rbrakk> \<Longrightarrow> approx ?tr s'"
    by (auto intro: big_step_pres_approx_remove_all_lvars)
  ultimately have "approx ?tr \<Turnstile>
         WHILE x1 DO c \<sim> WHILE bcopy x1 ?tr DO copy c ?tr"
    by (auto intro!: equiv_up_to_while_weak)
  with While have Hweak: "approx t \<Turnstile> WHILE x1 DO c \<sim> WHILE bcopy x1 ?tr DO copy c ?tr"
    by (auto intro: equiv_up_to_weaken approx_map_le)
  show ?case
    by (auto intro: Hweak split: bexp.split)
qed auto

lemma approx_empty [simp]:
  "approx empty = (\<lambda>_. True)"
  by (auto simp: approx_def)

theorem "copy c empty \<sim> c"
  using copy_equiv [of empty c]
  by (simp add: equiv_up_to_True)

text \<open> \endexercise \<close>

end

