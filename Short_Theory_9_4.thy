theory Short_Theory_9_4 imports "HOL-IMP.Star" Complex_Main begin

datatype val = Iv int | Bv bool

type_synonym vname = string
type_synonym state = "vname \<Rightarrow> val"

datatype exp =  Ic int | Bc bool | V vname | Not exp | Plus exp exp | And exp exp | Less exp exp

inductive eval :: "exp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"eval (Ic i) _ (Iv i)" |
"eval (Bc v) _ (Bv v)" |
"eval (V x) s (s x)" |
"eval e s (Bv v) \<Longrightarrow> eval (Not e) s (Bv (\<not> v))" |
"\<lbrakk>eval a1 s (Iv i1); eval a2 s (Iv i2)\<rbrakk>
 \<Longrightarrow> eval (Plus a1 a2) s (Iv (i1 + i2))" |
"\<lbrakk>eval b1 s (Bv v1); eval b2 s (Bv v2)\<rbrakk>
 \<Longrightarrow> eval (And b1 b2) s (Bv (v1 \<and> v2))" |
"\<lbrakk>eval a1 s (Iv i1); eval a2 s (Iv i2)\<rbrakk>
 \<Longrightarrow> eval (Less a1 a2) s (Bv (i1 < i2))"

inductive_cases [elim!]:
  "eval (Ic i) s v"
  "eval (Bc bv) s v"
  "eval (V x) s v"
  "eval (Plus a1 a2) s v"
  "eval (And b1 b2) s v"
  "eval (Less a1 a2) s v"

datatype
  com = SKIP 
      | Assign vname exp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;; _"  [60, 61] 60)
      | If     exp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  exp com         ("WHILE _ DO _"  [0, 61] 61)

inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
  Assign: "eval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |
  Seq1: "(SKIP;; c, s) \<rightarrow> (c, s)" |
  Seq2: "(c1, s) \<rightarrow> (c1', s') \<Longrightarrow> (c1;; c2,s) \<rightarrow> (c1';; c2,s')" |
  IfTrue: "eval b s (Bv True) \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c1, s)" |
  IfFalse: "eval b s (Bv False) \<Longrightarrow> (IF b THEN c1 ELSE c2,s) \<rightarrow> (c2, s)" |
  While: "(WHILE b DO c, s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

datatype ty = Ity | Bty

type_synonym tyenv = "vname \<Rightarrow> ty"

inductive etyping :: "tyenv \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> Ic i : Ity" |
Bc_ty: "\<Gamma> \<turnstile> Bc r : Bty" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Plus a1 a2 : Ity" |
And_ty: "\<Gamma> \<turnstile> b1 : Bty \<Longrightarrow> \<Gamma> \<turnstile> b2 : Bty \<Longrightarrow> \<Gamma> \<turnstile> And b1 b2 : Bty" |
Less_ty: "\<Gamma> \<turnstile> a1 : Ity \<Longrightarrow> \<Gamma> \<turnstile> a2 : Ity \<Longrightarrow> \<Gamma> \<turnstile> Less a1 a2 : Bty"

declare etyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> V x : \<tau>" "\<Gamma> \<turnstile> Ic i : \<tau>" "\<Gamma> \<turnstile> Bc r : \<tau>" "\<Gamma> \<turnstile> Plus a1 a2 : \<tau>"
  "\<Gamma> \<turnstile> And b1 b2 : \<tau>" "\<Gamma> \<turnstile> Less a1 a2 : \<tau>"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma> x \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Seq_ty: "\<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> c1;; c2" |
If_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> c1 \<Longrightarrow> \<Gamma> \<turnstile> c2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c1 ELSE c2" |
While_ty: "\<Gamma> \<turnstile> b : Bty \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

declare ctyping.intros [intro!]
inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"  "\<Gamma> \<turnstile> c1;;c2"
  "\<Gamma> \<turnstile> IF b THEN c1 ELSE c2"
  "\<Gamma> \<turnstile> WHILE b DO c"

fun type :: "val \<Rightarrow> ty" where
  "type (Iv i) = Ity" |
  "type (Bv r) = Bty"

lemma type_eq_Ity [simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
  by (cases v) auto

lemma type_eq_Bty [simp]: "type v = Bty \<longleftrightarrow> (\<exists>b. v = Bv b)"
  by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> s \<longleftrightarrow> (\<forall>x. type (s x) = \<Gamma> x)"

lemma epreservation: "\<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> eval e s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
  by(induct arbitrary: v rule: etyping.induct) (fastforce simp: styping_def)+

lemma eprogress: "\<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. eval e s v"
proof(induct rule: etyping.induct)
  case (Plus_ty \<Gamma> a1 a2)
  then obtain v1 v2 where v: "eval a1 s v1" "eval a2 s v2" by blast
  with Plus_ty show ?case by (fastforce intro: eval.intros(5) dest!: epreservation)
next
  case (And_ty \<Gamma> b1 b2)
  thm eval.intros
  then obtain v1 v2 where v: "eval b1 s v1" "eval b2 s v2" by blast
  with And_ty show ?case by (fastforce intro: eval.intros(6) dest!: epreservation)
next
  case (Less_ty \<Gamma> a1 a2)
  then obtain v1 v2 where v: "eval a1 s v1" "eval a2 s v2" by blast
  with Less_ty show ?case by (fastforce intro: eval.intros(7) dest!: epreservation)
qed (auto intro: eval.intros)

theorem progress: "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c, s) \<rightarrow> cs'"
proof(induct rule: ctyping.induct)
  case Skip_ty thus ?case by simp
next
  case Assign_ty 
  thus ?case by (metis Assign eprogress)
next
  case Seq_ty thus ?case by simp (metis Seq1 Seq2)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where Heval: "eval b s bv" by (metis eprogress)
  with If_ty(1, 6) obtain b where Hb: "bv = Bv b" by (auto dest!: epreservation)
  show ?case
  proof (cases b)
    case True
    with Heval Hb show ?thesis by simp (metis IfTrue)
  next
    case False
    with Heval Hb show ?thesis by simp (metis IfFalse)
  qed
next
  case While_ty show ?case by (metis While)
qed

theorem styping_preservation: "(c, s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induct rule: small_step_induct)
  case Assign thus ?case
    by (auto simp: styping_def) (metis Assign(1,3) epreservation)
qed auto

theorem ctyping_preservation: "(c, s) \<rightarrow> (c', s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
by (induct rule: small_step_induct) (auto simp: ctyping.intros)

abbreviation small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

theorem type_sound: "(c, s) \<rightarrow>* (c', s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c', s') \<rightarrow> cs''"
  by (induction rule: star_induct)
    ((metis progress)?, metis styping_preservation ctyping_preservation)

end
